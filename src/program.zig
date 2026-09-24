//! Running statements against a database.
//!
//! A program is a sequence of `input.Statement`s, whether parsed from source
//! or built by hand. Each statement either commits completely or leaves the
//! database exactly as it was, so a failure part-way through keeps every
//! earlier statement and none of the failing one. This module compiles each
//! statement against the transaction it runs in, which is how a statement's
//! query-local names and values stay out of the committed database.

const std = @import("std");
const compile = @import("compile.zig");
const database = @import("database.zig");
const input = @import("input.zig");
const parser = @import("parser.zig");
const results = @import("results.zig");
const syntax = @import("syntax.zig");
const transaction = @import("transaction.zig");
const errors = @import("errors.zig");
const test_support = @import("test_support.zig");
const update = @import("update.zig");

/// The source a program was parsed from, so a statement that fails when it
/// runs can be pointed at.
pub const Source = struct {
    text: []const u8,
    /// One span per statement, as `parser.Program.spans`.
    spans: []const parser.Span,
};

/// The transaction a run of consecutive assertions shares.
///
/// `staged` is whether any of them has landed in it. A run whose very first
/// statement fails has staged nothing and is discarded rather than committed:
/// installing a copy holding exactly what the database already holds would
/// leave the database equal to itself but not identical, since the lazily
/// built caches it would come away with are the copy's rather than its own.
const Run = struct {
    transaction: transaction.Transaction,
    staged: bool = false,

    /// Commits what the run has staged, if anything, and ends it.
    fn close(run: *?Run) void {
        if (run.*) |*open| {
            if (open.staged) open.transaction.commitAssertions();
            open.transaction.deinit();
            run.* = null;
        }
    }
};

/// Runs `statements` in order, with a run of consecutive assertions sharing
/// one transaction, and returns the last statement's result.
///
/// Sharing is what makes loading facts affordable: a transaction clones the
/// database, and 2000 assertions with a transaction each copy 1,999,000 fact
/// entries between them. It changes nothing about what a statement promises.
/// A statement that fails inside a run is rolled back to its own savepoint and
/// the run it was in is committed without it, so a failure still leaves every
/// earlier statement and none of the failing one — including what the failing
/// one interned, which is observable rather than merely untidy, since a novel
/// ground structure joins the seed set of admissible structural recursion.
///
/// On failure `diagnostic`, if given, names the failing statement, and points
/// at it when `source` says where it was written.
///
/// The facts the statements assert are `contributor`'s, or the direct
/// contributor's when that is null (see "Contributor" in CONTEXT.md). Only
/// assertions are attributed: a retraction among the statements still takes
/// its facts from every contributor, in its place in the order, so
/// `p(a)~. p(a).` leaves `p(a)` asserted by `contributor` alone.
pub fn execute(
    db: *database.Database,
    statements: []const input.Statement,
    source: ?Source,
    diagnostic: ?*parser.Diagnostic,
    contributor: ?[]const u8,
) !results.ExecutionResult {
    var last: ?results.ExecutionResult = null;
    errdefer if (last) |*result| result.deinit();
    var run: ?Run = null;
    errdefer if (run) |*open| open.transaction.deinit();
    for (statements, 0..) |statement, index| {
        errdefer describe(diagnostic, source, index);
        if (last) |*result| result.deinit();
        last = null;
        switch (statement) {
            .fact, .rule, .schema => {
                if (run == null) run = .{
                    .transaction = try transaction.Transaction.begin(db),
                };
                const open = &run.?.transaction;
                const mark = open.savepoint();
                assert(open.target(), statement, contributor) catch |err| {
                    // The statements before this one are staged on the copy
                    // it has just been rolled back out of, so committing is
                    // what keeps them and drops it.
                    open.rollback(mark);
                    Run.close(&run);
                    return err;
                };
                run.?.staged = true;
                last = .none;
            },
            .query, .retraction => {
                Run.close(&run);
                last = try evaluate(db, statement);
            },
        }
    }
    Run.close(&run);
    return last orelse .none;
}

fn describe(diagnostic: ?*parser.Diagnostic, source: ?Source, index: usize) void {
    const out = diagnostic orelse return;
    if (source) |located| {
        out.* = .at(located.text, located.spans[index], index, null);
    } else {
        out.* = .{ .statement = index };
    }
}

/// Adds a fact or a rule to `db`, which is a transaction's staging copy.
/// Either it lands or `db` is left as it was, save for what compiling it
/// interned — which the caller's savepoint takes back out.
fn assert(db: *database.Database, statement: input.Statement, contributor: ?[]const u8) !void {
    switch (statement) {
        .fact => |fact| try addFact(db, fact, contributor),
        .rule => |rule| try addRule(db, rule),
        .schema => |declared| try declareSchema(db, declared),
        .query, .retraction => unreachable,
    }
}

/// Asserts `fact` on behalf of `contributor`, or of the direct contributor
/// when that is null.
pub fn addFact(db: *database.Database, fact: input.Relation, contributor: ?[]const u8) !void {
    const expression = try compile.compileRelation(db, fact.predicate, fact.terms, false);
    defer syntax.freeExpr(db.allocator, expression);
    try transaction.addFactExpr(db, expression, contributor);
}

pub fn declareSchema(db: *database.Database, declared: input.Schema) !void {
    const compiled = try compile.compileSchema(db, declared);
    const name = db.strings.intern(declared.predicate) catch |err| {
        compiled.deinit(db.allocator);
        return err;
    };
    try transaction.declareSchema(db, name, compiled);
}

pub fn addRule(db: *database.Database, rule: input.Rule) !void {
    const head = try compile.compileRelation(db, rule.head.predicate, rule.head.terms, false);
    var head_owned = true;
    defer if (head_owned) syntax.freeExpr(db.allocator, head);
    const body = try compile.compileGoals(db, rule.body);
    var body_owned = true;
    defer {
        if (body_owned) for (body) |clause| syntax.freeClauseTree(db.allocator, clause);
        db.allocator.free(body);
    }
    try transaction.addRuleClauses(db, head, body);
    head_owned = false;
    body_owned = false;
}

/// Runs a query or a retraction, each on a copy of `db` of its own, exactly
/// as `Jatalog.query` and `Jatalog.retract` do: see `transaction.query` and
/// `transaction.retract`, which is where the copy is made and its work
/// charged back.
fn evaluate(db: *database.Database, statement: input.Statement) !results.ExecutionResult {
    return switch (statement) {
        .query => |query| .{ .query = try transaction.query(db, query.goals, query.order) },
        .retraction => |goals| .{ .changed = try transaction.retract(db, goals) },
        .fact, .rule, .schema => unreachable,
    };
}

/// Parses and runs a source program against `db`, which is what
/// `Jatalog.execute` does one layer up. Spelled out here so these tests need
/// nothing above this layer to build the database they run against.
fn runSource(db: *database.Database, text: []const u8) !results.ExecutionResult {
    const parsed = try parser.parseProgram(db.allocator, text, null);
    defer parsed.deinit();
    return execute(db, parsed.value.statements, null, null, null);
}

test "a parse error after a query releases nothing because nothing ran" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db,
        \\p(a). p(X)?
        \\bad(X) :- q(X), X <>.
    ));
    try std.testing.expectEqual(@as(usize, 0), db.facts.len());
}

test "a semantic failure keeps earlier statements and names the failing one" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    const text =
        \\p(a). p(b).
        \\q(X).
        \\p(c).
    ;
    const parsed = try parser.parseProgram(std.testing.allocator, text, null);
    defer parsed.deinit();
    var diagnostic: parser.Diagnostic = .{};
    try std.testing.expectError(errors.Error.InvalidFact, execute(
        &db,
        parsed.value.statements,
        .{ .text = text, .spans = parsed.value.spans },
        &diagnostic,
        null,
    ));
    try std.testing.expectEqual(@as(usize, 2), db.facts.len());
    try std.testing.expectEqual(@as(?usize, 2), diagnostic.statement);
    try std.testing.expectEqual(@as(u32, 2), diagnostic.line);
    try std.testing.expectEqual(@as(u32, 1), diagnostic.column);
    try std.testing.expectEqual(@as(?[]const u8, null), diagnostic.expected);

    var unlocated: parser.Diagnostic = .{};
    const statements = [_]input.Statement{
        .{ .fact = input.fact("r", &.{input.atom("a")}) },
        .{ .query = .{ .goals = &.{input.relation("r", &.{input.variable("X")})} } },
        .{ .rule = input.rule(input.fact("h", &.{input.variable("Y")}), &.{
            input.relation("r", &.{input.variable("X")}),
        }) },
    };
    try std.testing.expectError(
        errors.Error.InvalidRule,
        execute(&db, &statements, null, &unlocated, null),
    );
    try std.testing.expectEqual(@as(?usize, 2), unlocated.statement);
    try std.testing.expectEqual(@as(?parser.Span, null), unlocated.span);
    try std.testing.expectEqual(@as(usize, 3), db.facts.len());
}

/// Checks that `variable` takes the values `expected` across the answers, in
/// the order the answers are listed.
fn expectColumn(result: *const results.ExecutionResult, variable: []const u8, expected: []const []const u8) !void {
    try std.testing.expectEqual(expected.len, result.query.answers.items.len);
    for (result.query.answers.items, expected) |*answer, value|
        try test_support.expectBindingValue(answer, variable, value);
}

test "answers list in the default answer order whatever order the facts arrived in" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\v(b, 2). v([a], 1). v(a, 3). v(10, 0). v(2.5, 9). v([], 4).
        \\v(X, N)?
    );
    defer result.deinit();
    try expectColumn(&result, "X", &.{ "2.5", "10", "a", "b", "[]", "[a]" });
}

test "sort keys order answers, and ties fall back to the default order" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var facts = try runSource(&db, "score(dan, 5). score(ann, 3). score(eve, 1). score(bob, 5). score(cat, 3).");
    facts.deinit();

    var descending = try runSource(&db, "score(P, S) order by S desc?");
    defer descending.deinit();
    try expectColumn(&descending, "P", &.{ "bob", "dan", "ann", "cat", "eve" });

    var mixed = try runSource(&db, "score(P, S) order by S, P desc?");
    defer mixed.deinit();
    try expectColumn(&mixed, "P", &.{ "eve", "cat", "ann", "dan", "bob" });

    // A repeated key only decides what the keys before it left tied, and the
    // same key never leaves anything tied.
    var repeated = try runSource(&db, "score(P, S) order by S desc, S?");
    defer repeated.deinit();
    try expectColumn(&repeated, "P", &.{ "bob", "dan", "ann", "cat", "eve" });

    // A hand-built statement carries the same keys the source does.
    const p = input.variable("P");
    const s = input.variable("S");
    var built = try execute(&db, &.{.{ .query = input.query(
        &.{input.relation("score", &.{ p, s })},
        &.{ input.ascending("S"), input.descending("P") },
    ) }}, null, null, null);
    defer built.deinit();
    try expectColumn(&built, "P", &.{ "eve", "cat", "ann", "dan", "bob" });
}

test "a sort key must name a variable the answers list" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var facts = try runSource(&db, "score(ann, 3). score(bob, 5).");
    facts.deinit();
    try std.testing.expectError(
        errors.Error.UnknownVariable,
        runSource(&db, "score(P, S) order by Q?"),
    );
    // A variable inside an aggregate's body is not one the answers list.
    try std.testing.expectError(
        errors.Error.UnknownVariable,
        runSource(&db, "score(P, S), setof(X, score(X, S), L) order by X?"),
    );
}

test "a statement that evaluates charges its work to the database, whatever becomes of its copy" {
    // A query and a retraction both evaluate on a copy that is never
    // committed, so a counter that went with the copy would report nothing
    // for either — and nothing is what a program used to report, while the
    // same statements issued through `query` and `retract` counted. See
    // "Evaluation work" in CONTEXT.md. No rule is involved, so none of this
    // is materialization, which happens on the database itself.
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var facts = try runSource(&db, "p(a). p(b). n(9223372036854775807).");
    facts.deinit();

    var work = db.eval.cost.work;
    var answered = try runSource(&db, "p(X)?");
    answered.deinit();
    try std.testing.expect(db.eval.cost.work > work);

    // A retraction naming nothing is evaluation and nothing else: no fact
    // reaches the update path to be charged there instead.
    work = db.eval.cost.work;
    var retracted = try runSource(&db, "p(c)~");
    defer retracted.deinit();
    try std.testing.expect(!retracted.changed);
    try std.testing.expect(db.eval.cost.work > work);

    // Failing does not take the work back: the lookup of `n` was done before
    // the addition overflowed.
    work = db.eval.cost.work;
    try std.testing.expectError(errors.Error.NumericOverflow, runSource(&db, "n(X), Y = X + 1?"));
    try std.testing.expect(db.eval.cost.work > work);
}

test "head tail patterns work in rules and cons syntax is equivalent" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\items(cons(a, cons(b, []))).
        \\tail(T) :- items(H!T).
        \\tail(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "[b]");
}

test "structural equality binds variables recursively and parse errors clean up" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db, "seed(a). seed(X), [X] = [a]?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));

    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db, "broken([a, [b])."));
}

test "negated built-ins evaluate as the source says" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\n(1). n(2). n(3).
        \\small(X) :- n(X), not X > 1.
        \\other(X) :- n(X), not X = 2.
        \\setof(X, small(X), S), setof(Y, other(Y), T)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[1]");
    try test_support.expectBindingValue(&result.query.answers.items[0], "T", "[1, 3]");
}

fn structuralAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\items([a, [b], c]).
        \\tail(T) :- items(H!T).
        \\tail([X, c])?
    );
    defer result.deinit();
    const value = try result.query.answers.items[0].getValue("X");
    const formatted = try value.formatAlloc(allocator);
    defer allocator.free(formatted);
    try std.testing.expectEqualStrings("[b]", formatted);
}

test "structural parsing and evaluation release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(structuralAllocationScenario);
}

/// Runs a query whose plan reads an aggregate and a negation, then explains
/// the same goals: planning and rendering a plan, under every allocation
/// failure.
fn planningAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var setup = try runSource(&db,
        \\edge(a, b). edge(b, c). node(a). node(b). node(c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\reach(X, S) :- node(X), setof(Y, path(X, Y), S).
    );
    setup.deinit();
    var result = try runSource(&db, "reach(a, S), not path(a, a)?");
    result.deinit();
    const explained = try transaction.explain(&db, &.{
        input.relation("reach", &.{ input.variable("X"), input.variable("S") }),
        input.not("path", &.{ input.variable("X"), input.variable("X") }),
    });
    allocator.free(explained);
}

test "planning and explaining release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(planningAllocationScenario);
}

fn aggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\seed(k).
        \\nested(S) :- seed(k), setof(T, (group(G), setof([Y, G], parent(G, Y), T)), S).
    );
    result.deinit();
    const malformed_source = "broken(S) :- seed(k), setof(X, (parent(X, Y), bad([Y])), S.";
    var malformed = runSource(&db, malformed_source) catch |err| switch (err) {
        errors.Error.InvalidSyntax => return,
        else => return err,
    };
    malformed.deinit();
    return error.ExpectedInvalidSyntax;
}

test "aggregate parser errors release all partial clause trees" {
    try test_support.expectEveryAllocationFailureReleased(aggregateAllocationScenario);
}

test "quoted numeric atoms remain distinct from numeric scalars" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db, "value(1). value('1'). value('1.0'). setof(X, value(X), S)?");
    defer result.deinit();
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[1, '1', '1.0']");

    var inequality = try runSource(&db, "1 = '1'?");
    defer inequality.deinit();
    try std.testing.expectEqual(@as(usize, 0), inequality.query.answers.items.len);

    var quoted_float = try runSource(&db, "1000 = '1e3'?");
    defer quoted_float.deinit();
    try std.testing.expectEqual(@as(usize, 0), quoted_float.query.answers.items.len);

    var nested = try runSource(&db, "nested([1]). nested(['1']). nested([1.0]). nested([1])?");
    defer nested.deinit();
    try std.testing.expectEqual(@as(usize, 1), nested.query.answers.items.len);

    var quoted_setof = try runSource(&db, "text('2.5'). text(2.5). setof(X, text(X), S)?");
    defer quoted_setof.deinit();
    try test_support.expectBindingValue(&quoted_setof.query.answers.items[0], "S", "[2.5, '2.5']");

    var arithmetic = try runSource(&db, "01 = +0 + 1?");
    defer arithmetic.deinit();
    try std.testing.expectEqual(@as(usize, 1), arithmetic.query.answers.items.len);

    try std.testing.expectError(errors.Error.NumericType, runSource(&db, "value(X), X < 2?"));
}

test "non-finite and malformed numeric source reports stable errors" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NumericOverflow, runSource(&db, "value(1e400)."));
    try std.testing.expectError(errors.Error.NumericOverflow, runSource(&db, "value(-1e400)."));
    try std.testing.expectError(errors.Error.NumericOverflow, runSource(&db, "value(2e308)."));

    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db, "value(1e)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db, "value(1e+)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db, "value(1.2.3)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db, "value(12abc)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, runSource(&db, "value(1.)."));

    var absent = try runSource(&db, "value(X)?");
    defer absent.deinit();
    try std.testing.expectEqual(@as(usize, 0), absent.query.answers.items.len);
}

test "float literals parse and integral values canonicalize to integers" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\value(2.5). value(0.5). value(-0.025). value(1.0).
        \\value(1). value(1e0). value(1e3). value(-0.0).
        \\value(0). value(1e-999).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "S",
        "[-0.025, 0, 0.5, 1, 2.5, 1000]",
    );

    var canonical = try runSource(&db, "nested([1.0]). nested([1])?");
    defer canonical.deinit();
    try std.testing.expectEqual(@as(usize, 1), canonical.query.answers.items.len);

    var integral = try runSource(&db, "value(X), X = 1e0?");
    defer integral.deinit();
    try std.testing.expectEqual(@as(usize, 1), integral.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 1),
        try integral.query.answers.items[0].getInteger("X"),
    );
}

test "float extremes format deterministically and round-trip" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\extreme(5e-324). extreme(2.2250738585072014e-308).
        \\extreme(1.7976931348623157e308). extreme(-1.7976931348623157e308).
        \\extreme(1e300).
        \\setof(X, extreme(X), S)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "S",
        "[-1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, 1e300, " ++
            "1.7976931348623157e308]",
    );

    for ([_][]const u8{
        "extreme(5e-324)?",
        "extreme(2.2250738585072014e-308)?",
        "extreme(1.7976931348623157e308)?",
        "extreme(-1.7976931348623157e308)?",
        "extreme(1e300)?",
    }) |query| {
        var ground = try runSource(&db, query);
        defer ground.deinit();
        try std.testing.expectEqual(@as(usize, 1), ground.query.answers.items.len);
    }

    var formatted = try runSource(&db, "half(0.5). half(X)?");
    defer formatted.deinit();
    const value = try formatted.query.answers.items[0].getValue("X");
    const spelled = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("0.5", spelled);
    try std.testing.expectEqual(results.ResultValue.Kind.float, value.kind());
    try std.testing.expectError(errors.Error.TypeMismatch, value.getInteger());
}

/// Runs `text` and discards what it returns, for statements run for their
/// effect.
fn runQuietly(db: *database.Database, text: []const u8) !void {
    var result = try runSource(db, text);
    result.deinit();
}

test "a schema rejects facts of the wrong arity or type and keeps the rest" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\schema age(Person: atom, Years: int).
        \\schema scores(atom, list(number)).
        \\age(alice, 36). age(bob, 1.0).
        \\scores(alice, [1, 2.5]). scores(bob, []).
    );
    try std.testing.expectEqual(@as(usize, 4), db.facts.len());
    const rejected = [_][]const u8{
        "age(carol, old).",
        "age(carol, 2.5).",
        "age(carol).",
        "age(carol, 1, 2).",
        "age(36, 36).",
        "scores(carol, [1, a]).",
        "scores(carol, 1).",
        "scores(carol, cons(1, 2)).",
    };
    for (rejected) |text|
        try std.testing.expectError(errors.Error.SchemaViolation, runQuietly(&db, text));
    try std.testing.expectEqual(@as(usize, 4), db.facts.len());
}

test "a typed predicate at the wrong arity is ill-typed wherever it is used" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db, "schema age(atom, int). age(alice, 36).");
    for ([_][]const u8{
        "age(X)?",
        "age(X)~",
        "young(X) :- age(X).",
        "age(X) :- person(X).",
        "p(X) :- person(X), not age(X).",
        "p(S) :- person(X), setof(A, age(A), S).",
    }) |text| try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, text));
    try std.testing.expectEqual(@as(usize, 0), db.eval.rules.items.len);
}

test "a goal the schema proves impossible is an error, not an empty answer" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db, "schema age(atom, int). schema named(atom). age(alice, 36).");
    for ([_][]const u8{
        "age(X, old)?",
        "age(7, Y)?",
        "age(X, Y), named(Y)?",
        "age(X, Y), Y = foo?",
        "age(X, Y), X < 3?",
        "age(X, [])?",
        "age(X, H!T)?",
        "age(X, old)~",
        "p(X) :- age(X, Y), Y : atom.",
    }) |text| try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, text));
}

test "a rule must prove its head fits, and a type test is how an untyped value does" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\schema tagged(atom).
        \\raw(a). raw(1). raw([b]).
    );
    try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, "tagged(X) :- raw(X)."));
    // A negated test filters, but proves nothing about what passes it.
    try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, "tagged(X) :- raw(X), not X : int."));
    var result = try runSource(&db,
        \\tagged(X) :- raw(X), X : atom.
        \\tagged(X)?
    );
    defer result.deinit();
    try expectColumn(&result, "X", &.{"a"});
}

test "types flow through equality, arithmetic, lists and setof" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\schema age(atom, int).
        \\schema next_age(atom, int).
        \\schema mean(atom, number).
        \\schema names(list(atom)).
        \\schema pair(list(int)).
        \\age(alice, 36). age(bob, 17).
        \\next_age(P, N) :- age(P, A), N = A + 1.
        \\mean(P, N) :- age(P, A), N = A + 0.5.
        \\names(S) :- setof(P, age(P, A), S).
        \\pair([A, B]) :- age(alice, A), age(bob, B).
    );
    // `+ 0.5` may leave the integers, and `setof` collects `list(int)`.
    try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, "next_age(P, N) :- age(P, A), N = A + 0.5."));
    try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, "names(S) :- setof(A, age(P, A), S)."));
    var result = try runSource(&db, "names(S)?");
    defer result.deinit();
    try expectColumn(&result, "S", &.{"[alice, bob]"});
}

test "structural recursion over a typed list checks its elements with a test" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\schema sum(list(int), int).
        \\sum([], 0).
    );
    // Nothing in the body says what the seed's head is.
    try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, "sum(H!T, N) :- sum(T, M), N = M + H."));
    var result = try runSource(&db,
        \\sum(H!T, N) :- sum(T, M), H : int, N = M + H.
        \\sum([1, 2, 3], N)?
    );
    defer result.deinit();
    try expectColumn(&result, "N", &.{"6"});
}

test "a schema can be declared over what fits it, and otherwise changes nothing" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\age(alice, 36). age(bob, old).
        \\adult(P) :- age(P, A).
    );
    try std.testing.expectError(errors.Error.SchemaViolation, runQuietly(&db, "schema age(atom, int)."));
    try std.testing.expectError(errors.Error.SchemaViolation, runQuietly(&db, "schema age(atom)."));
    try std.testing.expectEqual(@as(usize, 0), db.schemas.count());
    try runQuietly(&db, "age(bob, old)~");
    try runQuietly(&db, "schema age(atom, int).");
    try std.testing.expectEqual(@as(usize, 1), db.schemas.count());

    // A rule already there must fit too.
    try runQuietly(&db, "label(P, adult) :- adult(P).");
    try std.testing.expectError(errors.Error.IllTyped, runQuietly(&db, "schema label(atom, int)."));
    try std.testing.expectEqual(@as(usize, 1), db.schemas.count());
    try runQuietly(&db, "schema label(any, atom).");
}

test "a schema cannot change: the same one again is nothing, any other is a conflict" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\schema age(Person: atom, Years: int).
        \\schema age(Person: atom, Years: int).
    );
    for ([_][]const u8{
        "schema age(atom, int).",
        "schema age(Who: atom, Years: int).",
        "schema age(Person: atom, Years: number).",
        "schema age(Person: atom).",
    }) |text| try std.testing.expectError(errors.Error.SchemaConflict, runQuietly(&db, text));
    try std.testing.expectError(errors.Error.InvalidTerm, runQuietly(&db, "schema p(A: int, A: int)."));
}

test "a type test filters on the value's type" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db, "v(a). v(1). v(2.5). v([]). v([1, 2]). v([1, b]). v(cons(1, 2)).");
    const cases = [_]struct { []const u8, []const []const u8 }{
        .{ "v(X), X : atom?", &.{"a"} },
        .{ "v(X), X : int?", &.{"1"} },
        .{ "v(X), X : number?", &.{ "1", "2.5" } },
        .{ "v(X), X : list(int)?", &.{ "[]", "[1, 2]" } },
        .{ "v(X), X : list?", &.{ "[]", "[1, 2]", "[1, b]" } },
        .{ "v(X), not X : list?", &.{ "1", "2.5", "a", "cons(1, 2)" } },
    };
    for (cases) |case| {
        var result = try runSource(&db, case[0]);
        defer result.deinit();
        try expectColumn(&result, "X", case[1]);
    }
}

fn schemaAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var result = try runSource(&db,
        \\raw(a). raw(1).
        \\schema tagged(Name: atom).
        \\tagged(X) :- raw(X), X : atom.
        \\schema count(list(atom), int).
        \\count(S, N) :- setof(X, tagged(X), S), N = 0 + 1.
        \\tagged(X)?
    );
    result.deinit();
}

test "declaring and checking schemas release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(schemaAllocationScenario);
}

/// Runs one program's statements against `db`, then an update after the
/// closure exists, so that maintenance has something to maintain.
fn runMaintained(db: *database.Database, schemas: []const u8) !void {
    try runQuietly(db, schemas);
    try runQuietly(db,
        \\edge(a, b). edge(b, c). weight(a, 1). weight(b, 2).
        \\reach(X, Y) :- edge(X, Y).
        \\reach(X, Z) :- reach(X, Y), edge(Y, Z).
        \\heavier(X, N) :- weight(X, W), N = W + 1.
        \\targets(X, S) :- weight(X, W), setof(Y, reach(X, Y), S).
        \\reach(a, Y)?
    );
    try runQuietly(db, "edge(c, d). weight(c, 3). reach(X, Y)?");
    try runQuietly(db, "edge(a, b)~");
    try runQuietly(db, "targets(X, S)?");
}

test "schemas change nothing about how a program is maintained" {
    var untyped: database.Database = .init(std.testing.allocator);
    defer untyped.deinit();
    try runMaintained(&untyped, "");
    var typed: database.Database = .init(std.testing.allocator);
    defer typed.deinit();
    try runMaintained(&typed,
        \\schema edge(atom, atom).
        \\schema weight(atom, int).
        \\schema reach(atom, atom).
        \\schema heavier(atom, int).
        \\schema targets(atom, list(atom)).
    );
    try std.testing.expectEqual(@as(usize, 5), typed.schemas.count());
    // The retraction did reach incremental maintenance — delete-and-rederive
    // and a maintained aggregate group — rather than the stats being equal
    // because both are empty. Fact statements dirty the closure and rebuild
    // it lazily, which the stratum expansions count.
    const stats = typed.maintenanceStats();
    try std.testing.expect(stats.maintain_choices > 0);
    try std.testing.expect(stats.overdeleted_facts > 0);
    try std.testing.expect(stats.maintained_groups > 0);
    try std.testing.expect(stats.stratum_expansions > 1);
    try std.testing.expectEqual(untyped.maintenanceStats(), typed.maintenanceStats());
    try std.testing.expectEqual(untyped.eval.cost.work, typed.eval.cost.work);
    try std.testing.expectEqual(untyped.closure.?.len(), typed.closure.?.len());
    try test_support.expectClosureMatchesRebuild(&typed);
}

test "an aggregate round whose removals rebuild still installs its recomputed head" {
    // `cnt`'s stale tuple reaches `other` through negation, so the round's
    // removals fall back to a rebuild from `other`'s stratum. That rebuild
    // reuses `cnt`'s stratum as it stood, without the recomputed tuple, so the
    // round still has to stage it afterwards.
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\item(a). item(b). tag(t).
        \\cnt(S) :- setof(X, item(X), S).
        \\other(Y) :- tag(Y), not cnt(Y).
        \\cnt(S)?
    );
    try runQuietly(&db, "item(b)~");
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.maintained_groups);
    // Twice: the recomputed tuple reaches the same negation when it is
    // propagated, and that rebuild is what finally settles `other`.
    try std.testing.expectEqual(@as(usize, 2), stats.rebuild_fallbacks);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "an aggregate cascade outlasts a round whose removals rebuild" {
    // The round's stale `held` tuple reaches `other` through negation, so its
    // removals fall back to a rebuild, which recomputes `all` while `cnt`
    // holds no tuple at all. `held`'s recomputed tuple is a base fact already,
    // so staging skips it, and `cnt`'s is propagated without reaching any
    // negation — the round is `.rebuilt`, yet it leaves `all` stale for a
    // next round to recompute.
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\item(a). item(b). tag(t). held([a]).
        \\held(S) :- setof(X, item(X), S).
        \\cnt(S) :- setof(X, item(X), S).
        \\all(T) :- setof(S, cnt(S), T).
        \\other(Y) :- tag(Y), not held(Y).
        \\cnt(S)?
    );
    try runQuietly(&db, "item(b)~");
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.rebuild_fallbacks);
    try std.testing.expectEqual(@as(usize, 3), stats.maintained_groups);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "a rebuild starts low enough to recompute an aggregate the delta reached" {
    // The round's `cnt` tuples reach `other` through negation, the stale one
    // as it is removed and the recomputed one as it is propagated, so both
    // halves of the round fall back to a rebuild. `all` aggregates over `cnt`
    // a stratum below `other`, and a rebuild starting at `other` would reuse
    // it as it stood — and with `touched` emptied by the rebuild, no later
    // round would recompute it either. It is the second rebuild, the one the
    // additions fall back to, that settles what `all` ends up holding.
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\item(a). item(b). tag(t).
        \\cnt(S) :- setof(X, item(X), S).
        \\all(T) :- setof(S, cnt(S), T).
        \\other(Y) :- tag(Y), not cnt(Y), not all(Y).
        \\cnt(S)?
    );
    try runQuietly(&db, "item(b)~");
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "a retraction's rebuild starts low enough to recompute an aggregate over it" {
    // The same fault reached by a base delta's removals instead of an
    // aggregate round's additions: `item(b)` reaches `other` through
    // negation, and `cnt` aggregates over `item` strata below it. No round
    // follows a rebuild, so only the rebuild can recompute `cnt`.
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\item(a). item(b). tag(t).
        \\cnt(S) :- setof(X, item(X), S).
        \\all(T) :- setof(S, cnt(S), T).
        \\other(Y) :- tag(Y), not item(Y), not all(Y).
        \\cnt(S)?
    );
    try runQuietly(&db, "item(b)~");
    try std.testing.expectEqual(@as(usize, 1), db.maintenanceStats().rebuild_fallbacks);
    try test_support.expectClosureMatchesRebuild(&db);
}

/// Replaces what `contributor` asserts with the facts `text` states, as
/// `Jatalog.setContribution` does. Anything else `text` says is ignored.
fn contribute(db: *database.Database, contributor: []const u8, text: []const u8) !bool {
    const parsed = try parser.parseProgram(db.allocator, text, null);
    defer parsed.deinit();
    var facts: std.ArrayList(input.Relation) = .empty;
    defer facts.deinit(db.allocator);
    for (parsed.value.statements) |statement| switch (statement) {
        .fact => |fact| try facts.append(db.allocator, fact),
        else => {},
    };
    return transaction.contribute(db, contributor, facts.items);
}

/// Runs `text` with the facts it asserts attributed to `contributor`, as
/// `Jatalog.executeStatements` does.
fn runContributed(db: *database.Database, contributor: []const u8, text: []const u8) !void {
    const parsed = try parser.parseProgram(db.allocator, text, null);
    defer parsed.deinit();
    var result = try execute(db, parsed.value.statements, null, null, contributor);
    result.deinit();
}

/// Checks that `query`'s single variable `X` takes exactly `expected`.
fn expectAnswers(db: *database.Database, query: []const u8, expected: []const []const u8) !void {
    var result = try runSource(db, query);
    defer result.deinit();
    try expectColumn(&result, "X", expected);
}

test "a fact two contributors assert outlives either one withdrawing" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expect(try contribute(&db, "a.dl", "p(shared). p(mine)."));
    // Nothing new is present, but `b.dl` now holds `shared` up too.
    try std.testing.expect(!try contribute(&db, "b.dl", "p(shared)."));
    try expectAnswers(&db, "p(X)?", &.{ "mine", "shared" });

    try std.testing.expect(try contribute(&db, "a.dl", ""));
    try expectAnswers(&db, "p(X)?", &.{"shared"});
    try std.testing.expect(try contribute(&db, "b.dl", ""));
    try expectAnswers(&db, "p(X)?", &.{});
    // Withdrawn contributors leave nothing behind.
    try std.testing.expectEqual(@as(usize, 0), db.contributions.named.count());
    try std.testing.expectEqual(@as(usize, 0), db.contributions.supported());
    // And withdrawing one that asserts nothing changes nothing.
    try std.testing.expect(!try contribute(&db, "c.dl", ""));
}

test "contributors agree on sameness as scalar identity does" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expect(try contribute(&db, "ints.dl", "n(1). n([2])."));
    try std.testing.expect(!try contribute(&db, "floats.dl", "n(1.0). n([2.0]). n(1e0)."));
    try std.testing.expectEqual(@as(usize, 2), db.facts.len());
    try std.testing.expect(!try contribute(&db, "ints.dl", ""));
    try expectAnswers(&db, "n(X)?", &.{ "1", "[2]" });
    try std.testing.expect(try contribute(&db, "floats.dl", ""));
    try std.testing.expectEqual(@as(usize, 0), db.facts.len());
}

test "a long cons chain is the fact the list it spells is" {
    // 65 heads: one more than a chain a fixed-size walk of 64 would see whole.
    var chain: std.ArrayList(u8) = .empty;
    defer chain.deinit(std.testing.allocator);
    var list: std.ArrayList(u8) = .empty;
    defer list.deinit(std.testing.allocator);
    try chain.appendSlice(std.testing.allocator, "p(");
    try list.appendSlice(std.testing.allocator, "p([");
    for (0..65) |index| {
        try chain.print(std.testing.allocator, "e{d}!", .{index});
        try list.print(std.testing.allocator, "{s}e{d}", .{ if (index == 0) "" else ", ", index });
    }
    try chain.appendSlice(std.testing.allocator, "[]).");
    try list.appendSlice(std.testing.allocator, "]).");

    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expect(try contribute(&db, "list.dl", list.items));
    try std.testing.expect(!try contribute(&db, "chain.dl", chain.items));
    try std.testing.expect(!try contribute(&db, "list.dl", ""));
    try std.testing.expectEqual(@as(usize, 1), db.facts.len());
    try std.testing.expect(try contribute(&db, "chain.dl", ""));
    try std.testing.expectEqual(@as(usize, 0), db.facts.len());
}

test "a deletion takes a fact from every contributor until one asserts it again" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    _ = try contribute(&db, "a.dl", "p(a). p(b).");
    _ = try contribute(&db, "b.dl", "p(a). p(c).");
    try runQuietly(&db, "p(c).");

    try runQuietly(&db, "p(a)~");
    try expectAnswers(&db, "p(X)?", &.{ "b", "c" });
    // Neither contributor holds `a` up any more, so it stays gone however
    // they change around it.
    _ = try contribute(&db, "a.dl", "p(b).");
    try expectAnswers(&db, "p(X)?", &.{ "b", "c" });

    // A batch deletion is a deletion too, of the direct contributor's `c`
    // and `b.dl`'s alike.
    const expression = try compile.compileRelation(&db, "p", &.{input.atom("c")}, false);
    defer syntax.freeExpr(db.allocator, expression);
    try std.testing.expectEqual(@as(usize, 1), try update.apply(&db, .{ .named = &.{expression} }, &.{}));
    _ = try contribute(&db, "a.dl", "");
    try expectAnswers(&db, "p(X)?", &.{});

    // Asserting it again brings it back.
    try std.testing.expect(try contribute(&db, "b.dl", "p(a). p(c)."));
    try expectAnswers(&db, "p(X)?", &.{ "a", "c" });
}

test "a contribution that fails changes neither the facts nor any contribution" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db, "schema age(atom, int).");
    _ = try contribute(&db, "a.dl", "p(a). age(ann, 3).");
    _ = try contribute(&db, "b.dl", "p(a).");

    const facts = [_]input.Relation{
        input.fact("p", &.{input.atom("b")}),
        input.fact("p", &.{input.variable("X")}),
    };
    try std.testing.expectError(errors.Error.InvalidFact, transaction.contribute(&db, "a.dl", &facts));
    try std.testing.expectError(errors.Error.SchemaViolation, contribute(&db, "a.dl", "p(b). age(bob, old)."));
    try std.testing.expectError(errors.Error.SchemaViolation, contribute(&db, "c.dl", "age(bob, old)."));
    try expectAnswers(&db, "p(X)?", &.{"a"});
    try std.testing.expectEqual(@as(usize, 2), db.contributions.named.count());
    try std.testing.expectEqual(@as(usize, 2), db.contributions.supported());

    // `a.dl` still asserts what it did, and only that: withdrawing it keeps
    // the fact `b.dl` shares and takes the one it alone asserted.
    _ = try contribute(&db, "a.dl", "");
    try expectAnswers(&db, "p(X)?", &.{"a"});
    try expectAnswers(&db, "age(X, Y)?", &.{});
}

test "statements run for a contributor keep their order" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    _ = try contribute(&db, "other.dl", "p(a). p(b).");
    // The retraction takes `a` from `other.dl`, and the fact after it is the
    // file's own.
    try runContributed(&db, "file.dl", "p(a)~ p(a). p(b). p(b)~ p(c).");
    try expectAnswers(&db, "p(X)?", &.{ "a", "c" });
    // `b` was retracted after the file asserted it, so it is nobody's.
    _ = try contribute(&db, "other.dl", "");
    try expectAnswers(&db, "p(X)?", &.{ "a", "c" });
    _ = try contribute(&db, "file.dl", "");
    try expectAnswers(&db, "p(X)?", &.{});
}

test "a direct fact outlives a named contributor asserting it too" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    // Direct first, then named.
    try runQuietly(&db, "p(first).");
    _ = try contribute(&db, "a.dl", "p(first). p(second). p(third).");
    // Named first, then direct: the direct assertion is recorded although
    // the fact was already there.
    try runQuietly(&db, "p(second).");
    try std.testing.expect(try contribute(&db, "a.dl", ""));
    try expectAnswers(&db, "p(X)?", &.{ "first", "second" });
    // With no named contributor left, nothing is recorded at all.
    try std.testing.expectEqual(@as(usize, 0), db.contributions.supported());
}

test "a statement that fails under a contributor takes its record with it" {
    // A run of assertions shares one staging copy, and the failing statement
    // is rolled back out of it by savepoint: see `Database.rollback`, which
    // checks the records are where the savepoint left them.
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db, "schema age(atom, int).");
    try std.testing.expectError(
        errors.Error.SchemaViolation,
        runContributed(&db, "file.dl", "p(a). age(ann, 3). age(bob, old). p(b)."),
    );
    try expectAnswers(&db, "p(X)?", &.{"a"});
    try std.testing.expectEqual(@as(usize, 2), db.contributions.supported());
    _ = try contribute(&db, "file.dl", "");
    try std.testing.expectEqual(@as(usize, 0), db.facts.len());
}

fn contributionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\q(a).
        \\r(X) :- p(X), q(X).
        \\r(X)?
    );
    // Ends in a failing statement, so that the rollback runs too.
    runContributed(&db, "a.dl", "p(a). p(b). p(b)~ p(c). q(X).") catch |err| switch (err) {
        errors.Error.InvalidFact => {},
        else => return err,
    };
}

test "asserting for a contributor releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(contributionAllocationScenario);
}

fn replacementAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\p(a).
        \\r(X) :- p(X).
        \\r(X)?
    );
    _ = try contribute(&db, "a.dl", "p(a). p(b).");
    _ = try contribute(&db, "b.dl", "p(b). p(c).");
    _ = try contribute(&db, "a.dl", "p(c).");
    _ = try contribute(&db, "b.dl", "");
}

test "replacing a contribution releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(replacementAllocationScenario);
}

test "a replaced contribution maintains the closure a rebuild would hold" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try runQuietly(&db,
        \\reach(X, Y) :- edge(X, Y).
        \\reach(X, Z) :- reach(X, Y), edge(Y, Z).
        \\node(a). node(b). node(c). node(d).
        \\cut(X) :- node(X), not reach(a, X).
        \\out(X, S) :- node(X), setof(Y, reach(X, Y), S).
        \\reach(a, X)?
    );
    db.eval.cost.policy = .incremental;
    const steps = [_]struct { []const u8, []const u8 }{
        .{ "one.dl", "edge(a, b). edge(b, c)." },
        .{ "two.dl", "edge(b, c). edge(c, d)." },
        .{ "one.dl", "edge(a, b)." },
        .{ "two.dl", "edge(c, d). edge(b, a)." },
        .{ "one.dl", "" },
        .{ "two.dl", "" },
    };
    for (steps) |step| {
        const before = db.maintenanceStats().maintain_choices;
        if (try contribute(&db, step[0], step[1])) {
            // One decision per contribution that moved anything: the facts
            // that moved took the update path as one batch.
            try std.testing.expectEqual(before + 1, db.maintenanceStats().maintain_choices);
        }
        try std.testing.expect(db.canMaintain());
        try test_support.expectClosureMatchesRebuild(&db);
    }
    // Nothing reaches anything any more.
    try expectAnswers(&db, "cut(X)?", &.{ "a", "b", "c", "d" });
}
