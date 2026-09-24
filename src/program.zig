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
pub fn execute(
    db: *database.Database,
    statements: []const input.Statement,
    source: ?Source,
    diagnostic: ?*parser.Diagnostic,
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
            .fact, .rule => {
                if (run == null) run = .{
                    .transaction = try transaction.Transaction.begin(db, .assertion),
                };
                const open = &run.?.transaction;
                const mark = open.savepoint();
                assert(open.target(), statement) catch |err| {
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
                var evaluation = try transaction.Transaction.begin(db, switch (statement) {
                    .query => .query,
                    else => .retraction,
                });
                defer evaluation.deinit();
                var result = try evaluate(&evaluation, statement);
                errdefer result.deinit();
                try evaluation.commit(result);
                last = result;
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
fn assert(db: *database.Database, statement: input.Statement) !void {
    switch (statement) {
        .fact => |fact| try addFact(db, fact),
        .rule => |rule| try addRule(db, rule),
        .query, .retraction => unreachable,
    }
}

pub fn addFact(db: *database.Database, fact: input.Relation) !void {
    const expression = try compile.compileRelation(db, fact.predicate, fact.terms, false);
    defer syntax.freeExpr(db.allocator, expression);
    try transaction.addFactExpr(db, expression);
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

fn evaluate(
    evaluation: *transaction.Transaction,
    statement: input.Statement,
) !results.ExecutionResult {
    const target = evaluation.target();
    const goals = switch (statement) {
        .query => |query| query.goals,
        .retraction => |goals| goals,
        .fact, .rule => unreachable,
    };
    const compiled = try compile.compileGoals(target, goals);
    defer {
        for (compiled) |clause| syntax.freeClauseTree(target.allocator, clause);
        target.allocator.free(compiled);
    }
    return switch (statement) {
        .query => |query| .{ .query = try transaction.queryClauses(target, compiled, query.order) },
        else => .{ .changed = try evaluation.retract(compiled) },
    };
}

/// Parses and runs a source program against `db`, which is what
/// `Jatalog.execute` does one layer up. Spelled out here so these tests need
/// nothing above this layer to build the database they run against.
fn runSource(db: *database.Database, text: []const u8) !results.ExecutionResult {
    const parsed = try parser.parseProgram(db.allocator, text, null);
    defer parsed.deinit();
    return execute(db, parsed.value.statements, null, null);
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
        execute(&db, &statements, null, &unlocated),
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
    ) }}, null, null);
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
