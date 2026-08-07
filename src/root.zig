//! A small, embeddable Datalog engine modeled after Jatalog.
//!
//! This is the public interface: the database an embedder holds, and the names
//! it needs to use one. `Jatalog` owns the engine's state and exposes the
//! operations that change it; everything those operations are built from lives
//! below and is not re-exported. Nothing inside the engine imports this file,
//! which is what keeps the dependency graph pointing one way.

const std = @import("std");
const aggregate_view = @import("aggregate_view.zig");
const auxiliary_view = @import("auxiliary_view.zig");
const compile = @import("compile.zig");
const cost_model = @import("cost_model.zig");
const database = @import("database.zig");
const errors = @import("errors.zig");
const evaluator = @import("evaluator.zig");
const input_compiler = @import("input_compiler.zig");
const maintenance = @import("maintenance.zig");
const materialization = @import("materialization.zig");
const parser = @import("parser.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const scalar = @import("scalar.zig");
const statement = @import("statement.zig");
const update = @import("update.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");
const test_support = @import("test_support.zig");
const validation = @import("validation.zig");

/// Descriptors a caller builds facts, rules, and goals out of.
pub const input = @import("input.zig");

/// Re-exported so embedders name one error set, whichever layer produced it.
pub const Error = errors.Error;
pub const ResultValue = results.ResultValue;
pub const Answer = results.Answer;
pub const QueryResult = results.QueryResult;
pub const ExecutionResult = results.ExecutionResult;
/// Re-exported so callers select a policy without importing the model.
pub const MaintenancePolicy = cost_model.MaintenancePolicy;
pub const MaintenanceStats = database.MaintenanceStats;
pub const Statement = statement.Statement;

/// An embeddable Datalog database.
///
/// The engine's state is `state`, and every operation here is expressed in
/// terms of the layers that act on it. Those layers are not part of this
/// interface: an embedder drives the database through these methods, and a
/// statement front end additionally through `Statement`.
pub const Jatalog = struct {
    state: database.Database,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{ .state = .init(allocator) };
    }

    pub fn deinit(self: *Jatalog) void {
        self.state.deinit();
        self.* = undefined;
    }

    /// A copy sharing nothing with this one, so the two can be updated
    /// independently.
    pub fn clone(self: *const Jatalog) !Jatalog {
        return .{ .state = try self.state.clone() };
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const input.Term) !void {
        var staging = try self.state.clone();
        defer staging.deinit();
        const expression = try compile.compileRelation(&staging, predicate, terms, false);
        defer syntax.freeExpr(staging.allocator, expression);
        try statement.addFactExpr(&staging, expression);
        self.state.commit(&staging);
    }

    pub fn addRule(self: *Jatalog, head: input.Goal, body: []const input.Goal) !void {
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled_head = switch (head) {
            .relation => |relation| try compile.compileRelation(&staging, relation.predicate, relation.terms, false),
            else => return errors.Error.InvalidRule,
        };
        var head_owned = true;
        defer if (head_owned) syntax.freeExpr(staging.allocator, compiled_head);
        const compiled_body = try compile.compileGoals(&staging, body);
        var body_owned = true;
        defer {
            if (body_owned) for (compiled_body) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled_body);
        }
        try statement.addRuleClauses(&staging, compiled_head, compiled_body);
        head_owned = false;
        body_owned = false;
        self.state.commit(&staging);
    }

    pub fn query(self: *Jatalog, goals: []const input.Goal) !results.QueryResult {
        try materialization.ensureMaterialized(&self.state);
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        return statement.queryClauses(&staging, compiled);
    }

    pub fn retract(self: *Jatalog, goals: []const input.Goal) !bool {
        try materialization.ensureMaterialized(&self.state);
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        var removed = try statement.resolveRetraction(&staging, compiled);
        defer removed.deinit();
        if (removed.len() == 0) return false;
        try statement.commitRetraction(&self.state, &removed);
        return true;
    }

    /// Applies one batch of exact ground base-fact insertions and deletions
    /// with set semantics: re-inserting an existing fact and deleting an
    /// absent fact are no-ops.
    ///
    /// Against a clean materialized closure the batch may be maintained
    /// incrementally — insertions through the semi-naive delta engine,
    /// deletions through delete-and-rederive, followed by aggregate group
    /// maintenance — or the affected strata may be marked dirty and
    /// recomputed. Both produce the same database, so the choice is the cost
    /// model's unless `setMaintenancePolicy` pins it. Maintenance that
    /// reaches negation or an aggregate outside the maintainable class
    /// abandons the incremental path for a dirty-stratum rebuild.
    ///
    /// The batch commits atomically: any failure leaves the database
    /// unchanged. Returns whether the base fact set changed.
    pub fn applyChanges(
        self: *Jatalog,
        insertions: []const input.Relation,
        deletions: []const input.Relation,
    ) !bool {
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled_deletions = try compileRelations(&staging, deletions);
        defer freeRelations(staging.allocator, compiled_deletions);
        const compiled_insertions = try compileRelations(&staging, insertions);
        defer freeRelations(staging.allocator, compiled_insertions);
        const changed = try update.apply(
            &staging,
            .{ .named = compiled_deletions },
            compiled_insertions,
        ) > 0;
        try materialization.verifyShadow(&staging);
        if (changed) self.state.commit(&staging);
        return changed;
    }

    /// Brings the derived closure up to date now instead of at the next
    /// query. Maintenance is otherwise lazy: an update marks the affected
    /// strata and the next evaluation repairs them. Calling this on a
    /// database without rules is a no-op and allocates nothing.
    pub fn materialize(self: *Jatalog) !void {
        var staging = try self.state.clone();
        defer staging.deinit();
        try materialization.ensureMaterialized(&staging);
        try materialization.verifyShadow(&staging);
        self.state.commit(&staging);
    }

    /// Discards the derived closure and every auxiliary view and recomputes
    /// them from the current base facts and rules. This is the reference
    /// path incremental maintenance is checked against; it is always
    /// available and always correct, at the cost of full recomputation.
    pub fn rebuild(self: *Jatalog) !void {
        var staging = try self.state.clone();
        defer staging.deinit();
        if (staging.closure) |*closure| {
            closure.deinit();
            staging.closure = null;
        }
        materialization.dropAuxiliaryViews(&staging);
        staging.materialization = .uninitialized;
        try materialization.ensureMaterialized(&staging);
        self.state.commit(&staging);
    }

    /// Enables or disables shadow verification. When enabled, every
    /// maintained closure is compared against a fresh rebuild from the same
    /// base facts before the change is committed, and a disagreement is
    /// reported as `MaintenanceMismatch` with the database unchanged. This
    /// roughly doubles update cost and is intended for tests and debugging.
    pub fn setShadowVerification(self: *Jatalog, enabled: bool) void {
        self.state.shadow_verification = enabled;
    }

    /// Selects how updates bring the closure up to date. The default is
    /// `.automatic`; pin `.incremental` or `.recompute` when a caller needs
    /// one specific path regardless of cost.
    pub fn setMaintenancePolicy(self: *Jatalog, policy: cost_model.MaintenancePolicy) void {
        self.state.eval.cost.policy = policy;
    }

    /// Records how the maintained views are classified and how much work
    /// incremental maintenance has done. A view whose head retains every
    /// outer variable is self-maintainable in the sense of Chapter 5: its
    /// tuple belongs to exactly one group, so an update decides the tuple
    /// without consulting other derivations. A projected view needs the
    /// auxiliary view's derivation counts, and recomputing an aggregate
    /// member set always consults the closure.
    pub fn maintenanceStats(self: *const Jatalog) MaintenanceStats {
        return self.state.maintenanceStats();
    }

    pub fn execute(self: *Jatalog, source: []const u8) !results.ExecutionResult {
        var statement_parser: parser.Parser = .{ .jatalog = &self.state, .source = source };
        return statement_parser.executeAll();
    }
};

/// Compiles a batch's relation descriptors into expressions the update path
/// applies. Compilation belongs here rather than below because it is what
/// turns *descriptors* — this front end's input — into the engine's syntax;
/// the source front end arrives with expressions already.
fn compileRelations(db: *database.Database, relations: []const input.Relation) ![]syntax.Expr {
    const compiled = try db.allocator.alloc(syntax.Expr, relations.len);
    var built: usize = 0;
    errdefer {
        for (compiled[0..built]) |expression| syntax.freeExpr(db.allocator, expression);
        db.allocator.free(compiled);
    }
    for (relations, compiled) |relation, *slot| {
        slot.* = try compile.compileRelation(db, relation.predicate, relation.terms, false);
        built += 1;
    }
    return compiled;
}

fn freeRelations(allocator: std.mem.Allocator, compiled: []syntax.Expr) void {
    for (compiled) |expression| syntax.freeExpr(allocator, expression);
    allocator.free(compiled);
}

test {
    // Zig contributes a file's tests only once something has referenced the
    // file, and the interface above does not reference every module it is
    // built from. Naming them here is what puts their tests in this build; a
    // module left out still compiles and still passes, it just stops being
    // tested.
    _ = aggregate_view;
    _ = auxiliary_view;
    _ = compile;
    _ = cost_model;
    _ = database;
    _ = evaluator;
    _ = input_compiler;
    _ = maintenance;
    _ = relation_store;
    _ = scalar;
    _ = string_table;
    _ = syntax;
    _ = test_support;
    _ = validation;
}

/// Runs one source query and asserts how many answers it produces. This one
/// assertion needs `execute`, so unlike the rest of `test_support` it cannot
/// live below the interface.
fn expectAnswerCount(db: *Jatalog, source: []const u8, expected: usize) !void {
    var result = try db.execute(source);
    defer result.deinit();
    try std.testing.expectEqual(expected, result.query.answers.items.len);
}

test "string table maps strings to stable ids and back" {
    var table: string_table.StringTable = .init(std.testing.allocator);
    defer table.deinit();
    const alice = try table.intern("alice");
    try std.testing.expectEqual(alice, try table.intern("alice"));
    try std.testing.expectEqualStrings("alice", table.resolve(alice));
}

test "recursive query and numeric builtins" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\parent(alice, bob). parent(bob, carol).
        \\ancestor(X, Y) :- parent(X, Y).
        \\ancestor(X, Y) :- ancestor(X, Z), parent(Z, Y).
        \\ancestor(X, carol), X != carol?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
}

test "stratified negation and retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). employed(alice).
        \\idle(X) :- person(X), not employed(X).
        \\idle(X)?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();
    result = try db.execute("person(bob)~");
    defer result.deinit();
    try std.testing.expect(result.changed);
}

test "negative recursion is rejected" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NotStratified, db.execute(
        \\p(X) :- q(X).
        \\q(X) :- not p(X), seed(X).
    ));
}

test "repeated queries reuse the persistent closure without expansion" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try std.testing.expectEqual(@as(usize, 0), db.state.eval.expansions);

    try expectAnswerCount(&db, "path(a, X)?", 3);
    const after_first = db.state.eval.expansions;
    try std.testing.expect(after_first > 0);
    try std.testing.expect(db.state.materialization == .clean);

    for (0..3) |_| try expectAnswerCount(&db, "path(a, X)?", 3);
    var typed = try db.query(&.{input.relation("path", &.{
        input.atom("a"),
        input.variable("target"),
    })});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 3), typed.answers.items.len);
    try std.testing.expectEqual(after_first, db.state.eval.expansions);
}

test "persistent closure equals a fresh naive rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\blocked(c).
        \\open(X) :- path(a, X), not blocked(X).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    setup.deinit();
    try expectAnswerCount(&db, "numchildren(alice, 1)?", 1);
    try std.testing.expect(db.state.materialization == .clean);

    var staging = try db.clone();
    defer staging.deinit();
    var reference = try staging.state.facts.clone();
    defer reference.deinit();
    try staging.state.eval.expandNaive(&reference);
    try std.testing.expectEqual(reference.len(), db.state.closure.?.len());
    for (0..reference.len()) |index|
        try std.testing.expect(try db.state.closure.?.contains(reference.factAt(index)));
}

test "base updates and rule additions rebuild the closure correctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // A base insertion marks the closure dirty and the next query repairs it.
    var inserted = try db.execute("edge(c, d).");
    inserted.deinit();
    try std.testing.expect(db.state.materialization == .dirty_from_stratum);
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try std.testing.expect(db.state.materialization == .clean);

    // Retraction removes derived consequences through the dirty rebuild.
    var retracted = try db.execute("edge(a, b)~");
    retracted.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try expectAnswerCount(&db, "path(b, d)?", 1);

    // Typed updates take the same paths.
    try db.addFact("edge", &.{ input.atom("d"), input.atom("e") });
    try expectAnswerCount(&db, "path(b, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try expectAnswerCount(&db, "path(b, e)?", 0);

    // Rule addition invalidates from the new head's stratum.
    var extended = try db.execute("reach(X) :- path(b, X).");
    extended.deinit();
    try std.testing.expect(db.state.materialization == .dirty_from_stratum);
    try expectAnswerCount(&db, "reach(d)?", 1);
}

test "dirty stratum rebuild skips clean lower strata" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). flag(a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\note(X) :- flag(X), not path(a, X).
    );
    setup.deinit();
    // First materialization runs both strata.
    try expectAnswerCount(&db, "note(a)?", 1);
    const full_build = db.state.eval.expansions;
    try std.testing.expectEqual(@as(usize, 2), full_build);

    // Only the negation stratum reads flag, so its update rebuilds one level.
    var flagged = try db.execute("flag(c).");
    flagged.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 1, db.state.eval.expansions);

    // An edge update dirties the recursive stratum and rebuilds both levels.
    var edged = try db.execute("edge(c, d).");
    edged.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 3, db.state.eval.expansions);
}

test "a database without rules allocates no derived machinery" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    try expectAnswerCount(&db, "kept(1)?", 1);
    var typed = try db.query(&.{input.relation("kept", &.{input.variable("n")})});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 1), typed.answers.items.len);
    try std.testing.expect(db.state.closure == null);
    try std.testing.expect(db.state.materialization == .uninitialized);
    try std.testing.expect(db.state.eval.analysis == null);
    try std.testing.expectEqual(@as(usize, 0), db.state.eval.expansions);
}

fn materializationAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    );
    setup.deinit();
    var first = try db.execute("summary(S)?");
    first.deinit();
    var inserted = try db.execute("edge(c, d).");
    inserted.deinit();
    var second = try db.execute("path(a, d)?");
    second.deinit();
    var retracted = try db.execute("edge(c, d)~");
    retracted.deinit();
    var third = try db.execute("path(a, d)?");
    defer third.deinit();
    if (third.query.answers.items.len != 0) return error.UnexpectedAnswer;
}

test "materialization lifecycle releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(materializationAllocationScenario);
}

test "materialize rebuild and stats form the explicit maintenance API" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\group(g). member(g, m1).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();

    // Maintenance is lazy until asked: nothing is materialized yet.
    try std.testing.expect(db.state.closure == null);
    try std.testing.expectEqual(@as(usize, 0), db.maintenanceStats().closure_facts);

    try db.materialize();
    try std.testing.expect(db.state.materialization == .clean);
    const after_materialize = db.maintenanceStats();
    try std.testing.expect(after_materialize.closure_facts > 0);
    try std.testing.expectEqual(@as(usize, 0), after_materialize.rebuild_fallbacks);

    // materialize is idempotent and performs no further expansion.
    try db.materialize();
    try std.testing.expectEqual(
        after_materialize.stratum_expansions,
        db.maintenanceStats().stratum_expansions,
    );

    // rebuild recomputes from base facts and reproduces the same closure.
    try db.rebuild();
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_materialize.closure_facts, db.maintenanceStats().closure_facts);
    try test_support.expectClosureMatchesRebuild(&db.state);
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // The single-statement entry points keep working alongside the batch
    // API. Pattern retraction is not a subset of it: it deletes every base
    // fact matching a goal, which exact-fact batch deletion cannot express.
    try db.addFact("edge", &.{ input.atom("c"), input.atom("d") });
    try expectAnswerCount(&db, "path(a, d)?", 1);
    var executed = try db.execute("edge(d, e).");
    executed.deinit();
    try expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try expectAnswerCount(&db, "path(a, e)?", 0);

    // Retraction takes the same incremental deletion path as a batch, so
    // the closure stays clean and this materialize is a no-op.
    try std.testing.expect(db.state.materialization == .clean);
    const before_materialize = db.maintenanceStats();
    try db.materialize();
    try std.testing.expectEqual(
        before_materialize.stratum_expansions,
        db.maintenanceStats().stratum_expansions,
    );

    // An inserted edge derives new path facts through the delta engine.
    const before_edge = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
    try expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(db.maintenanceStats().propagated_facts > before_edge.propagated_facts);

    // An inserted member recomputes exactly the affected aggregate group.
    const before_member = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g"), input.atom("m2") }),
    }, &.{}));
    var collected = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&collected.query.answers.items[0], "S", "[m1, m2]");
    collected.deinit();
    try std.testing.expect(db.maintenanceStats().maintained_groups > before_member.maintained_groups);
    try test_support.expectClosureMatchesRebuild(&db.state);

    const before_delete = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }));
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try std.testing.expect(db.maintenanceStats().removed_facts > before_delete.removed_facts);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Every update category is accounted for by one of the documented
    // paths: incremental propagation, delete-and-rederive, or rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.propagated_facts > 0);
    try std.testing.expect(stats.removed_facts > 0);
    try std.testing.expectEqual(@as(usize, 1), stats.self_maintainable_views);
}

test "lists round trip through queries and nested terms unify structurally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\nested([a, [b, []]]).
        \\nested(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "[a, [b, []]]");
}

test "repeated variables inside structures enforce equality" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\pair([a, [a]]). pair([a, [b]]).
        \\pair([X, [X]])?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));
}

test "facts reject variables at every structural depth" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidFact, db.execute("bad([a, X])."));
    try std.testing.expectError(errors.Error.InvalidFact, db.execute("bad(a!T)."));

    var result = try db.execute("improper(a!b). improper(X)?");
    defer result.deinit();
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "cons(a, b)");
}

test "ground values have a deterministic structural total order" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\value(z). value(a). value('1'). value(-2). value(10). value(2). value([]).
        \\value([-1]). value(cons(a, z)). value([a]). value([a, b]).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "S",
        "[-2, 2, 10, '1', a, z, [], [-1], cons(a, z), [a], [a, b]]",
    );
}

test "correlated aggregate clauses parse and validate without evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). parent(alice, bob). passed(bob).
        \\children(X, S) :- person(X), setof([Y, X], (parent(X, Y), passed(Y)), S).
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.state.eval.rules.items.len);
    try std.testing.expect(db.state.eval.rules.items[0].body[0] == .relational);
    const aggregate = db.state.eval.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), aggregate.body.len);
    try std.testing.expect(aggregate.body[0] == .relational);
    try std.testing.expect(aggregate.body[1] == .relational);
}

test "rule bodies classify every clause kind distinctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(a).
        \\classified(X, S) :- seed(X), X = X, not blocked(X), setof(Y, item(X, Y), S).
    );
    defer result.deinit();
    const body = db.state.eval.rules.items[0].body;
    try std.testing.expect(body[0] == .relational);
    try std.testing.expect(body[1] == .builtin);
    try std.testing.expect(body[2] == .aggregate);
    try std.testing.expect(body[3] == .negated);
}

test "aggregate safety rejects unbound correlations and escaping locals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidRule, db.execute(
        "bad(X, S) :- setof(Y, parent(X, Y), S).",
    ));
    try std.testing.expectError(errors.Error.InvalidRule, db.execute(
        "bad(Y, S) :- seed(k), setof(Y, parent(X, Y), S).",
    ));
}

test "aggregate output binds head variables and aggregate locals stay local" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\all_parents(S) :- seed(k), setof([X, Y], parent(X, Y), S).
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.state.eval.rules.items.len);
}

test "nested aggregates are represented directly and validate recursively" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\grouped(S) :- seed(k), setof(T, (group(G), setof(Y, parent(G, Y), T)), S).
    );
    defer result.deinit();
    const outer = db.state.eval.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), outer.body.len);
    try std.testing.expect(outer.body[1] == .aggregate);
}

test "direct and indirect recursion through aggregation are rejected" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(errors.Error.NotStratified, direct.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, p(X), S).
    ));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(errors.Error.NotStratified, indirect.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, q(X), S).
        \\q(X) :- p(X).
    ));
}

test "positive recursion may complete below an aggregate stratum" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all_reachable(S) :- seed(k), setof([X, Y], reachable(X, Y), S).
    );
    defer result.deinit();
    var levels = try db.state.eval.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const reachable: relation_store.PredicateKey = .{ .name = db.state.strings.get("reachable").?, .arity = 2 };
    const all_reachable: relation_store.PredicateKey = .{ .name = db.state.strings.get("all_reachable").?, .arity = 1 };
    try std.testing.expectEqual(@as(usize, 0), levels.get(reachable).?);
    try std.testing.expectEqual(@as(usize, 1), levels.get(all_reachable).?);
}

test "negation and aggregate strict edges share one dependency graph" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(a). excluded(b).
        \\allowed(X) :- seed(X), not excluded(X).
        \\summary(S) :- seed(a), setof(X, allowed(X), S).
    );
    defer result.deinit();
    var levels = try db.state.eval.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const allowed: relation_store.PredicateKey = .{ .name = db.state.strings.get("allowed").?, .arity = 1 };
    const summary: relation_store.PredicateKey = .{ .name = db.state.strings.get("summary").?, .arity = 1 };
    try std.testing.expectEqual(@as(usize, 1), levels.get(allowed).?);
    try std.testing.expectEqual(@as(usize, 2), levels.get(summary).?);
}

test "grouped setof is sorted, deduplicated, and includes empty groups" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(bob). person(alice). parent(alice, carol). parent(alice, bob).
        \\from_left(X, Y) :- parent(X, Y).
        \\from_right(X, Y) :- parent(X, Y).
        \\child(X, Y) :- from_left(X, Y).
        \\child(X, Y) :- from_right(X, Y).
        \\children(X, S) :- person(X), setof(Y, child(X, Y), S).
        \\children(X, S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    for (result.query.answers.items) |*answer| {
        const person = try answer.getAtom("X");
        if (std.mem.eql(u8, person, "alice")) {
            try test_support.expectBindingValue(answer, "S", "[bob, carol]");
        } else if (std.mem.eql(u8, person, "bob")) {
            try test_support.expectBindingValue(answer, "S", "[]");
        } else return error.UnexpectedPerson;
    }
}

test "setof evaluates directly in queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("item(c). item(a). setof(X, item(X), S)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a, c]");
}

test "setof sees completed recursive strata and preserves structural templates" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all(S) :- seed(k), setof([Y, X], reachable(X, Y), S).
        \\all(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "S",
        "[[b, a], [c, a], [c, b], [d, a], [d, b], [d, c]]",
    );
}

test "nested and multiple setof goals evaluate from correlated bindings" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). group(g2). group(g1). item(g1, b). item(g1, a).
        \\summary(All, Groups) :- seed(k), setof(X, item(g1, X), All),
        \\  setof([G, S], (group(G), setof(X, item(G, X), S)), Groups).
        \\summary(All, Groups)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "All", "[a, b]");
    try test_support.expectBindingValue(&result.query.answers.items[0], "Groups", "[[g1, [a, b]], [g2, []]]");
}

test "setof recomputes after retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). item(b). item(a).
        \\items(S) :- seed(k), setof(X, item(X), S).
        \\item(b)~
    );
    result.deinit();
    result = try db.execute("items(S)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a]");
}

test "setof ordering is independent of insertion and rule order" {
    var first: Jatalog = .init(std.testing.allocator);
    defer first.deinit();
    var first_result = try first.execute(
        \\seed(k). base(c). base(a). base(b).
        \\value(X) :- base(X).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\values(S)?
    );
    defer first_result.deinit();

    var second: Jatalog = .init(std.testing.allocator);
    defer second.deinit();
    var second_result = try second.execute(
        \\base(b). base(c). base(a). seed(k).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\value(X) :- base(X).
        \\values(S)?
    );
    defer second_result.deinit();

    const first_value = try first_result.query.answers.items[0].getValue("S");
    const first_text = try first_value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(first_text);
    const second_value = try second_result.query.answers.items[0].getValue("S");
    const second_text = try second_value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(second_text);
    try std.testing.expectEqualStrings(first_text, second_text);
}

fn aggregateEvaluationAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\group(g1). group(g2). item(g1, b). item(g1, a).
        \\grouped(Groups) :- group(g1), setof([G, S], (group(G), setof(X, item(G, X), S)), Groups).
        \\grouped(Groups)?
    );
    defer result.deinit();
}

test "aggregate evaluation releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(aggregateEvaluationAllocationScenario);
}

fn floatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 1e-3). measure(c, 4.0).
        \\small(X) :- measure(X, V), V < 3.
        \\setof([X, V], measure(X, V), S)?
    );
    result.deinit();
    var overflow = db.execute("measure(d, 1e400).") catch |err| switch (err) {
        errors.Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "float parsing evaluation and overflow release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(floatAllocationScenario);
}

fn mixedArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 0.5).
        \\shifted(X, S) :- measure(X, V), S = V + 0.5.
        \\setof([X, S], shifted(X, S), Out)?
    );
    result.deinit();
    var overflow = db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
    ) catch |err| switch (err) {
        errors.Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "mixed arithmetic releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(mixedArithmeticAllocationScenario);
}

test "recursive list length and sum use checked integer arithmetic" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
        \\numbers([1, 2, 3]).
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\total(N) :- numbers(S), sum(S, N).
        \\numchildren(X, N)?
    );
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("total(N)?");
    try std.testing.expectEqual(@as(i64, 6), try result.query.answers.items[0].getInteger("N"));
    result.deinit();

    result = try db.execute("person(alice), 3 = 1 + 2, -2 = 1 - 3?");
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("person(alice), 4 = 1 + 2?");
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
    result.deinit();

    try std.testing.expectError(errors.Error.NumericType, db.execute("person(alice), N = nope + 1?"));
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.execute("person(alice), N = 9223372036854775807 + 1?"),
    );
}

test "ground list query inputs seed recursive evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var result = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([3, 3, 3], Total)?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try result.query.answers.items[0].getInteger("Total"));
    result.deinit();

    result = try db.execute(
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\length([a, b, c], Count)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 3), try result.query.answers.items[0].getInteger("Count"));

    const value_count_before_typed_query = db.state.eval.values.values.items.len;
    var query_result = try db.query(&.{input.relation("sum", &.{
        input.list(&.{ input.integer(4), input.integer(5) }),
        input.variable("total"),
    })});
    defer query_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), query_result.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try query_result.answers.items[0].getInteger("total"));
    try std.testing.expectEqual(value_count_before_typed_query, db.state.eval.values.values.items.len);

    var open_result = try db.execute("sum(Input, Total)?");
    defer open_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), open_result.query.answers.items.len);
    try test_support.expectBindingValue(&open_result.query.answers.items[0], "Input", "[]");
    try std.testing.expectEqual(@as(i64, 0), try open_result.query.answers.items[0].getInteger("Total"));

    var structural_result = try db.execute("Value = [a, b]?");
    defer structural_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), structural_result.query.answers.items.len);
    try test_support.expectBindingValue(&structural_result.query.answers.items[0], "Value", "[a, b]");
}

test "member and collectfirst are ordinary admissible list relations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items([a, b, c]).
        \\member(X, H!T) :- X = H.
        \\member(X, H!T) :- member(X, T).
        \\collectfirst([], []).
        \\collectfirst([H, K]!T, H!R) :- collectfirst(T, R).
        \\score(s1, 10). score(s2, 10). score(s3, 20). seed(k).
        \\bag(S) :- seed(k), setof([Score, Student], score(Student, Score), Pairs), collectfirst(Pairs, S).
        \\items(S), member(X, S)?
    );
    try std.testing.expectEqual(@as(usize, 3), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("bag(S)?");
    const value = try result.query.answers.items[0].getValue("S");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[10, 10, 20]", text);
    result.deinit();
}

test "structurally growing recursion is not admissible" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NotAdmissible, db.execute(
        \\q([X]) :- q(X).
    ));
}

test "non-recursive rules may construct structural head values" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\item(a).
        \\wrapped([X]) :- item(X).
        \\wrapped(Value)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "Value", "[a]");
}

test "structurally recursive rules retain their proven input seed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\base(a).
        \\p([a]).
        \\p(H!T) :- base(H), p(T).
        \\p(Value)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "Value", "[a]");
}

test "recursive arithmetic generators are not admissible" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(errors.Error.NotAdmissible, direct.execute(
        \\number(0).
        \\number(N) :- number(M), N = M + 1.
    ));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(errors.Error.NotAdmissible, indirect.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    ));
}

fn recursiveArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = db.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    ) catch |err| switch (err) {
        errors.Error.NotAdmissible => return,
        else => return err,
    };
    result.deinit();
    return error.ExpectedNotAdmissible;
}

test "recursive arithmetic rejection is allocation safe" {
    try test_support.expectEveryAllocationFailureReleased(recursiveArithmeticAllocationScenario);
}

test "embedding API constructs structural aggregate rules and queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("person", &.{input.atom("alice")});
    try db.addFact("person", &.{input.atom("bob")});
    try db.addFact("parent", &.{ input.atom("alice"), input.atom("bob") });

    const x = input.variable("x");
    const y = input.variable("y");
    const children = input.variable("children");
    const aggregate_body = [_]input.Goal{input.relation("parent", &.{ x, y })};
    try db.addRule(
        input.relation("children", &.{ x, children }),
        &.{
            input.relation("person", &.{x}),
            input.setof(y, &aggregate_body, children),
        },
    );

    var result = try db.query(&.{input.relation("children", &.{ x, children })});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.answers.items.len);
    for (result.answers.items) |*answer| {
        const person_name = try answer.getAtom("x");
        if (std.mem.eql(u8, person_name, "alice")) {
            try test_support.expectBindingValue(answer, "children", "[bob]");
        } else {
            try std.testing.expectEqualStrings("bob", person_name);
            try test_support.expectBindingValue(answer, "children", "[]");
        }
    }
}

test "typed nested setof matches source aggregate semantics" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("group", &.{input.atom("g1")});
    try db.addFact("group", &.{input.atom("g2")});
    try db.addFact("item", &.{ input.atom("g1"), input.atom("a") });

    const group = input.variable("group");
    const item = input.variable("item");
    const values = input.variable("values");
    const groups = input.variable("groups");
    const inner_body = [_]input.Goal{input.relation("item", &.{ group, item })};
    const outer_body = [_]input.Goal{
        input.relation("group", &.{group}),
        input.setof(item, &inner_body, values),
    };
    var result = try db.query(&.{input.setof(
        input.list(&.{ group, values }),
        &outer_body,
        groups,
    )});
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.answers.items[0],
        "groups",
        "[[g1, [a]], [g2, []]]",
    );
}

fn embeddedAggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("item", &.{input.atom("b")});
    try db.addFact("item", &.{input.atom("a")});

    const x = input.variable("x");
    const output = input.variable("output");
    const body = [_]input.Goal{input.relation("item", &.{x})};
    var result = try db.query(&.{input.setof(input.list(&.{x}), &body, output)});
    defer result.deinit();
    try test_support.expectBindingValue(&result.answers.items[0], "output", "[[a], [b]]");
}

test "embedding aggregate ownership is allocation safe" {
    try test_support.expectEveryAllocationFailureReleased(embeddedAggregateAllocationScenario);
}

test "aggregate retraction is correct across the complete language tour" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
        \\numchildren(X, N)?
    );
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("parent(alice, bob)~");
    try std.testing.expect(result.changed);
    result.deinit();

    result = try db.execute("children(alice, S), numchildren(alice, N)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[]");
    try std.testing.expectEqual(@as(i64, 0), try result.query.answers.items[0].getInteger("N"));
}

test "public errors distinguish each aggregation failure boundary" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidSyntax, db.execute("broken([a)."));
    try std.testing.expectError(
        errors.Error.InvalidRule,
        db.execute("bad(X, S) :- setof(Y, parent(X, Y), S)."),
    );
    try std.testing.expectError(
        errors.Error.NotStratified,
        db.execute("seed(k). cycle(S) :- seed(k), setof(X, cycle(X), S)."),
    );
    try std.testing.expectError(
        errors.Error.InvalidQuery,
        db.query(&.{input.add(input.variable("x"), input.variable("y"), input.integer(1))}),
    );
    try std.testing.expectError(errors.Error.NotAdmissible, db.execute("grow([X]) :- grow(X)."));
}

test "public source interface canonicalizes the complete i64 domain" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(0). number(-0). number(+0). number(00).
        \\number(1). number(01). number(+1).
        \\number(-9223372036854775808). number(9223372036854775807).
        \\setof(X, number(X), Values)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "Values",
        "[-9223372036854775808, 0, 1, 9223372036854775807]",
    );

    try std.testing.expectError(errors.Error.NumericOverflow, db.execute("number(9223372036854775808)."));
    try std.testing.expectError(errors.Error.NumericOverflow, db.execute("number(-9223372036854775809)."));
}

test "mixed numeric comparison and query-local float literals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var less = try db.execute("1.5 < 2?");
    defer less.deinit();
    try std.testing.expectEqual(@as(usize, 1), less.query.answers.items.len);

    var greater = try db.execute("2 < 1.5?");
    defer greater.deinit();
    try std.testing.expectEqual(@as(usize, 0), greater.query.answers.items.len);

    const scalar_count = db.state.eval.scalars.values.items.len;
    var bound = try db.execute("X = 2.5?");
    const spelled = try (try bound.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    bound.deinit();
    try std.testing.expectEqual(scalar_count, db.state.eval.scalars.values.items.len);
}

test "mixed arithmetic promotes to f64 and canonicalizes integral results" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var promoted = try db.execute("X = 1.5 + 1?");
    const spelled = try (try promoted.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    promoted.deinit();

    var integral = try db.execute("X = 1.5 + 2.5?");
    defer integral.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try integral.query.answers.items[0].getInteger("X"),
    );

    var negative = try db.execute("X = -0.5 - 0.5?");
    defer negative.deinit();
    try std.testing.expectEqual(
        @as(i64, -1),
        try negative.query.answers.items[0].getInteger("X"),
    );

    // Bound-output success, mismatch, and subtraction with both signs.
    try expectAnswerCount(&db, "4 = 1.5 + 2.5?", 1);
    try expectAnswerCount(&db, "5 = 1.5 + 2?", 0);
    try expectAnswerCount(&db, "-2.5 = -1.5 - 1?", 1);
    try expectAnswerCount(&db, "2.5 = 1 - -1.5?", 1);

    // Gradual underflow keeps exact subnormal results.
    try expectAnswerCount(
        &db,
        "1.1125369292536007e-308 = 2.2250738585072014e-308 - 1.1125369292536007e-308?",
        1,
    );
    try expectAnswerCount(&db, "0 = 5e-324 - 5e-324?", 1);

    // A mixed operation on an i64 extreme produces the rounded f64, which
    // stays a float because its integral value is outside the i64 range.
    var extreme = try db.execute("X = 9223372036854775807 + 0.5?");
    const extreme_spelled = try (try extreme.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(extreme_spelled);
    try std.testing.expectEqualStrings("9.223372036854776e18", extreme_spelled);
    extreme.deinit();

    try std.testing.expectError(errors.Error.NumericOverflow, db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
    ));
    try std.testing.expectError(errors.Error.NumericOverflow, db.execute(
        "N = -1.7976931348623157e308 - 1.7976931348623157e308?",
    ));
    try std.testing.expectError(errors.Error.NumericType, db.execute("N = nope + 0.5?"));

    // Integer-only overflow behavior is unchanged by promotion.
    try std.testing.expectError(errors.Error.NumericOverflow, db.execute(
        "N = 9223372036854775807 + 1?",
    ));
}

test "mixed equality and ordering are exact at numeric boundaries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    // Around 2^53: float literals canonicalize to their exact integer, so
    // nearby odd integers stay distinct.
    try expectAnswerCount(&db, "9007199254740993 > 9.007199254740992e15?", 1);
    try expectAnswerCount(&db, "9007199254740993 = 9.007199254740993e15?", 0);
    try expectAnswerCount(&db, "9007199254740992 = 9.007199254740992e15?", 1);

    // Both i64 limits against the adjacent representable floats.
    try expectAnswerCount(&db, "9223372036854775807 < 9.223372036854776e18?", 1);
    try expectAnswerCount(&db, "-9223372036854775808 = -9.223372036854775808e18?", 1);
    try expectAnswerCount(&db, "-9223372036854775807 > -9.223372036854776e18?", 1);

    // Adjacent representable floats around 1.
    try expectAnswerCount(&db, "1.0000000000000002 > 1?", 1);
    try expectAnswerCount(&db, "0.9999999999999999 < 1?", 1);
    try expectAnswerCount(&db, "1.0000000000000002 = 1?", 0);

    var ordered = try db.execute(
        \\near(0.9999999999999999). near(1). near(1.0000000000000002).
        \\setof(X, near(X), S)?
    );
    defer ordered.deinit();
    try test_support.expectBindingValue(
        &ordered.query.answers.items[0],
        "S",
        "[0.9999999999999999, 1, 1.0000000000000002]",
    );
}

test "canonical numeric identity holds inside lists and nested aggregates" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var dedup = try db.execute(
        \\one(1). one(1.0). one(01). one(1e0). one('1'). one('1.0').
        \\setof(X, one(X), S)?
    );
    defer dedup.deinit();
    try test_support.expectBindingValue(&dedup.query.answers.items[0], "S", "[1, '1', '1.0']");

    try expectAnswerCount(&db, "nested([1.0, 2.5]). nested([1, 2.5])?", 1);
    try expectAnswerCount(&db, "pair(cons(0.5, 1.0)). pair(cons(0.5, 1))?", 1);

    var grouped = try db.execute(
        \\kind(g). kind(h). item(g, 0.5). item(g, 1.0). item(g, 1). item(h, 2.5).
        \\grouped(Out) :- kind(g), setof([G, S], (kind(G), setof(V, item(G, V), S)), Out).
        \\grouped(Out)?
    );
    defer grouped.deinit();
    try test_support.expectBindingValue(
        &grouped.query.answers.items[0],
        "Out",
        "[[g, [0.5, 1]], [h, [2.5]]]",
    );

    var summed = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([1, 0.5, 2.5], Total)?
    );
    defer summed.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try summed.query.answers.items[0].getInteger("Total"),
    );
}

test "source and typed mixed numeric operations produce identical answers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute("measure(a, 2.5). measure(b, 3). measure(c, 0.5).");
    setup.deinit();

    const x = input.variable("x");
    const v = input.variable("v");
    const s = input.variable("s");
    const d = input.variable("d");
    var typed = try db.query(&.{
        input.relation("measure", &.{ x, v }),
        input.compare(.less_than, v, input.integer(3)),
        input.add(s, v, input.integer(1)),
        input.subtract(d, v, input.integer(2)),
    });
    defer typed.deinit();

    var source = try db.execute("measure(X, V), V < 3, S = V + 1, D = V - 2?");
    defer source.deinit();

    try std.testing.expectEqual(@as(usize, 2), typed.answers.items.len);
    try std.testing.expectEqual(
        typed.answers.items.len,
        source.query.answers.items.len,
    );
    for (typed.answers.items, source.query.answers.items) |*typed_answer, *source_answer| {
        for ([_][2][]const u8{
            .{ "v", "V" },
            .{ "s", "S" },
            .{ "d", "D" },
        }) |names| {
            const typed_value = try (try typed_answer.getValue(names[0]))
                .formatAlloc(std.testing.allocator);
            defer std.testing.allocator.free(typed_value);
            const source_value = try (try source_answer.getValue(names[1]))
                .formatAlloc(std.testing.allocator);
            defer std.testing.allocator.free(source_value);
            try std.testing.expectEqualStrings(source_value, typed_value);
        }
    }

    const typed_shifted = try (try typed.answers.items[0].getValue("s"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(typed_shifted);
    try std.testing.expectEqualStrings("3.5", typed_shifted);
}

test "typed float descriptors canonicalize and getters never coerce" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("measure", &.{ input.atom("a"), input.float(2.5) });
    try db.addFact("measure", &.{ input.atom("b"), input.float(1.0) });
    try db.addFact("measure", &.{ input.atom("c"), input.float(-0.0) });
    try db.addFact("items", &.{input.list(&.{ input.float(0.5), input.integer(2) })});

    var fractional = try db.query(&.{
        input.relation("measure", &.{ input.atom("a"), input.variable("v") }),
    });
    defer fractional.deinit();
    const value = try fractional.answers.items[0].getValue("v");
    try std.testing.expectEqual(results.ResultValue.Kind.float, value.kind());
    try std.testing.expectEqual(@as(f64, 2.5), try fractional.answers.items[0].getFloat("v"));
    try std.testing.expectError(errors.Error.TypeMismatch, fractional.answers.items[0].getInteger("v"));
    try std.testing.expectError(errors.Error.TypeMismatch, fractional.answers.items[0].getAtom("v"));
    try std.testing.expectError(errors.Error.UnknownVariable, fractional.answers.items[0].getFloat("missing"));

    // Integral typed floats canonicalize to integers, so the float getter
    // reports TypeMismatch and the integer getter succeeds.
    var canonical = try db.query(&.{
        input.relation("measure", &.{ input.atom("b"), input.variable("v") }),
    });
    defer canonical.deinit();
    try std.testing.expectEqual(@as(i64, 1), try canonical.answers.items[0].getInteger("v"));
    try std.testing.expectError(errors.Error.TypeMismatch, canonical.answers.items[0].getFloat("v"));

    // Identity across construction paths: source literals match typed facts.
    try expectAnswerCount(&db, "measure(a, 2.5)?", 1);
    try expectAnswerCount(&db, "measure(b, 1)?", 1);
    try expectAnswerCount(&db, "measure(c, 0)?", 1);
    try expectAnswerCount(&db, "items([0.5, 2])?", 1);

    // Typed retraction matches a fact added from source, and vice versa.
    var added = try db.execute("measure(d, 3.5).");
    added.deinit();
    try std.testing.expect(try db.retract(&.{
        input.relation("measure", &.{ input.atom("d"), input.float(3.5) }),
    }));
    try expectAnswerCount(&db, "measure(d, X)?", 0);
}

test "non-finite typed floats fail compilation transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const scalar_count = db.state.eval.scalars.values.items.len;
    const fact_count = db.state.facts.len();

    try std.testing.expectError(
        errors.Error.NumericType,
        db.addFact("bad", &.{input.float(std.math.nan(f64))}),
    );
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.addFact("bad", &.{input.float(std.math.inf(f64))}),
    );
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.addFact("bad", &.{input.float(-std.math.inf(f64))}),
    );
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.query(&.{input.relation("kept", &.{input.float(std.math.inf(f64))})}),
    );
    const v = input.variable("v");
    try std.testing.expectError(
        errors.Error.NumericType,
        db.addRule(
            input.relation("derived", &.{v}),
            &.{input.equal(v, input.float(std.math.nan(f64)))},
        ),
    );

    try std.testing.expectEqual(scalar_count, db.state.eval.scalars.values.items.len);
    try std.testing.expectEqual(fact_count, db.state.facts.len());
    try std.testing.expectEqual(@as(usize, 0), db.state.eval.rules.items.len);
    try expectAnswerCount(&db, "kept(1)?", 1);
    try expectAnswerCount(&db, "bad(X)?", 0);
}

fn typedFloatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("measure", &.{ input.atom("a"), input.float(2.5) });
    try db.addFact("measure", &.{ input.atom("b"), input.float(1.0) });
    var result = try db.query(&.{
        input.relation("measure", &.{ input.variable("x"), input.variable("v") }),
        input.compare(.less_than, input.variable("v"), input.integer(3)),
        input.add(input.variable("s"), input.variable("v"), input.float(0.25)),
    });
    result.deinit();
    db.addFact("bad", &.{input.float(std.math.inf(f64))}) catch |err| switch (err) {
        error.NumericOverflow => return,
        else => return err,
    };
    return error.ExpectedNumericOverflow;
}

test "typed float input releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(typedFloatAllocationScenario);
}

test "integer identity is exact above 2^53 and recursive inside lists" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(9007199254740992). number(9007199254740993).
        \\nested([9007199254740992]). nested([9007199254740993]).
        \\number(X), X = 9007199254740993?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740993),
        try result.query.answers.items[0].getInteger("X"),
    );
    result.deinit();

    result = try db.execute("nested([X]), X = 9007199254740992?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740992),
        try result.query.answers.items[0].getInteger("X"),
    );
}

test "numeric comparisons reject every nonnumeric ground value kind" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). seed(X), X < 1?"));
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). [] < 1?"));
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). [1] < 2?"));
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). cons(1, 2) < 3?"));
}

test "typed descriptors cover scalars lists rules builtins negation and retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("age", &.{ input.atom("alice"), input.integer(20) });
    try db.addFact("age", &.{ input.atom("bob"), input.integer(17) });
    try db.addFact("banned", &.{input.atom("bob")});
    try db.addFact("payload", &.{input.atom("123")});

    const person = input.variable("person");
    const age = input.variable("age");
    try db.addRule(
        input.relation("adult", &.{person}),
        &.{
            input.relation("age", &.{ person, age }),
            input.compare(.greater_or_equal, age, input.integer(18)),
            input.not("banned", &.{person}),
        },
    );

    var result = try db.query(&.{input.relation("adult", &.{person})});
    try std.testing.expectEqual(@as(usize, 1), result.answers.items.len);
    try std.testing.expectEqualStrings("alice", try result.answers.items[0].getAtom("person"));
    result.deinit();

    const head = input.atom("head");
    const tail = input.atom("tail");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    try db.addFact("improper", &.{input.cons(&pair)});
    result = try db.query(&.{input.relation("improper", &.{input.variable("value")})});
    try test_support.expectBindingValue(&result.answers.items[0], "value", "cons(head, tail)");
    result.deinit();

    try db.addFact("items", &.{input.list(&.{ input.integer(1), input.integer(2) })});
    const list_head = input.variable("list_head");
    const list_tail = input.variable("list_tail");
    const list_pair: input.Term.Cons = .{ .head = &list_head, .tail = &list_tail };
    try db.addRule(
        input.relation("tail", &.{list_tail}),
        &.{input.relation("items", &.{input.cons(&list_pair)})},
    );
    result = try db.query(&.{input.relation("tail", &.{input.variable("result")})});
    try test_support.expectBindingValue(&result.answers.items[0], "result", "[2]");
    result.deinit();

    try std.testing.expect(try db.retract(&.{input.relation("age", &.{
        input.atom("bob"),
        input.integer(17),
    })}));
    result = try db.query(&.{input.relation("age", &.{ input.atom("bob"), input.variable("n") })});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
}

test "typed equality inequality and arithmetic use canonical integer identity" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const value = input.variable("value");
    const sum = input.variable("sum");
    var result = try db.query(&.{
        input.equal(value, input.integer(1)),
        input.notEqual(value, input.integer(2)),
        input.add(sum, value, input.integer(2)),
        input.equal(sum, input.integer(3)),
    });
    defer result.deinit();
    try std.testing.expectEqual(@as(i64, 1), try result.answers.items[0].getInteger("value"));
    try std.testing.expectEqual(@as(i64, 3), try result.answers.items[0].getInteger("sum"));

    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.query(&.{input.add(
            sum,
            input.integer(std.math.maxInt(i64)),
            input.integer(1),
        )}),
    );
    try std.testing.expectError(
        errors.Error.NumericType,
        db.query(&.{input.subtract(sum, input.atom("one"), input.integer(1))}),
    );

    var difference = try db.query(&.{input.subtract(
        input.variable("difference"),
        input.integer(-2),
        input.integer(3),
    )});
    try std.testing.expectEqual(
        @as(i64, -5),
        try difference.answers.items[0].getInteger("difference"),
    );
    difference.deinit();

    var mismatch = try db.query(&.{input.add(input.integer(0), input.integer(1), input.integer(2))});
    try std.testing.expectEqual(@as(usize, 0), mismatch.answers.items.len);
    mismatch.deinit();
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.query(&.{input.subtract(
            sum,
            input.integer(std.math.minInt(i64)),
            input.integer(1),
        )}),
    );
}

test "malformed and cyclic typed descriptors are rejected transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.atom("yes")});

    var cyclic: input.Term = undefined;
    var pair: input.Term.Cons = .{ .head = &cyclic, .tail = &cyclic };
    cyclic = input.cons(&pair);
    try std.testing.expectError(errors.Error.InvalidTerm, db.addFact("broken", &.{cyclic}));

    var cyclic_items: [1]input.Term = undefined;
    cyclic_items[0] = input.list(&cyclic_items);
    try std.testing.expectError(errors.Error.InvalidTerm, db.addFact("broken", &cyclic_items));

    var cyclic_goals: [1]input.Goal = undefined;
    cyclic_goals[0] = input.setof(input.integer(1), &cyclic_goals, input.variable("values"));
    try std.testing.expectError(errors.Error.InvalidTerm, db.query(&cyclic_goals));

    try std.testing.expectError(errors.Error.InvalidTerm, db.addFact("", &.{input.atom("value")}));
    try std.testing.expectError(
        errors.Error.InvalidTerm,
        db.query(&.{input.relation("kept", &.{input.variable("")})}),
    );

    const shared_items = [_]input.Term{input.atom("shared")};
    const shared_list = input.list(&shared_items);
    try db.addFact("shared", &.{ shared_list, shared_list });

    var result = try db.query(&.{input.relation("kept", &.{input.variable("value")})});
    defer result.deinit();
    try std.testing.expectEqualStrings("yes", try result.answers.items[0].getAtom("value"));
}

test "query results own names scalars and structures after database destruction" {
    var db: Jatalog = .init(std.testing.allocator);
    var result = blk: {
        try db.addFact("answer", &.{input.list(&.{ input.atom("x"), input.integer(42) })});
        try db.addFact("scalars", &.{ input.atom("atom"), input.integer(7), input.float(2.5) });
        const query_result = try db.query(&.{
            input.relation("answer", &.{input.variable("value")}),
            input.relation("scalars", &.{
                input.variable("atom"),
                input.variable("integer"),
                input.variable("float"),
            }),
        });
        db.deinit();
        break :blk query_result;
    };
    defer result.deinit();

    const value = try result.answers.items[0].getValue("value");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[x, 42]", text);
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getAtom("value"));
    try std.testing.expectError(errors.Error.UnknownVariable, result.answers.items[0].getInteger("missing"));
    try std.testing.expectEqualStrings("atom", try result.answers.items[0].getAtom("atom"));
    try std.testing.expectEqual(@as(i64, 7), try result.answers.items[0].getInteger("integer"));
    try std.testing.expectEqual(@as(f64, 2.5), try result.answers.items[0].getFloat("float"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getInteger("atom"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getAtom("integer"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getFloat("integer"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getInteger("float"));
    try std.testing.expectEqualStrings("x", try (try value.head()).getAtom());
    try std.testing.expectEqual(@as(i64, 42), try (try (try value.tail()).head()).getInteger());
}

test "novel typed queries release all query-local storage" {
    var tracking = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    var db: Jatalog = .init(tracking.allocator());
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const persistent_bytes = tracking.allocated_bytes - tracking.freed_bytes;

    for (0..100) |index| {
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "novel_{d}", .{index});
        var result = try db.query(&.{input.relation("missing", &.{input.atom(novel)})});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        const novel = @as(f64, @floatFromInt(index)) + 0.5;
        var result = try db.query(&.{input.relation("missing", &.{input.float(novel)})});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "retract_{d}", .{index});
        try std.testing.expect(!try db.retract(&.{input.relation("missing", &.{
            input.variable(novel),
        })}));
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    try db.addFact("temporary", &.{input.integer(1)});
    try std.testing.expect(try db.retract(&.{input.relation("temporary", &.{
        input.variable("warmup"),
    })}));
    const retracted_bytes = tracking.allocated_bytes - tracking.freed_bytes;
    for (0..100) |index| {
        try db.addFact("temporary", &.{input.integer(1)});
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "changed_{d}", .{index});
        try std.testing.expect(try db.retract(&.{input.relation("temporary", &.{
            input.variable(novel),
        })}));
        try std.testing.expectEqual(
            retracted_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }
}

test "source statements are atomic while prior statements remain committed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.execute("kept(ok). rejected(9223372036854775808)."),
    );
    var result = try db.execute("kept(X)?");
    try std.testing.expectEqualStrings("ok", try result.query.answers.items[0].getAtom("X"));
    result.deinit();
    result = try db.execute("rejected(X)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
}

test "typed persistent operations roll back every allocation failure point" {
    var fact_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.addFact("added", &.{input.atom("fresh")});
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |_| {
            fact_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(fact_succeeded);

    var rule_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.addRule(
            input.relation("derived", &.{input.variable("x")}),
            &.{input.relation("kept", &.{input.variable("x")})},
        );
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |_| {
            rule_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var kept = try db.query(&.{input.relation("kept", &.{input.variable("x")})});
                defer kept.deinit();
                try std.testing.expectEqual(@as(i64, 1), try kept.answers.items[0].getInteger("x"));
                var absent = try db.query(&.{input.relation("derived", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(rule_succeeded);

    var retraction_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        try db.addFact("removed", &.{input.atom("value")});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.retract(&.{input.relation("removed", &.{input.variable("novel")})});
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |changed| {
            try std.testing.expect(changed);
            retraction_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var present = try db.query(&.{input.relation("removed", &.{input.variable("x")})});
                defer present.deinit();
                try std.testing.expectEqualStrings("value", try present.answers.items[0].getAtom("x"));
            },
            else => return err,
        }
    }
    try std.testing.expect(retraction_succeeded);
}

test "source persistent statements roll back every allocation failure point" {
    var observed_success = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.execute("added(fresh).");
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |result_value| {
            var result = result_value;
            result.deinit();
            observed_success = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(observed_success);
}

// ---------------------------------------------------------------------------
// Evaluation, maintenance and aggregate tests.
//
// These build their database from source, so they need the parser and the
// interface above it — which is above the modules they cover. They live here
// rather than in `evaluator.zig`, `maintenance.zig` and `aggregate_view.zig`
// so that those modules never import the interface built on top of them.
// ---------------------------------------------------------------------------

test "semi-naive and naive closures agree across rule classes" {
    // Non-recursive joins.
    var joins: Jatalog = .init(std.testing.allocator);
    defer joins.deinit();
    var joins_setup = try joins.execute(
        \\parent(a, b). parent(b, c). parent(c, d).
        \\grand(X, Z) :- parent(X, Y), parent(Y, Z).
    );
    joins_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&joins.state);

    // Direct recursion.
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    var direct_setup = try direct.execute(
        \\edge(a, b). edge(b, c). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    direct_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&direct.state);

    // Mutual recursion across two predicates in one stratum.
    var mutual: Jatalog = .init(std.testing.allocator);
    defer mutual.deinit();
    var mutual_setup = try mutual.execute(
        \\start(n0). step(n0, n1). step(n1, n2). step(n2, n3). step(n3, n4).
        \\even(X) :- start(X).
        \\even(X) :- odd(Y), step(Y, X).
        \\odd(X) :- even(Y), step(Y, X).
    );
    mutual_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&mutual.state);

    // Seeded structural recursion feeding a same-stratum consumer.
    var structural: Jatalog = .init(std.testing.allocator);
    defer structural.deinit();
    var structural_setup = try structural.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    structural_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&structural.state);

    // Stratified negation above a recursive stratum.
    var negated: Jatalog = .init(std.testing.allocator);
    defer negated.deinit();
    var negated_setup = try negated.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\reachable(X) :- edge(a, X).
        \\reachable(X) :- reachable(Y), edge(Y, X).
        \\isolated(X) :- node(X), not reachable(X).
    );
    negated_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&negated.state);

    // Aggregation over a recursive relation.
    var aggregated: Jatalog = .init(std.testing.allocator);
    defer aggregated.deinit();
    var aggregated_setup = try aggregated.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    );
    aggregated_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&aggregated.state);
}

test "multiple recursive body occurrences miss no derivations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(n1, n2). edge(n2, n3). edge(n3, n4). edge(n4, n5).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- path(X, Y), path(Y, Z).
    );
    setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&db.state);

    // The doubling rule needs delta joins on both occurrences: n1 to n5
    // only exists by combining two derived paths.
    try expectAnswerCount(&db, "path(n1, n5)?", 1);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
}

test "duplicate derivations create no duplicate facts or endless rounds" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // A diamond plus a cycle derives many facts through multiple proofs.
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&db.state);
    // Every node reaches every node exactly once in the answer set.
    try expectAnswerCount(&db, "path(X, Y)?", 16);
    try expectAnswerCount(&db, "path(a, d)?", 1);
}

test "indexed lookups match every structural binding pattern deterministically" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(a, c).
        \\holds([1, 2], a). holds([1, [2, 3]], b). holds(cons(1, 2), c). holds([], d).
        \\p(a). p(a, b).
    );
    setup.deinit();

    // Bound-position patterns over atoms.
    try expectAnswerCount(&db, "edge(a, X)?", 2);
    try expectAnswerCount(&db, "edge(X, Y)?", 3);
    try expectAnswerCount(&db, "edge(a, b)?", 1);
    try expectAnswerCount(&db, "edge(c, X)?", 0);

    // Answers arrive in fact insertion order.
    var ordered = try db.execute("edge(X, c)?");
    defer ordered.deinit();
    try std.testing.expectEqual(@as(usize, 2), ordered.query.answers.items.len);
    try std.testing.expectEqualStrings("b", try ordered.query.answers.items[0].getAtom("X"));
    try std.testing.expectEqualStrings("a", try ordered.query.answers.items[1].getAtom("X"));

    // Bound structural values: proper, nested, improper, and empty lists.
    var proper = try db.execute("holds([1, 2], X)?");
    defer proper.deinit();
    try std.testing.expectEqualStrings("a", try proper.query.answers.items[0].getAtom("X"));
    var nested = try db.execute("holds([1, [2, 3]], X)?");
    defer nested.deinit();
    try std.testing.expectEqualStrings("b", try nested.query.answers.items[0].getAtom("X"));
    var improper = try db.execute("holds(cons(1, 2), X)?");
    defer improper.deinit();
    try std.testing.expectEqualStrings("c", try improper.query.answers.items[0].getAtom("X"));
    var empty = try db.execute("holds([], X)?");
    defer empty.deinit();
    try std.testing.expectEqualStrings("d", try empty.query.answers.items[0].getAtom("X"));

    // A structural value bound through the second position.
    var reverse = try db.execute("holds(X, c)?");
    defer reverse.deinit();
    try test_support.expectBindingValue(&reverse.query.answers.items[0], "X", "cons(1, 2)");

    // A partially ground structure is unbound for indexing and still unifies.
    try expectAnswerCount(&db, "holds([1, T], X)?", 2);

    // One predicate name at two arities never shares matches.
    try expectAnswerCount(&db, "p(X)?", 1);
    try expectAnswerCount(&db, "p(X, Y)?", 1);

    // Retraction through the same lookup interface removes exactly one fact.
    var retract = try db.execute("edge(a, X)~");
    defer retract.deinit();
    try expectAnswerCount(&db, "edge(X, Y)?", 1);
    try expectAnswerCount(&db, "edge(b, c)?", 1);
}

test "stratification distinguishes predicate arities" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\p(a, b). seed(k).
        \\p(S) :- seed(k), setof([X, Y], p(X, Y), S).
        \\p(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[[a, b]]");
}
test "insert-only batches propagate incrementally and match full rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(n0, n1). edge(n1, n2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(n0, n2)?", 1);
    const expansions_after_build = db.state.eval.expansions;

    // Each batch extends the chain; the closure stays clean and matches a
    // full rebuild after every batch without any stratum expansion.
    var name_buffer: [16]u8 = undefined;
    var next_buffer: [16]u8 = undefined;
    for (2..6) |index| {
        const from = try std.fmt.bufPrint(&name_buffer, "n{d}", .{index});
        const to = try std.fmt.bufPrint(&next_buffer, "n{d}", .{index + 1});
        try std.testing.expect(try db.applyChanges(&.{
            input.fact("edge", &.{ input.atom(from), input.atom(to) }),
        }, &.{}));
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    try std.testing.expect(db.state.propagated_facts > 0);
    try expectAnswerCount(&db, "path(n0, n6)?", 1);
    try expectAnswerCount(&db, "path(X, Y)?", 21);
}

test "one inserted edge propagates each recursive consequence exactly once" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(X, Y)?", 6);

    // Inserting edge(d, e) derives exactly the four new paths a-e, b-e,
    // c-e, and d-e; each is propagated and counted exactly once.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
    try std.testing.expectEqual(@as(usize, 4), db.state.propagated_facts);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "duplicate base insertions produce no derived delta" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, b)?", 1);
    const closure_len = db.state.closure.?.len();
    const propagated = db.state.propagated_facts;

    try std.testing.expect(!try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }, &.{}));
    try std.testing.expectEqual(closure_len, db.state.closure.?.len());
    try std.testing.expectEqual(propagated, db.state.propagated_facts);
    try std.testing.expect(db.state.materialization == .clean);
}

test "propagation reaching negation or setof falls back to dirty rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(a, b). flag(a). flag(b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\note(X) :- flag(X), not path(a, X).
    );
    setup.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    const expansions_after_build = db.state.eval.expansions;

    // flag is only read positively, so its insertion propagates through the
    // negation stratum without any rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("flag", &.{input.atom("c")}),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "note(c)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // An edge insertion grows path, which the negation reads, so the
    // negation stratum rebuilds while the positive stratum stays
    // incremental.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build + 1, db.state.eval.expansions);
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "note(c)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "batch deletions and mixed batches maintain the closure correctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // Deleting an absent fact alone is a no-op that commits nothing.
    try std.testing.expect(!try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("x"), input.atom("y") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);

    // A mixed batch deletes one edge and inserts another as one transition.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
    }, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try expectAnswerCount(&db, "path(b, d)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expectError(errors.Error.InvalidFact, db.applyChanges(&.{
        input.fact("edge", &.{ input.variable("x"), input.atom("y") }),
    }, &.{}));
    try std.testing.expectError(errors.Error.InvalidFact, db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.variable("x"), input.atom("y") }),
    }));
}

test "over-deletion reaches a seeded rule fed by values from a higher stratum" {
    // `length` is a seeded structural rule: it is driven by the value table
    // rather than by a fact relation, so it sits in stratum zero while the
    // lists it consumes are interned by `collected` in a higher stratum. That
    // is the one case where a rule keeps deriving facts above its own stratum,
    // and it is why `expandLevel` and `propagateLevel` select rules with
    // `ruleActiveAt` while `overdeleteLevel` uses `ruleStratum`.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2).
        \\member(g1, a). member(g1, b). member(g2, c).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
    );
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "size(g1, 2)?", 1);

    // Removing a member shortens g1's list. The old list value stays interned,
    // so `length` keeps deriving its length — a rebuild does the same, because
    // the value table is monotone and nothing withdraws a structural value.
    // What must disappear is `size(g1, 2)`, whose support went with the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("b") }),
    }));
    try expectAnswerCount(&db, "size(g1, 2)?", 0);
    try expectAnswerCount(&db, "size(g1, 1)?", 1);
    try expectAnswerCount(&db, "size(g2, 1)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting the structural rule's own base case removes the whole chain,
    // and with it every `size`. Over-deletion cannot *build* `length(H!T, N)`
    // backwards from `length(T, M)` — nothing there names `H` — so it looks the
    // head up in the closure instead, and the stratum is maintained rather than
    // rebuilt.
    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try std.testing.expectEqual(before.rebuild_fallbacks, db.maintenanceStats().rebuild_fallbacks);
    try std.testing.expectEqual(before.stratum_expansions, db.state.eval.expansions);
    try std.testing.expect(db.maintenanceStats().removed_facts > before.removed_facts);
    try expectAnswerCount(&db, "size(G, N)?", 0);
    try expectAnswerCount(&db, "length(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "deleting a structural base case unwinds the whole chain incrementally" {
    // The shape M7 exists for: the deleted fact is the seeded rule's own base
    // case, so every derived length in the value table loses its support at
    // once. Over-deletion cannot build `length(H!T, N)` from `length(T, M)` —
    // nothing in that body names `H` — so it enumerates the head out of the
    // closure instead.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\chain([a, b, c]). chain([d]).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
    );
    setup.deinit();
    try db.materialize();
    // [a, b, c], [b, c], [c], [d] and [] are interned, and each has a length:
    // the base fact plus four derived.
    try expectAnswerCount(&db, "length(L, N)?", 5);

    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try expectAnswerCount(&db, "length(L, N)?", 0);
    const after = db.maintenanceStats();
    try std.testing.expectEqual(before.rebuild_fallbacks, after.rebuild_fallbacks);
    try std.testing.expectEqual(before.stratum_expansions, after.stratum_expansions);
    // The four derived lengths, and none of them rederivable.
    try std.testing.expectEqual(before.overdeleted_facts + 4, after.overdeleted_facts);
    try std.testing.expectEqual(before.rederived_facts, after.rederived_facts);
    // The removal count nets the base fact in with them.
    try std.testing.expectEqual(before.removed_facts + 5, after.removed_facts);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting a leaf instead of the base case is the other shape: putting the
    // base case back rebuilds the chain, and removing the fact that interned
    // the long list leaves the derived lengths standing, because the value
    // table is monotone and a rebuild keeps them too.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    }, &.{}));
    try expectAnswerCount(&db, "length(L, N)?", 5);
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("chain", &.{input.list(&.{input.atom("d")})}),
    }));
    try expectAnswerCount(&db, "length(L, N)?", 5);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a seeded rule whose body consumes the seed over-deletes correctly" {
    // `H` appears in the body as well as the head here, so the candidate head
    // has to be unified into the binding *before* the remaining goals run.
    // Solving `N = M + H` first would report UnboundVariable, which is the
    // defect that sent this whole class to the rebuild path.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\item([1, 2, 4]).
        \\total([], 0).
        \\total(H!T, N) :- total(T, M), N = M + H.
    );
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "total([1, 2, 4], 7)?", 1);

    const fallbacks_before = db.maintenanceStats().rebuild_fallbacks;
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("total", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try std.testing.expectEqual(fallbacks_before, db.maintenanceStats().rebuild_fallbacks);
    try expectAnswerCount(&db, "total(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a chain fact with an alternative proof survives its support's deletion" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\list([a, b]). list([q]). unit([q]).
        \\len([], 0).
        \\len(H!T, N) :- len(T, M), N = M + 1.
        \\len(H!T, N) :- unit(H!T), N = 1.
    );
    setup.deinit();
    try db.materialize();
    // [], [b], [a, b] and [q] all have lengths, and [q] has two proofs.
    try expectAnswerCount(&db, "len(L, N)?", 4);

    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("len", &.{ input.list(&.{}), input.integer(0) }),
    }));
    const after = db.maintenanceStats();
    try std.testing.expectEqual(before.rebuild_fallbacks, after.rebuild_fallbacks);
    // len([q], 1) is rederived from the unit rule; len([b], 1) and
    // len([a, b], 2) had only the chain, and go.
    try std.testing.expectEqual(before.overdeleted_facts + 3, after.overdeleted_facts);
    try std.testing.expectEqual(before.rederived_facts + 1, after.rederived_facts);
    try expectAnswerCount(&db, "len(L, N)?", 1);
    try expectAnswerCount(&db, "len([q], 1)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "several seeded occurrences and mutual seeded recursion over-delete each head once" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\list([a, b, c]).
        \\twice([], 0).
        \\twice(H!T, N) :- twice(T, M), twice(T, K), N = M + K.
        \\even([]).
        \\even(H!T) :- odd(T).
        \\odd(H!T) :- even(T).
    );
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "twice(L, N)?", 4);
    try expectAnswerCount(&db, "even(L)?", 2);
    try expectAnswerCount(&db, "odd(L)?", 2);

    // Both occurrences of `twice(T, _)` reach the same heads. `deleted` is a
    // set, so the second pinning finds each head already queued; a head taken
    // twice would double the removal count.
    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("twice", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try std.testing.expectEqual(before.rebuild_fallbacks, db.maintenanceStats().rebuild_fallbacks);
    try std.testing.expectEqual(
        before.removed_facts + 4,
        db.maintenanceStats().removed_facts,
    );
    try expectAnswerCount(&db, "twice(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // The mutually recursive pair shares one base case, and deleting it must
    // unwind both predicates. Their alternation crosses no stratum: mutual
    // recursion is one strongly connected component, so both rules are
    // over-deleted in the same level.
    const mutual_before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("even", &.{input.list(&.{})}),
    }));
    try std.testing.expectEqual(
        mutual_before.rebuild_fallbacks,
        db.maintenanceStats().rebuild_fallbacks,
    );
    try expectAnswerCount(&db, "even(L)?", 0);
    try expectAnswerCount(&db, "odd(L)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

/// Deletes a structural base case incrementally, which is the path that
/// enumerates head candidates out of the closure and unwinds the chain.
fn seededDeletionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\chain([a, b]).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\longest(N) :- length(L, N), N > 1.
    );
    setup.deinit();
    try db.materialize();
    _ = try db.applyChanges(&.{}, &.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    });
    var result = try db.execute("length(L, N)?");
    defer result.deinit();
    if (result.query.answers.items.len != 0) return error.UnexpectedAnswer;
}

test "seeded over-deletion releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(seededDeletionAllocationScenario);
}

test "randomized structural deletions match a clean rebuild under shadow verification" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\tag(t).
        \\box(k1, [a, b]). box(k2, [c]).
        \\len([], 0).
        \\len(H!T, N) :- len(T, M), N = M + 1.
        \\size(K, N) :- box(K, L), len(L, N).
        \\big(K) :- size(K, N), N > 1.
        \\quiet(K) :- box(K, L), not big(K).
        \\spread(S) :- tag(t), setof(N, size(K, N), S).
    );
    setup.deinit();
    try db.materialize();

    const keys = [_][]const u8{ "k1", "k2", "k3" };
    const lists = [_][]const input.Term{
        &.{ input.atom("a"), input.atom("b") },
        &.{input.atom("c")},
        &.{ input.atom("d"), input.atom("e"), input.atom("f") },
    };
    var prng = std.Random.DefaultPrng.init(0x5eeded5eeded);
    const random = prng.random();
    for (0..30) |step| {
        var box_terms: [2]input.Term = .{
            input.atom(keys[random.uintLessThan(usize, keys.len)]),
            input.list(lists[random.uintLessThan(usize, lists.len)]),
        };
        var base_terms: [2]input.Term = .{ input.list(&.{}), input.integer(0) };
        var inserts: [2]input.Relation = undefined;
        var deletes: [2]input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (random.boolean()) {
            inserts[insert_count] = input.fact("box", &box_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("box", &box_terms);
            delete_count += 1;
        }
        // Toggling the seeded rule's base case is what drives the whole chain
        // in and out of the closure.
        if (step % 3 == 0) {
            if (random.boolean()) {
                inserts[insert_count] = input.fact("len", &base_terms);
                insert_count += 1;
            } else {
                deletes[delete_count] = input.fact("len", &base_terms);
                delete_count += 1;
            }
        }
        // Shadow verification asserts rebuild equality inside the call.
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

test "deleting the only base support removes the entire unsupported cycle" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    // The full cycle reaches every node from every node.
    try expectAnswerCount(&db, "path(X, Y)?", 9);
    const expansions_after_build = db.state.eval.expansions;

    // After deleting edge(a, b) the cyclically self-supporting facts such
    // as path(a, a) must all disappear; reference counts alone would keep
    // them alive. The deletion is incremental: no stratum expansion runs.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    try std.testing.expect(db.state.removed_facts > 0);
    try expectAnswerCount(&db, "path(a, a)?", 0);
    try expectAnswerCount(&db, "path(X, Y)?", 3);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "alternative recursive and non-recursive derivations preserve facts" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\marked(a).
        \\special(X) :- marked(X).
        \\special(X) :- path(X, d).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try expectAnswerCount(&db, "special(b)?", 1);

    // path(a, d) survives the deletion through the c branch of the diamond,
    // while path(b, d) and with it special(b) lose their only test_support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("d") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try expectAnswerCount(&db, "special(b)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // special(a) loses its non-recursive derivation but survives through
    // the recursive path(a, d) alternative.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("marked", &.{input.atom("a")}),
    }));
    try expectAnswerCount(&db, "special(a)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a deletion falling back to rebuild leaves the batch's insertions a clean closure" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
    );
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "isolated(b)?", 0);

    // Deleting the edge over-deletes path(a, b), which reaches `isolated`
    // through negation and forces delete-and-rederive to abandon the
    // incremental path. The insertion in the same batch then has to find a
    // clean closure to propagate into: the fallback repairs the closure
    // through `ensureMaterialized` rather than leaving it dirty, which is
    // the invariant `applyInsertions` asserts.
    const before = db.maintenanceStats().rebuild_fallbacks;
    try std.testing.expect(try db.applyChanges(
        &.{input.fact("edge", &.{ input.atom("b"), input.atom("c") })},
        &.{input.fact("edge", &.{ input.atom("a"), input.atom("b") })},
    ));
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before);

    try expectAnswerCount(&db, "isolated(b)?", 1);
    try expectAnswerCount(&db, "path(b, c)?", 1);
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "adding and removing a fact toggles negation-dependent conclusions" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\item(a). item(b).
        \\blocked(b).
        \\allowed(X) :- item(X), not blocked(X).
    );
    setup.deinit();
    try expectAnswerCount(&db, "allowed(a)?", 1);
    try expectAnswerCount(&db, "allowed(b)?", 0);

    try std.testing.expect(try db.applyChanges(&.{
        input.fact("blocked", &.{input.atom("a")}),
    }, &.{}));
    try expectAnswerCount(&db, "allowed(a)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("blocked", &.{input.atom("a")}),
    }));
    try expectAnswerCount(&db, "allowed(a)?", 1);
    try expectAnswerCount(&db, "allowed(b)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "projection counts change without prematurely deleting supported tuples" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\holds(a, b1). holds(a, b2).
        \\present(X) :- holds(X, Y).
    );
    setup.deinit();
    try expectAnswerCount(&db, "present(a)?", 1);
    const present_id = db.state.strings.get("present").?;
    const support_before = blk: {
        for (0..db.state.closure.?.len()) |index| {
            const fact = db.state.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.state.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_before >= 2);

    // Removing one of two supports keeps the tuple with changed test_support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("holds", &.{ input.atom("a"), input.atom("b1") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "present(a)?", 1);
    const support_after = blk: {
        for (0..db.state.closure.?.len()) |index| {
            const fact = db.state.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.state.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_after != support_before);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Removing the last support deletes the tuple.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("holds", &.{ input.atom("a"), input.atom("b2") }),
    }));
    try expectAnswerCount(&db, "present(a)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "random mixed update traces match a clean rebuild after every batch" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e).
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
        \\summary(S) :- node(a), setof([X, Y], path(X, Y), S).
    );
    setup.deinit();
    try expectAnswerCount(&db, "summary(S)?", 1);

    const names = [_][]const u8{ "a", "b", "c", "d", "e" };
    var prng = std.Random.DefaultPrng.init(0x5eed5eed5eed5eed);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [3][2]input.Term = undefined;
        var inserts: [3]input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            insert_buffer[slot] = .{
                input.atom(names[random.uintLessThan(usize, names.len)]),
                input.atom(names[random.uintLessThan(usize, names.len)]),
            };
            inserts[slot] = input.fact("edge", &insert_buffer[slot]);
        }
        var delete_buffer: [3][2]input.Term = undefined;
        var deletes: [3]input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            delete_buffer[slot] = .{
                input.atom(names[random.uintLessThan(usize, names.len)]),
                input.atom(names[random.uintLessThan(usize, names.len)]),
            };
            deletes[slot] = input.fact("edge", &delete_buffer[slot]);
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

test "retraction maintains the closure incrementally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a). edge(x, y).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "path(X, Y)?", 10);
    const after_build = db.maintenanceStats();

    // A typed retraction runs delete-and-rederive rather than dirtying the
    // stratum, so no rule expansion happens and the closure stays clean.
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("x"), input.atom("y") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().removed_facts > after_build.removed_facts);
    try expectAnswerCount(&db, "path(x, y)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Retracting the only base support of a cycle removes the whole
    // unsupported cycle, still without a rebuild.
    const before_cycle = db.maintenanceStats();
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("c"), input.atom("a") }),
    }));
    try std.testing.expectEqual(before_cycle.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "path(a, a)?", 0);
    try expectAnswerCount(&db, "path(a, c)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "pattern retraction removes every matching fact incrementally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(a, d). edge(b, e).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // One goal with a variable retracts all three outgoing edges of a.
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("a"), input.variable("target") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "edge(a, X)?", 0);
    try expectAnswerCount(&db, "path(a, X)?", 0);
    try expectAnswerCount(&db, "path(b, e)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Source-level retraction takes the same path.
    const before_source = db.maintenanceStats();
    var retracted = try db.execute("edge(b, e)~");
    retracted.deinit();
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(before_source.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "path(X, Y)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "retraction maintains aggregate groups and negation strata" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a). member(g1, b). member(g2, z).
        \\banned(g2).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\allowed(G) :- group(G), not banned(G).
    );
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // Retracting a member updates only the affected group's list.
    try std.testing.expect(try db.retract(&.{
        input.relation("member", &.{ input.atom("g1"), input.atom("a") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().maintained_groups > after_build.maintained_groups);
    var collected = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&collected.query.answers.items[0], "S", "[b]");
    collected.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Retracting the last member leaves the enumerated group empty.
    try std.testing.expect(try db.retract(&.{
        input.relation("member", &.{ input.atom("g1"), input.atom("b") }),
    }));
    var emptied = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Retracting a negated predicate is the documented rebuild category.
    const before_negation = db.maintenanceStats();
    try expectAnswerCount(&db, "allowed(g2)?", 0);
    try std.testing.expect(try db.retract(&.{
        input.relation("banned", &.{input.atom("g2")}),
    }));
    try expectAnswerCount(&db, "allowed(g2)?", 1);
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before_negation.rebuild_fallbacks);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

fn retractionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, c). group(g). member(g, m1). member(g, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    try db.materialize();
    _ = try db.retract(&.{
        input.relation("edge", &.{ input.atom("a"), input.variable("target") }),
    });
    _ = try db.retract(&.{
        input.relation("member", &.{ input.atom("g"), input.atom("m1") }),
    });
    var result = try db.execute("collected(g, S)?");
    defer result.deinit();
    const formatted = try (try result.query.answers.items[0].getValue("S")).formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[m2]")) return error.UnexpectedAggregate;
}

test "incremental retraction releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(retractionAllocationScenario);
}

/// Runs one deterministic update trace under a fixed policy and returns the
/// materialized database for comparison.
fn batchUpdateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    var first = try db.execute("path(a, c)?");
    first.deinit();
    _ = try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
    }, &.{});
    _ = try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    });
    var second = try db.execute("path(b, e)?");
    defer second.deinit();
    if (second.query.answers.items.len != 1) return error.UnexpectedAnswer;
}

test "batch updates roll back completely on failure" {
    try test_support.expectEveryAllocationFailureReleased(batchUpdateAllocationScenario);
}

fn runPolicyTrace(db: *Jatalog, policy: cost_model.MaintenancePolicy) !void {
    db.setMaintenancePolicy(policy);
    var setup = try db.execute(
        \\node(a). node(b). node(c). group(g1). group(g2).
        \\edge(a, b). member(g1, m1). member(g2, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\isolated(X) :- node(X), not path(a, X).
    );
    setup.deinit();
    try db.materialize();

    const nodes = [_][]const u8{ "a", "b", "c" };
    const groups = [_][]const u8{ "g1", "g2" };
    const members = [_][]const u8{ "m1", "m2", "m3" };
    var prng = std.Random.DefaultPrng.init(0xc05715c05715);
    const random = prng.random();
    for (0..40) |step| {
        var edge_terms: [2]input.Term = .{
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
        };
        var member_terms: [2]input.Term = .{
            input.atom(groups[random.uintLessThan(usize, groups.len)]),
            input.atom(members[random.uintLessThan(usize, members.len)]),
        };
        if (step % 4 == 3) {
            // Exercise pattern retraction as well as the batch API.
            _ = try db.retract(&.{input.relation("member", &.{
                input.atom(groups[random.uintLessThan(usize, groups.len)]),
                input.variable("any"),
            })});
            continue;
        }
        var inserts: [2]input.Relation = undefined;
        var deletes: [2]input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (random.boolean()) {
            inserts[insert_count] = input.fact("edge", &edge_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("edge", &edge_terms);
            delete_count += 1;
        }
        if (random.boolean()) {
            inserts[insert_count] = input.fact("member", &member_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("member", &member_terms);
            delete_count += 1;
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
    }
    try db.materialize();
}

/// Program used by the cost-attribution tests below: a transitive closure
/// small enough that one edge change is cheap to maintain.
const cost_attribution_program =
    \\edge(a, b). edge(b, c).
    \\path(X, Y) :- edge(X, Y).
    \\path(X, Z) :- edge(X, Y), path(Y, Z).
;

test "the maintenance estimate counts facts changed, not facts named" {
    const new_edge = input.fact("edge", &.{ input.atom("c"), input.atom("d") });

    var lean: Jatalog = .init(std.testing.allocator);
    defer lean.deinit();
    lean.setMaintenancePolicy(.incremental);
    var lean_setup = try lean.execute(cost_attribution_program);
    lean_setup.deinit();
    try lean.materialize();
    _ = try lean.applyChanges(&.{new_edge}, &.{});

    var padded: Jatalog = .init(std.testing.allocator);
    defer padded.deinit();
    padded.setMaintenancePolicy(.incremental);
    var padded_setup = try padded.execute(cost_attribution_program);
    padded_setup.deinit();
    try padded.materialize();
    // The same single real insertion, named alongside deletions of facts the
    // database does not hold. Deleting an absent fact is a no-op, so the cost
    // per changed fact must match the lean batch rather than being divided by
    // the number of relations the caller happened to name.
    _ = try padded.applyChanges(&.{new_edge}, &.{
        input.fact("edge", &.{ input.atom("p"), input.atom("q") }),
        input.fact("edge", &.{ input.atom("q"), input.atom("r") }),
        input.fact("edge", &.{ input.atom("r"), input.atom("s") }),
        input.fact("edge", &.{ input.atom("s"), input.atom("t") }),
        input.fact("edge", &.{ input.atom("t"), input.atom("u") }),
        input.fact("edge", &.{ input.atom("u"), input.atom("v") }),
        input.fact("edge", &.{ input.atom("v"), input.atom("w") }),
    });

    try std.testing.expectEqual(
        lean.maintenanceStats().maintenance_work_per_fact,
        padded.maintenanceStats().maintenance_work_per_fact,
    );
}

test "a rebuild fallback is charged to the rebuild estimate, not to maintenance" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e). edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
    );
    setup.deinit();
    try db.materialize();

    // Deleting this edge over-deletes path facts that reach `isolated`
    // through negation, so delete-and-rederive abandons the incremental path
    // and rebuilds. The rebuild is real work, but it is recomputation work:
    // charging it to the maintenance estimate as well would let one event
    // push both estimates in opposite directions.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.rebuild_fallbacks > 0);
    try std.testing.expect(stats.rebuild_work != null);
    try std.testing.expect(stats.maintenance_work_per_fact != null);
    // One base fact changed, so the per-fact estimate is the whole measured
    // maintenance cost. With the rebuild excluded it is only the abandoned
    // over-deletion attempt, which is far cheaper than the rebuild itself.
    try std.testing.expect(stats.maintenance_work_per_fact.? < stats.rebuild_work.?);
}

test "the cost model changes the path taken but never the result" {
    var automatic: Jatalog = .init(std.testing.allocator);
    defer automatic.deinit();
    try runPolicyTrace(&automatic, .automatic);

    var incremental: Jatalog = .init(std.testing.allocator);
    defer incremental.deinit();
    try runPolicyTrace(&incremental, .incremental);

    var recompute: Jatalog = .init(std.testing.allocator);
    defer recompute.deinit();
    try runPolicyTrace(&recompute, .recompute);

    // Every policy must leave the same base facts and the same closure.
    for ([_]*Jatalog{ &incremental, &recompute }) |other| {
        try std.testing.expectEqual(automatic.state.facts.len(), other.state.facts.len());
        for (0..automatic.state.facts.len()) |index|
            try std.testing.expect(try other.state.facts.contains(automatic.state.facts.factAt(index)));
        try std.testing.expectEqual(automatic.state.closure.?.len(), other.state.closure.?.len());
        for (0..automatic.state.closure.?.len()) |index|
            try std.testing.expect(try other.state.closure.?.contains(automatic.state.closure.?.factAt(index)));
    }
    try test_support.expectClosureMatchesRebuild(&automatic.state);

    // The pinned policies really did take different paths, and the
    // automatic one made a real decision rather than defaulting.
    const automatic_stats = automatic.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 0), incremental.maintenanceStats().recompute_choices);
    try std.testing.expectEqual(@as(usize, 0), recompute.maintenanceStats().maintain_choices);
    try std.testing.expect(automatic_stats.maintain_choices > 0);
    try std.testing.expect(automatic_stats.rebuild_work != null);
    try std.testing.expect(automatic_stats.maintenance_work_per_fact != null);
}

test "the cost model learns to prefer the cheaper path per workload" {
    // A recursive closure over a chain: one new edge derives a handful of
    // paths, while recomputing re-derives the entire transitive closure.
    var closure_db: Jatalog = .init(std.testing.allocator);
    defer closure_db.deinit();
    var chain_source: std.ArrayList(u8) = .empty;
    defer chain_source.deinit(std.testing.allocator);
    for (0..30) |index| {
        var buffer: [64]u8 = undefined;
        const line = try std.fmt.bufPrint(&buffer, "edge(n{d}, n{d}). ", .{ index, index + 1 });
        try chain_source.appendSlice(std.testing.allocator, line);
    }
    try chain_source.appendSlice(
        std.testing.allocator,
        "path(X, Y) :- edge(X, Y). path(X, Z) :- edge(X, Y), path(Y, Z).",
    );
    var chain_setup = try closure_db.execute(chain_source.items);
    chain_setup.deinit();
    try closure_db.materialize();
    for (0..8) |index| {
        var from: [16]u8 = undefined;
        var to: [16]u8 = undefined;
        const source = try std.fmt.bufPrint(&from, "s{d}", .{index});
        const target = try std.fmt.bufPrint(&to, "n{d}", .{index});
        const terms: [2]input.Term = .{ input.atom(source), input.atom(target) };
        _ = try closure_db.applyChanges(&.{input.fact("edge", &terms)}, &.{});
        // Query between batches so a recompute decision is actually paid and
        // the closure is clean again when the next decision is made.
        var query = try closure_db.execute("path(n0, X)?");
        query.deinit();
    }
    const closure_stats = closure_db.maintenanceStats();
    try std.testing.expect(closure_stats.maintain_choices > closure_stats.recompute_choices);
    try test_support.expectClosureMatchesRebuild(&closure_db.state);

    // A shallow program whose closure is cheap to recompute: maintenance
    // has no recursion to save and the model should stop choosing it.
    var flat_db: Jatalog = .init(std.testing.allocator);
    defer flat_db.deinit();
    var flat_setup = try flat_db.execute(
        \\item(a). item(b). item(c).
        \\present(X) :- item(X).
    );
    flat_setup.deinit();
    try flat_db.materialize();
    for (0..8) |index| {
        var buffer: [16]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "i{d}", .{index});
        const terms: [1]input.Term = .{input.atom(name)};
        _ = try flat_db.applyChanges(&.{input.fact("item", &terms)}, &.{});
        var query = try flat_db.execute("present(X)?");
        query.deinit();
    }
    try test_support.expectClosureMatchesRebuild(&flat_db.state);
    const flat_stats = flat_db.maintenanceStats();
    try std.testing.expect(flat_stats.recompute_choices > 0);
}

test "shadow verification accepts maintained closures and reports corruption" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). group(g). member(g, m1).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\reachable(X) :- path(a, X).
        \\unreachable(X) :- edge(X, Y), not reachable(X).
    );
    setup.deinit();
    try db.materialize();

    // Insertions, deletions, and aggregate changes all pass verification.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
        input.fact("member", &.{ input.atom("g"), input.atom("m2") }),
    }, &.{}));
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }, &.{
        input.fact("member", &.{ input.atom("g"), input.atom("m1") }),
    }));
    try test_support.expectClosureMatchesRebuild(&db.state);

    // A closure corrupted behind the maintenance engine's back is caught:
    // this path tuple has no derivation from any base fact.
    const terms = try std.testing.allocator.alloc(relation_store.ValueId, 2);
    var terms_owned = true;
    defer if (terms_owned) std.testing.allocator.free(terms);
    terms[0] = try db.state.eval.values.intern(.{ .scalar = try db.state.eval.scalars.internAtom("phantom1") });
    terms[1] = try db.state.eval.values.intern(.{ .scalar = try db.state.eval.scalars.internAtom("phantom2") });
    const added = try db.state.closure.?.insert(.{
        .predicate = db.state.strings.get("path").?,
        .terms = terms,
    }, true);
    terms_owned = false;
    try std.testing.expect(added);
    try std.testing.expectError(errors.Error.MaintenanceMismatch, db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
}

test "randomized mixed traces hold under shadow verification" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\node(a). node(b). node(c). group(g1). group(g2).
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\quiet(G) :- group(G), not member(G, m1).
    );
    setup.deinit();
    try db.materialize();

    const nodes = [_][]const u8{ "a", "b", "c" };
    const groups = [_][]const u8{ "g1", "g2" };
    const members = [_][]const u8{ "m1", "m2" };
    var prng = std.Random.DefaultPrng.init(0x5ade0e5ade0e);
    const random = prng.random();
    for (0..30) |_| {
        var edge_terms: [2]input.Term = .{
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
        };
        var member_terms: [2]input.Term = .{
            input.atom(groups[random.uintLessThan(usize, groups.len)]),
            input.atom(members[random.uintLessThan(usize, members.len)]),
        };
        const insert_edge = random.boolean();
        var inserts: [2]input.Relation = undefined;
        var deletes: [2]input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (insert_edge) {
            inserts[insert_count] = input.fact("edge", &edge_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("edge", &edge_terms);
            delete_count += 1;
        }
        if (random.boolean()) {
            inserts[insert_count] = input.fact("member", &member_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("member", &member_terms);
            delete_count += 1;
        }
        // Shadow verification asserts rebuild equality inside the call.
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}
test "aggregate groups are maintained incrementally across member changes" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2).
        \\member(g1, b). member(g1, a). member(g2, z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var initial = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[a, b]");
    initial.deinit();
    const expansions_after_build = db.state.eval.expansions;

    // Member insertion updates only the affected group, with no rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g1"), input.atom("c") }),
    }, &.{}));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    var inserted = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&inserted.query.answers.items[0], "S", "[a, b, c]");
    inserted.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // The untouched group keeps its list and there is exactly one tuple
    // per group after the change.
    var untouched = try db.execute("collected(g2, S)?");
    try test_support.expectBindingValue(&untouched.query.answers.items[0], "S", "[z]");
    untouched.deinit();
    try expectAnswerCount(&db, "collected(G, S)?", 2);

    // Member deletion shrinks the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("a") }),
    }));
    var deleted = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&deleted.query.answers.items[0], "S", "[b, c]");
    deleted.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting the last member leaves the enumerated group with an empty
    // list, because its outer goal still derives the group.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g2"), input.atom("z") }),
    }));
    var emptied = try db.execute("collected(g2, S)?");
    try test_support.expectBindingValue(&emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting the group key removes the tuple entirely.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("group", &.{input.atom("g2")}),
    }));
    try expectAnswerCount(&db, "collected(g2, S)?", 0);
    try expectAnswerCount(&db, "collected(G, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Restoring the group key brings back an empty group.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("group", &.{input.atom("g2")}),
    }, &.{}));
    var restored = try db.execute("collected(g2, S)?");
    try test_support.expectBindingValue(&restored.query.answers.items[0], "S", "[]");
    restored.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "duplicate member derivations do not disturb a maintained group" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g). direct(g, a). mirrored(g, a). direct(g, b).
        \\member(G, X) :- direct(G, X).
        \\member(G, X) :- mirrored(G, X).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var initial = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[a, b]");
    initial.deinit();

    // Removing one of two derivations of member(g, a) keeps the member.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("mirrored", &.{ input.atom("g"), input.atom("a") }),
    }));
    var kept = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&kept.query.answers.items[0], "S", "[a, b]");
    kept.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Removing the last derivation drops it from the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("direct", &.{ input.atom("g"), input.atom("a") }),
    }));
    var dropped = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&dropped.query.answers.items[0], "S", "[b]");
    dropped.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "canonical aggregate lists are independent of update order" {
    const orders = [_][3][]const u8{
        .{ "c", "a", "b" },
        .{ "b", "c", "a" },
        .{ "a", "b", "c" },
    };
    for (orders) |order| {
        var db: Jatalog = .init(std.testing.allocator);
        defer db.deinit();
        var setup = try db.execute(
            \\group(g).
            \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        );
        setup.deinit();
        var empty = try db.execute("collected(g, S)?");
        try test_support.expectBindingValue(&empty.query.answers.items[0], "S", "[]");
        empty.deinit();

        for (order) |name| {
            _ = try db.applyChanges(&.{
                input.fact("member", &.{ input.atom("g"), input.atom(name) }),
            }, &.{});
        }
        var result = try db.execute("collected(g, S)?");
        try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a, b, c]");
        result.deinit();
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

test "bag emulation retains equal values with distinct discriminators" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g). reading(g, r1, 5). reading(g, r2, 5). reading(g, r3, 7).
        \\bag(G, S) :- group(G), setof([V, D], reading(G, D, V), S).
    );
    setup.deinit();
    var initial = try db.execute("bag(g, S)?");
    try test_support.expectBindingValue(
        &initial.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [7, r3]]",
    );
    initial.deinit();

    try std.testing.expect(try db.applyChanges(&.{
        input.fact("reading", &.{ input.atom("g"), input.atom("r4"), input.integer(5) }),
    }, &.{}));
    var added = try db.execute("bag(g, S)?");
    try test_support.expectBindingValue(
        &added.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [5, r4], [7, r3]]",
    );
    added.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Removing one duplicate value keeps the others.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("reading", &.{ input.atom("g"), input.atom("r2"), input.integer(5) }),
    }));
    var removed = try db.execute("bag(g, S)?");
    try test_support.expectBindingValue(
        &removed.query.answers.items[0],
        "S",
        "[[5, r1], [5, r4], [7, r3]]",
    );
    removed.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "maintained aggregates feed downstream strata and recursive consumers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\person(alice). person(bob).
        \\parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    setup.deinit();
    var initial = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 1), try initial.query.answers.items[0].getInteger("N"));
    initial.deinit();

    // A new child changes the aggregate list, which must flow through the
    // downstream structural list function.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("person", &.{input.atom("carol")}),
        input.fact("parent", &.{ input.atom("alice"), input.atom("carol") }),
    }, &.{}));
    var grown = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    try expectAnswerCount(&db, "numchildren(X, N)?", 3);
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("parent", &.{ input.atom("alice"), input.atom("bob") }),
    }));
    var shrunk = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 1), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "multiple and nested aggregates stay correct through the rebuild path" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). item(g1, a). item(g2, b). tag(g1, t1). tag(g2, t2).
        \\both(G, S, T) :- group(G), setof(X, item(G, X), S), setof(Y, tag(G, Y), T).
        \\nested(S) :- group(g1), setof([G, T], (group(G), setof(X, item(G, X), T)), S).
    );
    setup.deinit();
    var initial = try db.execute("both(g1, S, T)?");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[a]");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "T", "[t1]");
    initial.deinit();

    // Rules outside the maintainable class fall back to the stratum
    // rebuild, which must still produce rebuild-equivalent results.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("item", &.{ input.atom("g1"), input.atom("c") }),
        input.fact("tag", &.{ input.atom("g1"), input.atom("t3") }),
    }, &.{}));
    var updated = try db.execute("both(g1, S, T)?");
    try test_support.expectBindingValue(&updated.query.answers.items[0], "S", "[a, c]");
    try test_support.expectBindingValue(&updated.query.answers.items[0], "T", "[t1, t3]");
    updated.deinit();
    var nested = try db.execute("nested(S)?");
    try test_support.expectBindingValue(
        &nested.query.answers.items[0],
        "S",
        "[[g1, [a, c]], [g2, [b]]]",
    );
    nested.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("item", &.{ input.atom("g1"), input.atom("a") }),
    }));
    var reduced = try db.execute("both(g1, S, T)?");
    try test_support.expectBindingValue(&reduced.query.answers.items[0], "S", "[c]");
    reduced.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "random aggregate update traces match a clean rebuild after every batch" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\group(g1). group(g2). group(g3).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\empty(G) :- group(G), not member(G, m1), not member(G, m2), not member(G, m3).
    );
    setup.deinit();
    try expectAnswerCount(&db, "size(G, N)?", 3);

    const groups = [_][]const u8{ "g1", "g2", "g3" };
    const members = [_][]const u8{ "m1", "m2", "m3" };
    var prng = std.Random.DefaultPrng.init(0xa99a6a7e5eed);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [2][2]input.Term = undefined;
        var inserts: [2]input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            insert_buffer[slot] = .{
                input.atom(groups[random.uintLessThan(usize, groups.len)]),
                input.atom(members[random.uintLessThan(usize, members.len)]),
            };
            inserts[slot] = input.fact("member", &insert_buffer[slot]);
        }
        var delete_buffer: [2][2]input.Term = undefined;
        var deletes: [2]input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            delete_buffer[slot] = .{
                input.atom(groups[random.uintLessThan(usize, groups.len)]),
                input.atom(members[random.uintLessThan(usize, members.len)]),
            };
            deletes[slot] = input.fact("member", &delete_buffer[slot]);
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

/// Derivation count the auxiliary view records for the single tuple of
/// `predicate` whose first argument is the atom `first_atom`.
fn derivationCountOf(
    db: *Jatalog,
    predicate: []const u8,
    first_atom: []const u8,
) !u32 {
    const predicate_id = db.state.strings.get(predicate) orelse return error.MissingPredicate;
    const scalar_id = try db.state.eval.scalars.internAtom(first_atom);
    const first_value = try db.state.eval.values.intern(.{ .scalar = scalar_id });
    for (db.state.eval.rules.items) |rule| {
        if (rule.head.predicate != predicate_id) continue;
        const view = materialization.auxiliaryFor(&db.state, rule.id) orelse return error.NotProjected;
        const closure = &db.state.closure.?;
        for (0..closure.len()) |index| {
            const fact = closure.factAt(index);
            if (fact.predicate != predicate_id or fact.terms[0] != first_value) continue;
            return view.derivationCount(fact.terms);
        }
        return 0;
    }
    return error.MissingPredicate;
}

test "Chapter 5 Example 5.2.1 maintains a view without projections" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a). p(b). r(a, 1). r(c, 3).
        \\v(X, S) :- p(X), setof(Y, r(X, Y), S).
    );
    setup.deinit();

    // The materialization contains v(a, [1]) and v(b, []).
    var initial = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[1]");
    initial.deinit();
    var empty = try db.execute("v(b, S)?");
    try test_support.expectBindingValue(&empty.query.answers.items[0], "S", "[]");
    empty.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 2);

    // Deleting p(a) and inserting r(b, 2) deletes v(a, [1]) and updates
    // v(b, []) to v(b, [2]).
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("r", &.{ input.atom("b"), input.integer(2) }),
    }, &.{
        input.fact("p", &.{input.atom("a")}),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "v(a, S)?", 0);
    var updated = try db.execute("v(b, S)?");
    try test_support.expectBindingValue(&updated.query.answers.items[0], "S", "[2]");
    updated.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // This view retains every outer variable, so it is self-maintainable and
    // needs no auxiliary derivation counts.
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.self_maintainable_views);
    try std.testing.expectEqual(@as(usize, 0), stats.projected_views);
    try std.testing.expectEqual(@as(usize, 0), stats.auxiliary_tuples);
}

test "Chapter 5 Example 5.3.1 counts derivations of a projected view" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a, 1). p(a, 2). p(b, 1). r(a, 1). r(a, 2). r(b, 2).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();

    var initial = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[1, 2]");
    initial.deinit();
    var other = try db.execute("v(b, S)?");
    try test_support.expectBindingValue(&other.query.answers.items[0], "S", "[2]");
    other.deinit();

    // The auxiliary counting view holds v(a, [1, 2]) with two derivations
    // and v(b, [2]) with one, matching the chapter's v_c extension.
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.projected_views);
    try std.testing.expectEqual(@as(usize, 0), stats.self_maintainable_views);
    try std.testing.expectEqual(@as(usize, 3), stats.auxiliary_tuples);
    try std.testing.expectEqual(@as(u32, 2), try derivationCountOf(&db, "v", "a"));
    try std.testing.expectEqual(@as(u32, 1), try derivationCountOf(&db, "v", "b"));

    // Deleting p(a, 2) removes one of two derivations, so the tuple stays.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("p", &.{ input.atom("a"), input.integer(2) }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    var retained = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&retained.query.answers.items[0], "S", "[1, 2]");
    retained.deinit();
    try std.testing.expectEqual(@as(u32, 1), try derivationCountOf(&db, "v", "a"));
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting p(a, 1) removes the last derivation, so the tuple goes.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("p", &.{ input.atom("a"), input.integer(1) }),
    }));
    try expectAnswerCount(&db, "v(a, S)?", 0);
    try std.testing.expectEqual(@as(u32, 0), try derivationCountOf(&db, "v", "a"));
    try expectAnswerCount(&db, "v(X, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a changed aggregate list transfers support to the new tuple" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a, 1). p(a, 2). p(a, 3). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();
    var initial = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[1]");
    initial.deinit();
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));

    // Growing the member set replaces the old tuple with the new one and
    // carries all three derivations across in the same batch.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("r", &.{ input.atom("a"), input.integer(2) }),
    }, &.{}));
    try std.testing.expect(db.state.materialization == .clean);
    var moved = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&moved.query.answers.items[0], "S", "[1, 2]");
    moved.deinit();
    try expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try std.testing.expectEqual(@as(usize, 3), db.maintenanceStats().auxiliary_tuples);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Shrinking it back transfers the support again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("r", &.{ input.atom("a"), input.integer(1) }),
    }));
    var shrunk = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&shrunk.query.answers.items[0], "S", "[2]");
    shrunk.deinit();
    try expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "projected view counts agree with explicit proof enumeration" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\p(a, 1). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 1);

    const keys = [_][]const u8{ "a", "b", "c" };
    var prng = std.Random.DefaultPrng.init(0xc0107501c0107);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [2][2]input.Term = undefined;
        var inserts: [2]input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            const key = keys[random.uintLessThan(usize, keys.len)];
            const number: i64 = @intCast(random.uintLessThan(usize, 3) + 1);
            insert_buffer[slot] = .{ input.atom(key), input.integer(number) };
            inserts[slot] = input.fact(
                if (random.boolean()) "p" else "r",
                &insert_buffer[slot],
            );
        }
        var delete_buffer: [2][2]input.Term = undefined;
        var deletes: [2]input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            const key = keys[random.uintLessThan(usize, keys.len)];
            const number: i64 = @intCast(random.uintLessThan(usize, 3) + 1);
            delete_buffer[slot] = .{ input.atom(key), input.integer(number) };
            deletes[slot] = input.fact(
                if (random.boolean()) "p" else "r",
                &delete_buffer[slot],
            );
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);

        // Every proof of v(k, S) comes from one p(k, Z) fact, so the stored
        // derivation count must equal the number of such base facts.
        for (keys) |key| {
            var proofs = try db.execute("p(K, Z)?");
            defer proofs.deinit();
            var expected: u32 = 0;
            for (proofs.query.answers.items) |*answer| {
                const bound = try answer.getAtom("K");
                if (std.mem.eql(u8, bound, key)) expected += 1;
            }
            try std.testing.expectEqual(expected, try derivationCountOf(&db, "v", key));
        }
    }
}

test "aggregate changes propagate through downstream list functions and arithmetic" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\team(red). team(blue).
        \\roster(T, S) :- team(T), setof(P, plays(T, P), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(T, N) :- roster(T, S), length(S, N).
        \\headcount(T, N) :- size(T, M), N = M + 1.
        \\staffed(T) :- size(T, N), N > 1.
    );
    setup.deinit();
    try db.materialize();

    // Empty rosters flow through length, arithmetic, and the comparison.
    var initial = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 1), try initial.query.answers.items[0].getInteger("N"));
    initial.deinit();
    try expectAnswerCount(&db, "staffed(T)?", 0);

    // Growing one group must reach every downstream stratum.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("plays", &.{ input.atom("red"), input.atom("ann") }),
        input.fact("plays", &.{ input.atom("red"), input.atom("bo") }),
    }, &.{}));
    var grown = try db.execute("size(red, N)?");
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    var counted = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 3), try counted.query.answers.items[0].getInteger("N"));
    counted.deinit();
    try expectAnswerCount(&db, "staffed(red)?", 1);
    try expectAnswerCount(&db, "staffed(blue)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Shrinking it retracts the downstream conclusions again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("plays", &.{ input.atom("red"), input.atom("bo") }),
    }));
    var shrunk = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 2), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try expectAnswerCount(&db, "staffed(T)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // A downstream structural-recursive component recomputes within its own
    // stratum rather than forcing a whole-closure rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.maintained_groups > 0);
}

fn aggregateMaintenanceAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var first = try db.execute("collected(G, S)?");
    first.deinit();
    _ = try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g1"), input.atom("b") }),
        input.fact("member", &.{ input.atom("g2"), input.atom("c") }),
    }, &.{});
    _ = try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("a") }),
    });
    var second = try db.execute("collected(g1, S)?");
    defer second.deinit();
    const formatted = try (try second.query.answers.items[0].getValue("S"))
        .formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[b]")) return error.UnexpectedAggregate;
}

test "aggregate maintenance releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(aggregateMaintenanceAllocationScenario);
}
