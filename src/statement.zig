//! What a statement does to a database, and the transaction it does it in.
//!
//! A source program is a sequence of statements, each of which either commits
//! completely or leaves the database exactly as it was. The operations here
//! are the compiled form of those statements — they take clauses the parser
//! has already built rather than caller descriptors — and `Statement` is the
//! transaction that stages them.

const std = @import("std");
const compile = @import("compile.zig");
const database = @import("database.zig");
const errors = @import("errors.zig");
const materialization = @import("materialization.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const syntax = @import("syntax.zig");
const update = @import("update.zig");
const validation = @import("validation.zig");

/// Applies the base facts a retraction resolved its goals to, which
/// `resolveRetraction` produced against a staging copy of `db`. They are
/// applied to a fresh clone rather than to `db` itself, so that a failure
/// part-way through leaves the database untouched — and they take the ordinary
/// update path, which is what makes a retraction and a batch deletion the same
/// operation on the closure.
///
/// Only the facts cross over. The staging copy the goals were evaluated on is
/// discarded with everything its evaluation interned, which is how values a
/// retraction mentions but the database does not hold stay out of it.
pub fn commitRetraction(db: *database.Database, removed: *const relation_store.RelationStore) !void {
    var committed = try db.clone();
    defer committed.deinit();
    _ = try update.apply(&committed, .{ .resolved = removed }, &.{});
    try materialization.verifyShadow(&committed);
    db.commit(&committed);
}

pub fn addFactExpr(db: *database.Database, value: syntax.Expr) !void {
    const fact = try db.applyInsertion(value) orelse return;
    const key: relation_store.PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
    db.markBaseChanged(key) catch |err| {
        // The insertion comes back out. A statement leaves the fact store
        // either as it was or with its fact in it and nothing between, which
        // is what lets a run of assertions share one transaction and still be
        // undone one statement at a time: see `Database.rollback`, which has
        // no way to put a fact back.
        //
        // The fact stamp stays where the insertion left it, which is the one
        // direction it is allowed to be wrong in: a reader rebuilds something
        // that was still good, rather than keeping something that is not.
        db.facts.removeAt(db.facts.len() - 1);
        return err;
    };
}

/// Adds a rule whose body may contain aggregate clauses. On success the
/// database owns `head` and every clause in `body`; on failure the caller
/// retains ownership. The body slice itself is only borrowed.
pub fn addRuleClauses(db: *database.Database, head: syntax.Expr, body: []const syntax.Clause) !void {
    const seed_argument = try validation.validateRule(db, head, body);
    const owned_body = try validation.orderClauses(db, body);
    errdefer db.allocator.free(owned_body);
    try db.eval.rules.append(db.allocator, .{
        .id = db.eval.next_rule_id,
        .head = head,
        .body = owned_body,
        .seed_argument = seed_argument,
    });
    // Past here the rule is installed and every failure takes it back out,
    // which is both halves of what this promises: the caller keeps ownership
    // of `head` and `body`, and the rule set is left exactly as it was, since
    // `Database.rollback` has no way to put a rule back. The identifier is
    // spent only once the rule is certain to stay.
    errdefer _ = db.eval.rules.pop();
    try validation.validateRecursiveGeneration(db);
    try validation.validateStratification(db);
    materialization.invalidateAnalysis(db);
    if (db.closure != null) {
        // Lazy rebuild policy for rule additions: invalidate from the new
        // head's stratum now, rebuild at the next evaluation.
        const analysis = try db.eval.ensureAnalysis();
        db.markDirty(analysis.strata.get(syntax.predicateKey(head)) orelse 0);
    }
    db.eval.next_rule_id += 1;
}

/// Evaluates relational, built-in, negated, or aggregate goals. Goals and
/// their structural terms remain caller-owned and may be freed immediately
/// after this function returns.
pub fn queryClauses(db: *database.Database, goals: []const syntax.Clause) !results.QueryResult {
    var internal_answers = try evaluateClauses(db, goals);
    defer {
        for (internal_answers.items) |*answer| answer.deinit(db.allocator);
        internal_answers.deinit(db.allocator);
    }
    const order = try queryVariableOrder(db, goals);
    defer db.allocator.free(order);
    return db.copyQueryResult(internal_answers.items, order);
}

/// The query's variables in the order it first mentions them, which is the
/// order its answers list them in. Built from the goals as written rather than
/// from the plan, so that what a caller sees does not move when the planner
/// picks a different join order.
fn queryVariableOrder(db: *database.Database, goals: []const syntax.Clause) ![]syntax.Id {
    var order: std.ArrayList(syntax.Id) = .empty;
    errdefer order.deinit(db.allocator);
    var seen: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer seen.deinit(db.allocator);
    for (goals) |clause| try appendClauseVariables(db, clause, &seen, &order);
    return order.toOwnedSlice(db.allocator);
}

/// Appends the variables a goal binds at its surface — the ones that can reach
/// an answer — in the order the goal writes them.
fn appendClauseVariables(
    db: *database.Database,
    clause: syntax.Clause,
    seen: *std.AutoHashMapUnmanaged(syntax.Id, void),
    order: *std.ArrayList(syntax.Id),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| for (expression.terms) |term|
            try appendTermVariables(db, term, seen, order),
        .aggregate => |aggregate| try appendTermVariables(db, aggregate.output, seen, order),
    }
}

fn appendTermVariables(
    db: *database.Database,
    term: syntax.Term,
    seen: *std.AutoHashMapUnmanaged(syntax.Id, void),
    order: *std.ArrayList(syntax.Id),
) !void {
    switch (term) {
        .variable => |variable| {
            const entry = try seen.getOrPut(db.allocator, variable);
            if (!entry.found_existing) try order.append(db.allocator, variable);
        },
        .cons => |pair| {
            try appendTermVariables(db, pair.head, seen, order);
            try appendTermVariables(db, pair.tail, seen, order);
        },
        else => {},
    }
}

pub fn evaluateClauses(db: *database.Database, goals: []const syntax.Clause) !std.ArrayList(syntax.Binding) {
    if (goals.len == 0) return error.InvalidQuery;
    var outer_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer outer_variables.deinit(db.allocator);
    for (goals) |clause| try syntax.collectClauseSurfaceVariables(db.allocator, clause, &outer_variables);
    var bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer bound.deinit(db.allocator);
    const ordered = try validation.orderClauses(db, goals);
    defer db.allocator.free(ordered);
    for (ordered) |clause|
        try validation.validateClause(db, clause, &bound, &outer_variables, errors.Error.InvalidQuery);

    try materialization.ensureMaterialized(db);
    const values_before = db.eval.values.values.items.len;
    for (goals) |clause| try compile.internGroundStructuresInClause(db, clause);
    if (db.eval.values.values.items.len != values_before) {
        // Novel ground query structures must join the seed set of
        // admissible structural recursion, so derive their consequences
        // on this database's own (discardable) closure.
        if (db.closure) |*closure| {
            if ((try db.eval.ensureAnalysis()).has_seed_rules)
                try db.eval.expandFrom(closure, 0);
        }
    }

    var internal_answers: std.ArrayList(syntax.Binding) = .empty;
    errdefer {
        for (internal_answers.items) |*answer| answer.deinit(db.allocator);
        internal_answers.deinit(db.allocator);
    }
    var initial: syntax.Binding = .{};
    defer initial.deinit(db.allocator);
    try db.eval.solve(db.closureStore(), null, ordered, &initial, &internal_answers, null);
    return internal_answers;
}

/// The plan a query's goals would be solved under, rendered for a caller that
/// wants to see the clause order and the indexes it chose. Planning reads the
/// materialized closure's statistics, so this materializes first, exactly as
/// evaluating the query would.
pub fn explainClauses(db: *database.Database, goals: []const syntax.Clause) ![]u8 {
    if (goals.len == 0) return error.InvalidQuery;
    const ordered = try validation.orderClauses(db, goals);
    defer db.allocator.free(ordered);
    try materialization.ensureMaterialized(db);
    var initial: syntax.Binding = .{};
    defer initial.deinit(db.allocator);
    var chosen = try db.eval.planFor(db.closureStore(), null, ordered, &initial);
    defer chosen.deinit();
    return chosen.explainAlloc(db.allocator, &db.strings);
}

/// Resolves a retraction's goals to the exact base facts they name, and hands
/// them back in a store of its own. Removes nothing: the goals are evaluated
/// against whichever database the caller points this at, and the facts are
/// copied out of that database's fact store rather than taken out of it.
///
/// A retraction is the one statement whose goals have to be evaluated
/// somewhere other than where its effect lands, because evaluating them can
/// intern values the database does not hold. The caller therefore points this
/// at a staging copy and hands what comes back to `commitRetraction`, which
/// applies it to the database that copy came from — the facts are that
/// database's own, so its value identifiers are what they carry.
pub fn resolveRetraction(
    db: *database.Database,
    goals: []const syntax.Clause,
) !relation_store.RelationStore {
    var answers = try evaluateClauses(db, goals);
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    var resolved: relation_store.RelationStore = .init(db.allocator);
    errdefer resolved.deinit();
    // Deduplicating by entry rather than leaving it to the store's set
    // semantics: a fact reached twice is one removal, not one removal with a
    // second unit of support, and delete-and-rederive reads that support.
    var seen: std.AutoHashMapUnmanaged(usize, void) = .empty;
    defer seen.deinit(db.allocator);
    for (answers.items) |*answer| {
        for (goals) |clause| {
            const goal = switch (clause) {
                .relational => |expression| expression,
                else => continue,
            };
            for (try db.eval.lookupCandidates(&db.facts, goal, answer)) |candidate| {
                if (seen.contains(candidate)) continue;
                var matched = try answer.clone(db.allocator);
                defer matched.deinit(db.allocator);
                if (try db.eval.unify(db.facts.factAt(candidate), goal, &matched)) {
                    try seen.put(db.allocator, candidate, {});
                    try relation_store.copyFactInto(
                        db.allocator,
                        &resolved,
                        db.facts.factAt(candidate),
                        false,
                    );
                }
            }
        }
    }
    return resolved;
}

/// One statement's transaction.
///
/// A source program is a sequence of statements, each of which either commits
/// completely or leaves the database exactly as it was, so a failure part-way
/// through a program keeps every earlier statement and none of this one. A
/// front end executes a statement by beginning one of these, running the
/// statement against `target`, and committing the result.
///
/// This is deliberately the whole transaction interface a front end gets for
/// that. The primitives it is built from — cloning the database, replacing it
/// with a staged copy, applying a retraction's facts through the deletion
/// engine — are not part of the public interface, because committing a foreign
/// staging database is not an operation an embedder should be able to name.
pub const Statement = struct {
    /// What the next statement will turn out to be, as far as scanning for
    /// its terminator can tell. Only whether it evaluates matters here.
    pub const Kind = enum { assertion, query, retraction, end };

    database: *database.Database,
    staging: database.Database,
    /// The base facts a retraction resolved its goals to, held from the point
    /// the statement runs to the point it commits. A retraction is the one
    /// statement whose commit needs something the statement itself produced,
    /// and this transaction is what spans the two.
    removed: relation_store.RelationStore,

    /// Opens a transaction for one statement, or — with `.assertion` — for a
    /// run of consecutive ones. A statement that evaluates needs the committed
    /// closure materialized first, so that the staged copy shares its value
    /// identifiers and evaluation never expands.
    pub fn begin(db: *database.Database, kind: Kind) !Statement {
        switch (kind) {
            .query, .retraction => try materialization.ensureMaterialized(db),
            .assertion, .end => {},
        }
        return .{
            .database = db,
            .staging = try db.clone(),
            .removed = .init(db.allocator),
        };
    }

    /// The database to execute the statement against. Everything it interns —
    /// including values a query mentions but the database does not hold — stays
    /// here unless the statement commits.
    pub fn target(self: *Statement) *database.Database {
        return &self.staging;
    }

    /// Where the staging copy stands, to undo a statement back to.
    ///
    /// Cloning the database is what a transaction costs, and for a source file
    /// of facts it is nearly the whole cost of loading it: 2000 assertions one
    /// statement at a time copy 1,999,000 fact entries between them. A run of
    /// consecutive assertions therefore shares one of these. What a statement
    /// promises is unweakened, because a statement that fails inside a run is
    /// rolled back to its own savepoint and the run is committed without it —
    /// which leaves every earlier statement and none of the failing one,
    /// exactly as a transaction each would.
    pub fn savepoint(self: *Statement) database.Savepoint {
        return self.staging.savepoint();
    }

    /// Takes a statement that failed back out of the staging copy the
    /// statements before it are on. Allocates nothing.
    pub fn rollback(self: *Statement, mark: database.Savepoint) void {
        self.staging.rollback(mark);
    }

    /// Installs what a run of assertions has staged so far.
    ///
    /// This is `commit(.none)` without the error union. A run is committed
    /// both when it ends and when a statement inside it fails, and on that
    /// second path there is nothing to spend on an allocation and no room for
    /// a second error to report — so the operation a run commits through is
    /// spelled as one that cannot fail.
    pub fn commitAssertions(self: *Statement) void {
        self.database.commit(&self.staging);
    }

    /// Runs a retraction against the staging copy, keeping the base facts its
    /// goals resolved to for the commit. Returns whether it named any.
    pub fn retract(self: *Statement, goals: []const syntax.Clause) !bool {
        const resolved = try resolveRetraction(self.target(), goals);
        self.removed.deinit();
        self.removed = resolved;
        return self.removed.len() > 0;
    }

    /// Commits according to what the statement turned out to be. A query
    /// changes nothing and keeps its query-local interning out of the
    /// database; an assertion installs the staged copy; a retraction applies
    /// the facts it resolved, so that they take the incremental deletion path,
    /// and discards the copy it resolved them on.
    pub fn commit(self: *Statement, result: results.ExecutionResult) !void {
        switch (result) {
            .query => {},
            .none => self.database.commit(&self.staging),
            .changed => |changed| if (changed) try commitRetraction(self.database, &self.removed),
        }
    }

    pub fn deinit(self: *Statement) void {
        self.removed.deinit();
        self.staging.deinit();
        self.* = undefined;
    }
};

const testing = std.testing;
const input = @import("input.zig");

/// Installs `reachable(X) :- node(X)`, which is enough of a rule for a
/// retraction to have a derived consequence to lose. Built from descriptors
/// rather than parsed, because the parser is the layer above this one.
fn defineReachableRule(db: *database.Database) !void {
    const head = try compile.compileRelation(db, "reachable", &.{input.variable("X")}, false);
    const body = try compileGoal(db, "node", input.variable("X"));
    defer db.allocator.free(body);
    try addRuleClauses(db, head, body);
}

fn addAtomFact(db: *database.Database, predicate: []const u8, atom: []const u8) !void {
    const expression = try compile.compileRelation(db, predicate, &.{input.atom(atom)}, false);
    defer syntax.freeExpr(db.allocator, expression);
    try addFactExpr(db, expression);
}

/// Compiles one relational goal against `db`, interning whatever it names
/// there. The caller owns the returned slice and the clauses in it.
fn compileGoal(db: *database.Database, predicate: []const u8, term: input.Term) ![]syntax.Clause {
    return compile.compileGoals(db, &.{input.relation(predicate, &.{term})});
}

fn freeGoals(db: *database.Database, goals: []syntax.Clause) void {
    for (goals) |clause| syntax.freeClauseTree(db.allocator, clause);
    db.allocator.free(goals);
}

test "the facts a retraction resolves on a copy are the original database's own" {
    // This is the claim the retraction path rests on, and the only place it
    // is visible: a removal set crosses from the database its goals were
    // evaluated against to the database that copy was made from. The value
    // identifiers it carries are indexes into tables that cloning copies
    // verbatim and interning only appends to, so they mean the same facts on
    // both sides. Were that not so, nothing would be found on this side and
    // the retraction would silently remove nothing.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachableRule(&db);
    try addAtomFact(&db, "node", "a");
    try addAtomFact(&db, "node", "b");
    try materialization.ensureMaterialized(&db);
    try testing.expectEqual(@as(usize, 4), db.closure.?.len());

    var staging = try db.clone();
    defer staging.deinit();
    const goals = try compileGoal(&staging, "node", input.atom("a"));
    defer freeGoals(&staging, goals);
    var removed = try resolveRetraction(&staging, goals);
    defer removed.deinit();
    try testing.expectEqual(@as(usize, 1), removed.len());
    // Resolving is not removing: the copy still holds both facts.
    try testing.expectEqual(@as(usize, 2), staging.facts.len());

    try commitRetraction(&db, &removed);
    try testing.expectEqual(@as(usize, 1), db.facts.len());
    // And the fact took its derived consequence with it, which is what makes
    // this the deletion path rather than a fact store edit.
    try testing.expectEqual(@as(usize, 2), db.closure.?.len());
}

test "a retraction naming a value the database does not hold leaves it uninterned" {
    // The reason the goals are evaluated somewhere else at all. Evaluating
    // them interns what they name, and a retraction may name values the
    // database has never held; only the facts come back, so only facts the
    // database already had can reach it.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachableRule(&db);
    try addAtomFact(&db, "node", "a");
    try materialization.ensureMaterialized(&db);
    const scalars_before = db.eval.scalars.values.items.len;

    var staging = try db.clone();
    defer staging.deinit();
    const goals = try compileGoal(&staging, "node", input.atom("absent"));
    defer freeGoals(&staging, goals);
    var removed = try resolveRetraction(&staging, goals);
    defer removed.deinit();

    try testing.expectEqual(@as(usize, 0), removed.len());
    try testing.expect(staging.eval.scalars.values.items.len > scalars_before);
    try testing.expectEqual(scalars_before, db.eval.scalars.values.items.len);
    try testing.expectEqual(@as(usize, 1), db.facts.len());
}
