//! What a statement does to a database, and the transaction it does it in.
//!
//! A source program is a sequence of statements, each of which either commits
//! completely or leaves the database exactly as it was. The operations here
//! are the compiled form of those statements — they take clauses the parser
//! has already built rather than caller descriptors — and `Statement` is the
//! transaction that stages them.

const std = @import("std");
const aggregate_view = @import("aggregate_view.zig");
const compile = @import("compile.zig");
const database = @import("database.zig");
const errors = @import("errors.zig");
const maintenance = @import("maintenance.zig");
const materialization = @import("materialization.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const syntax = @import("syntax.zig");
const validation = @import("validation.zig");

/// Applies the base facts a retraction removed. `staging` holds the
/// post-retraction base facts computed by goal evaluation; the removals
/// are replayed onto a fresh clone so query-local values interned while
/// evaluating the goals never reach the committed database. The removals
/// then take the same incremental deletion path as a batch: exact facts
/// through delete-and-rederive and aggregate maintenance when the
/// closure is clean, and dirty-stratum rebuild otherwise.
pub fn commitRetraction(db: *database.Database, staging: *database.Database) !void {
    var committed = try db.clone();
    defer committed.deinit();
    var removed: relation_store.RelationStore = .init(committed.allocator);
    defer removed.deinit();
    var index = committed.facts.len();
    while (index > 0) {
        index -= 1;
        const fact = committed.facts.factAt(index);
        if (try staging.facts.contains(fact)) continue;
        try relation_store.copyFactInto(committed.allocator, &removed, fact, false);
        committed.facts.removeAt(index);
    }
    // Retraction resolves its goals before deciding, so unlike a batch it
    // knows exactly how many base facts it changes: the estimate the
    // model decides on and the count it later measures are the same.
    const delta = removed.len();
    const maintain = committed.canMaintain() and
        committed.eval.cost.decide(delta) == .maintain;
    if (maintain and delta > 0) {
        const span = committed.eval.cost.begin();
        try maintenance.propagateDeletions(&committed, &removed);
        var touched: relation_store.RelationStore = .init(committed.allocator);
        defer touched.deinit();
        for (0..removed.len()) |position|
            try relation_store.copyFactInto(committed.allocator, &touched, removed.factAt(position), false);
        if (touched.len() > 0) try aggregate_view.maintainAggregates(&committed, &touched);
        committed.eval.cost.noteMaintenance(delta, span);
    } else {
        for (0..removed.len()) |position| {
            const fact = removed.factAt(position);
            try committed.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
        }
    }
    try materialization.verifyShadow(&committed);
    db.commit(&committed);
}

pub fn addFactExpr(db: *database.Database, value: syntax.Expr) !void {
    _ = try db.applyInsertion(value, false);
}

/// Adds a rule whose body may contain aggregate clauses. On success the
/// database owns `head` and every clause in `body`; on failure the caller
/// retains ownership. The body slice itself is only borrowed.
pub fn addRuleClauses(db: *database.Database, head: syntax.Expr, body: []const syntax.Clause) !void {
    const seed_argument = try validation.validateRule(db, head, body);
    const owned_body = try validation.orderClauses(db, body);
    errdefer db.allocator.free(owned_body);
    const id = db.eval.next_rule_id;
    db.eval.next_rule_id += 1;
    try db.eval.rules.append(db.allocator, .{
        .id = id,
        .head = head,
        .body = owned_body,
        .seed_argument = seed_argument,
    });
    validation.validateRecursiveArithmetic(db) catch |err| {
        _ = db.eval.rules.pop();
        return err;
    };
    validation.validateStratification(db) catch |err| {
        _ = db.eval.rules.pop();
        return err;
    };
    materialization.invalidateAnalysis(db);
    if (db.closure != null) {
        // Lazy rebuild policy for rule additions: invalidate from the new
        // head's stratum now, rebuild at the next evaluation.
        const analysis = try db.eval.ensureAnalysis();
        db.markDirty(analysis.strata.get(syntax.predicateKey(head)) orelse 0);
    }
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
    return db.copyQueryResult(internal_answers.items);
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
    try db.eval.matchClauses(ordered, db.closureStore(), 0, &initial, &internal_answers, null);
    return internal_answers;
}

pub fn deleteClauses(db: *database.Database, goals: []const syntax.Clause) !bool {
    var answers = try evaluateClauses(db, goals);
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    var to_remove: std.ArrayList(usize) = .empty;
    defer to_remove.deinit(db.allocator);
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
                    try to_remove.append(db.allocator, candidate);
                }
            }
        }
    }
    std.mem.sort(usize, to_remove.items, {}, std.sort.desc(usize));
    for (to_remove.items) |index| {
        const fact = db.facts.factAt(index);
        try db.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
        db.facts.removeAt(index);
    }
    return to_remove.items.len > 0;
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
/// with a staged copy, replaying a retraction's removals through the deletion
/// engine — are not part of the public interface, because committing a foreign
/// staging database is not an operation an embedder should be able to name.
pub const Statement = struct {
    /// What the next statement will turn out to be, as far as scanning for
    /// its terminator can tell. Only whether it evaluates matters here.
    pub const Kind = enum { assertion, query, retraction, end };

    database: *database.Database,
    staging: database.Database,

    /// Opens a transaction for one statement. A statement that evaluates needs
    /// the committed closure materialized first, so that the staged copy
    /// shares its value identifiers and evaluation never expands.
    pub fn begin(db: *database.Database, kind: Kind) !Statement {
        switch (kind) {
            .query, .retraction => try materialization.ensureMaterialized(db),
            .assertion, .end => {},
        }
        return .{ .database = db, .staging = try db.clone() };
    }

    /// The database to execute the statement against. Everything it interns —
    /// including values a query mentions but the database does not hold — stays
    /// here unless the statement commits.
    pub fn target(self: *Statement) *database.Database {
        return &self.staging;
    }

    /// Commits according to what the statement turned out to be. A query
    /// changes nothing and keeps its query-local interning out of the
    /// database; an assertion installs the staged copy; a retraction that
    /// removed facts replays those removals so they take the incremental
    /// deletion path rather than committing the staged copy wholesale.
    pub fn commit(self: *Statement, result: results.ExecutionResult) !void {
        switch (result) {
            .query => {},
            .none => self.database.commit(&self.staging),
            .changed => |changed| if (changed) try commitRetraction(self.database, &self.staging),
        }
    }

    pub fn deinit(self: *Statement) void {
        self.staging.deinit();
        self.* = undefined;
    }
};
