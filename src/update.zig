//! The update path: how one batch of base-fact changes reaches the derived
//! closure.
//!
//! Every base update takes exactly one of three paths, all of which yield the
//! database a clean rebuild would: incremental insertion propagation through
//! positive rules, delete-and-rederive for deletions, or a stratum rebuild
//! when the update reaches negation or an aggregate outside the maintained
//! class. Because maintaining and recomputing differ only in cost, the cost
//! model chooses per update — and because it learns from what it observes,
//! the choice, the work it produces, and the measurement of that work have to
//! stay one sequence. That sequence is this module.
//!
//! This is the layer between the state and the interface: it takes a
//! `*Database` and never names `Jatalog`. Compilation stays above — a caller
//! hands over a batch it has already resolved as far as it can, whether that
//! is expressions built from descriptors or from source, or the facts a
//! retraction's goals turned out to name. Staging and commit stay above too:
//! everything here mutates the database it is given, and a caller that needs
//! the update to be atomic runs it against a clone.

const std = @import("std");
const aggregate_view = @import("aggregate_view.zig");
const database = @import("database.zig");
const maintenance = @import("maintenance.zig");
const relation_store = @import("relation_store.zig");
const syntax = @import("syntax.zig");

/// What a batch deletes, in whichever form its caller holds it.
///
/// A batch of expressions names facts the database may or may not hold, so
/// the names have to be interned against it before they can be looked up. A
/// retraction instead evaluates its goals against a copy of the database and
/// arrives holding the facts themselves. That copy shares the original's value
/// identifiers — the tables they index into are append-only, and cloning
/// copies them verbatim — so facts resolved on the copy name the same facts
/// here, which is what makes handing them over sound.
pub const Deletions = union(enum) {
    named: []const syntax.Expr,
    resolved: *const relation_store.RelationStore,

    pub fn len(self: Deletions) usize {
        return switch (self) {
            .named => |expressions| expressions.len,
            .resolved => |facts| facts.len(),
        };
    }
};

/// Applies one batch of exact ground base-fact deletions and insertions with
/// set semantics, and returns how many base facts really changed — fewer than
/// the batch names whenever it deletes an absent fact or re-inserts a present
/// one.
///
/// Deletions run before insertions. Delete-and-rederive joins against a
/// snapshot of the pre-deletion closure, so a fact inserted first would be
/// over-deleted against a closure it was never absent from. When maintaining,
/// that order and everything else about reaching the closure is
/// `maintenance.applyDelta`'s; what stays here is choosing whether to
/// maintain at all, and recomputing when not.
pub fn apply(
    db: *database.Database,
    deletions: Deletions,
    insertions: []const syntax.Expr,
) !usize {
    // The batch size is only an estimate of the work ahead — it counts what
    // the caller named, and a batch naming facts the database already agrees
    // with does proportionally less. What it actually changed is measured
    // afterwards and fed back as the realized count. A batch of resolved
    // deletions is the case where the two numbers coincide: every fact in it
    // is one this database holds.
    const maintain = db.canMaintain() and
        db.eval.cost.decide(deletions.len() + insertions.len) == .maintain;
    if (!maintain) return recompute(db, deletions, insertions);

    const span = db.eval.cost.begin();
    // Facts the aggregate phase must reconsider: every fact this batch took
    // out of the closure, and every fact it derived into it.
    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const outcome = try maintainBatch(db, deletions, insertions, &touched);
    if (touched.len() > 0) try aggregate_view.maintainAggregates(db, &touched);

    const realized = outcome.removed + outcome.added;
    db.eval.cost.noteMaintenance(realized, span);
    return realized;
}

/// Hands the batch to `maintenance.applyDelta` as one base delta, which
/// needs it as facts: the named deletions and the insertions are interned
/// against this database first, into stores this function owns.
fn maintainBatch(
    db: *database.Database,
    deletions: Deletions,
    insertions: []const syntax.Expr,
    touched: *relation_store.RelationStore,
) !maintenance.Outcome {
    var named: relation_store.RelationStore = .init(db.allocator);
    defer named.deinit();
    const removals = switch (deletions) {
        .named => |expressions| removals: {
            for (expressions) |expression| {
                if (!expression.isGround()) return error.InvalidFact;
                try internInto(db, expression, &named);
            }
            break :removals &named;
        },
        .resolved => |facts| facts,
    };

    var additions: std.ArrayList(relation_store.Fact) = .empty;
    defer {
        for (additions.items) |fact| db.allocator.free(fact.terms);
        additions.deinit(db.allocator);
    }
    for (insertions) |expression| {
        if (!expression.isGround() or expression.negated) return error.InvalidFact;
        const terms = try internTerms(db, expression);
        additions.append(db.allocator, .{ .predicate = expression.predicate, .terms = terms }) catch |err| {
            db.allocator.free(terms);
            return err;
        };
    }

    const outcome = try maintenance.applyDelta(db, .{
        .removals = removals,
        .additions = additions.items,
        .kind = .base,
    }, touched);
    // A resolved fact was found in a copy of this database, under the value
    // identifiers this database uses too, so this database holds it. Were
    // that ever not so the retraction would silently under-delete, which is
    // worth asserting rather than discovering.
    if (deletions == .resolved) std.debug.assert(outcome.removed == deletions.len());
    return outcome;
}

/// Interns a ground expression's terms against the database, into terms the
/// caller owns.
fn internTerms(db: *database.Database, expression: syntax.Expr) ![]syntax.ValueId {
    const terms = try db.allocator.alloc(syntax.ValueId, expression.terms.len);
    errdefer db.allocator.free(terms);
    for (expression.terms, terms) |term, *id| id.* = try db.eval.termToValue(term, null);
    return terms;
}

/// Interns a ground expression and adds the fact it names to `store`.
fn internInto(
    db: *database.Database,
    expression: syntax.Expr,
    store: *relation_store.RelationStore,
) !void {
    const terms = try internTerms(db, expression);
    _ = store.insert(.{ .predicate = expression.predicate, .terms = terms }, false) catch |err| {
        db.allocator.free(terms);
        return err;
    };
}

/// What replacing a contribution did.
pub const Contributed = struct {
    /// How many base facts became present or absent, as `apply` counts them.
    changed: usize,
    /// Whether the contributor's own set of facts changed, which can happen
    /// with no base fact moving: another contributor may assert every fact
    /// it gained or lost.
    recorded: bool,
};

/// Replaces the facts `contributor` asserts with `facts`, and applies to the
/// base facts only what that changes: a fact no contributor asserts any more
/// is deleted, and a fact no contributor asserted before is inserted. See
/// "Contributor" in CONTEXT.md.
///
/// Those facts, and nothing else, go through `apply`, so the cost model is
/// asked about the facts that really move rather than the whole contribution,
/// and the closure is maintained as for any other batch. Mutates `db`
/// throughout and fails with it half-changed, like `apply`: a caller runs this
/// against a clone, as `transaction.contribute` does.
pub fn contribute(
    db: *database.Database,
    contributor: []const u8,
    facts: []const syntax.Expr,
) !Contributed {
    var interned: std.ArrayList(relation_store.Fact) = .empty;
    defer {
        for (interned.items) |fact| db.allocator.free(fact.terms);
        interned.deinit(db.allocator);
    }
    try interned.ensureTotalCapacity(db.allocator, facts.len);
    for (facts) |expression| {
        if (!expression.isGround() or expression.negated) return error.InvalidFact;
        const terms = try internTerms(db, expression);
        interned.appendAssumeCapacity(.{ .predicate = expression.predicate, .terms = terms });
    }

    var gone: relation_store.RelationStore = .init(db.allocator);
    defer gone.deinit();
    var arriving: std.ArrayList(usize) = .empty;
    defer arriving.deinit(db.allocator);
    const recorded = try db.contributions.replace(
        db.allocator,
        contributor,
        interned.items,
        &db.facts,
        &gone,
        &arriving,
    );
    if (gone.len() == 0 and arriving.items.len == 0) return .{ .changed = 0, .recorded = recorded };

    const insertions = try db.allocator.alloc(syntax.Expr, arriving.items.len);
    defer db.allocator.free(insertions);
    for (arriving.items, insertions) |position, *insertion| insertion.* = facts[position];
    return .{ .changed = try apply(db, .{ .resolved = &gone }, insertions), .recorded = recorded };
}

/// Applies the batch to the base facts alone, dirtying the strata that read
/// each predicate it really changed, for the next read to rebuild from.
fn recompute(
    db: *database.Database,
    deletions: Deletions,
    insertions: []const syntax.Expr,
) !usize {
    var count: usize = 0;
    switch (deletions) {
        .named => |expressions| for (expressions) |expression| {
            if (!expression.isGround()) return error.InvalidFact;
            const terms = try internTerms(db, expression);
            defer db.allocator.free(terms);
            if (try removeOne(db, .{ .predicate = expression.predicate, .terms = terms })) count += 1;
        },
        .resolved => |facts| for (0..facts.len()) |position| {
            const present = try removeOne(db, facts.factAt(position));
            // See `maintainBatch`: a resolved fact is one this database holds.
            std.debug.assert(present);
            if (present) count += 1;
        },
    }
    for (insertions) |expression| {
        const fact = try db.applyInsertion(expression, null) orelse continue;
        count += 1;
        try db.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
    }
    return count;
}

/// Takes one fact out of the base facts and dirties the strata that read its
/// predicate. Returns whether the database held the fact at all.
fn removeOne(db: *database.Database, fact: relation_store.Fact) !bool {
    if (!try db.applyRemoval(fact)) return false;
    try db.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
    return true;
}

const testing = std.testing;
const compile = @import("compile.zig");
const input = @import("input.zig");
const materialization = @import("materialization.zig");
const test_support = @import("test_support.zig");

/// Applies `predicate(atom)` as a one-fact insertion batch through the whole
/// update path, and returns the realized count.
fn applyOneInsertion(db: *database.Database, predicate: []const u8, atom: []const u8) !usize {
    const expression = try compile.compileRelation(db, predicate, &.{input.atom(atom)}, false);
    defer syntax.freeExpr(db.allocator, expression);
    return apply(db, .{ .named = &.{} }, &.{expression});
}

test "the estimate the model decides on and the count it measures are one batch" {
    // Neither number is observable through the public interface: a batch that
    // changes nothing is discarded with its transaction, so a caller cannot
    // tell an uncounted decision from a counted one, and the work the model
    // learns from is never reported. Both are asserted here because this is
    // the seam that pairs them.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try test_support.defineRule(&db, input.relation("reachable", &.{input.variable("X")}), &.{
        input.relation("node", &.{input.variable("X")}),
    });
    try materialization.ensureMaterialized(&db);
    // Pinned so both batches take the same path: what is under test is which
    // number reaches which half of the model, not which path it picks.
    db.eval.cost.policy = .incremental;

    // A batch naming one fact the database does not hold realizes one change,
    // is one decision, and is what the model learns its per-fact cost from.
    try testing.expectEqual(@as(usize, 1), try applyOneInsertion(&db, "node", "a"));
    try testing.expectEqual(@as(usize, 1), db.eval.cost.maintain_choices);
    try testing.expect(db.eval.cost.maintenance_work_per_fact != null);

    // Re-inserting it is still a decision — the model is asked before anything
    // is applied, and one fact is what the caller named. But the batch
    // realizes nothing, so it teaches the model nothing: the two numbers are
    // the same batch seen before and after, and only the second may be
    // learned from.
    const learned = db.eval.cost.maintenance_work_per_fact.?;
    try testing.expectEqual(@as(usize, 0), try applyOneInsertion(&db, "node", "a"));
    try testing.expectEqual(@as(usize, 2), db.eval.cost.maintain_choices);
    try testing.expectEqual(learned, db.eval.cost.maintenance_work_per_fact.?);
}
