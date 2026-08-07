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
//! hands over expressions it has already built, from descriptors or from
//! source. Staging and commit stay above too: everything here mutates the
//! database it is given, and a caller that needs the update to be atomic runs
//! it against a clone.

const std = @import("std");
const aggregate_view = @import("aggregate_view.zig");
const database = @import("database.zig");
const maintenance = @import("maintenance.zig");
const relation_store = @import("relation_store.zig");
const syntax = @import("syntax.zig");

/// Applies one batch of exact ground base-fact deletions and insertions with
/// set semantics, and returns how many base facts really changed — fewer than
/// the batch names whenever it deletes an absent fact or re-inserts a present
/// one.
///
/// Deletions run before insertions. Delete-and-rederive joins against a
/// snapshot of the pre-deletion closure, so a fact inserted first would be
/// over-deleted against a closure it was never absent from.
pub fn apply(
    db: *database.Database,
    deletions: []const syntax.Expr,
    insertions: []const syntax.Expr,
) !usize {
    // The batch size is only an estimate of the work ahead — it counts what
    // the caller named, and a batch naming facts the database already agrees
    // with does proportionally less. What it actually changed is measured
    // afterwards and fed back as the realized count.
    const maintain = db.canMaintain() and
        db.eval.cost.decide(deletions.len + insertions.len) == .maintain;
    const span = db.eval.cost.begin();

    // Facts the aggregate phase must reconsider: every fact this batch took
    // out of the closure, and every fact it derived into it.
    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const deleted = try applyDeletions(db, deletions, maintain, &touched);
    const inserted = try applyInsertions(db, insertions, maintain, &touched);
    if (touched.len() > 0) try aggregate_view.maintainAggregates(db, &touched);

    const realized = deleted + inserted;
    if (maintain) db.eval.cost.noteMaintenance(realized, span);
    return realized;
}

/// Applies base facts a caller has already removed from `db.facts`, and
/// returns how many there were.
///
/// This exists for retraction, which resolves its goals by evaluating them
/// against a staging database and recovers what it removed by comparing that
/// database against the committed one — so unlike a batch it arrives holding
/// facts rather than expressions, and holding them already removed. It is the
/// same path as `apply` from the cost decision down, and it is temporary:
/// once retraction hands over the facts its goals resolved to instead of
/// diffing two databases for them, it can call `apply` and this goes away.
pub fn applyRemoved(
    db: *database.Database,
    removed: *relation_store.RelationStore,
) !usize {
    // Retraction resolves its goals before deciding, so unlike a batch it
    // knows exactly how many base facts it changes: the estimate the model
    // decides on and the count it later measures are the same.
    const delta = removed.len();
    const maintain = db.canMaintain() and db.eval.cost.decide(delta) == .maintain;
    if (maintain and delta > 0) {
        const span = db.eval.cost.begin();
        var touched: relation_store.RelationStore = .init(db.allocator);
        defer touched.deinit();
        _ = try maintenance.applyRemovals(db, removed, &touched);
        if (touched.len() > 0) try aggregate_view.maintainAggregates(db, &touched);
        db.eval.cost.noteMaintenance(delta, span);
    } else {
        for (0..removed.len()) |position| {
            const fact = removed.factAt(position);
            try db.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
        }
    }
    return delta;
}

/// Removes this batch's deletions from the base facts. When maintaining, they
/// take the delete-and-rederive path and everything that leaves the closure is
/// added to `touched`; otherwise each removal dirties the strata that read its
/// predicate.
fn applyDeletions(
    db: *database.Database,
    deletions: []const syntax.Expr,
    maintain: bool,
    touched: *relation_store.RelationStore,
) !usize {
    var removed: relation_store.RelationStore = .init(db.allocator);
    defer removed.deinit();
    var count: usize = 0;
    for (deletions) |expression| {
        if (!expression.isGround()) return error.InvalidFact;
        const terms = try db.allocator.alloc(syntax.ValueId, expression.terms.len);
        defer db.allocator.free(terms);
        for (expression.terms, terms) |term, *id| id.* = try db.eval.termToValue(term, null);
        const fact: relation_store.Fact = .{ .predicate = expression.predicate, .terms = terms };
        if (!try db.facts.removeFact(fact)) continue;
        count += 1;
        if (maintain) {
            try relation_store.copyFactInto(db.allocator, &removed, fact, false);
        } else {
            try db.markBaseChanged(.{ .name = fact.predicate, .arity = terms.len });
        }
    }
    _ = try maintenance.applyRemovals(db, &removed, touched);
    return count;
}

/// Adds this batch's insertions to the base facts. When maintaining, the ones
/// that were really new also join the clean closure and propagate through the
/// positive strata, with everything derived added to `touched`; otherwise each
/// insertion dirties the strata that read its predicate.
fn applyInsertions(
    db: *database.Database,
    insertions: []const syntax.Expr,
    maintain: bool,
    touched: *relation_store.RelationStore,
) !usize {
    // Maintaining the deletions cannot have taken the closure out from under
    // this phase: a delete-and-rederive fallback repairs the closure through
    // `ensureMaterialized` rather than leaving it dirty.
    std.debug.assert(!maintain or
        (db.closure != null and db.materialization == .clean));
    // Facts borrowed from `db.facts`, which owns their terms. Inserting more
    // facts can move the entries holding them but not the terms themselves,
    // and nothing here removes a fact, so these stay valid until they are
    // copied into the closure below.
    var staged: std.ArrayList(relation_store.Fact) = .empty;
    defer staged.deinit(db.allocator);
    var count: usize = 0;
    for (insertions) |expression| {
        const fact = try db.applyInsertion(expression) orelse continue;
        count += 1;
        if (maintain) {
            try staged.append(db.allocator, fact);
        } else {
            try db.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
        }
    }
    if (!maintain) return count;
    const batch_start = try maintenance.stageInsertions(db, staged.items, .base);
    _ = try maintenance.applyStaged(db, batch_start, touched);
    return count;
}

const testing = std.testing;
const compile = @import("compile.zig");
const input = @import("input.zig");
const materialization = @import("materialization.zig");
const validation = @import("validation.zig");

/// Installs a rule from descriptors, which is the part of `addRuleClauses`
/// these tests need. That function belongs to `statement.zig`, one layer above
/// this one, so a test here cannot call it — and the parser is two above.
fn defineRule(
    db: *database.Database,
    head: input.Goal,
    body: []const input.Goal,
) !void {
    const compiled_head = try compile.compileRelation(db, head.relation.predicate, head.relation.terms, false);
    const compiled_body = try compile.compileGoals(db, body);
    defer db.allocator.free(compiled_body);
    const ordered = try validation.orderClauses(db, compiled_body);
    errdefer db.allocator.free(ordered);
    const id = db.eval.next_rule_id;
    db.eval.next_rule_id += 1;
    try db.eval.rules.append(db.allocator, .{ .id = id, .head = compiled_head, .body = ordered });
    materialization.invalidateAnalysis(db);
}

/// Applies `predicate(atom)` as a one-fact insertion batch through the whole
/// update path, and returns the realized count.
fn applyOneInsertion(db: *database.Database, predicate: []const u8, atom: []const u8) !usize {
    const expression = try compile.compileRelation(db, predicate, &.{input.atom(atom)}, false);
    defer syntax.freeExpr(db.allocator, expression);
    return apply(db, &.{}, &.{expression});
}

test "the estimate the model decides on and the count it measures are one batch" {
    // Neither number is observable through the public interface: a batch that
    // changes nothing is discarded with its transaction, so a caller cannot
    // tell an uncounted decision from a counted one, and the work the model
    // learns from is never reported. Both are asserted here because this is
    // the seam that pairs them.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineRule(&db, input.relation("reachable", &.{input.variable("X")}), &.{
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

test "an insertion reaching negation surfaces as a rebuild, not as a clean maintain" {
    // `db.materialization` cannot answer this: the fallback repairs the
    // closure before returning, so it reads `.clean` on both paths. The
    // outcome the delta reports is what separates them, and the reason the
    // watermark must not be collected from afterwards.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineRule(&db, input.relation("blocked", &.{input.variable("X")}), &.{
        input.relation("node", &.{input.variable("X")}),
        input.not("skip", &.{input.variable("X")}),
    });
    _ = try applyOneInsertion(&db, "node", "a");
    try materialization.ensureMaterialized(&db);
    try testing.expectEqual(database.Materialization.clean, db.materialization);

    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const expression = try compile.compileRelation(&db, "skip", &.{input.atom("a")}, false);
    defer syntax.freeExpr(db.allocator, expression);
    const fact = (try db.applyInsertion(expression)).?;
    const batch_start = try maintenance.stageInsertions(&db, &.{fact}, .base);

    try testing.expectEqual(
        maintenance.DeltaOutcome.rebuilt,
        try maintenance.applyStaged(&db, batch_start, &touched),
    );
    try testing.expectEqual(@as(usize, 1), db.rebuild_fallbacks);
    // Clean, and yet not maintained — and `touched` is empty, because the
    // rebuild already recomputed everything the aggregate phase would have
    // been given it to reconsider.
    try testing.expectEqual(database.Materialization.clean, db.materialization);
    try testing.expectEqual(@as(usize, 0), touched.len());
}
