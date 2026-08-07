//! The persistent closure's lifecycle: when it is valid, what invalidates it,
//! and how a rebuild reuses the strata an update did not touch.
//!
//! Materialization is lazy. An update marks the first stratum that depends on
//! what it changed, and the next evaluation repairs from there, reusing the
//! derived facts of every stratum below. The tri-state that records this is
//! the pivot the whole maintenance layer turns on: `canMaintain` is what the
//! cost model is only consulted behind, and `markDirty` plus
//! `ensureMaterialized` are the fallback every incremental path abandons to.

const root = @import("root.zig");
const relation_store = @import("relation_store.zig");
const aggregate_view = @import("aggregate_view.zig");

const Jatalog = root.Jatalog;
const PredicateKey = relation_store.PredicateKey;
const RelationStore = relation_store.RelationStore;
const copyFactInto = relation_store.copyFactInto;

pub const Materialization = union(enum) {
    uninitialized,
    clean,
    dirty_from_stratum: usize,
};

/// Whether the closure is in a state incremental maintenance can start
/// from. A dirty closure has to be repaired regardless of cost, so the
/// cost model is consulted only when this holds.
pub fn canMaintain(db: *const Jatalog) bool {
    return db.closure != null and db.materialization == .clean;
}
/// Compares the maintained closure against a rebuild performed on a
/// throwaway copy, so verification never disturbs this database.
pub fn verifyShadow(db: *Jatalog) !void {
    if (!db.shadow_verification) return;
    const closure = if (db.closure) |*value| value else return;
    var staging = try db.clone();
    defer staging.deinit();
    var reference = try staging.facts.clone();
    defer reference.deinit();
    try staging.eval.expandNaive(&reference);
    if (reference.len() != closure.len()) return error.MaintenanceMismatch;
    for (0..reference.len()) |index|
        if (!try closure.contains(reference.factAt(index))) return error.MaintenanceMismatch;
}
pub fn closureStore(db: *Jatalog) *RelationStore {
    if (db.closure) |*closure| return closure;
    return &db.facts;
}
/// Drops everything derived from the rule set: the evaluator's cached
/// stratification and the auxiliary views built from it.
pub fn invalidateAnalysis(db: *Jatalog) void {
    db.eval.invalidateAnalysis();
    aggregate_view.dropAuxiliaryViews(db);
}
pub fn markDirty(db: *Jatalog, level: usize) void {
    switch (db.materialization) {
        .uninitialized => {},
        .clean => db.materialization = .{ .dirty_from_stratum = level },
        .dirty_from_stratum => |existing| db.materialization = .{
            .dirty_from_stratum = @min(existing, level),
        },
    }
}
/// Marks the first stratum that depends on a changed base predicate as
/// dirty. A predicate no rule reads dirties the level past the last
/// stratum, so the rebuild refreshes only the closure's base partition.
pub fn markBaseChanged(db: *Jatalog, key: PredicateKey) !void {
    if (db.closure == null) return;
    const analysis = try db.eval.ensureAnalysis();
    markDirty(db, analysis.first_dependent.get(key) orelse analysis.max_level + 1);
}
/// Builds or refreshes the persistent closure. Materialization is lazy:
/// a database whose rule set is empty never allocates derived-state
/// machinery, and a dirty closure is rebuilt from its first dirty
/// stratum, reusing the derived facts of every stratum below it. On
/// failure the previous closure and state remain installed; values
/// interned by the aborted expansion stay in the value table and are
/// reclaimed at deinit.
pub fn ensureMaterialized(db: *Jatalog) !void {
    if (db.eval.rules.items.len == 0) return;
    const from_level: usize = switch (db.materialization) {
        .clean => return,
        .uninitialized => 0,
        .dirty_from_stratum => |level| level,
    };
    // Only a dirty-stratum rebuild is the alternative an update chooses
    // against. The first full build from `uninitialized` is a different
    // and much larger operation, so recording it would permanently
    // overstate what recomputation costs.
    const repairs_update = db.materialization == .dirty_from_stratum;
    const span = db.eval.cost.begin();
    const closure = try buildClosure(db, from_level);
    if (db.closure) |*old| old.deinit();
    db.closure = closure;
    db.materialization = .clean;
    try aggregate_view.rebuildAuxiliaryViews(db);
    // This also runs as the fallback inside a maintenance attempt, where
    // claiming the work keeps it out of the maintenance estimate.
    if (repairs_update) db.eval.cost.noteRebuild(span);
}
fn buildClosure(db: *Jatalog, from_level: usize) !RelationStore {
    var closure = try db.facts.clone();
    errdefer closure.deinit();
    if (from_level > 0) {
        const analysis = try db.eval.ensureAnalysis();
        if (db.closure) |*old| {
            for (0..old.len()) |index| {
                if (!old.isDerived(index)) continue;
                const fact = old.factAt(index);
                const key: PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
                if ((analysis.strata.get(key) orelse 0) >= from_level) continue;
                try copyFactInto(db.allocator, &closure, fact, true);
            }
        }
    }
    try db.eval.expandFrom(&closure, from_level);
    return closure;
}
pub fn expand(db: *Jatalog, facts: *RelationStore) !void {
    try db.eval.expandFrom(facts, 0);
}
