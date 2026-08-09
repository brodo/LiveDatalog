//! The persistent closure's lifecycle: when it is valid, what invalidates it,
//! and how a rebuild reuses the strata an update did not touch.
//!
//! Materialization is lazy. An update marks the first stratum that depends on
//! what it changed, and the next evaluation repairs from there, reusing the
//! derived facts of every stratum below. The tri-state that records this is
//! the pivot the whole maintenance layer turns on: it lives on the database
//! itself, along with the predicates that read and set it, and
//! `ensureMaterialized` here is the fallback every incremental path abandons
//! to.
//!
//! The auxiliary views projected aggregate rules keep are derived state too,
//! so they are built and dropped here, on the same schedule as the closure
//! they are computed from.

const std = @import("std");
const database = @import("database.zig");
const auxiliary_view = @import("auxiliary_view.zig");
const errors = @import("errors.zig");
const relation_store = @import("relation_store.zig");
const syntax = @import("syntax.zig");

/// Compares the maintained closure against a rebuild performed on a
/// throwaway copy, so verification never disturbs this database.
pub fn verifyShadow(db: *database.Database) !void {
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
/// Drops everything derived from the rule set: the evaluator's cached
/// stratification and the auxiliary views built from it.
pub fn invalidateAnalysis(db: *database.Database) void {
    db.eval.invalidateAnalysis();
    dropAuxiliaryViews(db);
}
/// Builds or refreshes the persistent closure. Materialization is lazy:
/// a database whose rule set is empty never allocates derived-state
/// machinery, and a dirty closure is rebuilt from its first dirty
/// stratum, reusing the derived facts of every stratum below it. On
/// failure the previous closure and state remain installed; values
/// interned by the aborted expansion stay in the value table and are
/// reclaimed at deinit.
pub fn ensureMaterialized(db: *database.Database) !void {
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
    try rebuildAuxiliaryViews(db);
    // This also runs as the fallback inside a maintenance attempt, where
    // claiming the work keeps it out of the maintenance estimate.
    if (repairs_update) db.eval.cost.noteRebuild(span);
}
fn buildClosure(db: *database.Database, from_level: usize) !relation_store.RelationStore {
    var closure = try db.facts.clone();
    errdefer closure.deinit();
    if (from_level > 0) {
        const analysis = try db.eval.ensureAnalysis();
        if (db.closure) |*old| {
            for (0..old.len()) |index| {
                if (!old.isDerived(index)) continue;
                const fact = old.factAt(index);
                const key: relation_store.PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
                if ((analysis.strata.get(key) orelse 0) >= from_level) continue;
                try relation_store.copyFactInto(db.allocator, &closure, fact, true);
            }
        }
    }
    try db.eval.expandFrom(&closure, from_level);
    return closure;
}
pub fn expand(db: *database.Database, facts: *relation_store.RelationStore) !void {
    try db.eval.expandFrom(facts, 0);
}

pub fn dropAuxiliaryViews(db: *database.Database) void {
    for (db.auxiliary.items) |*view| view.deinit(db.allocator);
    db.auxiliary.clearRetainingCapacity();
}
pub fn auxiliaryFor(db: *database.Database, rule_id: u32) ?*auxiliary_view.AuxiliaryView {
    for (db.auxiliary.items) |*view| if (view.rule_id == rule_id) return view;
    return null;
}
/// Rebuilds every projected aggregate view from the materialized
/// closure. Views are built into a temporary list and installed only on
/// success, so a failure leaves the previous views in place.
pub fn rebuildAuxiliaryViews(db: *database.Database) !void {
    var built: std.ArrayList(auxiliary_view.AuxiliaryView) = .empty;
    errdefer {
        for (built.items) |*view| view.deinit(db.allocator);
        built.deinit(db.allocator);
    }
    for (db.eval.rules.items) |rule| {
        const clause_index = syntax.maintainableAggregateIndex(rule) orelse continue;
        var view = (try buildAuxiliaryView(db, rule, clause_index)) orelse continue;
        built.append(db.allocator, view) catch |err| {
            view.deinit(db.allocator);
            return err;
        };
    }
    for (db.auxiliary.items) |*view| view.deinit(db.allocator);
    db.auxiliary.deinit(db.allocator);
    db.auxiliary = built;
}
/// Returns the projected variables of a maintained aggregate rule: the
/// outer-goal variables its head omits. An empty result means the head
/// retains every outer variable, so each head tuple already belongs to
/// exactly one group and no auxiliary view is needed.
fn projectedVariables(db: *database.Database, rule: syntax.Rule, clause_index: usize) ![]syntax.Id {
    const outer = try syntax.outerClauses(db.allocator, rule, clause_index);
    defer db.allocator.free(outer);
    var outer_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer outer_variables.deinit(db.allocator);
    for (outer) |clause|
        try syntax.collectClauseSurfaceVariables(db.allocator, clause, &outer_variables);
    var head_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer head_variables.deinit(db.allocator);
    for (rule.head.terms) |term| try syntax.collectTermVariables(db.allocator, term, &head_variables);

    var projected: std.ArrayList(syntax.Id) = .empty;
    errdefer projected.deinit(db.allocator);
    var iterator = outer_variables.keyIterator();
    while (iterator.next()) |variable| {
        if (!head_variables.contains(variable.*))
            try projected.append(db.allocator, variable.*);
    }
    std.mem.sort(syntax.Id, projected.items, {}, std.sort.asc(syntax.Id));
    return projected.toOwnedSlice(db.allocator);
}
fn buildAuxiliaryView(db: *database.Database, rule: syntax.Rule, clause_index: usize) !?auxiliary_view.AuxiliaryView {
    const projected = try projectedVariables(db, rule, clause_index);
    var projected_owned = true;
    defer if (projected_owned) db.allocator.free(projected);
    if (projected.len == 0) return null;
    // The lookup mask addresses one bit per auxiliary column.
    if (projected.len + rule.head.terms.len > 64) return null;

    var view: auxiliary_view.AuxiliaryView = .{
        .rule_id = rule.id,
        .projected = projected,
        .head_arity = rule.head.terms.len,
        .tuples = .init(db.allocator),
    };
    projected_owned = false;
    errdefer view.deinit(db.allocator);

    const outer = try syntax.outerClauses(db.allocator, rule, clause_index);
    defer db.allocator.free(outer);
    var groups: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (groups.items) |*group| group.deinit(db.allocator);
        groups.deinit(db.allocator);
    }
    var initial: syntax.Binding = .{};
    defer initial.deinit(db.allocator);
    db.eval.solve(
        &db.closure.?,
        rule.head,
        outer,
        &initial,
        &groups,
        null,
    ) catch |err| switch (err) {
        errors.Error.NumericType, errors.Error.NumericOverflow => return view,
        else => return err,
    };
    for (groups.items) |*group| try recordGroupTuples(db, rule, &view, group);
    return view;
}
/// Records the auxiliary tuples one group contributes: its projected
/// values followed by each head tuple the rule derives for it.
fn recordGroupTuples(
    db: *database.Database,
    rule: syntax.Rule,
    view: *auxiliary_view.AuxiliaryView,
    group: *const syntax.Binding,
) !void {
    var answers: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    db.eval.solve(
        &db.closure.?,
        rule.head,
        rule.body,
        group,
        &answers,
        null,
    ) catch |err| switch (err) {
        errors.Error.NumericType, errors.Error.NumericOverflow => return,
        else => return err,
    };
    for (answers.items) |*answer| {
        const head_fact = try db.eval.deriveFact(rule.head, answer);
        defer db.allocator.free(head_fact.terms);
        const terms = (try auxiliaryTerms(db, view, group, head_fact)) orelse continue;
        _ = view.tuples.insert(.{ .predicate = view.rule_id, .terms = terms }, false) catch |err| {
            db.allocator.free(terms);
            return err;
        };
    }
}
pub fn auxiliaryTerms(
    db: *database.Database,
    view: *const auxiliary_view.AuxiliaryView,
    group: *const syntax.Binding,
    head: relation_store.Fact,
) !?[]relation_store.ValueId {
    const terms = try db.allocator.alloc(relation_store.ValueId, view.arity());
    var owned = true;
    defer if (owned) db.allocator.free(terms);
    for (view.projected, 0..) |variable, index| {
        terms[index] = group.values.get(variable) orelse return null;
    }
    @memcpy(terms[view.projected.len..], head.terms);
    owned = false;
    return terms;
}
