//! Incremental maintenance of rules containing one unnested `setof`.
//!
//! An aggregate is evaluated during rule matching rather than stored as its
//! own relation, so the maintained unit is a *group*: the binding of the
//! rule's outer goals, whose value is the head tuple that binding derives.
//! When a batch changes an aggregate's inner relations, only the groups a
//! changed fact can reach are recomputed; a group whose canonical list moved
//! emits its stale head tuples as deletions and its new one as an insertion,
//! which then cascade through the ordinary maintenance engine.
//!
//! A rule whose head projects some outer variable away needs more: several
//! groups can derive the same head tuple, so each such rule owns a CReaM-style
//! auxiliary view counting derivations, and the head tuple appears and
//! disappears only on the zero-to-one and one-to-zero transitions.
//!
//! This layer sits on top of maintenance.zig — it emits changes and lets the
//! deletion and insertion engines apply them — and, like that module, takes
//! the database because the views it maintains are the database's own state.

const std = @import("std");
const database = @import("database.zig");
const auxiliary_view = @import("auxiliary_view.zig");
const errors = @import("errors.zig");
const materialization = @import("materialization.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");
const maintenance = @import("maintenance.zig");

/// Maintains rules containing one unnested `setof` after a batch changed
/// the aggregate's inner relations. Only groups reachable from a changed
/// inner fact are recomputed. A group whose canonical list changed emits
/// its stale head tuples as deletions and its recomputed tuple as an
/// insertion, which then cascade through the ordinary deletion and
/// insertion maintenance. Rounds repeat while aggregate results keep
/// changing, with a bounded fallback to a full rebuild.
pub fn maintainAggregates(db: *database.Database, touched: *relation_store.RelationStore) !void {
    if (db.closure == null or db.materialization != .clean) return;
    const round_cap = (try db.eval.ensureAnalysis()).max_level + 4;
    var round: usize = 0;
    while (true) {
        round += 1;
        if (round > round_cap) {
            db.rebuild_fallbacks += 1;
            db.markDirty(0);
            return materialization.ensureMaterialized(db);
        }
        var removals: relation_store.RelationStore = .init(db.allocator);
        defer removals.deinit();
        var additions: std.ArrayList(relation_store.Fact) = .empty;
        defer {
            for (additions.items) |fact| db.allocator.free(fact.terms);
            additions.deinit(db.allocator);
        }
        var changed: std.AutoHashMapUnmanaged(relation_store.PredicateKey, void) = .empty;
        defer changed.deinit(db.allocator);
        try relation_store.collectPredicateKeys(db.allocator, touched, 0, &changed);
        for (db.eval.rules.items) |rule| {
            const clause_index = syntax.maintainableAggregateIndex(rule) orelse continue;
            // A projected view also reacts to outer-goal changes, which
            // create and destroy whole groups.
            const trigger = if (materialization.auxiliaryFor(db, rule.id) == null)
                rule.body[clause_index].aggregate.body
            else
                rule.body;
            if (!syntax.clausesReadGrownAnywhere(trigger, &changed)) continue;
            try maintainAggregateRule(db, rule, clause_index, touched, &removals, &additions);
        }
        if (removals.len() == 0 and additions.items.len == 0) return;

        // This round's stale head tuples and recomputed ones are one delta,
        // and reach the closure the way a base update's do. What it moved
        // replaces `touched` as the next round's input, and the cascade ends
        // when that is nothing. A round that falls back to a rebuild does not
        // end it by itself: when only its removals rebuilt, its additions
        // were propagated afterwards, and an aggregate over what they derived
        // is left for the next round like any other.
        _ = try maintenance.applyDelta(db, .{
            .removals = &removals,
            .additions = additions.items,
            .kind = .derived,
        }, touched);
        if (touched.len() == 0) return;
    }
}
fn maintainAggregateRule(
    db: *database.Database,
    rule: syntax.Rule,
    clause_index: usize,
    touched: *relation_store.RelationStore,
    removals: *relation_store.RelationStore,
    additions: *std.ArrayList(relation_store.Fact),
) !void {
    const aggregate = rule.body[clause_index].aggregate;
    const outer = try syntax.outerClauses(db.allocator, rule, clause_index);
    defer db.allocator.free(outer);

    // Only variables the outer goals or the head can constrain identify a
    // group; variables local to the aggregate body must stay free.
    var scope: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer scope.deinit(db.allocator);
    for (outer) |clause|
        try syntax.collectClauseSurfaceVariables(db.allocator, clause, &scope);
    for (rule.head.terms) |term| try syntax.collectTermVariables(db.allocator, term, &scope);

    var groups: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (groups.items) |*group| group.deinit(db.allocator);
        groups.deinit(db.allocator);
    }
    // A changed fact reaches a group either through the aggregate's
    // inner goals (its member set changed) or through the outer goals
    // (the group itself appeared or disappeared).
    const view = materialization.auxiliaryFor(db, rule.id);
    for (0..touched.len()) |index| {
        const fact = touched.factAt(index);
        for ([_][]const syntax.Clause{ aggregate.body, outer }) |clauses| {
            for (clauses) |candidate| {
                const expression = switch (candidate) {
                    .relational => |value| value,
                    else => continue,
                };
                if (expression.predicate != fact.predicate or
                    expression.terms.len != fact.terms.len) continue;
                var seed: syntax.Binding = .{};
                defer seed.deinit(db.allocator);
                if (!try db.eval.unify(fact, expression, &seed)) continue;
                var restricted: syntax.Binding = .{};
                defer restricted.deinit(db.allocator);
                for (seed.values.keys(), seed.values.values()) |variable, value| {
                    if (scope.contains(variable))
                        try restricted.values.put(db.allocator, variable, value);
                }
                try collectAggregateGroups(db, outer, &restricted, &groups);
            }
        }
    }

    db.maintained_groups += groups.items.len;
    for (groups.items) |*group| {
        if (view) |projected| {
            try maintainProjectedGroup(db, rule, projected, group, removals, additions);
        } else {
            try maintainAggregateGroup(db, rule, group, removals, additions);
        }
    }
    if (view) |projected|
        try sweepVanishedGroups(db, rule, clause_index, projected, touched, removals);
}
/// Maintains one group of a projected view through its derivation
/// counts: an auxiliary tuple that no longer holds is retracted, and its
/// head tuple is deleted only on the resulting one-to-zero transition;
/// a newly derived auxiliary tuple makes its head tuple visible only on
/// the zero-to-one transition. A group whose aggregate list changed
/// therefore transfers support from the old head tuple to the new one
/// within a single batch.
fn maintainProjectedGroup(
    db: *database.Database,
    rule: syntax.Rule,
    view: *auxiliary_view.AuxiliaryView,
    group: *const syntax.Binding,
    removals: *relation_store.RelationStore,
    additions: *std.ArrayList(relation_store.Fact),
) !void {
    var derived: relation_store.RelationStore = .init(db.allocator);
    defer derived.deinit();
    try deriveGroupHeads(db, rule, group, &derived);

    // Auxiliary tuples this group currently contributes.
    var mask: u64 = 0;
    var bound: [64]relation_store.ValueId = undefined;
    for (view.projected, 0..) |variable, index| {
        bound[index] = group.values.get(variable) orelse return;
        mask |= @as(u64, 1) << @intCast(index);
    }
    var stale: std.ArrayList(relation_store.Fact) = .empty;
    defer {
        for (stale.items) |fact| db.allocator.free(fact.terms);
        stale.deinit(db.allocator);
    }
    {
        const candidates = try view.tuples.lookup(view.key(), mask, bound[0..view.projected.len]);
        for (candidates) |candidate| {
            const tuple = view.tuples.factAt(candidate);
            if (!std.mem.eql(relation_store.ValueId, tuple.terms[0..view.projected.len], bound[0..view.projected.len]))
                continue;
            const head: relation_store.Fact = .{
                .predicate = rule.head.predicate,
                .terms = @constCast(view.headTerms(tuple)),
            };
            // Projected values alone do not identify a group: head
            // variables the group binds must agree as well, or the
            // tuple belongs to a different group sharing these values.
            var owner = try group.clone(db.allocator);
            defer owner.deinit(db.allocator);
            if (!try db.eval.unify(head, rule.head, &owner)) continue;
            if (try derived.contains(head)) continue;
            try relation_store.appendFactCopy(db.allocator, &stale, tuple);
        }
    }
    for (stale.items) |tuple| {
        const head = view.headTerms(tuple);
        const before = try view.derivationCount(head);
        if (!try view.tuples.removeFact(tuple)) continue;
        if (before == 1) try recordHeadRemoval(db, rule, head, removals);
    }

    for (0..derived.len()) |index| {
        const head = derived.factAt(index);
        const terms = (try materialization.auxiliaryTerms(db, view, group, head)) orelse continue;
        var owned = true;
        defer if (owned) db.allocator.free(terms);
        const tuple: relation_store.Fact = .{ .predicate = view.rule_id, .terms = terms };
        if (try view.tuples.contains(tuple)) continue;
        const before = try view.derivationCount(view.headTerms(tuple));
        owned = false;
        _ = view.tuples.insert(tuple, false) catch |err| {
            db.allocator.free(terms);
            return err;
        };
        if (before == 0 and !try db.closure.?.contains(head))
            try relation_store.appendFactCopy(db.allocator, additions, head);
    }
}
/// Retracts auxiliary tuples whose group no longer has any solution of
/// the rule's outer goals, deleting the head tuple on a one-to-zero
/// derivation-count transition. Only groups a changed outer-goal fact
/// can reach are examined: a group can vanish only when an outer fact
/// disappears, so batches that touch just the aggregate's members do no
/// sweeping at all.
fn sweepVanishedGroups(
    db: *database.Database,
    rule: syntax.Rule,
    clause_index: usize,
    view: *auxiliary_view.AuxiliaryView,
    touched: *relation_store.RelationStore,
    removals: *relation_store.RelationStore,
) !void {
    const outer = try syntax.outerClauses(db.allocator, rule, clause_index);
    defer db.allocator.free(outer);

    var candidates: relation_store.RelationStore = .init(db.allocator);
    defer candidates.deinit();
    try collectSweepCandidates(db, rule, view, outer, touched, &candidates);

    for (0..candidates.len()) |index| {
        const tuple = candidates.factAt(index);
        var seed: syntax.Binding = .{};
        defer seed.deinit(db.allocator);
        // The group is identified by its projected values together with
        // the head variables the outer goals bind.
        const stored: relation_store.Fact = .{
            .predicate = rule.head.predicate,
            .terms = @constCast(view.headTerms(tuple)),
        };
        if (!try db.eval.unify(stored, rule.head, &seed)) continue;
        for (view.projected, 0..) |variable, position|
            try seed.values.put(db.allocator, variable, tuple.terms[position]);
        var solutions: std.ArrayList(syntax.Binding) = .empty;
        defer {
            for (solutions.items) |*solution| solution.deinit(db.allocator);
            solutions.deinit(db.allocator);
        }
        db.eval.solve(
            &db.closure.?,
            rule.head,
            outer,
            &seed,
            &solutions,
            null,
        ) catch |err| switch (err) {
            errors.Error.NumericType, errors.Error.NumericOverflow => continue,
            else => return err,
        };
        if (solutions.items.len > 0) continue;
        const head = view.headTerms(tuple);
        const before = try view.derivationCount(head);
        if (!try view.tuples.removeFact(tuple)) continue;
        if (before == 1) try recordHeadRemoval(db, rule, head, removals);
    }
}
/// Auxiliary tuples a changed outer-goal fact could have invalidated,
/// found by binding the fact against each outer goal and looking up the
/// auxiliary columns that binding determines.
fn collectSweepCandidates(
    db: *database.Database,
    rule: syntax.Rule,
    view: *auxiliary_view.AuxiliaryView,
    outer: []const syntax.Clause,
    touched: *relation_store.RelationStore,
    candidates: *relation_store.RelationStore,
) !void {
    for (0..touched.len()) |index| {
        const fact = touched.factAt(index);
        for (outer) |clause| {
            const expression = switch (clause) {
                .relational => |value| value,
                else => continue,
            };
            if (expression.predicate != fact.predicate or
                expression.terms.len != fact.terms.len) continue;
            var binding: syntax.Binding = .{};
            defer binding.deinit(db.allocator);
            if (!try db.eval.unify(fact, expression, &binding)) continue;

            var mask: u64 = 0;
            var bound: [64]relation_store.ValueId = undefined;
            var count: usize = 0;
            for (view.projected, 0..) |variable, position| {
                const value = binding.values.get(variable) orelse continue;
                mask |= @as(u64, 1) << @intCast(position);
                bound[count] = value;
                count += 1;
            }
            for (rule.head.terms, 0..) |term, position| {
                const variable = switch (term) {
                    .variable => |name| name,
                    else => continue,
                };
                const value = binding.values.get(variable) orelse continue;
                mask |= @as(u64, 1) << @intCast(view.projected.len + position);
                bound[count] = value;
                count += 1;
            }
            for (try view.tuples.lookup(view.key(), mask, bound[0..count])) |candidate| {
                const tuple = view.tuples.factAt(candidate);
                if (try candidates.contains(tuple)) continue;
                try relation_store.copyFactInto(db.allocator, candidates, tuple, false);
            }
        }
    }
}
fn recordHeadRemoval(
    db: *database.Database,
    rule: syntax.Rule,
    head: []const relation_store.ValueId,
    removals: *relation_store.RelationStore,
) !void {
    const fact: relation_store.Fact = .{ .predicate = rule.head.predicate, .terms = @constCast(head) };
    if (!try db.closure.?.contains(fact)) return;
    if (try removals.contains(fact)) return;
    try relation_store.copyFactInto(db.allocator, removals, fact, true);
}
fn deriveGroupHeads(
    db: *database.Database,
    rule: syntax.Rule,
    group: *const syntax.Binding,
    derived: *relation_store.RelationStore,
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
        const fact = try db.eval.deriveFact(rule.head, answer);
        _ = derived.insert(fact, true) catch |err| {
            db.allocator.free(fact.terms);
            return err;
        };
    }
}
fn collectAggregateGroups(
    db: *database.Database,
    outer: []const syntax.Clause,
    seed: *const syntax.Binding,
    groups: *std.ArrayList(syntax.Binding),
) !void {
    var solutions: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (solutions.items) |*solution| solution.deinit(db.allocator);
        solutions.deinit(db.allocator);
    }
    db.eval.solve(
        &db.closure.?,
        null,
        outer,
        seed,
        &solutions,
        null,
    ) catch |err| switch (err) {
        errors.Error.NumericType, errors.Error.NumericOverflow => return,
        else => return err,
    };
    for (solutions.items) |*solution| {
        var duplicate = false;
        for (groups.items) |*existing| {
            if (syntax.bindingsEqual(existing, solution)) {
                duplicate = true;
                break;
            }
        }
        if (duplicate) continue;
        var copy = try solution.clone(db.allocator);
        groups.append(db.allocator, copy) catch |err| {
            copy.deinit(db.allocator);
            return err;
        };
    }
}
/// Recomputes one group: the head tuples currently stored for it become
/// deletions unless the recomputation still derives them, and newly
/// derived tuples become insertions.
fn maintainAggregateGroup(
    db: *database.Database,
    rule: syntax.Rule,
    group: *const syntax.Binding,
    removals: *relation_store.RelationStore,
    additions: *std.ArrayList(relation_store.Fact),
) !void {
    var derived: relation_store.RelationStore = .init(db.allocator);
    defer derived.deinit();
    try deriveGroupHeads(db, rule, group, &derived);

    // Stale stored tuples for this group: head matches under the group
    // binding but the recomputation no longer derives them.
    for (try db.eval.lookupCandidates(&db.closure.?, rule.head, group)) |candidate| {
        const stored = db.closure.?.factAt(candidate);
        var matched = try group.clone(db.allocator);
        defer matched.deinit(db.allocator);
        if (!try db.eval.unify(stored, rule.head, &matched)) continue;
        if (try derived.contains(stored)) continue;
        if (try removals.contains(stored)) continue;
        try relation_store.copyFactInto(db.allocator, removals, stored, true);
    }

    for (0..derived.len()) |index| {
        const fact = derived.factAt(index);
        if (try db.closure.?.contains(fact)) continue;
        try relation_store.appendFactCopy(db.allocator, additions, fact);
    }
}
