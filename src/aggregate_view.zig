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
const test_support = @import("test_support.zig");
const root = @import("root.zig");
const materialization = @import("materialization.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");
const maintenance = @import("maintenance.zig");

/// CReaM-style auxiliary view for a maintained aggregate rule whose head
/// projects out some of its outer-goal variables. Each tuple retains those
/// projected values followed by the head values they derive, so the number
/// of auxiliary tuples carrying a head tuple is that tuple's derivation
/// count. A projected head tuple becomes visible on a zero-to-one count
/// transition and is deleted on a one-to-zero transition.
pub const AuxiliaryView = struct {
    rule_id: u32,
    /// Outer-goal variables omitted from the head, in ascending id order.
    projected: []syntax.Id,
    head_arity: usize,
    tuples: relation_store.RelationStore,

    pub fn deinit(self: *AuxiliaryView, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
        allocator.free(self.projected);
        self.tuples.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const AuxiliaryView, allocator: std.mem.Allocator) !AuxiliaryView { // ziglint-ignore: Z023
        const projected = try allocator.dupe(syntax.Id, self.projected);
        errdefer allocator.free(projected);
        return .{
            .rule_id = self.rule_id,
            .projected = projected,
            .head_arity = self.head_arity,
            .tuples = try self.tuples.clone(),
        };
    }

    pub fn arity(self: *const AuxiliaryView) usize {
        return self.projected.len + self.head_arity;
    }

    pub fn key(self: *const AuxiliaryView) relation_store.PredicateKey {
        return .{ .name = self.rule_id, .arity = self.arity() };
    }

    /// How many auxiliary tuples carry `head`, which is its derivation count:
    /// the head tuple is visible exactly while this is non-zero. Reports
    /// `NumericOverflow` rather than wrapping when it exceeds the counter.
    pub fn derivationCount(self: *AuxiliaryView, head: []const relation_store.ValueId) !u32 {
        var mask: u64 = 0;
        var bound: [64]relation_store.ValueId = undefined;
        for (head, 0..) |term, index| {
            mask |= @as(u64, 1) << @intCast(self.projected.len + index);
            bound[index] = term;
        }
        const candidates = try self.tuples.lookup(self.key(), mask, bound[0..head.len]);
        var count: usize = 0;
        for (candidates) |candidate| {
            const tuple = self.tuples.factAt(candidate);
            if (std.mem.eql(relation_store.ValueId, self.headTerms(tuple), head)) count += 1;
        }
        return std.math.cast(u32, count) orelse root.Error.NumericOverflow;
    }

    pub fn headTerms(self: *const AuxiliaryView, tuple: relation_store.Fact) []const relation_store.ValueId {
        return tuple.terms[self.projected.len..];
    }
};

/// Maintains rules containing one unnested `setof` after a batch changed
/// the aggregate's inner relations. Only groups reachable from a changed
/// inner fact are recomputed. A group whose canonical list changed emits
/// its stale head tuples as deletions and its recomputed tuple as an
/// insertion, which then cascade through the ordinary deletion and
/// insertion maintenance. Rounds repeat while aggregate results keep
/// changing, with a bounded fallback to a full rebuild.
pub fn maintainAggregates(db: *root.Jatalog, touched: *relation_store.RelationStore) !void {
    if (db.closure == null or db.materialization != .clean) return;
    const round_cap = (try db.eval.ensureAnalysis()).max_level + 4;
    var round: usize = 0;
    while (true) {
        round += 1;
        if (round > round_cap) {
            db.rebuild_fallbacks += 1;
            materialization.markDirty(db, 0);
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
            const trigger = if (auxiliaryFor(db, rule.id) == null)
                rule.body[clause_index].aggregate.body
            else
                rule.body;
            if (!syntax.clausesReadGrownAnywhere(trigger, &changed)) continue;
            try maintainAggregateRule(db, rule, clause_index, touched, &removals, &additions);
        }
        if (removals.len() == 0 and additions.items.len == 0) return;

        touched.clear();
        if (removals.len() > 0) {
            try maintenance.propagateDeletions(db, &removals);
            for (0..removals.len()) |index|
                try relation_store.copyFactInto(db.allocator, touched, removals.factAt(index), false);
        }
        if (db.materialization != .clean) return;
        const batch_start = db.closure.?.len();
        for (additions.items) |fact| {
            if (try db.closure.?.contains(fact)) continue;
            try relation_store.copyFactInto(db.allocator, &db.closure.?, fact, true);
        }
        if (db.closure.?.len() > batch_start) {
            try maintenance.propagateInsertions(db, batch_start);
            if (db.materialization != .clean) return;
            for (batch_start..db.closure.?.len()) |index|
                try relation_store.copyFactInto(db.allocator, touched, db.closure.?.factAt(index), false);
        }
    }
}
fn maintainAggregateRule(
    db: *root.Jatalog,
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
    const view = auxiliaryFor(db, rule.id);
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
    db: *root.Jatalog,
    rule: syntax.Rule,
    view: *AuxiliaryView,
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
        const terms = (try auxiliaryTerms(db, view, group, head)) orelse continue;
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
    db: *root.Jatalog,
    rule: syntax.Rule,
    clause_index: usize,
    view: *AuxiliaryView,
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
        db.eval.matchClauses(
            outer,
            &db.closure.?,
            0,
            &seed,
            &solutions,
            null,
        ) catch |err| switch (err) {
            root.Error.NumericType, root.Error.NumericOverflow => continue,
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
    db: *root.Jatalog,
    rule: syntax.Rule,
    view: *AuxiliaryView,
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
    db: *root.Jatalog,
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
    db: *root.Jatalog,
    rule: syntax.Rule,
    group: *const syntax.Binding,
    derived: *relation_store.RelationStore,
) !void {
    var answers: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    db.eval.matchClauses(
        rule.body,
        &db.closure.?,
        0,
        group,
        &answers,
        null,
    ) catch |err| switch (err) {
        root.Error.NumericType, root.Error.NumericOverflow => return,
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
    db: *root.Jatalog,
    outer: []const syntax.Clause,
    seed: *const syntax.Binding,
    groups: *std.ArrayList(syntax.Binding),
) !void {
    var solutions: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (solutions.items) |*solution| solution.deinit(db.allocator);
        solutions.deinit(db.allocator);
    }
    db.eval.matchClauses(
        outer,
        &db.closure.?,
        0,
        seed,
        &solutions,
        null,
    ) catch |err| switch (err) {
        root.Error.NumericType, root.Error.NumericOverflow => return,
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
    db: *root.Jatalog,
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
pub fn dropAuxiliaryViews(db: *root.Jatalog) void {
    for (db.auxiliary.items) |*view| view.deinit(db.allocator);
    db.auxiliary.clearRetainingCapacity();
}
pub fn auxiliaryFor(db: *root.Jatalog, rule_id: u32) ?*AuxiliaryView {
    for (db.auxiliary.items) |*view| if (view.rule_id == rule_id) return view;
    return null;
}
/// Rebuilds every projected aggregate view from the materialized
/// closure. Views are built into a temporary list and installed only on
/// success, so a failure leaves the previous views in place.
pub fn rebuildAuxiliaryViews(db: *root.Jatalog) !void {
    var built: std.ArrayList(AuxiliaryView) = .empty;
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
fn projectedVariables(db: *root.Jatalog, rule: syntax.Rule, clause_index: usize) ![]syntax.Id {
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
fn buildAuxiliaryView(db: *root.Jatalog, rule: syntax.Rule, clause_index: usize) !?AuxiliaryView {
    const projected = try projectedVariables(db, rule, clause_index);
    var projected_owned = true;
    defer if (projected_owned) db.allocator.free(projected);
    if (projected.len == 0) return null;
    // The lookup mask addresses one bit per auxiliary column.
    if (projected.len + rule.head.terms.len > 64) return null;

    var view: AuxiliaryView = .{
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
    db.eval.matchClauses(
        outer,
        &db.closure.?,
        0,
        &initial,
        &groups,
        null,
    ) catch |err| switch (err) {
        root.Error.NumericType, root.Error.NumericOverflow => return view,
        else => return err,
    };
    for (groups.items) |*group| try recordGroupTuples(db, rule, &view, group);
    return view;
}
/// Records the auxiliary tuples one group contributes: its projected
/// values followed by each head tuple the rule derives for it.
fn recordGroupTuples(
    db: *root.Jatalog,
    rule: syntax.Rule,
    view: *AuxiliaryView,
    group: *const syntax.Binding,
) !void {
    var answers: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    db.eval.matchClauses(
        rule.body,
        &db.closure.?,
        0,
        group,
        &answers,
        null,
    ) catch |err| switch (err) {
        root.Error.NumericType, root.Error.NumericOverflow => return,
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
fn auxiliaryTerms(
    db: *root.Jatalog,
    view: *const AuxiliaryView,
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

test "aggregate groups are maintained incrementally across member changes" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
    const expansions_after_build = db.eval.expansions;

    // Member insertion updates only the affected group, with no rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("member", &.{ root.input.atom("g1"), root.input.atom("c") }),
    }, &.{}));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.eval.expansions);
    var inserted = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&inserted.query.answers.items[0], "S", "[a, b, c]");
    inserted.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // The untouched group keeps its list and there is exactly one tuple
    // per group after the change.
    var untouched = try db.execute("collected(g2, S)?");
    try test_support.expectBindingValue(&untouched.query.answers.items[0], "S", "[z]");
    untouched.deinit();
    try test_support.expectAnswerCount(&db, "collected(G, S)?", 2);

    // Member deletion shrinks the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("member", &.{ root.input.atom("g1"), root.input.atom("a") }),
    }));
    var deleted = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&deleted.query.answers.items[0], "S", "[b, c]");
    deleted.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // Deleting the last member leaves the enumerated group with an empty
    // list, because its outer goal still derives the group.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("member", &.{ root.input.atom("g2"), root.input.atom("z") }),
    }));
    var emptied = try db.execute("collected(g2, S)?");
    try test_support.expectBindingValue(&emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // Deleting the group key removes the tuple entirely.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("group", &.{root.input.atom("g2")}),
    }));
    try test_support.expectAnswerCount(&db, "collected(g2, S)?", 0);
    try test_support.expectAnswerCount(&db, "collected(G, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);

    // Restoring the group key brings back an empty group.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("group", &.{root.input.atom("g2")}),
    }, &.{}));
    var restored = try db.execute("collected(g2, S)?");
    try test_support.expectBindingValue(&restored.query.answers.items[0], "S", "[]");
    restored.deinit();
    try test_support.expectClosureMatchesRebuild(&db);
}

test "duplicate member derivations do not disturb a maintained group" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
        root.input.fact("mirrored", &.{ root.input.atom("g"), root.input.atom("a") }),
    }));
    var kept = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&kept.query.answers.items[0], "S", "[a, b]");
    kept.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // Removing the last derivation drops it from the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("direct", &.{ root.input.atom("g"), root.input.atom("a") }),
    }));
    var dropped = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&dropped.query.answers.items[0], "S", "[b]");
    dropped.deinit();
    try test_support.expectClosureMatchesRebuild(&db);
}

test "canonical aggregate lists are independent of update order" {
    const orders = [_][3][]const u8{
        .{ "c", "a", "b" },
        .{ "b", "c", "a" },
        .{ "a", "b", "c" },
    };
    for (orders) |order| {
        var db: root.Jatalog = .init(std.testing.allocator);
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
                root.input.fact("member", &.{ root.input.atom("g"), root.input.atom(name) }),
            }, &.{});
        }
        var result = try db.execute("collected(g, S)?");
        try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a, b, c]");
        result.deinit();
        try test_support.expectClosureMatchesRebuild(&db);
    }
}

test "bag emulation retains equal values with distinct discriminators" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
        root.input.fact("reading", &.{ root.input.atom("g"), root.input.atom("r4"), root.input.integer(5) }),
    }, &.{}));
    var added = try db.execute("bag(g, S)?");
    try test_support.expectBindingValue(
        &added.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [5, r4], [7, r3]]",
    );
    added.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // Removing one duplicate value keeps the others.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("reading", &.{ root.input.atom("g"), root.input.atom("r2"), root.input.integer(5) }),
    }));
    var removed = try db.execute("bag(g, S)?");
    try test_support.expectBindingValue(
        &removed.query.answers.items[0],
        "S",
        "[[5, r1], [5, r4], [7, r3]]",
    );
    removed.deinit();
    try test_support.expectClosureMatchesRebuild(&db);
}

test "maintained aggregates feed downstream strata and recursive consumers" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
        root.input.fact("person", &.{root.input.atom("carol")}),
        root.input.fact("parent", &.{ root.input.atom("alice"), root.input.atom("carol") }),
    }, &.{}));
    var grown = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    try test_support.expectAnswerCount(&db, "numchildren(X, N)?", 3);
    try test_support.expectClosureMatchesRebuild(&db);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("parent", &.{ root.input.atom("alice"), root.input.atom("bob") }),
    }));
    var shrunk = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 1), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try test_support.expectClosureMatchesRebuild(&db);
}

test "multiple and nested aggregates stay correct through the rebuild path" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
        root.input.fact("item", &.{ root.input.atom("g1"), root.input.atom("c") }),
        root.input.fact("tag", &.{ root.input.atom("g1"), root.input.atom("t3") }),
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
    try test_support.expectClosureMatchesRebuild(&db);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("item", &.{ root.input.atom("g1"), root.input.atom("a") }),
    }));
    var reduced = try db.execute("both(g1, S, T)?");
    try test_support.expectBindingValue(&reduced.query.answers.items[0], "S", "[c]");
    reduced.deinit();
    try test_support.expectClosureMatchesRebuild(&db);
}

test "random aggregate update traces match a clean rebuild after every batch" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
    try test_support.expectAnswerCount(&db, "size(G, N)?", 3);

    const groups = [_][]const u8{ "g1", "g2", "g3" };
    const members = [_][]const u8{ "m1", "m2", "m3" };
    var prng = std.Random.DefaultPrng.init(0xa99a6a7e5eed);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [2][2]root.input.Term = undefined;
        var inserts: [2]root.input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            insert_buffer[slot] = .{
                root.input.atom(groups[random.uintLessThan(usize, groups.len)]),
                root.input.atom(members[random.uintLessThan(usize, members.len)]),
            };
            inserts[slot] = root.input.fact("member", &insert_buffer[slot]);
        }
        var delete_buffer: [2][2]root.input.Term = undefined;
        var deletes: [2]root.input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            delete_buffer[slot] = .{
                root.input.atom(groups[random.uintLessThan(usize, groups.len)]),
                root.input.atom(members[random.uintLessThan(usize, members.len)]),
            };
            deletes[slot] = root.input.fact("member", &delete_buffer[slot]);
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db);
    }
}

/// Derivation count the auxiliary view records for the single tuple of
/// `predicate` whose first argument is the atom `first_atom`.
fn derivationCountOf(
    db: *root.Jatalog,
    predicate: []const u8,
    first_atom: []const u8,
) !u32 {
    const predicate_id = db.strings.get(predicate) orelse return error.MissingPredicate;
    const scalar_id = try db.eval.scalars.internAtom(first_atom);
    const first_value = try db.eval.values.intern(.{ .scalar = scalar_id });
    for (db.eval.rules.items) |rule| {
        if (rule.head.predicate != predicate_id) continue;
        const view = auxiliaryFor(db, rule.id) orelse return error.NotProjected;
        const closure = &db.closure.?;
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
    var db: root.Jatalog = .init(std.testing.allocator);
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
    try test_support.expectAnswerCount(&db, "v(X, S)?", 2);

    // Deleting p(a) and inserting r(b, 2) deletes v(a, [1]) and updates
    // v(b, []) to v(b, [2]).
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("r", &.{ root.input.atom("b"), root.input.integer(2) }),
    }, &.{
        root.input.fact("p", &.{root.input.atom("a")}),
    }));
    try std.testing.expect(db.materialization == .clean);
    try test_support.expectAnswerCount(&db, "v(a, S)?", 0);
    var updated = try db.execute("v(b, S)?");
    try test_support.expectBindingValue(&updated.query.answers.items[0], "S", "[2]");
    updated.deinit();
    try test_support.expectAnswerCount(&db, "v(X, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);

    // This view retains every outer variable, so it is self-maintainable and
    // needs no auxiliary derivation counts.
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.self_maintainable_views);
    try std.testing.expectEqual(@as(usize, 0), stats.projected_views);
    try std.testing.expectEqual(@as(usize, 0), stats.auxiliary_tuples);
}

test "Chapter 5 Example 5.3.1 counts derivations of a projected view" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
        root.input.fact("p", &.{ root.input.atom("a"), root.input.integer(2) }),
    }));
    try std.testing.expect(db.materialization == .clean);
    var retained = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&retained.query.answers.items[0], "S", "[1, 2]");
    retained.deinit();
    try std.testing.expectEqual(@as(u32, 1), try derivationCountOf(&db, "v", "a"));
    try test_support.expectClosureMatchesRebuild(&db);

    // Deleting p(a, 1) removes the last derivation, so the tuple goes.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("p", &.{ root.input.atom("a"), root.input.integer(1) }),
    }));
    try test_support.expectAnswerCount(&db, "v(a, S)?", 0);
    try std.testing.expectEqual(@as(u32, 0), try derivationCountOf(&db, "v", "a"));
    try test_support.expectAnswerCount(&db, "v(X, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "a changed aggregate list transfers support to the new tuple" {
    var db: root.Jatalog = .init(std.testing.allocator);
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
        root.input.fact("r", &.{ root.input.atom("a"), root.input.integer(2) }),
    }, &.{}));
    try std.testing.expect(db.materialization == .clean);
    var moved = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&moved.query.answers.items[0], "S", "[1, 2]");
    moved.deinit();
    try test_support.expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try std.testing.expectEqual(@as(usize, 3), db.maintenanceStats().auxiliary_tuples);
    try test_support.expectClosureMatchesRebuild(&db);

    // Shrinking it back transfers the support again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("r", &.{ root.input.atom("a"), root.input.integer(1) }),
    }));
    var shrunk = try db.execute("v(a, S)?");
    try test_support.expectBindingValue(&shrunk.query.answers.items[0], "S", "[2]");
    shrunk.deinit();
    try test_support.expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try test_support.expectClosureMatchesRebuild(&db);
}

test "projected view counts agree with explicit proof enumeration" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\p(a, 1). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "v(X, S)?", 1);

    const keys = [_][]const u8{ "a", "b", "c" };
    var prng = std.Random.DefaultPrng.init(0xc0107501c0107);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [2][2]root.input.Term = undefined;
        var inserts: [2]root.input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            const key = keys[random.uintLessThan(usize, keys.len)];
            const number: i64 = @intCast(random.uintLessThan(usize, 3) + 1);
            insert_buffer[slot] = .{ root.input.atom(key), root.input.integer(number) };
            inserts[slot] = root.input.fact(
                if (random.boolean()) "p" else "r",
                &insert_buffer[slot],
            );
        }
        var delete_buffer: [2][2]root.input.Term = undefined;
        var deletes: [2]root.input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            const key = keys[random.uintLessThan(usize, keys.len)];
            const number: i64 = @intCast(random.uintLessThan(usize, 3) + 1);
            delete_buffer[slot] = .{ root.input.atom(key), root.input.integer(number) };
            deletes[slot] = root.input.fact(
                if (random.boolean()) "p" else "r",
                &delete_buffer[slot],
            );
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db);

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
    var db: root.Jatalog = .init(std.testing.allocator);
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
    try test_support.expectAnswerCount(&db, "staffed(T)?", 0);

    // Growing one group must reach every downstream stratum.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("plays", &.{ root.input.atom("red"), root.input.atom("ann") }),
        root.input.fact("plays", &.{ root.input.atom("red"), root.input.atom("bo") }),
    }, &.{}));
    var grown = try db.execute("size(red, N)?");
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    var counted = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 3), try counted.query.answers.items[0].getInteger("N"));
    counted.deinit();
    try test_support.expectAnswerCount(&db, "staffed(red)?", 1);
    try test_support.expectAnswerCount(&db, "staffed(blue)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);

    // Shrinking it retracts the downstream conclusions again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("plays", &.{ root.input.atom("red"), root.input.atom("bo") }),
    }));
    var shrunk = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 2), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try test_support.expectAnswerCount(&db, "staffed(T)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);

    // A downstream structural-recursive component recomputes within its own
    // stratum rather than forcing a whole-closure rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.maintained_groups > 0);
}

fn aggregateMaintenanceAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: root.Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var first = try db.execute("collected(G, S)?");
    first.deinit();
    _ = try db.applyChanges(&.{
        root.input.fact("member", &.{ root.input.atom("g1"), root.input.atom("b") }),
        root.input.fact("member", &.{ root.input.atom("g2"), root.input.atom("c") }),
    }, &.{});
    _ = try db.applyChanges(&.{}, &.{
        root.input.fact("member", &.{ root.input.atom("g1"), root.input.atom("a") }),
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
