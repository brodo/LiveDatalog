//! Incremental maintenance of the derived closure: semi-naive propagation
//! of insertions, and delete-and-rederive for deletions.
//!
//! These take the database itself rather than a narrower context, because
//! maintaining the closure is the database's own state transition: a batch
//! that reaches negation or an unmaintainable aggregate abandons the
//! incremental path and repairs the closure through `ensureMaterialized`.
//! `ensureMaterialized` and `markDirty` are the whole of that interface.
//!
//! Everything else these need comes from the evaluator — matching rules
//! against a store, deriving head facts, the stratification — or from the
//! relation store.
//!
//! One delta reaches the closure through three calls in this order:
//! `applyRemovals`, then `stageInsertions`, then `applyStaged`. The order is
//! the interface, not an accident of it — delete-and-rederive joins against a
//! snapshot of the pre-deletion closure, so facts staged before the removals
//! propagate would be over-deleted against a closure they were never absent
//! from. `update.zig` and `aggregate_view.zig` are the two callers, and both
//! collect what moved into one `touched` store.

const std = @import("std");
const evaluator = @import("evaluator.zig");
const database = @import("database.zig");
const errors = @import("errors.zig");
const materialization = @import("materialization.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");

/// How a batch's changed predicates affect one stratum's maintenance.
pub const StratumImpact = enum { none, aggregate, rebuild };

/// Whether a delta reached the closure incrementally, or abandoned the
/// incremental path for a dirty-stratum rebuild.
///
/// The distinction is not readable from `db.materialization`: the fallback
/// repairs the closure through `ensureMaterialized` before returning, so the
/// database is `.clean` either way. What differs is that a rebuild replaces
/// the closure wholesale, which retires every index into it — including the
/// watermark a caller would collect its `touched` facts from.
pub const DeltaOutcome = enum { maintained, rebuilt };

/// Whether a fact enters the closure as one of the database's base facts or
/// as a fact some rule derived.
///
/// The two also differ in what a duplicate means. A base fact the closure
/// already holds is a second reason to hold it, and its support count says
/// so, which is what lets delete-and-rederive tell an exhausted fact from a
/// still-supported one. A derived fact is re-derived on every round of the
/// aggregate cascade, so counting those would inflate the same support with
/// no new reason behind it.
pub const FactKind = enum { base, derived };

/// Deletes `removals` from the closure through delete-and-rederive and
/// collects everything that actually left it into `touched`.
///
/// `removals` is rewritten in place into that set: over-deleted consequences
/// are added and rederived ones removed, so it is only meaningful afterwards.
/// A `.rebuilt` outcome leaves `touched` empty — the rebuild has already
/// recomputed every consequence, so there is nothing left for the aggregate
/// phase to reconsider.
pub fn applyRemovals(
    db: *database.Database,
    removals: *relation_store.RelationStore,
    touched: *relation_store.RelationStore,
) !DeltaOutcome {
    if (removals.len() == 0) return .maintained;
    if (try propagateDeletions(db, removals) == .rebuilt) {
        touched.clear();
        return .rebuilt;
    }
    for (0..removals.len()) |index|
        try relation_store.copyFactInto(db.allocator, touched, removals.factAt(index), false);
    return .maintained;
}

/// Appends `facts` to the closure and returns the watermark `applyStaged`
/// propagates from: the closure's length before the append.
///
/// Staging is separate from propagating because the two cannot be one call —
/// a delta's removals must reach the closure first, and only a caller can sit
/// between the two phases holding its own facts.
pub fn stageInsertions(
    db: *database.Database,
    facts: []const relation_store.Fact,
    kind: FactKind,
) !usize {
    const batch_start = db.closure.?.len();
    for (facts) |fact| {
        if (kind == .derived and try db.closure.?.contains(fact)) continue;
        try relation_store.copyFactInto(db.allocator, &db.closure.?, fact, kind == .derived);
    }
    return batch_start;
}

/// Propagates the facts staged at or after `batch_start` and collects
/// everything derived from them into `touched`. Staging that added nothing
/// propagates nothing.
///
/// A `.rebuilt` outcome clears `touched`, including anything an earlier phase
/// of the same delta put there: `batch_start` no longer indexes the closure
/// the rebuild installed, and the rebuild already recomputed what the
/// collection was for.
pub fn applyStaged(
    db: *database.Database,
    batch_start: usize,
    touched: *relation_store.RelationStore,
) !DeltaOutcome {
    if (db.closure.?.len() == batch_start) return .maintained;
    if (try propagateInsertions(db, batch_start) == .rebuilt) {
        touched.clear();
        return .rebuilt;
    }
    for (batch_start..db.closure.?.len()) |index|
        try relation_store.copyFactInto(db.allocator, touched, db.closure.?.factAt(index), false);
    return .maintained;
}

/// Propagates a batch of base insertions already appended to the clean
/// closure at `batch_start`, one stratum at a time. A stratum whose
/// negated or aggregated dependencies gained facts falls back to the
/// dirty-stratum rebuild; strata below it keep their incremental state.
fn propagateInsertions(db: *database.Database, batch_start: usize) !DeltaOutcome {
    const start_len = db.closure.?.len();
    const analysis = try db.eval.ensureAnalysis();
    const max_level = analysis.max_level;
    var level: usize = 0;
    while (level <= max_level) : (level += 1) {
        if (try insertionBlocked(db, level, batch_start)) {
            db.rebuild_fallbacks += 1;
            db.markDirty(level);
            try materialization.ensureMaterialized(db);
            return .rebuilt;
        }
        try propagateLevel(db, &db.closure.?, &analysis.strata, level, batch_start);
    }
    db.propagated_facts += db.closure.?.len() - start_len;
    return .maintained;
}
/// Whether stratum `level` must be rebuilt rather than maintained because the
/// facts appended to the closure from `batch_start` reach one of its rules
/// through negation or through an aggregate this phase cannot maintain.
fn insertionBlocked(db: *database.Database, level: usize, batch_start: usize) !bool {
    var keys: std.AutoHashMapUnmanaged(relation_store.PredicateKey, void) = .empty;
    defer keys.deinit(db.allocator);
    try relation_store.collectPredicateKeys(db.allocator, &db.closure.?, batch_start, &keys);
    return try stratumImpact(db, level, &keys) == .rebuild;
}

/// Whether stratum `level` must be rebuilt rather than maintained through
/// delete-and-rederive.
///
/// Deletion shares the insertion triggers and adds one of its own. Over-
/// deletion runs a rule backwards: it unifies a deleted fact against a body
/// occurrence, solves the remaining goals, and reconstructs the head. A seeded
/// structural rule has a head variable that no body goal binds — in
/// `length(H!T, N) :- length(T, M), N = M + 1` the value of `H` comes from the
/// value table, which is what `seed_argument` records — so running it backwards
/// cannot name the head tuple to delete. There is nothing to over-delete
/// against, so the stratum takes the rebuild instead.
///
/// Rederivation needs no such guard: it unifies a whole candidate fact against
/// the head, which binds every head variable including the seed.
fn deletionBlocked(db: *database.Database, level: usize, deleted: *const relation_store.RelationStore) !bool {
    var keys: std.AutoHashMapUnmanaged(relation_store.PredicateKey, void) = .empty;
    defer keys.deinit(db.allocator);
    try relation_store.collectPredicateKeys(db.allocator, deleted, 0, &keys);
    if (try stratumImpact(db, level, &keys) == .rebuild) return true;
    const analysis = try db.eval.ensureAnalysis();
    for (db.eval.rules.items) |rule| {
        if (rule.seed_argument == null) continue;
        if (evaluator.ruleStratum(&analysis.strata, rule) != level) continue;
        for (rule.body) |clause| switch (clause) {
            .relational => |expression| if (keys.contains(syntax.predicateKey(expression))) return true,
            .builtin, .negated, .aggregate => {},
        };
    }
    return false;
}
/// Classifies how a batch's changed predicates affect one stratum:
/// negation over a changed predicate always needs the rebuild path, an
/// aggregate over a changed predicate needs it only when the rule is
/// outside the maintainable class, and everything else is handled by
/// the ordinary delta and delete-and-rederive engines.
pub fn stratumImpact(
    db: *database.Database,
    level: usize,
    changed: *const std.AutoHashMapUnmanaged(relation_store.PredicateKey, void),
) !StratumImpact {
    if (changed.count() == 0) return .none;
    const analysis = try db.eval.ensureAnalysis();
    var impact: StratumImpact = .none;
    for (db.eval.rules.items) |rule| {
        if (!evaluator.ruleActiveAt(&analysis.strata, rule, level)) continue;
        for (rule.body) |clause| switch (clause) {
            .negated => |expression| if (changed.contains(syntax.predicateKey(expression))) return .rebuild,
            .aggregate => |aggregate| if (syntax.clausesReadGrownAnywhere(aggregate.body, changed)) {
                if (syntax.maintainableAggregateIndex(rule) == null) return .rebuild;
                impact = .aggregate;
            },
            .relational, .builtin => {},
        };
    }
    return impact;
}
/// Applies a batch of base deletions to the clean closure with
/// delete-and-rederive, one stratum at a time: over-delete every fact
/// whose derivation used a deleted fact, joining against a snapshot of
/// the pre-deletion closure, then reinsert facts that retain an
/// alternative proof in the reduced closure. Plain reference counts
/// would be unsound here because cyclic derivations support one another
/// after their base support disappears. A stratum whose negated or
/// aggregated dependencies lost facts is invalidated and recomputed
/// through the dirty-stratum rebuild instead.
///
/// A stratum containing a seeded structural rule whose body lost facts is
/// rebuilt rather than over-deleted; see `deletionBlocked`.
fn propagateDeletions(db: *database.Database, deleted: *relation_store.RelationStore) !DeltaOutcome {
    var old_closure = try db.closure.?.clone();
    defer old_closure.deinit();
    for (0..deleted.len()) |index| {
        _ = try db.closure.?.removeFact(deleted.factAt(index));
    }
    const analysis = try db.eval.ensureAnalysis();
    var level: usize = 0;
    while (level <= analysis.max_level) : (level += 1) {
        if (try deletionBlocked(db, level, deleted)) {
            db.rebuild_fallbacks += 1;
            db.markDirty(level);
            try materialization.ensureMaterialized(db);
            return .rebuilt;
        }
        try overdeleteLevel(db, &old_closure, deleted, &analysis.strata, level);
        try rederiveLevel(db, deleted, &analysis.strata, level);
    }
    db.removed_facts += deleted.len();
    return .maintained;
}
/// Over-deletes stratum `level`: every fact derivable by one of the
/// stratum's rules from at least one already-deleted fact is removed
/// from the closure and queued for rederivation. The remaining body
/// occurrences join against the pre-deletion snapshot so derivations
/// that used several deleted facts are still found.
///
/// Selecting rules by `ruleStratum` rather than the `ruleActiveAt` the
/// propagation and expansion phases use is deliberate and sufficient. Those
/// phases keep a seeded rule active above its own stratum because new values
/// are interned there, and values drive it. Over-deletion follows facts, not
/// values, and stratification puts every body predicate at or below its
/// head's stratum, so a rule can only lose support from strata this loop has
/// already reached. Extending the reach would re-examine rules against
/// victims their bodies cannot mention.
fn overdeleteLevel(
    db: *database.Database,
    old_closure: *relation_store.RelationStore,
    deleted: *relation_store.RelationStore,
    levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    level: usize,
) !void {
    var cursor: usize = 0;
    while (cursor < deleted.len()) : (cursor += 1) {
        const victim = deleted.factAt(cursor);
        for (db.eval.rules.items) |rule| {
            if (evaluator.ruleStratum(levels, rule) != level) continue;
            for (rule.body, 0..) |clause, clause_index| {
                const expression = switch (clause) {
                    .relational => |value| value,
                    else => continue,
                };
                if (expression.predicate != victim.predicate or
                    expression.terms.len != victim.terms.len) continue;
                try overdeleteOccurrence(
                    db,
                    old_closure,
                    deleted,
                    rule,
                    clause_index,
                    victim,
                );
            }
        }
    }
}
fn overdeleteOccurrence(
    db: *database.Database,
    old_closure: *relation_store.RelationStore,
    deleted: *relation_store.RelationStore,
    rule: syntax.Rule,
    clause_index: usize,
    victim: relation_store.Fact,
) !void {
    const expression = rule.body[clause_index].relational;
    var initial: syntax.Binding = .{};
    defer initial.deinit(db.allocator);
    if (!try db.eval.unify(victim, expression, &initial)) return;
    const rest = try syntax.outerClauses(db.allocator, rule, clause_index);
    defer db.allocator.free(rest);
    var answers: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    db.eval.matchClauses(rest, old_closure, 0, &initial, &answers, null) catch |err| switch (err) {
        errors.Error.NumericType, errors.Error.NumericOverflow => return,
        else => return err,
    };
    for (answers.items) |*answer| {
        const head_fact = try db.eval.deriveFact(rule.head, answer);
        var keep = false;
        defer if (!keep) db.allocator.free(head_fact.terms);
        if (try db.facts.contains(head_fact)) continue;
        if (try deleted.contains(head_fact)) continue;
        if (!try db.closure.?.contains(head_fact)) continue;
        _ = try db.closure.?.removeFact(head_fact);
        _ = try deleted.insert(head_fact, true);
        keep = true;
    }
}
/// Reinserts over-deleted facts of this stratum that retain an
/// alternative proof in the reduced closure, repeating until no further
/// fact can be rederived so that chains of rederivations settle.
fn rederiveLevel(
    db: *database.Database,
    deleted: *relation_store.RelationStore,
    levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    level: usize,
) !void {
    var progress = true;
    while (progress) {
        progress = false;
        var index: usize = 0;
        while (index < deleted.len()) {
            const candidate = deleted.factAt(index);
            const key: relation_store.PredicateKey = .{
                .name = candidate.predicate,
                .arity = candidate.terms.len,
            };
            if ((levels.get(key) orelse 0) != level or
                !try hasAlternativeDerivation(db, candidate))
            {
                index += 1;
                continue;
            }
            try relation_store.copyFactInto(db.allocator, &db.closure.?, candidate, true);
            deleted.removeAt(index);
            progress = true;
        }
    }
}
fn hasAlternativeDerivation(db: *database.Database, fact: relation_store.Fact) !bool {
    for (db.eval.rules.items) |rule| {
        if (rule.head.predicate != fact.predicate or
            rule.head.terms.len != fact.terms.len) continue;
        var bindings: syntax.Binding = .{};
        defer bindings.deinit(db.allocator);
        if (!try db.eval.unify(fact, rule.head, &bindings)) continue;
        var answers: std.ArrayList(syntax.Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(db.allocator);
            answers.deinit(db.allocator);
        }
        db.eval.matchClauses(
            rule.body,
            &db.closure.?,
            0,
            &bindings,
            &answers,
            null,
        ) catch |err| switch (err) {
            errors.Error.NumericType, errors.Error.NumericOverflow => continue,
            else => return err,
        };
        if (answers.items.len > 0) return true;
    }
    return false;
}
/// Runs semi-naive delta rounds for one stratum during batch
/// propagation. Unlike `expandLevel` there is no naive round zero: the
/// initial delta is everything appended since the batch began, and every
/// relational body occurrence is delta-joined because the batch may have
/// grown predicates at any lower stratum.
fn propagateLevel(
    db: *database.Database,
    facts: *relation_store.RelationStore,
    levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    level: usize,
    batch_start: usize,
) !void {
    const ActiveRule = struct {
        rule: syntax.Rule,
        occurrences: []usize,
    };
    var active: std.ArrayList(ActiveRule) = .empty;
    defer {
        for (active.items) |entry| db.allocator.free(entry.occurrences);
        active.deinit(db.allocator);
    }
    for (db.eval.rules.items) |rule| {
        if (!evaluator.ruleActiveAt(levels, rule, level)) continue;
        var occurrences: std.ArrayList(usize) = .empty;
        errdefer occurrences.deinit(db.allocator);
        if (rule.seed_argument == null) {
            for (rule.body, 0..) |clause, clause_index| {
                if (clause == .relational)
                    try occurrences.append(db.allocator, clause_index);
            }
        }
        const owned = try occurrences.toOwnedSlice(db.allocator);
        active.append(db.allocator, .{
            .rule = rule,
            .occurrences = owned,
        }) catch |err| {
            db.allocator.free(owned);
            return err;
        };
    }

    var delta_start = batch_start;
    var value_mark = db.eval.values.values.items.len;
    while (true) {
        const delta_end = facts.len();
        const values_grew = db.eval.values.values.items.len != value_mark;
        if (delta_end == delta_start and !values_grew) break;
        value_mark = db.eval.values.values.items.len;
        for (active.items) |entry| {
            if (entry.rule.seed_argument != null) {
                try db.eval.applyRule(facts, entry.rule, null);
            } else for (entry.occurrences) |occurrence| {
                try db.eval.applyRule(facts, entry.rule, .{
                    .clause_index = occurrence,
                    .delta_start = delta_start,
                    .delta_end = delta_end,
                });
            }
        }
        delta_start = delta_end;
    }
}
