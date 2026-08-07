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

const std = @import("std");
const root = @import("root.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");

const Jatalog = root.Jatalog;
const Fact = relation_store.Fact;
const PredicateKey = relation_store.PredicateKey;
const RelationStore = relation_store.RelationStore;
const ValueId = relation_store.ValueId;
const copyFactInto = relation_store.copyFactInto;
const collectPredicateKeys = relation_store.collectPredicateKeys;
const Rule = syntax.Rule;
const Clause = syntax.Clause;
const Binding = syntax.Binding;
const predicateKey = syntax.predicateKey;
const outerClauses = syntax.outerClauses;
const ruleActiveAt = @import("evaluator.zig").ruleActiveAt;
const ruleStratum = @import("evaluator.zig").ruleStratum;
const maintainableAggregateIndex = syntax.maintainableAggregateIndex;
const clausesReadGrownAnywhere = syntax.clausesReadGrownAnywhere;
const Error = root.Error;

/// How a batch's changed predicates affect one stratum's maintenance.
pub const StratumImpact = enum { none, aggregate, rebuild };

/// Propagates a batch of base insertions already appended to the clean
/// closure at `batch_start`, one stratum at a time. A stratum whose
/// negated or aggregated dependencies gained facts falls back to the
/// dirty-stratum rebuild; strata below it keep their incremental state.
pub fn propagateInsertions(db: *Jatalog, batch_start: usize) !void {
    const start_len = db.closure.?.len();
    const analysis = try db.eval.ensureAnalysis();
    const max_level = analysis.max_level;
    var level: usize = 0;
    while (level <= max_level) : (level += 1) {
        if (try strataBlockedBy(db, level, &db.closure.?, batch_start)) {
            db.rebuild_fallbacks += 1;
            db.markDirty(level);
            try db.ensureMaterialized();
            return;
        }
        try propagateLevel(db, &db.closure.?, &analysis.strata, level, batch_start);
    }
    db.propagated_facts += db.closure.?.len() - start_len;
}
/// Whether stratum `level` must be rebuilt rather than maintained because
/// the facts in `changed[from..]` reach one of its rules through negation
/// or through an aggregate this phase cannot maintain. Insertions pass the
/// closure from the batch's start, deletions the whole deleted set.
fn strataBlockedBy(
    db: *Jatalog,
    level: usize,
    changed: *const RelationStore,
    from: usize,
) !bool {
    var keys: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
    defer keys.deinit(db.allocator);
    try collectPredicateKeys(db.allocator, changed, from, &keys);
    return try stratumImpact(db, level, &keys) == .rebuild;
}
/// Classifies how a batch's changed predicates affect one stratum:
/// negation over a changed predicate always needs the rebuild path, an
/// aggregate over a changed predicate needs it only when the rule is
/// outside the maintainable class, and everything else is handled by
/// the ordinary delta and delete-and-rederive engines.
pub fn stratumImpact(
    db: *Jatalog,
    level: usize,
    changed: *const std.AutoHashMapUnmanaged(PredicateKey, void),
) !StratumImpact {
    if (changed.count() == 0) return .none;
    const analysis = try db.eval.ensureAnalysis();
    var impact: StratumImpact = .none;
    for (db.eval.rules.items) |rule| {
        if (!ruleActiveAt(&analysis.strata, rule, level)) continue;
        for (rule.body) |clause| switch (clause) {
            .negated => |expression| if (changed.contains(predicateKey(expression))) return .rebuild,
            .aggregate => |aggregate| if (clausesReadGrownAnywhere(aggregate.body, changed)) {
                if (maintainableAggregateIndex(rule) == null) return .rebuild;
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
/// Note: `overdeleteLevel` selects a stratum's rules by head stratum
/// alone, while `propagateLevel` and `expandLevel` also keep seeded
/// structural rules active in higher strata. Whether over-deletion needs
/// the same cross-stratum reach is unresolved; no test currently
/// distinguishes the two, and shadow verification has not caught a
/// disagreement.
pub fn propagateDeletions(db: *Jatalog, deleted: *RelationStore) !void {
    var old_closure = try db.closure.?.clone();
    defer old_closure.deinit();
    for (0..deleted.len()) |index| {
        _ = try db.closure.?.removeFact(deleted.factAt(index));
    }
    const analysis = try db.eval.ensureAnalysis();
    var level: usize = 0;
    while (level <= analysis.max_level) : (level += 1) {
        if (try strataBlockedBy(db, level, deleted, 0)) {
            db.rebuild_fallbacks += 1;
            db.markDirty(level);
            try db.ensureMaterialized();
            return;
        }
        try overdeleteLevel(db, &old_closure, deleted, &analysis.strata, level);
        try rederiveLevel(db, deleted, &analysis.strata, level);
    }
    db.removed_facts += deleted.len();
}
/// Over-deletes stratum `level`: every fact derivable by one of the
/// stratum's rules from at least one already-deleted fact is removed
/// from the closure and queued for rederivation. The remaining body
/// occurrences join against the pre-deletion snapshot so derivations
/// that used several deleted facts are still found.
///
/// Unlike the propagation and expansion phases this selects rules by
/// `ruleStratum` rather than `ruleActiveAt`, so a seeded structural rule
/// is over-deleted only in its own stratum and not in the higher strata
/// it stays active in. See the note in `propagateDeletions`.
fn overdeleteLevel(
    db: *Jatalog,
    old_closure: *RelationStore,
    deleted: *RelationStore,
    levels: *const std.array_hash_map.Auto(PredicateKey, usize),
    level: usize,
) !void {
    var cursor: usize = 0;
    while (cursor < deleted.len()) : (cursor += 1) {
        const victim = deleted.factAt(cursor);
        for (db.eval.rules.items) |rule| {
            if (ruleStratum(levels, rule) != level) continue;
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
    db: *Jatalog,
    old_closure: *RelationStore,
    deleted: *RelationStore,
    rule: Rule,
    clause_index: usize,
    victim: Fact,
) !void {
    const expression = rule.body[clause_index].relational;
    var initial: Binding = .{};
    defer initial.deinit(db.allocator);
    if (!try db.eval.unify(victim, expression, &initial)) return;
    const rest = try outerClauses(db.allocator, rule, clause_index);
    defer db.allocator.free(rest);
    var answers: std.ArrayList(Binding) = .empty;
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    db.eval.matchClauses(rest, old_closure, 0, &initial, &answers, null) catch |err| switch (err) {
        Error.NumericType, Error.NumericOverflow => return,
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
    db: *Jatalog,
    deleted: *RelationStore,
    levels: *const std.array_hash_map.Auto(PredicateKey, usize),
    level: usize,
) !void {
    var progress = true;
    while (progress) {
        progress = false;
        var index: usize = 0;
        while (index < deleted.len()) {
            const candidate = deleted.factAt(index);
            const key: PredicateKey = .{
                .name = candidate.predicate,
                .arity = candidate.terms.len,
            };
            if ((levels.get(key) orelse 0) != level or
                !try hasAlternativeDerivation(db, candidate))
            {
                index += 1;
                continue;
            }
            try copyFactInto(db.allocator, &db.closure.?, candidate, true);
            deleted.removeAt(index);
            progress = true;
        }
    }
}
fn hasAlternativeDerivation(db: *Jatalog, fact: Fact) !bool {
    for (db.eval.rules.items) |rule| {
        if (rule.head.predicate != fact.predicate or
            rule.head.terms.len != fact.terms.len) continue;
        var bindings: Binding = .{};
        defer bindings.deinit(db.allocator);
        if (!try db.eval.unify(fact, rule.head, &bindings)) continue;
        var answers: std.ArrayList(Binding) = .empty;
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
            Error.NumericType, Error.NumericOverflow => continue,
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
    db: *Jatalog,
    facts: *RelationStore,
    levels: *const std.array_hash_map.Auto(PredicateKey, usize),
    level: usize,
    batch_start: usize,
) !void {
    const ActiveRule = struct {
        rule: Rule,
        occurrences: []usize,
    };
    var active: std.ArrayList(ActiveRule) = .empty;
    defer {
        for (active.items) |entry| db.allocator.free(entry.occurrences);
        active.deinit(db.allocator);
    }
    for (db.eval.rules.items) |rule| {
        if (!ruleActiveAt(levels, rule, level)) continue;
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
