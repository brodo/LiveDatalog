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
//! A delta reaches the closure through one call, `applyDelta`, which owns the
//! order its phases run in. The order is the whole reason there is one call
//! rather than three — delete-and-rederive joins against a snapshot of the
//! pre-deletion closure, so an addition staged before the removals propagate
//! would be over-deleted against a closure it was never absent from, and a
//! base addition that joins the base facts before the removals have reached
//! the closure is invisible to the rebuild they may fall back to. `update.zig`
//! and `aggregate_view.zig` are the two callers, and both read what moved from
//! the `touched` store it fills.

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
/// watermark a phase would collect its `touched` facts from.
pub const Path = enum { maintained, rebuilt };

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

/// One set of removals and one set of additions reaching the closure
/// together: either base facts from an update, or the head tuples an
/// aggregate round recomputed. See "Update path" in CONTEXT.md.
///
/// Both halves are borrowed and only read, with their values already
/// interned against the database the delta is applied to. Neither may be
/// borrowed from `db.facts` itself, because a base delta changes that store
/// underneath them. The removals are a store because both callers already
/// hold them as one — a retraction resolves to a store, and an aggregate
/// round collects its stale tuples into one to drop duplicates — and the
/// additions a slice because neither caller does.
pub const Delta = struct {
    removals: *const relation_store.RelationStore,
    additions: []const relation_store.Fact,
    kind: FactKind,
};

/// What applying a delta did.
///
/// `path` is `.rebuilt` when either half fell back to a rebuild. `removed`
/// and `added` count the base facts that really left and joined `db.facts`,
/// which is fewer than the delta names whenever it removes an absent fact or
/// adds a present one; the update path teaches the cost model with them. A
/// derived delta leaves the base facts alone, so both are zero for it.
pub const Outcome = struct {
    path: Path,
    removed: usize,
    added: usize,
};

/// Applies one delta to the clean closure — removals through
/// delete-and-rederive, then additions through semi-naive propagation — and
/// collects into `touched` everything that left the closure or was derived
/// into it, which is what the aggregate phase reconsiders.
///
/// A base delta changes `db.facts` as well, and when it does is the point: a
/// removal leaves the base facts before its deletion propagates, and an
/// addition joins them only after every removal has reached the closure. A
/// rebuild the removals fall back to starts from the base facts but reuses the
/// strata below the one it starts at, so an addition already among the base
/// facts would be in the rebuilt closure with nothing below that stratum ever
/// derived from it — and staging it afterwards would find it present and
/// propagate nothing.
///
/// What a rebuild means for the additions depends on the kind. A base
/// delta's still go in and propagate, because nothing has derived from them
/// yet. A derived delta's are dropped: they are head tuples the rebuild
/// recomputed from the closure it rebuilt, so staging them again would stage
/// facts the closure already holds.
///
/// `touched` is cleared first, and a rebuild clears it again, so it only ever
/// holds what the delta moved after its last rebuild — nothing, when the last
/// half to run rebuilt, since the rebuild recomputed every consequence. A base
/// delta whose removals rebuilt and whose additions were then maintained
/// reports `.rebuilt` and still hands back what the additions derived: the
/// propagation that derived it does not maintain aggregate groups, so the
/// aggregate phase has to see it.
pub fn applyDelta(
    db: *database.Database,
    delta: Delta,
    touched: *relation_store.RelationStore,
) !Outcome {
    std.debug.assert(db.canMaintain());
    touched.clear();
    var outcome: Outcome = .{ .path = .maintained, .removed = 0, .added = 0 };

    // Delete-and-rederive rewrites the set it is given — over-deleted
    // consequences join it and rederived ones leave — so it works on a copy,
    // and for a base delta the copy is also where absent facts drop out.
    var removed: relation_store.RelationStore = .init(db.allocator);
    defer removed.deinit();
    for (0..delta.removals.len()) |index| {
        const fact = delta.removals.factAt(index);
        if (delta.kind == .base) {
            if (!try db.applyRemoval(fact)) continue;
            outcome.removed += 1;
        }
        try relation_store.copyFactInto(db.allocator, &removed, fact, false);
    }
    if (try applyRemovals(db, &removed, touched) == .rebuilt) {
        outcome.path = .rebuilt;
        if (delta.kind == .derived) return outcome;
    }

    // Facts borrowed from `db.facts`, which owns their terms. Inserting more
    // facts can move the entries holding them but not the terms themselves,
    // and nothing here removes a fact any more, so these stay valid until
    // staging copies them into the closure.
    var added: std.ArrayList(relation_store.Fact) = .empty;
    defer added.deinit(db.allocator);
    const staged = switch (delta.kind) {
        .derived => delta.additions,
        .base => staged: {
            for (delta.additions) |fact| {
                const stored = try db.applyFactInsertion(fact) orelse continue;
                try added.append(db.allocator, stored);
            }
            outcome.added = added.items.len;
            break :staged added.items;
        },
    };
    const batch_start = try stageInsertions(db, staged, delta.kind);
    if (try applyStaged(db, batch_start, touched) == .rebuilt) outcome.path = .rebuilt;
    return outcome;
}

/// Deletes `removals` from the closure through delete-and-rederive and
/// collects everything that actually left it into `touched`.
///
/// `removals` is rewritten in place into that set: over-deleted consequences
/// are added and rederived ones removed. A `.rebuilt` path leaves `touched`
/// empty.
fn applyRemovals(
    db: *database.Database,
    removals: *relation_store.RelationStore,
    touched: *relation_store.RelationStore,
) !Path {
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
fn stageInsertions(
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
/// A `.rebuilt` path clears `touched`, including anything the removals put
/// there: `batch_start` no longer indexes the closure the rebuild installed,
/// and the rebuild already recomputed what the collection was for.
fn applyStaged(
    db: *database.Database,
    batch_start: usize,
    touched: *relation_store.RelationStore,
) !Path {
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
fn propagateInsertions(db: *database.Database, batch_start: usize) !Path {
    const start_len = db.closure.?.len();
    const analysis = try db.eval.ensureAnalysis();
    const max_level = analysis.max_level;
    var level: usize = 0;
    while (level <= max_level) : (level += 1) {
        if (try levelBlocked(db, level, &db.closure.?, batch_start)) {
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
/// Whether stratum `level` must be rebuilt rather than maintained, because the
/// facts in `changed` from `from` onwards reach one of its rules through
/// negation or through an aggregate this phase cannot maintain.
///
/// Insertion and deletion share the whole of this test. Deletion used to add a
/// second one: over-deletion runs a rule backwards, and a seeded structural
/// rule has a head variable no body goal binds, so the head such a derivation
/// supported could not be named. `overdeleteEnumerated` names it by looking it
/// up in the closure instead, and the extra guard went with it.
fn levelBlocked(
    db: *database.Database,
    level: usize,
    changed: *const relation_store.RelationStore,
    from: usize,
) !bool {
    var keys: std.AutoHashMapUnmanaged(relation_store.PredicateKey, void) = .empty;
    defer keys.deinit(db.allocator);
    try relation_store.collectPredicateKeys(db.allocator, changed, from, &keys);
    return try stratumImpact(db, level, &keys) == .rebuild;
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
fn propagateDeletions(db: *database.Database, deleted: *relation_store.RelationStore) !Path {
    var old_closure = try db.closure.?.clone();
    defer old_closure.deinit();
    for (0..deleted.len()) |index| {
        _ = try db.closure.?.removeFact(deleted.factAt(index));
    }
    const analysis = try db.eval.ensureAnalysis();
    var level: usize = 0;
    while (level <= analysis.max_level) : (level += 1) {
        if (try levelBlocked(db, level, deleted, 0)) {
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
/// Runs one rule backwards through one of its body occurrences: bind that
/// occurrence to the deleted fact, and take out of the closure every head
/// tuple the resulting derivations supported.
///
/// Which head tuples those are is answered two ways. An ordinary rule's body
/// binding determines its head, so the head is *built*. A seeded structural
/// rule's does not, so its head is *enumerated*.
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
    if (rule.seed_argument == null)
        return overdeleteConstructed(db, old_closure, deleted, rule, rest, &initial);
    return overdeleteEnumerated(db, old_closure, deleted, rule, rest, &initial);
}
/// Over-deletes through an ordinary rule: solve the remaining goals against
/// the pre-deletion closure and build the head each solution derived.
/// `validateRuleSafety` requires every head variable of such a rule to be
/// bound by the body, so the build cannot fail for want of a binding.
fn overdeleteConstructed(
    db: *database.Database,
    old_closure: *relation_store.RelationStore,
    deleted: *relation_store.RelationStore,
    rule: syntax.Rule,
    rest: []const syntax.Clause,
    initial: *const syntax.Binding,
) !void {
    var answers: std.ArrayList(syntax.Binding) = .empty;
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    if (!try solveRest(db, rest, old_closure, initial, &answers)) return;
    for (answers.items) |*answer| {
        const head_fact = try db.eval.deriveFact(rule.head, answer);
        var taken = false;
        defer if (!taken) db.allocator.free(head_fact.terms);
        if (!try deletableHead(db, head_fact, deleted)) continue;
        try takeHead(db, head_fact, deleted);
        taken = true;
    }
}
/// Over-deletes through a seeded structural rule, whose head the body binding
/// does not determine.
///
/// Pinning `length(T, M)` in `length(H!T, N) :- length(T, M), N = M + 1`
/// against a deleted fact binds `T`, `M` and then `N`, but never `H`. Forward
/// evaluation binds it by enumerating the value table against
/// `head.terms[seed_argument]`; backwards there is no value to enumerate
/// against. So the head is looked up rather than built, which is sound because
/// over-deletion only ever acts on head tuples the closure holds — the built
/// ones are discarded when it does not.
///
/// The lookup is a candidate prefilter like every other, keyed by the head
/// arguments the body binding leaves ground, and for the canonical seeded rule
/// there are none: the seed argument is fixed only in its tail, and the
/// remaining head arguments are computed downstream of it. The unification
/// below is therefore the filter that matters, and the lookup usually hands it
/// the head predicate's whole relation. That costs candidates, not
/// correctness; making it cheaper wants a closure index keyed by the seed
/// argument's tail, which is deferred work.
///
/// The candidate is unified into the binding *before* the remaining goals are
/// solved, not after. It has to be: the seed argument's variables can appear in
/// the body too, as `H` does in `sum(H!T, N) :- sum(T, M), N = M + H`, and the
/// candidate is the only thing that binds them.
fn overdeleteEnumerated(
    db: *database.Database,
    old_closure: *relation_store.RelationStore,
    deleted: *relation_store.RelationStore,
    rule: syntax.Rule,
    rest: []const syntax.Clause,
    initial: *const syntax.Binding,
) !void {
    // The head unification is the selective test — it holds the candidate's
    // seed argument to the tail the body binding fixed — and it is also the
    // cheap one, so it runs first, over the store, before anything is copied.
    // Copies are needed at all only because taking a fact out of the closure
    // retires every index into it, including this lookup's candidate list.
    var seeded: syntax.Binding = .{};
    defer seeded.deinit(db.allocator);
    var candidates: std.ArrayList(relation_store.Fact) = .empty;
    defer {
        for (candidates.items) |fact| db.allocator.free(fact.terms);
        candidates.deinit(db.allocator);
    }
    for (try db.eval.lookupCandidates(&db.closure.?, rule.head, initial)) |index| {
        const candidate = db.closure.?.factAt(index);
        try refill(db.allocator, &seeded, initial);
        if (!try db.eval.unify(candidate, rule.head, &seeded)) continue;
        try relation_store.appendFactCopy(db.allocator, &candidates, candidate);
    }

    for (candidates.items) |candidate| {
        if (!try deletableHead(db, candidate, deleted)) continue;
        try refill(db.allocator, &seeded, initial);
        if (!try db.eval.unify(candidate, rule.head, &seeded)) continue;
        var answers: std.ArrayList(syntax.Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(db.allocator);
            answers.deinit(db.allocator);
        }
        if (!try solveRest(db, rest, old_closure, &seeded, &answers)) continue;
        // The candidate bound every head variable, so each answer derives the
        // candidate itself: one solution is a whole proof, and more of them are
        // more proofs of the same tuple.
        if (answers.items.len == 0) continue;
        const head_fact: relation_store.Fact = .{
            .predicate = candidate.predicate,
            .terms = try db.allocator.dupe(syntax.ValueId, candidate.terms),
        };
        var taken = false;
        defer if (!taken) db.allocator.free(head_fact.terms);
        try takeHead(db, head_fact, deleted);
        taken = true;
    }
}
/// Refills `scratch` from `source`, keeping the capacity it already has. The
/// filter above runs once per candidate fact of the head relation, which is
/// where over-deletion through a seeded rule spends its time, so it reuses one
/// binding rather than cloning `source` per candidate.
fn refill(
    allocator: std.mem.Allocator,
    scratch: *syntax.Binding,
    source: *const syntax.Binding,
) !void {
    scratch.values.clearRetainingCapacity();
    try scratch.values.ensureUnusedCapacity(allocator, source.values.count());
    for (source.values.keys(), source.values.values()) |variable, value|
        scratch.values.putAssumeCapacity(variable, value);
}
/// Solves a rule's remaining goals against the pre-deletion closure, and
/// reports whether the solve ran to completion. A numeric error abandons it
/// and its partial answers, exactly as forward seeded rule application does: a
/// derivation that could not be computed forwards never happened.
fn solveRest(
    db: *database.Database,
    rest: []const syntax.Clause,
    old_closure: *relation_store.RelationStore,
    bindings: *const syntax.Binding,
    answers: *std.ArrayList(syntax.Binding),
) !bool {
    db.eval.solve(old_closure, null, rest, bindings, answers, null) catch |err| switch (err) {
        errors.Error.NumericType, errors.Error.NumericOverflow => return false,
        else => return err,
    };
    return true;
}
/// Whether this head tuple is one over-deletion may take: a base fact is not
/// derived, a fact already queued has been taken, and a fact the reduced
/// closure no longer holds was never there to take.
fn deletableHead(
    db: *database.Database,
    head: relation_store.Fact,
    deleted: *relation_store.RelationStore,
) !bool {
    if (try db.facts.contains(head)) return false;
    if (try deleted.contains(head)) return false;
    return db.closure.?.contains(head);
}
/// Takes a head tuple out of the closure and queues it for rederivation,
/// adopting `head.terms` on success. On failure the caller still owns them.
fn takeHead(
    db: *database.Database,
    head: relation_store.Fact,
    deleted: *relation_store.RelationStore,
) !void {
    _ = try db.closure.?.removeFact(head);
    _ = try deleted.insert(head, true);
    db.overdeleted_facts += 1;
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
            db.rederived_facts += 1;
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
        db.eval.solve(
            &db.closure.?,
            rule.head,
            rule.body,
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

const testing = std.testing;
const compile = @import("compile.zig");
const input = @import("input.zig");
const test_support = @import("test_support.zig");

/// A store of one-atom facts, interned against `db`, for a delta to borrow.
fn atomFacts(
    db: *database.Database,
    facts: []const struct { []const u8, []const u8 },
) !relation_store.RelationStore {
    var store: relation_store.RelationStore = .init(db.allocator);
    errdefer store.deinit();
    for (facts) |fact| {
        const expression = try compile.compileRelation(db, fact[0], &.{input.atom(fact[1])}, false);
        defer syntax.freeExpr(db.allocator, expression);
        const terms = try db.allocator.alloc(syntax.ValueId, 1);
        terms[0] = db.eval.termToValue(expression.terms[0], null) catch |err| {
            db.allocator.free(terms);
            return err;
        };
        _ = store.insert(.{ .predicate = expression.predicate, .terms = terms }, false) catch |err| {
            db.allocator.free(terms);
            return err;
        };
    }
    return store;
}

/// Adds one-atom base facts and materializes the closure over them, the
/// clean state a delta starts from.
fn materializeWith(db: *database.Database, facts: []const struct { []const u8, []const u8 }) !void {
    var store = try atomFacts(db, facts);
    defer store.deinit();
    for (0..store.len()) |index| _ = try db.applyFactInsertion(store.factAt(index));
    try materialization.ensureMaterialized(db);
}

/// `reach` at stratum zero, and `lonely` above it, negating `linked`.
fn defineReachAndLonely(db: *database.Database) !void {
    try test_support.defineRule(db, input.relation("reach", &.{input.variable("X")}), &.{
        input.relation("node", &.{input.variable("X")}),
    });
    try test_support.defineRule(db, input.relation("lonely", &.{input.variable("X")}), &.{
        input.relation("node", &.{input.variable("X")}),
        input.not("linked", &.{input.variable("X")}),
    });
}

test "a base addition derives below the stratum its delta's removals rebuilt from" {
    // The removal reaches `lonely` through negation, so it falls back to a
    // rebuild from `lonely`'s stratum, reusing `reach` from the closure as it
    // stood. Had `node(b)` joined the base facts first, the rebuild would
    // have held it with no `reach(b)` below, and staging it afterwards would
    // have found it present and propagated nothing.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachAndLonely(&db);
    try materializeWith(&db, &.{ .{ "node", "a" }, .{ "linked", "a" } });

    var removals = try atomFacts(&db, &.{.{ "linked", "a" }});
    defer removals.deinit();
    var additions = try atomFacts(&db, &.{.{ "node", "b" }});
    defer additions.deinit();
    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const outcome = try applyDelta(&db, .{
        .removals = &removals,
        .additions = &.{additions.factAt(0)},
        .kind = .base,
    }, &touched);

    try testing.expectEqual(Path.rebuilt, outcome.path);
    try testing.expectEqual(@as(usize, 1), db.rebuild_fallbacks);
    var reach_b = try atomFacts(&db, &.{.{ "reach", "b" }});
    defer reach_b.deinit();
    try testing.expect(try db.closure.?.contains(reach_b.factAt(0)));
    try test_support.expectClosureMatchesRebuild(&db);
}

test "an insertion reaching negation surfaces as a rebuild, not as a clean maintain" {
    // `db.materialization` cannot answer this: the fallback repairs the
    // closure before returning, so it reads `.clean` on both paths. The
    // outcome the delta reports is what separates them.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try test_support.defineRule(&db, input.relation("blocked", &.{input.variable("X")}), &.{
        input.relation("node", &.{input.variable("X")}),
        input.not("skip", &.{input.variable("X")}),
    });
    try materializeWith(&db, &.{.{ "node", "a" }});
    try testing.expectEqual(database.Materialization.clean, db.materialization);

    var none: relation_store.RelationStore = .init(db.allocator);
    defer none.deinit();
    var additions = try atomFacts(&db, &.{.{ "skip", "a" }});
    defer additions.deinit();
    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const outcome = try applyDelta(&db, .{
        .removals = &none,
        .additions = &.{additions.factAt(0)},
        .kind = .base,
    }, &touched);

    try testing.expectEqual(Path.rebuilt, outcome.path);
    try testing.expectEqual(@as(usize, 1), db.rebuild_fallbacks);
    // Clean, and yet not maintained — and `touched` is empty, because the
    // rebuild already recomputed everything the aggregate phase would have
    // been given it to reconsider.
    try testing.expectEqual(database.Materialization.clean, db.materialization);
    try testing.expectEqual(@as(usize, 0), touched.len());
    try test_support.expectClosureMatchesRebuild(&db);
}

test "a base delta can take a fact out and put it back" {
    // The removal propagates first — `reach(a)` is over-deleted and finds no
    // other proof — and the addition then brings both back. Nothing is
    // left counted twice: the closure is the one the unchanged facts build.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachAndLonely(&db);
    try materializeWith(&db, &.{ .{ "node", "a" }, .{ "linked", "a" } });
    const closure_len = db.closure.?.len();

    var facts = try atomFacts(&db, &.{.{ "node", "a" }});
    defer facts.deinit();
    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const outcome = try applyDelta(&db, .{
        .removals = &facts,
        .additions = &.{facts.factAt(0)},
        .kind = .base,
    }, &touched);

    try testing.expectEqual(Path.maintained, outcome.path);
    try testing.expectEqual(@as(usize, 1), outcome.removed);
    try testing.expectEqual(@as(usize, 1), outcome.added);
    try testing.expect(try db.facts.contains(facts.factAt(0)));
    try testing.expectEqual(closure_len, db.closure.?.len());
    try test_support.expectClosureMatchesRebuild(&db);
}

test "a base delta counts the facts it changed, not the facts it names" {
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachAndLonely(&db);
    try materializeWith(&db, &.{ .{ "node", "a" }, .{ "node", "b" }, .{ "linked", "a" } });

    // Two removals of which one is absent, and three additions of which one
    // is already held and one is named twice.
    var removals = try atomFacts(&db, &.{ .{ "node", "b" }, .{ "node", "z" } });
    defer removals.deinit();
    var additions = try atomFacts(&db, &.{ .{ "node", "a" }, .{ "node", "c" } });
    defer additions.deinit();
    var touched: relation_store.RelationStore = .init(db.allocator);
    defer touched.deinit();
    const outcome = try applyDelta(&db, .{
        .removals = &removals,
        .additions = &.{ additions.factAt(0), additions.factAt(1), additions.factAt(1) },
        .kind = .base,
    }, &touched);

    try testing.expectEqual(Path.maintained, outcome.path);
    try testing.expectEqual(@as(usize, 1), outcome.removed);
    try testing.expectEqual(@as(usize, 1), outcome.added);
    try test_support.expectClosureMatchesRebuild(&db);

    // A derived delta leaves the base facts alone, so it counts nothing.
    var derived = try atomFacts(&db, &.{.{ "reach", "c" }});
    defer derived.deinit();
    const derived_outcome = try applyDelta(&db, .{
        .removals = &derived,
        .additions = &.{derived.factAt(0)},
        .kind = .derived,
    }, &touched);
    try testing.expectEqual(@as(usize, 0), derived_outcome.removed);
    try testing.expectEqual(@as(usize, 0), derived_outcome.added);
    try test_support.expectClosureMatchesRebuild(&db);
}
