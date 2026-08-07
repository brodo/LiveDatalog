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
const test_support = @import("test_support.zig");
const evaluator = @import("evaluator.zig");
const root = @import("root.zig");
const materialization = @import("materialization.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");

/// How a batch's changed predicates affect one stratum's maintenance.
pub const StratumImpact = enum { none, aggregate, rebuild };

/// Propagates a batch of base insertions already appended to the clean
/// closure at `batch_start`, one stratum at a time. A stratum whose
/// negated or aggregated dependencies gained facts falls back to the
/// dirty-stratum rebuild; strata below it keep their incremental state.
pub fn propagateInsertions(db: *root.Jatalog, batch_start: usize) !void {
    const start_len = db.closure.?.len();
    const analysis = try db.eval.ensureAnalysis();
    const max_level = analysis.max_level;
    var level: usize = 0;
    while (level <= max_level) : (level += 1) {
        if (try insertionBlocked(db, level, batch_start)) {
            db.rebuild_fallbacks += 1;
            materialization.markDirty(db, level);
            try materialization.ensureMaterialized(db);
            return;
        }
        try propagateLevel(db, &db.closure.?, &analysis.strata, level, batch_start);
    }
    db.propagated_facts += db.closure.?.len() - start_len;
}
/// Whether stratum `level` must be rebuilt rather than maintained because the
/// facts appended to the closure from `batch_start` reach one of its rules
/// through negation or through an aggregate this phase cannot maintain.
fn insertionBlocked(db: *root.Jatalog, level: usize, batch_start: usize) !bool {
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
fn deletionBlocked(db: *root.Jatalog, level: usize, deleted: *const relation_store.RelationStore) !bool {
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
    db: *root.Jatalog,
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
pub fn propagateDeletions(db: *root.Jatalog, deleted: *relation_store.RelationStore) !void {
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
            materialization.markDirty(db, level);
            try materialization.ensureMaterialized(db);
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
/// Selecting rules by `ruleStratum` rather than the `ruleActiveAt` the
/// propagation and expansion phases use is deliberate and sufficient. Those
/// phases keep a seeded rule active above its own stratum because new values
/// are interned there, and values drive it. Over-deletion follows facts, not
/// values, and stratification puts every body predicate at or below its
/// head's stratum, so a rule can only lose support from strata this loop has
/// already reached. Extending the reach would re-examine rules against
/// victims their bodies cannot mention.
fn overdeleteLevel(
    db: *root.Jatalog,
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
    db: *root.Jatalog,
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
        root.Error.NumericType, root.Error.NumericOverflow => return,
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
    db: *root.Jatalog,
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
fn hasAlternativeDerivation(db: *root.Jatalog, fact: relation_store.Fact) !bool {
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
            root.Error.NumericType, root.Error.NumericOverflow => continue,
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
    db: *root.Jatalog,
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

test "insert-only batches propagate incrementally and match full rebuild" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(n0, n1). edge(n1, n2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "path(n0, n2)?", 1);
    const expansions_after_build = db.eval.expansions;

    // Each batch extends the chain; the closure stays clean and matches a
    // full rebuild after every batch without any stratum expansion.
    var name_buffer: [16]u8 = undefined;
    var next_buffer: [16]u8 = undefined;
    for (2..6) |index| {
        const from = try std.fmt.bufPrint(&name_buffer, "n{d}", .{index});
        const to = try std.fmt.bufPrint(&next_buffer, "n{d}", .{index + 1});
        try std.testing.expect(try db.applyChanges(&.{
            root.input.fact("edge", &.{ root.input.atom(from), root.input.atom(to) }),
        }, &.{}));
        try std.testing.expect(db.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db);
    }
    try std.testing.expectEqual(expansions_after_build, db.eval.expansions);
    try std.testing.expect(db.propagated_facts > 0);
    try test_support.expectAnswerCount(&db, "path(n0, n6)?", 1);
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 21);
}

test "one inserted edge propagates each recursive consequence exactly once" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 6);

    // Inserting edge(d, e) derives exactly the four new paths a-e, b-e,
    // c-e, and d-e; each is propagated and counted exactly once.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("d"), root.input.atom("e") }),
    }, &.{}));
    try std.testing.expectEqual(@as(usize, 4), db.propagated_facts);
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 10);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "duplicate base insertions produce no derived delta" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "path(a, b)?", 1);
    const closure_len = db.closure.?.len();
    const propagated = db.propagated_facts;

    try std.testing.expect(!try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    }, &.{}));
    try std.testing.expectEqual(closure_len, db.closure.?.len());
    try std.testing.expectEqual(propagated, db.propagated_facts);
    try std.testing.expect(db.materialization == .clean);
}

test "propagation reaching negation or setof falls back to dirty rebuild" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(a, b). flag(a). flag(b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\note(X) :- flag(X), not path(a, X).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "note(X)?", 1);
    const expansions_after_build = db.eval.expansions;

    // flag is only read positively, so its insertion propagates through the
    // negation stratum without any rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("flag", &.{root.input.atom("c")}),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build, db.eval.expansions);
    try std.testing.expect(db.materialization == .clean);
    try test_support.expectAnswerCount(&db, "note(c)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);

    // An edge insertion grows path, which the negation reads, so the
    // negation stratum rebuilds while the positive stratum stays
    // incremental.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("b"), root.input.atom("c") }),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build + 1, db.eval.expansions);
    try std.testing.expect(db.materialization == .clean);
    try test_support.expectAnswerCount(&db, "note(c)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "batch deletions and mixed batches maintain the closure correctly" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "path(a, c)?", 1);

    // Deleting an absent fact alone is a no-op that commits nothing.
    try std.testing.expect(!try db.applyChanges(&.{}, &.{
        root.input.fact("edge", &.{ root.input.atom("x"), root.input.atom("y") }),
    }));
    try std.testing.expect(db.materialization == .clean);

    // A mixed batch deletes one edge and inserts another as one transition.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("c"), root.input.atom("d") }),
    }, &.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    }));
    try test_support.expectAnswerCount(&db, "path(a, c)?", 0);
    try test_support.expectAnswerCount(&db, "path(b, d)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);

    try std.testing.expectError(root.Error.InvalidFact, db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.variable("x"), root.input.atom("y") }),
    }, &.{}));
    try std.testing.expectError(root.Error.InvalidFact, db.applyChanges(&.{}, &.{
        root.input.fact("edge", &.{ root.input.variable("x"), root.input.atom("y") }),
    }));
}

test "over-deletion reaches a seeded rule fed by values from a higher stratum" {
    // `length` is a seeded structural rule: it is driven by the value table
    // rather than by a fact relation, so it sits in stratum zero while the
    // lists it consumes are interned by `collected` in a higher stratum. That
    // is the one case where a rule keeps deriving facts above its own stratum,
    // and it is why `expandLevel` and `propagateLevel` select rules with
    // `ruleActiveAt` while `overdeleteLevel` uses `ruleStratum`.
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2).
        \\member(g1, a). member(g1, b). member(g2, c).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
    );
    setup.deinit();
    try db.materialize();
    try test_support.expectAnswerCount(&db, "size(g1, 2)?", 1);

    // Removing a member shortens g1's list. The old list value stays interned,
    // so `length` keeps deriving its length — a rebuild does the same, because
    // the value table is monotone and nothing withdraws a structural value.
    // What must disappear is `size(g1, 2)`, whose support went with the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("member", &.{ root.input.atom("g1"), root.input.atom("b") }),
    }));
    try test_support.expectAnswerCount(&db, "size(g1, 2)?", 0);
    try test_support.expectAnswerCount(&db, "size(g1, 1)?", 1);
    try test_support.expectAnswerCount(&db, "size(g2, 1)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);

    // Deleting the structural rule's own seed fact removes the whole chain,
    // and with it every `size`. Over-deletion cannot run this rule backwards —
    // it would have to name `H` in `length(H!T, N)` from `length(T, M)` alone —
    // so the stratum takes the rebuild instead of reporting UnboundVariable.
    const fallbacks_before = db.maintenanceStats().rebuild_fallbacks;
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("length", &.{ root.input.list(&.{}), root.input.integer(0) }),
    }));
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > fallbacks_before);
    try test_support.expectAnswerCount(&db, "size(G, N)?", 0);
    try test_support.expectAnswerCount(&db, "length(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "deleting the only base support removes the entire unsupported cycle" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    // The full cycle reaches every node from every node.
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 9);
    const expansions_after_build = db.eval.expansions;

    // After deleting edge(a, b) the cyclically self-supporting facts such
    // as path(a, a) must all disappear; reference counts alone would keep
    // them alive. The deletion is incremental: no stratum expansion runs.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.eval.expansions);
    try std.testing.expect(db.removed_facts > 0);
    try test_support.expectAnswerCount(&db, "path(a, a)?", 0);
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 3);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "alternative recursive and non-recursive derivations preserve facts" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\marked(a).
        \\special(X) :- marked(X).
        \\special(X) :- path(X, d).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "path(a, d)?", 1);
    try test_support.expectAnswerCount(&db, "special(b)?", 1);

    // path(a, d) survives the deletion through the c branch of the diamond,
    // while path(b, d) and with it special(b) lose their only support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("edge", &.{ root.input.atom("b"), root.input.atom("d") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try test_support.expectAnswerCount(&db, "path(a, d)?", 1);
    try test_support.expectAnswerCount(&db, "special(b)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);

    // special(a) loses its non-recursive derivation but survives through
    // the recursive path(a, d) alternative.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("marked", &.{root.input.atom("a")}),
    }));
    try test_support.expectAnswerCount(&db, "special(a)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "a deletion falling back to rebuild leaves the batch's insertions a clean closure" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
    );
    setup.deinit();
    try db.materialize();
    try test_support.expectAnswerCount(&db, "isolated(b)?", 0);

    // Deleting the edge over-deletes path(a, b), which reaches `isolated`
    // through negation and forces delete-and-rederive to abandon the
    // incremental path. The insertion in the same batch then has to find a
    // clean closure to propagate into: the fallback repairs the closure
    // through `ensureMaterialized` rather than leaving it dirty, which is
    // the invariant `applyInsertions` asserts.
    const before = db.maintenanceStats().rebuild_fallbacks;
    try std.testing.expect(try db.applyChanges(
        &.{root.input.fact("edge", &.{ root.input.atom("b"), root.input.atom("c") })},
        &.{root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") })},
    ));
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before);

    try test_support.expectAnswerCount(&db, "isolated(b)?", 1);
    try test_support.expectAnswerCount(&db, "path(b, c)?", 1);
    try test_support.expectAnswerCount(&db, "path(a, c)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "adding and removing a fact toggles negation-dependent conclusions" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\item(a). item(b).
        \\blocked(b).
        \\allowed(X) :- item(X), not blocked(X).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "allowed(a)?", 1);
    try test_support.expectAnswerCount(&db, "allowed(b)?", 0);

    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("blocked", &.{root.input.atom("a")}),
    }, &.{}));
    try test_support.expectAnswerCount(&db, "allowed(a)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("blocked", &.{root.input.atom("a")}),
    }));
    try test_support.expectAnswerCount(&db, "allowed(a)?", 1);
    try test_support.expectAnswerCount(&db, "allowed(b)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "projection counts change without prematurely deleting supported tuples" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\holds(a, b1). holds(a, b2).
        \\present(X) :- holds(X, Y).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "present(a)?", 1);
    const present_id = db.strings.get("present").?;
    const support_before = blk: {
        for (0..db.closure.?.len()) |index| {
            const fact = db.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_before >= 2);

    // Removing one of two supports keeps the tuple with changed support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("holds", &.{ root.input.atom("a"), root.input.atom("b1") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try test_support.expectAnswerCount(&db, "present(a)?", 1);
    const support_after = blk: {
        for (0..db.closure.?.len()) |index| {
            const fact = db.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_after != support_before);
    try test_support.expectClosureMatchesRebuild(&db);

    // Removing the last support deletes the tuple.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("holds", &.{ root.input.atom("a"), root.input.atom("b2") }),
    }));
    try test_support.expectAnswerCount(&db, "present(a)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "random mixed update traces match a clean rebuild after every batch" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e).
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
        \\summary(S) :- node(a), setof([X, Y], path(X, Y), S).
    );
    setup.deinit();
    try test_support.expectAnswerCount(&db, "summary(S)?", 1);

    const names = [_][]const u8{ "a", "b", "c", "d", "e" };
    var prng = std.Random.DefaultPrng.init(0x5eed5eed5eed5eed);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [3][2]root.input.Term = undefined;
        var inserts: [3]root.input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            insert_buffer[slot] = .{
                root.input.atom(names[random.uintLessThan(usize, names.len)]),
                root.input.atom(names[random.uintLessThan(usize, names.len)]),
            };
            inserts[slot] = root.input.fact("edge", &insert_buffer[slot]);
        }
        var delete_buffer: [3][2]root.input.Term = undefined;
        var deletes: [3]root.input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            delete_buffer[slot] = .{
                root.input.atom(names[random.uintLessThan(usize, names.len)]),
                root.input.atom(names[random.uintLessThan(usize, names.len)]),
            };
            deletes[slot] = root.input.fact("edge", &delete_buffer[slot]);
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db);
    }
}

test "retraction maintains the closure incrementally" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a). edge(x, y).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try db.materialize();
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 10);
    const after_build = db.maintenanceStats();

    // A typed retraction runs delete-and-rederive rather than dirtying the
    // stratum, so no rule expansion happens and the closure stays clean.
    try std.testing.expect(try db.retract(&.{
        root.input.relation("edge", &.{ root.input.atom("x"), root.input.atom("y") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().removed_facts > after_build.removed_facts);
    try test_support.expectAnswerCount(&db, "path(x, y)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);

    // Retracting the only base support of a cycle removes the whole
    // unsupported cycle, still without a rebuild.
    const before_cycle = db.maintenanceStats();
    try std.testing.expect(try db.retract(&.{
        root.input.relation("edge", &.{ root.input.atom("c"), root.input.atom("a") }),
    }));
    try std.testing.expectEqual(before_cycle.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try test_support.expectAnswerCount(&db, "path(a, a)?", 0);
    try test_support.expectAnswerCount(&db, "path(a, c)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "pattern retraction removes every matching fact incrementally" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(a, d). edge(b, e).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // One goal with a variable retracts all three outgoing edges of a.
    try std.testing.expect(try db.retract(&.{
        root.input.relation("edge", &.{ root.input.atom("a"), root.input.variable("target") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try test_support.expectAnswerCount(&db, "edge(a, X)?", 0);
    try test_support.expectAnswerCount(&db, "path(a, X)?", 0);
    try test_support.expectAnswerCount(&db, "path(b, e)?", 1);
    try test_support.expectClosureMatchesRebuild(&db);

    // Source-level retraction takes the same path.
    const before_source = db.maintenanceStats();
    var retracted = try db.execute("edge(b, e)~");
    retracted.deinit();
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(before_source.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try test_support.expectAnswerCount(&db, "path(X, Y)?", 0);
    try test_support.expectClosureMatchesRebuild(&db);
}

test "retraction maintains aggregate groups and negation strata" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a). member(g1, b). member(g2, z).
        \\banned(g2).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\allowed(G) :- group(G), not banned(G).
    );
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // Retracting a member updates only the affected group's list.
    try std.testing.expect(try db.retract(&.{
        root.input.relation("member", &.{ root.input.atom("g1"), root.input.atom("a") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().maintained_groups > after_build.maintained_groups);
    var collected = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&collected.query.answers.items[0], "S", "[b]");
    collected.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // Retracting the last member leaves the enumerated group empty.
    try std.testing.expect(try db.retract(&.{
        root.input.relation("member", &.{ root.input.atom("g1"), root.input.atom("b") }),
    }));
    var emptied = try db.execute("collected(g1, S)?");
    try test_support.expectBindingValue(&emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try test_support.expectClosureMatchesRebuild(&db);

    // Retracting a negated predicate is the documented rebuild category.
    const before_negation = db.maintenanceStats();
    try test_support.expectAnswerCount(&db, "allowed(g2)?", 0);
    try std.testing.expect(try db.retract(&.{
        root.input.relation("banned", &.{root.input.atom("g2")}),
    }));
    try test_support.expectAnswerCount(&db, "allowed(g2)?", 1);
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before_negation.rebuild_fallbacks);
    try test_support.expectClosureMatchesRebuild(&db);
}

fn retractionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: root.Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, c). group(g). member(g, m1). member(g, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    try db.materialize();
    _ = try db.retract(&.{
        root.input.relation("edge", &.{ root.input.atom("a"), root.input.variable("target") }),
    });
    _ = try db.retract(&.{
        root.input.relation("member", &.{ root.input.atom("g"), root.input.atom("m1") }),
    });
    var result = try db.execute("collected(g, S)?");
    defer result.deinit();
    const formatted = try (try result.query.answers.items[0].getValue("S")).formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[m2]")) return error.UnexpectedAggregate;
}

test "incremental retraction releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(retractionAllocationScenario);
}

/// Runs one deterministic update trace under a fixed policy and returns the
/// materialized database for comparison.
fn batchUpdateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: root.Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    var first = try db.execute("path(a, c)?");
    first.deinit();
    _ = try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("c"), root.input.atom("d") }),
    }, &.{});
    _ = try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("d"), root.input.atom("e") }),
    }, &.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    });
    var second = try db.execute("path(b, e)?");
    defer second.deinit();
    if (second.query.answers.items.len != 1) return error.UnexpectedAnswer;
}

test "batch updates roll back completely on failure" {
    try test_support.expectEveryAllocationFailureReleased(batchUpdateAllocationScenario);
}

fn runPolicyTrace(db: *root.Jatalog, policy: root.MaintenancePolicy) !void {
    db.setMaintenancePolicy(policy);
    var setup = try db.execute(
        \\node(a). node(b). node(c). group(g1). group(g2).
        \\edge(a, b). member(g1, m1). member(g2, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\isolated(X) :- node(X), not path(a, X).
    );
    setup.deinit();
    try db.materialize();

    const nodes = [_][]const u8{ "a", "b", "c" };
    const groups = [_][]const u8{ "g1", "g2" };
    const members = [_][]const u8{ "m1", "m2", "m3" };
    var prng = std.Random.DefaultPrng.init(0xc05715c05715);
    const random = prng.random();
    for (0..40) |step| {
        var edge_terms: [2]root.input.Term = .{
            root.input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
            root.input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
        };
        var member_terms: [2]root.input.Term = .{
            root.input.atom(groups[random.uintLessThan(usize, groups.len)]),
            root.input.atom(members[random.uintLessThan(usize, members.len)]),
        };
        if (step % 4 == 3) {
            // Exercise pattern retraction as well as the batch API.
            _ = try db.retract(&.{root.input.relation("member", &.{
                root.input.atom(groups[random.uintLessThan(usize, groups.len)]),
                root.input.variable("any"),
            })});
            continue;
        }
        var inserts: [2]root.input.Relation = undefined;
        var deletes: [2]root.input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (random.boolean()) {
            inserts[insert_count] = root.input.fact("edge", &edge_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = root.input.fact("edge", &edge_terms);
            delete_count += 1;
        }
        if (random.boolean()) {
            inserts[insert_count] = root.input.fact("member", &member_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = root.input.fact("member", &member_terms);
            delete_count += 1;
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
    }
    try db.materialize();
}

/// Program used by the cost-attribution tests below: a transitive closure
/// small enough that one edge change is cheap to maintain.
const cost_attribution_program =
    \\edge(a, b). edge(b, c).
    \\path(X, Y) :- edge(X, Y).
    \\path(X, Z) :- edge(X, Y), path(Y, Z).
;

test "the maintenance estimate counts facts changed, not facts named" {
    const new_edge = root.input.fact("edge", &.{ root.input.atom("c"), root.input.atom("d") });

    var lean: root.Jatalog = .init(std.testing.allocator);
    defer lean.deinit();
    lean.setMaintenancePolicy(.incremental);
    var lean_setup = try lean.execute(cost_attribution_program);
    lean_setup.deinit();
    try lean.materialize();
    _ = try lean.applyChanges(&.{new_edge}, &.{});

    var padded: root.Jatalog = .init(std.testing.allocator);
    defer padded.deinit();
    padded.setMaintenancePolicy(.incremental);
    var padded_setup = try padded.execute(cost_attribution_program);
    padded_setup.deinit();
    try padded.materialize();
    // The same single real insertion, named alongside deletions of facts the
    // database does not hold. Deleting an absent fact is a no-op, so the cost
    // per changed fact must match the lean batch rather than being divided by
    // the number of relations the caller happened to name.
    _ = try padded.applyChanges(&.{new_edge}, &.{
        root.input.fact("edge", &.{ root.input.atom("p"), root.input.atom("q") }),
        root.input.fact("edge", &.{ root.input.atom("q"), root.input.atom("r") }),
        root.input.fact("edge", &.{ root.input.atom("r"), root.input.atom("s") }),
        root.input.fact("edge", &.{ root.input.atom("s"), root.input.atom("t") }),
        root.input.fact("edge", &.{ root.input.atom("t"), root.input.atom("u") }),
        root.input.fact("edge", &.{ root.input.atom("u"), root.input.atom("v") }),
        root.input.fact("edge", &.{ root.input.atom("v"), root.input.atom("w") }),
    });

    try std.testing.expectEqual(
        lean.maintenanceStats().maintenance_work_per_fact,
        padded.maintenanceStats().maintenance_work_per_fact,
    );
}

test "a rebuild fallback is charged to the rebuild estimate, not to maintenance" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e). edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
    );
    setup.deinit();
    try db.materialize();

    // Deleting this edge over-deletes path facts that reach `isolated`
    // through negation, so delete-and-rederive abandons the incremental path
    // and rebuilds. The rebuild is real work, but it is recomputation work:
    // charging it to the maintenance estimate as well would let one event
    // push both estimates in opposite directions.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    }));
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.rebuild_fallbacks > 0);
    try std.testing.expect(stats.rebuild_work != null);
    try std.testing.expect(stats.maintenance_work_per_fact != null);
    // One base fact changed, so the per-fact estimate is the whole measured
    // maintenance cost. With the rebuild excluded it is only the abandoned
    // over-deletion attempt, which is far cheaper than the rebuild itself.
    try std.testing.expect(stats.maintenance_work_per_fact.? < stats.rebuild_work.?);
}

test "the cost model changes the path taken but never the result" {
    var automatic: root.Jatalog = .init(std.testing.allocator);
    defer automatic.deinit();
    try runPolicyTrace(&automatic, .automatic);

    var incremental: root.Jatalog = .init(std.testing.allocator);
    defer incremental.deinit();
    try runPolicyTrace(&incremental, .incremental);

    var recompute: root.Jatalog = .init(std.testing.allocator);
    defer recompute.deinit();
    try runPolicyTrace(&recompute, .recompute);

    // Every policy must leave the same base facts and the same closure.
    for ([_]*root.Jatalog{ &incremental, &recompute }) |other| {
        try std.testing.expectEqual(automatic.facts.len(), other.facts.len());
        for (0..automatic.facts.len()) |index|
            try std.testing.expect(try other.facts.contains(automatic.facts.factAt(index)));
        try std.testing.expectEqual(automatic.closure.?.len(), other.closure.?.len());
        for (0..automatic.closure.?.len()) |index|
            try std.testing.expect(try other.closure.?.contains(automatic.closure.?.factAt(index)));
    }
    try test_support.expectClosureMatchesRebuild(&automatic);

    // The pinned policies really did take different paths, and the
    // automatic one made a real decision rather than defaulting.
    const automatic_stats = automatic.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 0), incremental.maintenanceStats().recompute_choices);
    try std.testing.expectEqual(@as(usize, 0), recompute.maintenanceStats().maintain_choices);
    try std.testing.expect(automatic_stats.maintain_choices > 0);
    try std.testing.expect(automatic_stats.rebuild_work != null);
    try std.testing.expect(automatic_stats.maintenance_work_per_fact != null);
}

test "the cost model learns to prefer the cheaper path per workload" {
    // A recursive closure over a chain: one new edge derives a handful of
    // paths, while recomputing re-derives the entire transitive closure.
    var closure_db: root.Jatalog = .init(std.testing.allocator);
    defer closure_db.deinit();
    var chain_source: std.ArrayList(u8) = .empty;
    defer chain_source.deinit(std.testing.allocator);
    for (0..30) |index| {
        var buffer: [64]u8 = undefined;
        const line = try std.fmt.bufPrint(&buffer, "edge(n{d}, n{d}). ", .{ index, index + 1 });
        try chain_source.appendSlice(std.testing.allocator, line);
    }
    try chain_source.appendSlice(
        std.testing.allocator,
        "path(X, Y) :- edge(X, Y). path(X, Z) :- edge(X, Y), path(Y, Z).",
    );
    var chain_setup = try closure_db.execute(chain_source.items);
    chain_setup.deinit();
    try closure_db.materialize();
    for (0..8) |index| {
        var from: [16]u8 = undefined;
        var to: [16]u8 = undefined;
        const source = try std.fmt.bufPrint(&from, "s{d}", .{index});
        const target = try std.fmt.bufPrint(&to, "n{d}", .{index});
        const terms: [2]root.input.Term = .{ root.input.atom(source), root.input.atom(target) };
        _ = try closure_db.applyChanges(&.{root.input.fact("edge", &terms)}, &.{});
        // Query between batches so a recompute decision is actually paid and
        // the closure is clean again when the next decision is made.
        var query = try closure_db.execute("path(n0, X)?");
        query.deinit();
    }
    const closure_stats = closure_db.maintenanceStats();
    try std.testing.expect(closure_stats.maintain_choices > closure_stats.recompute_choices);
    try test_support.expectClosureMatchesRebuild(&closure_db);

    // A shallow program whose closure is cheap to recompute: maintenance
    // has no recursion to save and the model should stop choosing it.
    var flat_db: root.Jatalog = .init(std.testing.allocator);
    defer flat_db.deinit();
    var flat_setup = try flat_db.execute(
        \\item(a). item(b). item(c).
        \\present(X) :- item(X).
    );
    flat_setup.deinit();
    try flat_db.materialize();
    for (0..8) |index| {
        var buffer: [16]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "i{d}", .{index});
        const terms: [1]root.input.Term = .{root.input.atom(name)};
        _ = try flat_db.applyChanges(&.{root.input.fact("item", &terms)}, &.{});
        var query = try flat_db.execute("present(X)?");
        query.deinit();
    }
    try test_support.expectClosureMatchesRebuild(&flat_db);
    const flat_stats = flat_db.maintenanceStats();
    try std.testing.expect(flat_stats.recompute_choices > 0);
}

test "shadow verification accepts maintained closures and reports corruption" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). group(g). member(g, m1).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\reachable(X) :- path(a, X).
        \\unreachable(X) :- edge(X, Y), not reachable(X).
    );
    setup.deinit();
    try db.materialize();

    // Insertions, deletions, and aggregate changes all pass verification.
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("c"), root.input.atom("d") }),
        root.input.fact("member", &.{ root.input.atom("g"), root.input.atom("m2") }),
    }, &.{}));
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    }));
    try std.testing.expect(try db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("a"), root.input.atom("b") }),
    }, &.{
        root.input.fact("member", &.{ root.input.atom("g"), root.input.atom("m1") }),
    }));
    try test_support.expectClosureMatchesRebuild(&db);

    // A closure corrupted behind the maintenance engine's back is caught:
    // this path tuple has no derivation from any base fact.
    const terms = try std.testing.allocator.alloc(relation_store.ValueId, 2);
    var terms_owned = true;
    defer if (terms_owned) std.testing.allocator.free(terms);
    terms[0] = try db.eval.values.intern(.{ .scalar = try db.eval.scalars.internAtom("phantom1") });
    terms[1] = try db.eval.values.intern(.{ .scalar = try db.eval.scalars.internAtom("phantom2") });
    const added = try db.closure.?.insert(.{
        .predicate = db.strings.get("path").?,
        .terms = terms,
    }, true);
    terms_owned = false;
    try std.testing.expect(added);
    try std.testing.expectError(root.Error.MaintenanceMismatch, db.applyChanges(&.{
        root.input.fact("edge", &.{ root.input.atom("d"), root.input.atom("e") }),
    }, &.{}));
}

test "randomized mixed traces hold under shadow verification" {
    var db: root.Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\node(a). node(b). node(c). group(g1). group(g2).
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\quiet(G) :- group(G), not member(G, m1).
    );
    setup.deinit();
    try db.materialize();

    const nodes = [_][]const u8{ "a", "b", "c" };
    const groups = [_][]const u8{ "g1", "g2" };
    const members = [_][]const u8{ "m1", "m2" };
    var prng = std.Random.DefaultPrng.init(0x5ade0e5ade0e);
    const random = prng.random();
    for (0..30) |_| {
        var edge_terms: [2]root.input.Term = .{
            root.input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
            root.input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
        };
        var member_terms: [2]root.input.Term = .{
            root.input.atom(groups[random.uintLessThan(usize, groups.len)]),
            root.input.atom(members[random.uintLessThan(usize, members.len)]),
        };
        const insert_edge = random.boolean();
        var inserts: [2]root.input.Relation = undefined;
        var deletes: [2]root.input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (insert_edge) {
            inserts[insert_count] = root.input.fact("edge", &edge_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = root.input.fact("edge", &edge_terms);
            delete_count += 1;
        }
        if (random.boolean()) {
            inserts[insert_count] = root.input.fact("member", &member_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = root.input.fact("member", &member_terms);
            delete_count += 1;
        }
        // Shadow verification asserts rebuild equality inside the call.
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try test_support.expectClosureMatchesRebuild(&db);
    }
}
