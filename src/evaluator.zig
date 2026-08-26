//! The program a database evaluates, and the machinery that evaluates it.
//!
//! The evaluator owns the interned ground values, the rule set and its
//! stratification. It does not own fact storage: every entry point takes the
//! store to read or extend as a parameter, which is what lets one evaluator
//! serve the base facts, the persistent closure, a staging clone and the
//! throwaway copies shadow verification builds.
//!
//! Layers above — incremental maintenance, aggregate views, the parser —
//! depend on this interface rather than on the database that holds it.
//!
//! The `ziglint-ignore: Z010` markers below are all one issue: the rule
//! asks for a bare `.Foo` error literal, but every one of these returns an
//! inferred error union, where `.Foo` resolves against the payload type
//! instead of the error set and does not compile.

const std = @import("std");
const intern_index = @import("intern_index.zig");
const scalar = @import("scalar.zig");
const syntax = @import("syntax.zig");
const planner = @import("planner.zig");
const relation_store = @import("relation_store.zig");
const cost_model = @import("cost_model.zig");

const errors = @import("errors.zig");

pub const Value = union(enum) {
    scalar: scalar.Id,
    nil,
    cons: struct { head: syntax.ValueId, tail: syntax.ValueId },
};

/// A hash agreeing with the `std.meta.eql` the table compares values by.
/// `Value` holds no slices, so the automatic hash covers exactly the bytes
/// equality compares.
fn hashValue(value: Value) u64 {
    var hasher: std.hash.Wyhash = .init(0);
    std.hash.autoHash(&hasher, value);
    return hasher.final();
}

pub const ValueTable = struct {
    allocator: std.mem.Allocator,
    values: std.ArrayList(Value) = .empty,
    /// Where a value equal to the one being interned already is. The ordered
    /// table above stays the source of truth and an identifier stays its
    /// position in it, so this accelerates the search and changes nothing
    /// about identity, ordering, or canonicalization.
    index: intern_index.Index = .empty,
    /// What interning this table has cost, machine-independently.
    counts: intern_index.Counts = .{},

    /// How the index reaches the table: what an entry hashes to, and whether
    /// the entry at an identifier is the value being looked for.
    const Lookup = struct {
        table: *const ValueTable,
        key: Value,

        pub fn matches(self: Lookup, id: u32) bool { // ziglint-ignore: Z012
            return std.meta.eql(self.table.values.items[id], self.key);
        }

        pub fn hash(self: Lookup, id: u32) u64 { // ziglint-ignore: Z012
            return hashValue(self.table.values.items[id]);
        }
    };

    pub fn init(allocator: std.mem.Allocator) ValueTable {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ValueTable) void {
        self.values.deinit(self.allocator);
        self.index.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const ValueTable) !ValueTable {
        var values = try self.values.clone(self.allocator);
        errdefer values.deinit(self.allocator);
        return .{
            .allocator = self.allocator,
            .values = values,
            .index = try self.index.clone(self.allocator),
            .counts = self.counts,
        };
    }

    pub fn intern(self: *ValueTable, value: Value) !syntax.ValueId {
        const lookup: Lookup = .{ .table = self, .key = value };
        const hash = hashValue(value);
        self.counts.calls += 1;
        const found = self.index.find(hash, lookup);
        self.counts.compared += found.compared;
        if (found.id) |id| return id;
        // The index reserves before the table appends, so a failure on either
        // side leaves the two agreeing with each other.
        try self.index.reserve(self.allocator, lookup);
        try self.values.append(self.allocator, value);
        const id: u32 = @intCast(self.values.items.len - 1);
        self.index.insertAssumeCapacity(hash, id);
        return id;
    }

    /// What the index needs to rehash an entry it is keeping when the table
    /// is truncated. Only `hash`, because nothing is being looked for.
    const Rehash = struct {
        table: *const ValueTable,

        pub fn hash(self: Rehash, id: u32) u64 { // ziglint-ignore: Z012
            return hashValue(self.table.values.items[id]);
        }
    };

    /// Drops every value interned at or after `count`, which is how a
    /// statement rolled back out of a shared transaction gives back what it
    /// interned. Identifiers are positions, so the values below `count` keep
    /// theirs and every fact holding one still means what it meant. Allocates
    /// nothing: a statement is usually being undone because an allocation
    /// failed.
    pub fn truncate(self: *ValueTable, count: usize) void {
        if (count >= self.values.items.len) return;
        self.values.shrinkRetainingCapacity(count);
        self.index.retainBelow(count, Rehash{ .table = self });
    }

    pub fn get(self: *const ValueTable, id: syntax.ValueId) Value {
        return self.values.items[@intCast(id)];
    }

    pub fn internFrom(self: *ValueTable, source: *const ValueTable, id: syntax.ValueId) !syntax.ValueId {
        return switch (source.get(id)) {
            .scalar => |value| try self.intern(.{ .scalar = value }),
            .nil => try self.intern(.nil),
            .cons => |pair| try self.intern(.{ .cons = .{
                .head = try self.internFrom(source, pair.head),
                .tail = try self.internFrom(source, pair.tail),
            } }),
        };
    }
};

/// Rule analysis cached after validation: the stratum mapping plus, for each
/// predicate read anywhere in a rule body, the lowest head stratum that
/// depends on it. Invalidated whenever the rule set changes.
pub const Analysis = struct {
    strata: std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    first_dependent: std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    max_level: usize,
    has_seed_rules: bool,

    pub fn deinit(self: *Analysis, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
        self.strata.deinit(allocator);
        self.first_dependent.deinit(allocator);
        self.* = undefined;
    }
};

/// Whether `rule` still derives facts while stratum `level` runs. An ordinary
/// rule is active only in its head's own stratum, which has reached its
/// fixpoint by the time a higher stratum starts. A seeded structural rule
/// stays active in every stratum at or above its own, because its seed set is
/// the growing value table rather than a completed relation.
pub fn ruleActiveAt(
    levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    rule: syntax.Rule,
    level: usize,
) bool {
    const rule_level = levels.get(syntax.predicateKey(rule.head)) orelse 0;
    if (rule_level == level) return true;
    return rule.seed_argument != null and rule_level < level;
}

/// The stratum a rule's head belongs to, ignoring the cross-stratum reach of
/// seeded rules that `ruleActiveAt` grants.
pub fn ruleStratum(
    levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    rule: syntax.Rule,
) usize {
    return levels.get(syntax.predicateKey(rule.head)) orelse 0;
}

/// The program a database evaluates: interned ground values, the rule set,
/// its stratification, and the machinery that matches rules against a fact
/// store.
///
/// Fact storage is deliberately not here. Every entry point takes the store
/// to read or extend as a parameter, which is what lets the same evaluator
/// serve the base facts, the persistent closure, a staging clone and the
/// throwaway copies that shadow verification builds.
///
/// The cost model lives here because the evaluator produces its unit of
/// work: `lookupCandidates` is where candidate facts are counted.
pub const Evaluator = struct {
    allocator: std.mem.Allocator,
    scalars: scalar.Store,
    values: ValueTable,
    rules: std.ArrayList(syntax.Rule) = .empty,
    next_rule_id: u32 = 0,
    analysis: ?Analysis = null,
    /// Counts stratum expansions; tests use it to prove that repeated
    /// queries perform no rule expansion after the first materialization.
    expansions: usize = 0,
    /// Chooses between maintaining and recomputing, and learns both costs.
    cost: cost_model.CostModel = .{},
    /// How a body's clause order is chosen before it is solved.
    plan_policy: planner.PlanPolicy = .cost_based,

    pub fn init(allocator: std.mem.Allocator) Evaluator {
        return .{
            .allocator = allocator,
            .scalars = .init(allocator),
            .values = .init(allocator),
        };
    }

    pub fn deinit(self: *Evaluator) void {
        if (self.analysis) |*analysis| analysis.deinit(self.allocator);
        for (self.rules.items) |rule| syntax.freeRule(self.allocator, rule);
        self.rules.deinit(self.allocator);
        self.values.deinit();
        self.scalars.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const Evaluator) !Evaluator {
        var result: Evaluator = .{
            .allocator = self.allocator,
            .scalars = try self.scalars.clone(),
            .values = undefined,
            .next_rule_id = self.next_rule_id,
            .expansions = self.expansions,
            .cost = self.cost,
            .plan_policy = self.plan_policy,
        };
        errdefer result.scalars.deinit();
        result.values = try self.values.clone();
        errdefer result.values.deinit();
        errdefer {
            for (result.rules.items) |rule| syntax.freeRule(self.allocator, rule);
            result.rules.deinit(self.allocator);
        }
        for (self.rules.items) |rule| {
            const copy = try syntax.cloneRule(self.allocator, rule);
            result.rules.append(self.allocator, copy) catch |err| {
                syntax.freeRule(self.allocator, copy);
                return err;
            };
        }
        return result;
    }

    /// Discards the cached stratification after a rule-set change.
    pub fn invalidateAnalysis(self: *Evaluator) void {
        if (self.analysis) |*analysis| analysis.deinit(self.allocator);
        self.analysis = null;
    }

    pub fn ensureAnalysis(self: *Evaluator) !*const Analysis {
        if (self.analysis == null) {
            var strata = try self.computeStrata();
            errdefer strata.deinit(self.allocator);
            var max_level: usize = 0;
            for (strata.values()) |level| max_level = @max(max_level, level);
            var first_dependent: std.array_hash_map.Auto(relation_store.PredicateKey, usize) = .empty;
            errdefer first_dependent.deinit(self.allocator);
            var has_seed_rules = false;
            for (self.rules.items) |rule| {
                if (rule.seed_argument != null) has_seed_rules = true;
                const head_level = strata.get(syntax.predicateKey(rule.head)) orelse 0;
                try syntax.noteBodyDependencies(self.allocator, rule.body, head_level, &first_dependent);
            }
            self.analysis = .{
                .strata = strata,
                .first_dependent = first_dependent,
                .max_level = max_level,
                .has_seed_rules = has_seed_rules,
            };
        }
        return &self.analysis.?;
    }

    pub fn expandFrom(self: *Evaluator, facts: *relation_store.RelationStore, first_level: usize) !void {
        const analysis = try self.ensureAnalysis();
        if (first_level > analysis.max_level) return;
        for (first_level..analysis.max_level + 1) |level|
            try self.expandLevel(facts, &analysis.strata, level);
    }

    /// Reference naive fixpoint kept as the semantic oracle for the
    /// semi-naive engine; differential tests compare both closures.
    pub fn expandNaive(self: *Evaluator, facts: *relation_store.RelationStore) !void {
        var levels = try self.computeStrata();
        defer levels.deinit(self.allocator);
        var max_level: usize = 0;
        for (levels.values()) |level| max_level = @max(max_level, level);

        for (0..max_level + 1) |level| {
            while (true) {
                const fact_count_before = facts.len();
                const value_count_before = self.values.values.items.len;
                for (self.rules.items) |rule| {
                    if (!ruleActiveAt(&levels, rule, level)) continue;
                    try self.applyRule(facts, rule, null);
                }
                if (facts.len() == fact_count_before and
                    self.values.values.items.len == value_count_before) break;
            }
        }
    }

    /// Runs one stratum to its fixpoint with semi-naive delta rounds. Round
    /// zero evaluates every active rule against the complete store. Later
    /// rounds re-evaluate a rule once per growing body occurrence with that
    /// occurrence restricted to the previous round's delta, while seeded
    /// structural recursion keeps its naive evaluation because its seed set
    /// is the growing value table rather than a fact relation. A predicate
    /// counts as growing when it belongs to this stratum or is the head of an
    /// active seed rule, since only those relations gain facts mid-stratum.
    fn expandLevel(
        self: *Evaluator,
        facts: *relation_store.RelationStore,
        levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
        level: usize,
    ) !void {
        self.expansions += 1;
        const ActiveRule = struct {
            rule: syntax.Rule,
            growing_occurrences: []usize,
        };
        var active: std.ArrayList(ActiveRule) = .empty;
        defer {
            for (active.items) |entry| self.allocator.free(entry.growing_occurrences);
            active.deinit(self.allocator);
        }
        var growing: std.AutoHashMapUnmanaged(relation_store.PredicateKey, void) = .empty;
        defer growing.deinit(self.allocator);
        for (self.rules.items) |rule| {
            if (!ruleActiveAt(levels, rule, level)) continue;
            if (rule.seed_argument != null)
                try growing.put(self.allocator, syntax.predicateKey(rule.head), {});
        }
        for (self.rules.items) |rule| {
            if (!ruleActiveAt(levels, rule, level)) continue;
            var occurrences: std.ArrayList(usize) = .empty;
            errdefer occurrences.deinit(self.allocator);
            if (rule.seed_argument == null) {
                for (rule.body, 0..) |clause, clause_index| {
                    const expression = switch (clause) {
                        .relational => |value| value,
                        else => continue,
                    };
                    const body_level = levels.get(syntax.predicateKey(expression)) orelse 0;
                    if (body_level == level or growing.contains(syntax.predicateKey(expression)))
                        try occurrences.append(self.allocator, clause_index);
                }
            }
            const owned = try occurrences.toOwnedSlice(self.allocator);
            active.append(self.allocator, .{
                .rule = rule,
                .growing_occurrences = owned,
            }) catch |err| {
                self.allocator.free(owned);
                return err;
            };
        }

        var delta_start = facts.len();
        var value_mark = self.values.values.items.len;
        for (active.items) |entry| try self.applyRule(facts, entry.rule, null);

        while (true) {
            const delta_end = facts.len();
            const values_grew = self.values.values.items.len != value_mark;
            if (delta_end == delta_start and !values_grew) break;
            value_mark = self.values.values.items.len;
            for (active.items) |entry| {
                if (entry.rule.seed_argument != null) {
                    try self.applyRule(facts, entry.rule, null);
                } else for (entry.growing_occurrences) |occurrence| {
                    try self.applyRule(facts, entry.rule, .{
                        .clause_index = occurrence,
                        .delta_start = delta_start,
                        .delta_end = delta_end,
                    });
                }
            }
            delta_start = delta_end;
        }
    }

    /// Plans `clauses` against `facts` and solves them in the planned order.
    ///
    /// A caller that addresses a body occurrence by its stored position — a
    /// semi-naive delta round is the only one that does — passes it in
    /// `constraint` and this translates it to the position the plan gave it,
    /// so the restriction follows the clause rather than the slot.
    pub fn solve(
        self: *Evaluator,
        facts: *relation_store.RelationStore,
        head: ?syntax.Expr,
        clauses: []const syntax.Clause,
        bindings: *const syntax.Binding,
        answers: *std.ArrayList(syntax.Binding),
        constraint: ?syntax.DeltaConstraint,
    ) !void {
        var chosen = try self.planFor(facts, head, clauses, bindings);
        defer chosen.deinit();
        try self.matchClauses(&chosen, facts, 0, bindings, answers, chosen.constrain(constraint));
    }

    /// Plans `clauses` taking whatever `bindings` already fixes as bound.
    pub fn planFor(
        self: *Evaluator,
        facts: *relation_store.RelationStore,
        head: ?syntax.Expr,
        clauses: []const syntax.Clause,
        bindings: *const syntax.Binding,
    ) !planner.Plan {
        return planner.plan(
            self.allocator,
            facts,
            head,
            clauses,
            bindings.values.keys(),
            self.plan_policy,
        );
    }

    pub fn applyRule(
        self: *Evaluator,
        facts: *relation_store.RelationStore,
        rule: syntax.Rule,
        constraint: ?syntax.DeltaConstraint,
    ) !void {
        var answers: std.ArrayList(syntax.Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        if (rule.seed_argument) |argument| {
            // One plan serves every seed value. A seed unification that
            // succeeds binds the whole seed term, so every iteration that gets
            // as far as solving the body starts from the same bound variables;
            // planning on the first of them is planning for all of them.
            //
            // Values are interned in dependency order: a cons cell's head and
            // tail must already have an identifier before the cons itself can
            // get one, so nothing a recursive occurrence in the body reads
            // (the tail bound by `unifyValueTerm`'s `.cons` case) ever has a
            // higher identifier than the seed value being tried. Walking
            // `0..value_count` in order and committing each value's answers
            // before moving to the next therefore reaches the whole closure of
            // a structurally recursive rule in one pass, where committing only
            // after the full range needs one pass per list position — the
            // rest of `expandLevel`'s rounds exist for other rules, and this
            // is safe beside them because a fact committed earlier than
            // before is a fact Datalog's monotone fixpoint would have derived
            // anyway, so the set of facts is the one it already was.
            var chosen: ?planner.Plan = null;
            defer if (chosen) |*value| value.deinit();
            const value_count = self.values.values.items.len;
            for (0..value_count) |value| {
                var initial: syntax.Binding = .{};
                defer initial.deinit(self.allocator);
                const seeded = try self.unifyValueTerm(
                    @intCast(value),
                    rule.head.terms[argument],
                    &initial,
                );
                if (seeded) {
                    if (chosen == null)
                        chosen = try self.planFor(facts, rule.head, rule.body, &initial);
                    self.matchClauses(
                        &chosen.?,
                        facts,
                        0,
                        &initial,
                        &answers,
                        null,
                    ) catch |err| switch (err) {
                        errors.Error.NumericType, errors.Error.NumericOverflow => continue,
                        else => return err,
                    };
                    for (answers.items) |*answer| {
                        const derived = try self.deriveFact(rule.head, answer);
                        _ = facts.insert(derived, true) catch |err| {
                            self.allocator.free(derived.terms);
                            return err;
                        };
                    }
                    for (answers.items) |*answer| answer.deinit(self.allocator);
                    answers.clearRetainingCapacity();
                }
            }
        } else {
            var initial: syntax.Binding = .{};
            defer initial.deinit(self.allocator);
            try self.solve(facts, rule.head, rule.body, &initial, &answers, constraint);
        }
        for (answers.items) |*answer| {
            const derived = try self.deriveFact(rule.head, answer);
            _ = facts.insert(derived, true) catch |err| {
                self.allocator.free(derived.terms);
                return err;
            };
        }
    }

    pub fn deriveFact(self: *Evaluator, head: syntax.Expr, bindings: *const syntax.Binding) !relation_store.Fact {
        const terms = try self.allocator.alloc(syntax.ValueId, head.terms.len);
        errdefer self.allocator.free(terms);
        for (head.terms, terms) |term, *id| id.* = try self.termToValue(term, bindings);
        return .{ .predicate = head.predicate, .terms = terms };
    }

    pub fn termToValue(self: *Evaluator, term: syntax.Term, bindings: ?*const syntax.Binding) !syntax.ValueId {
        return switch (term) {
            .scalar => |value| try self.values.intern(.{ .scalar = value }),
            .nil => try self.values.intern(.nil),
            .variable => |variable| if (bindings) |bound|
                bound.values.get(variable) orelse errors.Error.UnboundVariable
            else
                errors.Error.UnboundVariable,
            .cons => |pair| try self.values.intern(.{ .cons = .{
                .head = try self.termToValue(pair.head, bindings),
                .tail = try self.termToValue(pair.tail, bindings),
            } }),
        };
    }

    /// Solves a plan from step `index`, extending `bindings` and appending one
    /// answer per complete solution.
    ///
    /// The plan rather than the clause slice is what is walked, because a step
    /// carries more than its clause: the stored body position a delta
    /// restriction names, and the inner plan of a `setof`.
    pub fn matchClauses(
        self: *Evaluator,
        plan: *const planner.Plan,
        facts: *relation_store.RelationStore,
        index: usize,
        bindings: *const syntax.Binding,
        answers: *std.ArrayList(syntax.Binding),
        constraint: ?syntax.DeltaConstraint,
    ) !void {
        const clauses = plan.clauses;
        if (index == clauses.len) {
            var answer = try bindings.clone(self.allocator);
            answers.append(self.allocator, answer) catch |err| {
                answer.deinit(self.allocator);
                return err;
            };
            return;
        }
        if (clauses[index] == .aggregate) {
            const aggregate = clauses[index].aggregate;
            var inner_answers: std.ArrayList(syntax.Binding) = .empty;
            defer {
                for (inner_answers.items) |*answer| answer.deinit(self.allocator);
                inner_answers.deinit(self.allocator);
            }
            try self.matchClauses(plan.steps[index].inner.?, facts, 0, bindings, &inner_answers, null);

            var values: std.ArrayList(syntax.ValueId) = .empty;
            defer values.deinit(self.allocator);
            for (inner_answers.items) |*answer| {
                const value = try self.termToValue(aggregate.template, answer);
                var duplicate = false;
                for (values.items) |existing| {
                    if (existing == value) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) try values.append(self.allocator, value);
            }
            self.sortValues(values.items);

            var list = try self.values.intern(.nil);
            var value_index = values.items.len;
            while (value_index > 0) {
                value_index -= 1;
                list = try self.values.intern(.{ .cons = .{
                    .head = values.items[value_index],
                    .tail = list,
                } });
            }

            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unifyValueTerm(list, aggregate.output, &next))
                try self.matchClauses(plan, facts, index + 1, &next, answers, constraint);
            return;
        }
        const expression = switch (clauses[index]) {
            .aggregate => unreachable,
            .relational => |value| value,
            .builtin => |value| value,
            .negated => |value| value,
        };
        if (syntax.isBuiltin(expression)) {
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            const matched = try self.evalBuiltin(expression, &next);
            if (matched != expression.negated)
                try self.matchClauses(plan, facts, index + 1, &next, answers, constraint);
            return;
        }
        if (expression.negated) {
            for (try self.lookupCandidates(facts, expression, bindings)) |candidate| {
                var next = try bindings.clone(self.allocator);
                defer next.deinit(self.allocator);
                if (try self.unify(facts.factAt(candidate), expression, &next)) return;
            }
            try self.matchClauses(plan, facts, index + 1, bindings, answers, constraint);
            return;
        }
        for (try self.lookupCandidates(facts, expression, bindings)) |candidate| {
            if (constraint) |delta| {
                if (index == delta.clause_index and
                    (candidate < delta.delta_start or candidate >= delta.delta_end)) continue;
            }
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unify(facts.factAt(candidate), expression, &next))
                try self.matchClauses(plan, facts, index + 1, &next, answers, constraint);
        }
    }

    /// Resolves the goal's ground positions under the current bindings and
    /// asks the store for candidate facts, in insertion order, through its
    /// single lookup interface. Candidates are a superset of the matches;
    /// callers unify each candidate exactly.
    pub fn lookupCandidates(
        self: *Evaluator,
        facts: *relation_store.RelationStore,
        goal: syntax.Expr,
        bindings: *const syntax.Binding,
    ) ![]const u32 {
        const key: relation_store.PredicateKey = .{ .name = goal.predicate, .arity = goal.terms.len };
        var mask: u64 = 0;
        var bound: [64]syntax.ValueId = undefined;
        var count: usize = 0;
        for (goal.terms, 0..) |term, position| {
            if (position >= 64) break;
            const resolved = self.termToValue(term, bindings) catch |err| switch (err) {
                errors.Error.UnboundVariable => continue,
                else => return err,
            };
            mask |= @as(u64, 1) << @intCast(position);
            bound[count] = resolved;
            count += 1;
        }
        const candidates = try facts.lookup(key, mask, bound[0..count]);
        // Candidate examination dominates both maintenance and rebuild, so
        // counting candidates is the cost model's unit of work. It is a
        // deterministic, machine-independent proxy for elapsed time.
        self.cost.noteCandidates(candidates.len);
        return candidates;
    }

    pub fn unify(self: *Evaluator, fact: relation_store.Fact, goal: syntax.Expr, bindings: *syntax.Binding) !bool {
        for (fact.terms, goal.terms) |value, term| {
            if (!try self.unifyValueTerm(value, term, bindings)) return false;
        }
        return true;
    }

    fn unifyValueTerm(self: *Evaluator, value: syntax.ValueId, term: syntax.Term, bindings: *syntax.Binding) !bool {
        return switch (term) {
            .variable => |variable| if (bindings.values.get(variable)) |bound|
                bound == value
            else blk: {
                try bindings.values.put(self.allocator, variable, value);
                break :blk true;
            },
            .scalar => |expected| switch (self.values.get(value)) {
                .scalar => |actual| actual == expected,
                else => false,
            },
            .nil => self.values.get(value) == .nil,
            .cons => |pair| switch (self.values.get(value)) {
                .cons => |actual| try self.unifyValueTerm(actual.head, pair.head, bindings) and
                    try self.unifyValueTerm(actual.tail, pair.tail, bindings),
                else => false,
            },
        };
    }

    fn evalBuiltin(self: *Evaluator, expr_value: syntax.Expr, bindings: *syntax.Binding) !bool {
        if (expr_value.kind == .add or expr_value.kind == .subtract) {
            if (expr_value.terms.len != 3) return errors.Error.InvalidQuery; // ziglint-ignore: Z010
            const left_id = try self.termToValue(expr_value.terms[1], bindings);
            const right_id = try self.termToValue(expr_value.terms[2], bindings);
            const result_scalar = if (expr_value.kind == .add)
                try self.scalars.add(try self.valueScalar(left_id), try self.valueScalar(right_id))
            else
                try self.scalars.subtract(try self.valueScalar(left_id), try self.valueScalar(right_id));
            const value = try self.values.intern(.{ .scalar = result_scalar });
            return self.unifyValueTerm(value, expr_value.terms[0], bindings);
        }
        if (expr_value.terms.len != 2) return errors.Error.InvalidQuery; // ziglint-ignore: Z010
        const left = expr_value.terms[0];
        const right = expr_value.terms[1];
        const left_id = self.termToValue(left, bindings) catch |err| switch (err) {
            errors.Error.UnboundVariable => null,
            else => return err,
        };
        const right_id = self.termToValue(right, bindings) catch |err| switch (err) {
            errors.Error.UnboundVariable => null,
            else => return err,
        };

        if (expr_value.kind == .equality) {
            if (left_id == null and right_id == null) return errors.Error.UnboundVariable; // ziglint-ignore: Z010
            if (left_id == null) return self.unifyValueTerm(right_id.?, left, bindings);
            if (right_id == null) return self.unifyValueTerm(left_id.?, right, bindings);
            return self.valuesEqual(left_id.?, right_id.?);
        }
        if (left_id == null or right_id == null) return errors.Error.UnboundVariable; // ziglint-ignore: Z010
        if (expr_value.kind == .inequality) return !self.valuesEqual(left_id.?, right_id.?);

        const order = try self.scalars.compareNumeric(
            try self.valueScalar(left_id.?),
            try self.valueScalar(right_id.?),
        );
        return switch (expr_value.kind) {
            .less_than => order == .lt,
            .less_or_equal => order != .gt,
            .greater_than => order == .gt,
            .greater_or_equal => order != .lt,
            else => errors.Error.UnknownOperator,
        };
    }

    fn valueScalar(self: *const Evaluator, value: syntax.ValueId) !scalar.Id {
        return switch (self.values.get(value)) {
            .scalar => |scalar_id| scalar_id,
            else => errors.Error.NumericType,
        };
    }

    fn valuesEqual(self: *const Evaluator, left: syntax.ValueId, right: syntax.ValueId) bool {
        const left_value = self.values.get(left);
        const right_value = self.values.get(right);
        return switch (left_value) {
            .scalar => |left_scalar| switch (right_value) {
                .scalar => |right_scalar| left_scalar == right_scalar,
                else => false,
            },
            .nil => right_value == .nil,
            .cons => |left_cons| switch (right_value) {
                .cons => |right_cons| self.valuesEqual(left_cons.head, right_cons.head) and
                    self.valuesEqual(left_cons.tail, right_cons.tail),
                else => false,
            },
        };
    }

    pub fn computeStrata(self: *Evaluator) !std.array_hash_map.Auto(relation_store.PredicateKey, usize) {
        var levels: std.array_hash_map.Auto(relation_store.PredicateKey, usize) = .empty;
        errdefer levels.deinit(self.allocator);
        for (self.rules.items) |rule| {
            try levels.put(self.allocator, syntax.predicateKey(rule.head), 0);
            for (rule.body) |clause| try self.collectDependencyPredicates(clause, &levels);
        }
        const predicate_count = levels.count();
        for (0..predicate_count + 1) |iteration| {
            var changed = false;
            for (self.rules.items) |rule| {
                var required: usize = 0;
                for (rule.body) |clause|
                    required = @max(required, self.clauseRequiredStratum(clause, &levels, false));
                const head = syntax.predicateKey(rule.head);
                const current = levels.get(head) orelse 0;
                if (required > current) {
                    try levels.put(self.allocator, head, required);
                    changed = true;
                }
            }
            if (!changed) return levels;
            if (iteration == predicate_count) return errors.Error.NotStratified; // ziglint-ignore: Z010
        }
        return levels;
    }

    fn collectDependencyPredicates(
        self: *Evaluator,
        clause: syntax.Clause,
        levels: *std.array_hash_map.Auto(relation_store.PredicateKey, usize),
    ) !void {
        switch (clause) {
            .relational => |expression| try levels.put(self.allocator, syntax.predicateKey(expression), 0),
            .negated => |expression| if (!syntax.isBuiltin(expression))
                try levels.put(self.allocator, syntax.predicateKey(expression), 0),
            .builtin => {},
            .aggregate => |aggregate| for (aggregate.body) |body_clause|
                try self.collectDependencyPredicates(body_clause, levels),
        }
    }

    fn clauseRequiredStratum(
        self: *const Evaluator,
        clause: syntax.Clause,
        levels: *const std.array_hash_map.Auto(relation_store.PredicateKey, usize),
        aggregate_context: bool,
    ) usize {
        return switch (clause) {
            .relational => |expression| (levels.get(syntax.predicateKey(expression)) orelse 0) +
                @intFromBool(aggregate_context),
            .negated => |expression| if (syntax.isBuiltin(expression))
                0
            else
                (levels.get(syntax.predicateKey(expression)) orelse 0) + 1,
            .builtin => 0,
            .aggregate => |aggregate| blk: {
                var required: usize = 0;
                for (aggregate.body) |body_clause|
                    required = @max(required, self.clauseRequiredStratum(body_clause, levels, true));
                break :blk required;
            },
        };
    }

    /// Numbers by value, atoms by spelling, nil, then cons cells recursively.
    fn compareValues(self: *const Evaluator, left: syntax.ValueId, right: syntax.ValueId) std.math.Order {
        const a = self.values.get(left);
        const b = self.values.get(right);
        const a_rank: u2 = switch (a) {
            .scalar => 0,
            .nil => 1,
            .cons => 2,
        };
        const b_rank: u2 = switch (b) {
            .scalar => 0,
            .nil => 1,
            .cons => 2,
        };
        if (a_rank != b_rank) return std.math.order(a_rank, b_rank);
        return switch (a) {
            .scalar => |a_scalar| switch (b) {
                .scalar => |b_scalar| self.scalars.compare(a_scalar, b_scalar),
                else => unreachable,
            },
            .nil => .eq,
            .cons => |a_pair| switch (b) {
                .cons => |b_pair| blk: {
                    const head_order = self.compareValues(a_pair.head, b_pair.head);
                    break :blk if (head_order != .eq) head_order else self.compareValues(a_pair.tail, b_pair.tail);
                },
                else => unreachable,
            },
        };
    }

    fn sortValues(self: *const Evaluator, values: []syntax.ValueId) void {
        if (values.len < 2) return;
        for (values[1..], 1..) |value, index| {
            var insertion = index;
            while (insertion > 0 and self.compareValues(value, values[insertion - 1]) == .lt) {
                values[insertion] = values[insertion - 1];
                insertion -= 1;
            }
            values[insertion] = value;
        }
    }
};

const testing = std.testing;

/// What the table answered before it had an index: the scan `intern` used to
/// make over the ordered values.
fn scanFor(table: *const ValueTable, value: Value) ?syntax.ValueId {
    for (table.values.items, 0..) |existing, index| {
        if (std.meta.eql(existing, value)) return @intCast(index);
    }
    return null;
}

test "interning a value through the index agrees with a linear scan over the same table" {
    var scalars: scalar.Store = .init(testing.allocator);
    defer scalars.deinit();
    var table: ValueTable = .init(testing.allocator);
    defer table.deinit();

    // Scalars, `nil`, and lists nested deeply enough that the cons cells of
    // one list are the tails of another.
    var values: std.ArrayList(Value) = .empty;
    defer values.deinit(testing.allocator);
    try values.append(testing.allocator, .nil);
    for (0..64) |number| {
        try values.append(testing.allocator, .{
            .scalar = try scalars.internInteger(@intCast(number)),
        });
    }
    var tail = try table.intern(.nil);
    for (0..64) |number| {
        const head = try table.intern(.{
            .scalar = try scalars.internInteger(@intCast(number)),
        });
        const cell: Value = .{ .cons = .{ .head = head, .tail = tail } };
        try values.append(testing.allocator, cell);
        tail = try table.intern(cell);
    }

    for (values.items) |value| {
        const id = try table.intern(value);
        try testing.expectEqual(id, scanFor(&table, value).?);
    }
    // Everything above was already interned, so the table did not grow.
    try testing.expectEqual(@as(usize, 129), table.values.items.len);
    try testing.expectEqual(table.values.items.len, table.index.filled);

    // A value the table has never held is appended at the end, once.
    const fresh: Value = .{ .cons = .{ .head = tail, .tail = tail } };
    try testing.expectEqual(@as(?syntax.ValueId, null), scanFor(&table, fresh));
    try testing.expectEqual(@as(syntax.ValueId, 129), try table.intern(fresh));
    try testing.expectEqual(@as(syntax.ValueId, 129), try table.intern(fresh));
    try testing.expectEqual(@as(usize, 130), table.values.items.len);
}

test "a cloned value table interns to the same identifiers as the table it came from" {
    var table: ValueTable = .init(testing.allocator);
    defer table.deinit();
    var tail = try table.intern(.nil);
    for (0..200) |number| {
        tail = try table.intern(.{ .cons = .{
            .head = @intCast(number % 7),
            .tail = tail,
        } });
    }

    var copy = try table.clone();
    defer copy.deinit();
    for (table.values.items) |value| {
        try testing.expectEqual(try table.intern(value), try copy.intern(value));
    }
    try testing.expectEqual(table.values.items.len, copy.values.items.len);

    const fresh: Value = .{ .cons = .{ .head = tail, .tail = tail } };
    try testing.expectEqual(
        @as(syntax.ValueId, @intCast(table.values.items.len)),
        try copy.intern(fresh),
    );
}
