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
const scalar = @import("scalar.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");
const cost_model = @import("cost_model.zig");

const Error = @import("root.zig").Error;
const root_mod = @import("root.zig");
const Jatalog = root_mod.Jatalog;
const expectSemiNaiveMatchesNaive = @import("test_support.zig").expectSemiNaiveMatchesNaive;
const expectAnswerCount = @import("test_support.zig").expectAnswerCount;
const expectBindingValue = @import("test_support.zig").expectBindingValue;
const CostModel = cost_model.CostModel;
const Fact = relation_store.Fact;
const PredicateKey = relation_store.PredicateKey;
const RelationStore = relation_store.RelationStore;
const ValueId = syntax.ValueId;
const Term = syntax.Term;
const Expr = syntax.Expr;
const Clause = syntax.Clause;
const Rule = syntax.Rule;
const Binding = syntax.Binding;
const DeltaConstraint = syntax.DeltaConstraint;
const predicateKey = syntax.predicateKey;
const isBuiltin = syntax.isBuiltin;
const cloneRule = syntax.cloneRule;
const freeRule = syntax.freeRule;
const noteBodyDependencies = syntax.noteBodyDependencies;

pub const Value = union(enum) {
    scalar: scalar.Id,
    nil,
    cons: struct { head: ValueId, tail: ValueId },
};

pub const ValueTable = struct {
    allocator: std.mem.Allocator,
    values: std.ArrayList(Value) = .empty,

    pub fn init(allocator: std.mem.Allocator) ValueTable {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ValueTable) void {
        self.values.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const ValueTable) !ValueTable {
        return .{
            .allocator = self.allocator,
            .values = try self.values.clone(self.allocator),
        };
    }

    pub fn intern(self: *ValueTable, value: Value) !ValueId {
        for (self.values.items, 0..) |existing, index| {
            if (std.meta.eql(existing, value)) return @intCast(index);
        }
        try self.values.append(self.allocator, value);
        return @intCast(self.values.items.len - 1);
    }

    pub fn get(self: *const ValueTable, id: ValueId) Value {
        return self.values.items[@intCast(id)];
    }

    pub fn internFrom(self: *ValueTable, source: *const ValueTable, id: ValueId) !ValueId {
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
    strata: std.array_hash_map.Auto(PredicateKey, usize),
    first_dependent: std.array_hash_map.Auto(PredicateKey, usize),
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
    levels: *const std.array_hash_map.Auto(PredicateKey, usize),
    rule: Rule,
    level: usize,
) bool {
    const rule_level = levels.get(predicateKey(rule.head)) orelse 0;
    if (rule_level == level) return true;
    return rule.seed_argument != null and rule_level < level;
}

/// The stratum a rule's head belongs to, ignoring the cross-stratum reach of
/// seeded rules that `ruleActiveAt` grants.
pub fn ruleStratum(
    levels: *const std.array_hash_map.Auto(PredicateKey, usize),
    rule: Rule,
) usize {
    return levels.get(predicateKey(rule.head)) orelse 0;
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
    rules: std.ArrayList(Rule) = .empty,
    next_rule_id: u32 = 0,
    analysis: ?Analysis = null,
    /// Counts stratum expansions; tests use it to prove that repeated
    /// queries perform no rule expansion after the first materialization.
    expansions: usize = 0,
    /// Chooses between maintaining and recomputing, and learns both costs.
    cost: CostModel = .{},

    pub fn init(allocator: std.mem.Allocator) Evaluator {
        return .{
            .allocator = allocator,
            .scalars = .init(allocator),
            .values = .init(allocator),
        };
    }

    pub fn deinit(self: *Evaluator) void {
        if (self.analysis) |*analysis| analysis.deinit(self.allocator);
        for (self.rules.items) |rule| freeRule(self.allocator, rule);
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
        };
        errdefer result.scalars.deinit();
        result.values = try self.values.clone();
        errdefer result.values.deinit();
        errdefer {
            for (result.rules.items) |rule| freeRule(self.allocator, rule);
            result.rules.deinit(self.allocator);
        }
        for (self.rules.items) |rule| {
            const copy = try cloneRule(self.allocator, rule);
            result.rules.append(self.allocator, copy) catch |err| {
                freeRule(self.allocator, copy);
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
            var first_dependent: std.array_hash_map.Auto(PredicateKey, usize) = .empty;
            errdefer first_dependent.deinit(self.allocator);
            var has_seed_rules = false;
            for (self.rules.items) |rule| {
                if (rule.seed_argument != null) has_seed_rules = true;
                const head_level = strata.get(predicateKey(rule.head)) orelse 0;
                try noteBodyDependencies(self.allocator, rule.body, head_level, &first_dependent);
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

    pub fn expandFrom(self: *Evaluator, facts: *RelationStore, first_level: usize) !void {
        const analysis = try self.ensureAnalysis();
        if (first_level > analysis.max_level) return;
        for (first_level..analysis.max_level + 1) |level|
            try self.expandLevel(facts, &analysis.strata, level);
    }

    /// Reference naive fixpoint kept as the semantic oracle for the
    /// semi-naive engine; differential tests compare both closures.
    pub fn expandNaive(self: *Evaluator, facts: *RelationStore) !void {
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
        facts: *RelationStore,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        level: usize,
    ) !void {
        self.expansions += 1;
        const ActiveRule = struct {
            rule: Rule,
            growing_occurrences: []usize,
        };
        var active: std.ArrayList(ActiveRule) = .empty;
        defer {
            for (active.items) |entry| self.allocator.free(entry.growing_occurrences);
            active.deinit(self.allocator);
        }
        var growing: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
        defer growing.deinit(self.allocator);
        for (self.rules.items) |rule| {
            if (!ruleActiveAt(levels, rule, level)) continue;
            if (rule.seed_argument != null)
                try growing.put(self.allocator, predicateKey(rule.head), {});
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
                    const body_level = levels.get(predicateKey(expression)) orelse 0;
                    if (body_level == level or growing.contains(predicateKey(expression)))
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

    pub fn applyRule(
        self: *Evaluator,
        facts: *RelationStore,
        rule: Rule,
        constraint: ?DeltaConstraint,
    ) !void {
        var answers: std.ArrayList(Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        if (rule.seed_argument) |argument| {
            const value_count = self.values.values.items.len;
            for (0..value_count) |value| {
                var initial: Binding = .{};
                defer initial.deinit(self.allocator);
                const seeded = try self.unifyValueTerm(
                    @intCast(value),
                    rule.head.terms[argument],
                    &initial,
                );
                if (seeded) {
                    self.matchClauses(
                        rule.body,
                        facts,
                        0,
                        &initial,
                        &answers,
                        null,
                    ) catch |err| switch (err) {
                        Error.NumericType, Error.NumericOverflow => continue,
                        else => return err,
                    };
                }
            }
        } else {
            var initial: Binding = .{};
            defer initial.deinit(self.allocator);
            try self.matchClauses(rule.body, facts, 0, &initial, &answers, constraint);
        }
        for (answers.items) |*answer| {
            const derived = try self.deriveFact(rule.head, answer);
            _ = facts.insert(derived, true) catch |err| {
                self.allocator.free(derived.terms);
                return err;
            };
        }
    }

    pub fn deriveFact(self: *Evaluator, head: Expr, bindings: *const Binding) !Fact {
        const terms = try self.allocator.alloc(ValueId, head.terms.len);
        errdefer self.allocator.free(terms);
        for (head.terms, terms) |term, *id| id.* = try self.termToValue(term, bindings);
        return .{ .predicate = head.predicate, .terms = terms };
    }

    pub fn termToValue(self: *Evaluator, term: Term, bindings: ?*const Binding) !ValueId {
        return switch (term) {
            .scalar => |value| try self.values.intern(.{ .scalar = value }),
            .nil => try self.values.intern(.nil),
            .variable => |variable| if (bindings) |bound|
                bound.values.get(variable) orelse Error.UnboundVariable
            else
                Error.UnboundVariable,
            .cons => |pair| try self.values.intern(.{ .cons = .{
                .head = try self.termToValue(pair.head, bindings),
                .tail = try self.termToValue(pair.tail, bindings),
            } }),
        };
    }

    pub fn matchClauses(
        self: *Evaluator,
        clauses: []const Clause,
        facts: *RelationStore,
        index: usize,
        bindings: *const Binding,
        answers: *std.ArrayList(Binding),
        constraint: ?DeltaConstraint,
    ) !void {
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
            var inner_answers: std.ArrayList(Binding) = .empty;
            defer {
                for (inner_answers.items) |*answer| answer.deinit(self.allocator);
                inner_answers.deinit(self.allocator);
            }
            try self.matchClauses(aggregate.body, facts, 0, bindings, &inner_answers, null);

            var values: std.ArrayList(ValueId) = .empty;
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
                try self.matchClauses(clauses, facts, index + 1, &next, answers, constraint);
            return;
        }
        const expression = switch (clauses[index]) {
            .aggregate => unreachable,
            .relational => |value| value,
            .builtin => |value| value,
            .negated => |value| value,
        };
        if (isBuiltin(expression)) {
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            const matched = try self.evalBuiltin(expression, &next);
            if (matched != expression.negated)
                try self.matchClauses(clauses, facts, index + 1, &next, answers, constraint);
            return;
        }
        if (expression.negated) {
            for (try self.lookupCandidates(facts, expression, bindings)) |candidate| {
                var next = try bindings.clone(self.allocator);
                defer next.deinit(self.allocator);
                if (try self.unify(facts.factAt(candidate), expression, &next)) return;
            }
            try self.matchClauses(clauses, facts, index + 1, bindings, answers, constraint);
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
                try self.matchClauses(clauses, facts, index + 1, &next, answers, constraint);
        }
    }

    /// Resolves the goal's ground positions under the current bindings and
    /// asks the store for candidate facts, in insertion order, through its
    /// single lookup interface. Candidates are a superset of the matches;
    /// callers unify each candidate exactly.
    pub fn lookupCandidates(
        self: *Evaluator,
        facts: *RelationStore,
        goal: Expr,
        bindings: *const Binding,
    ) ![]const u32 {
        const key: PredicateKey = .{ .name = goal.predicate, .arity = goal.terms.len };
        var mask: u64 = 0;
        var bound: [64]ValueId = undefined;
        var count: usize = 0;
        for (goal.terms, 0..) |term, position| {
            if (position >= 64) break;
            const resolved = self.termToValue(term, bindings) catch |err| switch (err) {
                Error.UnboundVariable => continue,
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

    pub fn unify(self: *Evaluator, fact: Fact, goal: Expr, bindings: *Binding) !bool {
        for (fact.terms, goal.terms) |value, term| {
            if (!try self.unifyValueTerm(value, term, bindings)) return false;
        }
        return true;
    }

    fn unifyValueTerm(self: *Evaluator, value: ValueId, term: Term, bindings: *Binding) !bool {
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

    fn evalBuiltin(self: *Evaluator, expr_value: Expr, bindings: *Binding) !bool {
        if (expr_value.kind == .add or expr_value.kind == .subtract) {
            if (expr_value.terms.len != 3) return Error.InvalidQuery; // ziglint-ignore: Z010
            const left_id = try self.termToValue(expr_value.terms[1], bindings);
            const right_id = try self.termToValue(expr_value.terms[2], bindings);
            const result_scalar = if (expr_value.kind == .add)
                try self.scalars.add(try self.valueScalar(left_id), try self.valueScalar(right_id))
            else
                try self.scalars.subtract(try self.valueScalar(left_id), try self.valueScalar(right_id));
            const value = try self.values.intern(.{ .scalar = result_scalar });
            return self.unifyValueTerm(value, expr_value.terms[0], bindings);
        }
        if (expr_value.terms.len != 2) return Error.InvalidQuery; // ziglint-ignore: Z010
        const left = expr_value.terms[0];
        const right = expr_value.terms[1];
        const left_id = self.termToValue(left, bindings) catch |err| switch (err) {
            Error.UnboundVariable => null,
            else => return err,
        };
        const right_id = self.termToValue(right, bindings) catch |err| switch (err) {
            Error.UnboundVariable => null,
            else => return err,
        };

        if (expr_value.kind == .equality) {
            if (left_id == null and right_id == null) return Error.UnboundVariable; // ziglint-ignore: Z010
            if (left_id == null) return self.unifyValueTerm(right_id.?, left, bindings);
            if (right_id == null) return self.unifyValueTerm(left_id.?, right, bindings);
            return self.valuesEqual(left_id.?, right_id.?);
        }
        if (left_id == null or right_id == null) return Error.UnboundVariable; // ziglint-ignore: Z010
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
            else => Error.UnknownOperator,
        };
    }

    fn valueScalar(self: *const Evaluator, value: ValueId) !scalar.Id {
        return switch (self.values.get(value)) {
            .scalar => |scalar_id| scalar_id,
            else => Error.NumericType,
        };
    }

    fn valuesEqual(self: *const Evaluator, left: ValueId, right: ValueId) bool {
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

    pub fn computeStrata(self: *Evaluator) !std.array_hash_map.Auto(PredicateKey, usize) {
        var levels: std.array_hash_map.Auto(PredicateKey, usize) = .empty;
        errdefer levels.deinit(self.allocator);
        for (self.rules.items) |rule| {
            try levels.put(self.allocator, predicateKey(rule.head), 0);
            for (rule.body) |clause| try self.collectDependencyPredicates(clause, &levels);
        }
        const predicate_count = levels.count();
        for (0..predicate_count + 1) |iteration| {
            var changed = false;
            for (self.rules.items) |rule| {
                var required: usize = 0;
                for (rule.body) |clause|
                    required = @max(required, self.clauseRequiredStratum(clause, &levels, false));
                const head = predicateKey(rule.head);
                const current = levels.get(head) orelse 0;
                if (required > current) {
                    try levels.put(self.allocator, head, required);
                    changed = true;
                }
            }
            if (!changed) return levels;
            if (iteration == predicate_count) return Error.NotStratified; // ziglint-ignore: Z010
        }
        return levels;
    }

    fn collectDependencyPredicates(
        self: *Evaluator,
        clause: Clause,
        levels: *std.array_hash_map.Auto(PredicateKey, usize),
    ) !void {
        switch (clause) {
            .relational => |expression| try levels.put(self.allocator, predicateKey(expression), 0),
            .negated => |expression| if (!isBuiltin(expression))
                try levels.put(self.allocator, predicateKey(expression), 0),
            .builtin => {},
            .aggregate => |aggregate| for (aggregate.body) |body_clause|
                try self.collectDependencyPredicates(body_clause, levels),
        }
    }

    fn clauseRequiredStratum(
        self: *const Evaluator,
        clause: Clause,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        aggregate_context: bool,
    ) usize {
        return switch (clause) {
            .relational => |expression| (levels.get(predicateKey(expression)) orelse 0) +
                @intFromBool(aggregate_context),
            .negated => |expression| if (isBuiltin(expression))
                0
            else
                (levels.get(predicateKey(expression)) orelse 0) + 1,
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
    fn compareValues(self: *const Evaluator, left: ValueId, right: ValueId) std.math.Order {
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

    fn sortValues(self: *const Evaluator, values: []ValueId) void {
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

test "semi-naive and naive closures agree across rule classes" {
    // Non-recursive joins.
    var joins: Jatalog = .init(std.testing.allocator);
    defer joins.deinit();
    var joins_setup = try joins.execute(
        \\parent(a, b). parent(b, c). parent(c, d).
        \\grand(X, Z) :- parent(X, Y), parent(Y, Z).
    );
    joins_setup.deinit();
    try expectSemiNaiveMatchesNaive(&joins);

    // Direct recursion.
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    var direct_setup = try direct.execute(
        \\edge(a, b). edge(b, c). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    direct_setup.deinit();
    try expectSemiNaiveMatchesNaive(&direct);

    // Mutual recursion across two predicates in one stratum.
    var mutual: Jatalog = .init(std.testing.allocator);
    defer mutual.deinit();
    var mutual_setup = try mutual.execute(
        \\start(n0). step(n0, n1). step(n1, n2). step(n2, n3). step(n3, n4).
        \\even(X) :- start(X).
        \\even(X) :- odd(Y), step(Y, X).
        \\odd(X) :- even(Y), step(Y, X).
    );
    mutual_setup.deinit();
    try expectSemiNaiveMatchesNaive(&mutual);

    // Seeded structural recursion feeding a same-stratum consumer.
    var structural: Jatalog = .init(std.testing.allocator);
    defer structural.deinit();
    var structural_setup = try structural.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    structural_setup.deinit();
    try expectSemiNaiveMatchesNaive(&structural);

    // Stratified negation above a recursive stratum.
    var negated: Jatalog = .init(std.testing.allocator);
    defer negated.deinit();
    var negated_setup = try negated.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\reachable(X) :- edge(a, X).
        \\reachable(X) :- reachable(Y), edge(Y, X).
        \\isolated(X) :- node(X), not reachable(X).
    );
    negated_setup.deinit();
    try expectSemiNaiveMatchesNaive(&negated);

    // Aggregation over a recursive relation.
    var aggregated: Jatalog = .init(std.testing.allocator);
    defer aggregated.deinit();
    var aggregated_setup = try aggregated.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    );
    aggregated_setup.deinit();
    try expectSemiNaiveMatchesNaive(&aggregated);
}

test "multiple recursive body occurrences miss no derivations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(n1, n2). edge(n2, n3). edge(n3, n4). edge(n4, n5).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- path(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectSemiNaiveMatchesNaive(&db);

    // The doubling rule needs delta joins on both occurrences: n1 to n5
    // only exists by combining two derived paths.
    try expectAnswerCount(&db, "path(n1, n5)?", 1);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
}

test "duplicate derivations create no duplicate facts or endless rounds" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // A diamond plus a cycle derives many facts through multiple proofs.
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectSemiNaiveMatchesNaive(&db);
    // Every node reaches every node exactly once in the answer set.
    try expectAnswerCount(&db, "path(X, Y)?", 16);
    try expectAnswerCount(&db, "path(a, d)?", 1);
}

test "indexed lookups match every structural binding pattern deterministically" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(a, c).
        \\holds([1, 2], a). holds([1, [2, 3]], b). holds(cons(1, 2), c). holds([], d).
        \\p(a). p(a, b).
    );
    setup.deinit();

    // Bound-position patterns over atoms.
    try expectAnswerCount(&db, "edge(a, X)?", 2);
    try expectAnswerCount(&db, "edge(X, Y)?", 3);
    try expectAnswerCount(&db, "edge(a, b)?", 1);
    try expectAnswerCount(&db, "edge(c, X)?", 0);

    // Answers arrive in fact insertion order.
    var ordered = try db.execute("edge(X, c)?");
    defer ordered.deinit();
    try std.testing.expectEqual(@as(usize, 2), ordered.query.answers.items.len);
    try std.testing.expectEqualStrings("b", try ordered.query.answers.items[0].getAtom("X"));
    try std.testing.expectEqualStrings("a", try ordered.query.answers.items[1].getAtom("X"));

    // Bound structural values: proper, nested, improper, and empty lists.
    var proper = try db.execute("holds([1, 2], X)?");
    defer proper.deinit();
    try std.testing.expectEqualStrings("a", try proper.query.answers.items[0].getAtom("X"));
    var nested = try db.execute("holds([1, [2, 3]], X)?");
    defer nested.deinit();
    try std.testing.expectEqualStrings("b", try nested.query.answers.items[0].getAtom("X"));
    var improper = try db.execute("holds(cons(1, 2), X)?");
    defer improper.deinit();
    try std.testing.expectEqualStrings("c", try improper.query.answers.items[0].getAtom("X"));
    var empty = try db.execute("holds([], X)?");
    defer empty.deinit();
    try std.testing.expectEqualStrings("d", try empty.query.answers.items[0].getAtom("X"));

    // A structural value bound through the second position.
    var reverse = try db.execute("holds(X, c)?");
    defer reverse.deinit();
    try expectBindingValue(&reverse.query.answers.items[0], "X", "cons(1, 2)");

    // A partially ground structure is unbound for indexing and still unifies.
    try expectAnswerCount(&db, "holds([1, T], X)?", 2);

    // One predicate name at two arities never shares matches.
    try expectAnswerCount(&db, "p(X)?", 1);
    try expectAnswerCount(&db, "p(X, Y)?", 1);

    // Retraction through the same lookup interface removes exactly one fact.
    var retract = try db.execute("edge(a, X)~");
    defer retract.deinit();
    try expectAnswerCount(&db, "edge(X, Y)?", 1);
    try expectAnswerCount(&db, "edge(b, c)?", 1);
}

test "stratification distinguishes predicate arities" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\p(a, b). seed(k).
        \\p(S) :- seed(k), setof([X, Y], p(X, Y), S).
        \\p(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&result.query.answers.items[0], "S", "[[a, b]]");
}
