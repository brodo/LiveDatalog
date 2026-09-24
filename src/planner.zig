//! The order a body is solved in, and the index each goal is solved through.
//!
//! Clause order is decided twice, for two different reasons. Admission decides
//! it once and for all in `validation`, where it is part of what makes a rule
//! legal: a stored body is already an order in which every consumer is reached
//! with its bindings made. This module decides it again at evaluation time,
//! where it is purely a cost question — the stored order is a witness that a
//! safe order exists, and the planner looks for a cheaper one among the safe
//! orders of the same clauses.
//!
//! Safety comes first and is never traded away. A clause is *ready* when the
//! variables it consumes are bound, by exactly the rule `validation` admits it
//! under, so any order this module produces is one admission would have
//! accepted. Readiness only grows as clauses are placed, so a greedy walk that
//! always places some ready clause can never paint itself into a corner: if it
//! runs out of ready clauses, no order of the remainder was safe either, and
//! the planner falls back to the order it was handed.
//!
//! Among ready clauses it prefers the one expected to examine the fewest
//! candidate facts. The estimate comes from the store's own statistics — a
//! relation's size divided by the number of groups an index on the bound
//! positions splits it into — so it describes the index the lookup will
//! actually use rather than a guess about the data.
//!
//! Nothing here evaluates anything. A `Plan` is a reordering of borrowed
//! clauses plus what the planner believed about each one, which is what lets
//! `explain` report a plan without running it.

const std = @import("std");
const relation_store = @import("relation_store.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");

/// How a body's clause order is chosen.
pub const PlanPolicy = enum {
    /// Reorder safe clauses by estimated candidate count.
    cost_based,
    /// Keep the order the body was handed in, which is the order admission
    /// stored. Retained so a caller — a differential test above all — can run
    /// the same program both ways and compare the answers.
    source_order,
};

/// The kind of work one step does, which is what decides how it is costed and
/// how `explain` renders it.
pub const StepKind = enum {
    /// A positive relational goal: the only step that multiplies bindings.
    join,
    /// A negated relational goal: a lookup that can only remove bindings.
    anti_join,
    /// A comparison, equality, or arithmetic goal: no lookup at all.
    filter,
    /// A `setof` occurrence, whose inner body is planned in turn.
    aggregate,
};

/// One placed clause, and what the planner believed about it when it chose
/// the position. Estimates are recorded rather than recomputed so `explain`
/// reports the numbers the decision was actually made on.
pub const Step = struct {
    /// The clause's index in the body handed to `plan`. Callers that address
    /// a body occurrence by its stored position — semi-naive delta rounds do —
    /// translate through this.
    origin: usize,
    kind: StepKind,
    /// The goal's predicate, or null for a `setof` occurrence, which names no
    /// relation of its own.
    predicate: ?syntax.Id,
    arity: usize,
    /// Argument positions this step's goal has bound when it runs.
    mask: u64,
    /// Candidate facts the lookup is expected to examine.
    estimate: usize,
    /// The plan for a `setof` occurrence's inner body.
    inner: ?*Plan = null,
};

/// A body in the order it will be solved.
///
/// The clauses are borrowed from the rule or query they were planned from,
/// with one exception: an aggregate clause is rebuilt around its inner plan's
/// clause slice, so the plan owns that. Everything a plan owns is released by
/// `deinit`; nothing it borrows is.
pub const Plan = struct {
    allocator: std.mem.Allocator,
    clauses: []syntax.Clause,
    steps: []Step,

    pub fn deinit(self: *Plan) void {
        for (self.steps) |step| if (step.inner) |inner| {
            inner.deinit();
            self.allocator.destroy(inner);
        };
        self.allocator.free(self.clauses);
        self.allocator.free(self.steps);
        self.* = undefined;
    }

    /// Where the clause stored at `origin` ended up, or null when the body
    /// handed in was shorter than that.
    pub fn positionOf(self: *const Plan, origin: usize) ?usize {
        for (self.steps, 0..) |step, position| if (step.origin == origin) return position;
        return null;
    }

    /// Re-addresses a delta restriction from the stored body occurrence it
    /// names to the position this plan put that occurrence in.
    pub fn constrain(self: *const Plan, constraint: ?syntax.DeltaConstraint) ?syntax.DeltaConstraint {
        const delta = constraint orelse return null;
        return .{
            .clause_index = self.positionOf(delta.clause_index) orelse delta.clause_index,
            .delta_start = delta.delta_start,
            .delta_end = delta.delta_end,
        };
    }

    /// Renders the chosen order: one line per step, giving the goal, the index
    /// it is solved through, and the candidates the planner expected it to
    /// examine. A `setof` occurrence is followed by its inner plan, indented.
    pub fn write(
        self: *const Plan,
        writer: *std.Io.Writer,
        strings: *const string_table.StringTable,
        depth: usize,
    ) std.Io.Writer.Error!void {
        for (self.steps) |step| {
            for (0..depth) |_| try writer.writeAll("  ");
            switch (step.kind) {
                .aggregate => try writer.writeAll("setof"),
                else => try writer.print("{s}/{d}", .{ strings.resolve(step.predicate.?), step.arity }),
            }
            switch (step.kind) {
                .filter => try writer.writeAll(" filter"),
                .aggregate => try writer.writeAll(" aggregate"),
                .join, .anti_join => {
                    try writer.writeAll(if (step.kind == .anti_join) " anti-join " else " join ");
                    if (step.mask == 0) try writer.writeAll("scan") else try writeMask(writer, step.mask);
                    try writer.print(" ~{d}", .{step.estimate});
                },
            }
            try writer.writeByte('\n');
            if (step.inner) |inner| try inner.write(writer, strings, depth + 1);
        }
    }

    /// Renders the plan into a caller-owned string.
    pub fn explainAlloc(
        self: *const Plan,
        allocator: std.mem.Allocator,
        strings: *const string_table.StringTable,
    ) ![]u8 {
        var text: std.Io.Writer.Allocating = .init(allocator);
        defer text.deinit();
        self.write(&text.writer, strings, 0) catch return error.OutOfMemory;
        return text.toOwnedSlice();
    }
};

fn writeMask(writer: *std.Io.Writer, mask: u64) std.Io.Writer.Error!void {
    try writer.writeAll("index {");
    var written = false;
    for (0..64) |position| {
        if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
        if (written) try writer.writeAll(", ");
        try writer.print("{d}", .{position});
        written = true;
    }
    try writer.writeByte('}');
}

/// Plans `clauses` for solving against `facts` with `pre_bound` already bound.
///
/// `pre_bound` is what the caller's initial binding fixes: the seed argument's
/// variables for a seeded rule, the head variables for a rederivation probe,
/// nothing for a query. The variables a clause binds are tracked from there,
/// which is what makes the estimated masks the masks evaluation will use.
///
/// `head` is the rule's head when there is one. It is not a goal to place; it
/// contributes to the surrounding-variable set an aggregate's correlation is
/// measured against, which is how `validation` computes it, so that a plan
/// cannot decorrelate a `setof` that admission required to be correlated.
pub fn plan(
    allocator: std.mem.Allocator,
    facts: *relation_store.RelationStore,
    head: ?syntax.Expr,
    clauses: []const syntax.Clause,
    pre_bound: []const syntax.Id,
    policy: PlanPolicy,
) !Plan {
    var bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer bound.deinit(allocator);
    for (pre_bound) |variable| try bound.put(allocator, variable, {});

    // The variables an aggregate must have bound before it runs are the ones
    // it shares with the surrounding body, which is the same set `validation`
    // computes to admit the rule.
    var surface: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer surface.deinit(allocator);
    if (head) |expression| try syntax.collectExprVariables(allocator, expression, &surface);
    for (clauses) |clause| try syntax.collectClauseSurfaceVariables(allocator, clause, &surface);

    return planBound(allocator, facts, clauses, &bound, &surface, policy);
}

fn planBound(
    allocator: std.mem.Allocator,
    facts: *relation_store.RelationStore,
    clauses: []const syntax.Clause,
    bound: *std.AutoHashMapUnmanaged(syntax.Id, void),
    surface: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    policy: PlanPolicy,
) std.mem.Allocator.Error!Plan {
    var result: Plan = .{
        .allocator = allocator,
        .clauses = try allocator.alloc(syntax.Clause, clauses.len),
        .steps = &.{},
    };
    errdefer allocator.free(result.clauses);
    result.steps = try allocator.alloc(Step, clauses.len);
    var placed: usize = 0;
    errdefer {
        for (result.steps[0..placed]) |step| if (step.inner) |inner| {
            inner.deinit();
            allocator.destroy(inner);
        };
        allocator.free(result.steps);
    }

    var taken = try allocator.alloc(bool, clauses.len);
    defer allocator.free(taken);
    @memset(taken, false);

    while (placed < clauses.len) {
        const origin = try chooseNext(allocator, facts, clauses, taken, bound, surface, policy);
        taken[origin] = true;
        result.steps[placed] = try describe(allocator, facts, clauses[origin], origin, bound, policy);
        result.clauses[placed] = if (result.steps[placed].inner) |inner| .{ .aggregate = .{
            .template = clauses[origin].aggregate.template,
            .body = inner.clauses,
            .output = clauses[origin].aggregate.output,
        } } else clauses[origin];
        placed += 1;
        try bindClause(allocator, clauses[origin], bound);
    }
    return result;
}

/// The next clause to place: the cheapest ready one, or — when nothing is
/// ready, which means no safe order of the remainder exists — the first one
/// left, so that a plan is always produced and evaluation reports the same
/// unbound-variable error it would have reported without a planner.
fn chooseNext(
    allocator: std.mem.Allocator,
    facts: *relation_store.RelationStore,
    clauses: []const syntax.Clause,
    taken: []const bool,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    surface: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    policy: PlanPolicy,
) !usize {
    var first_remaining: ?usize = null;
    var best: ?usize = null;
    var best_cost: usize = 0;
    for (clauses, 0..) |clause, index| {
        if (taken[index]) continue;
        if (first_remaining == null) first_remaining = index;
        if (!clauseReady(clause, bound, surface)) continue;
        if (policy == .source_order) return index;
        const cost = try clauseCost(allocator, facts, clause, bound);
        if (best == null or cost < best_cost) {
            best = index;
            best_cost = cost;
        }
    }
    return best orelse first_remaining.?;
}

/// Describes one placed clause: what it will be looked up on, and what the
/// planner expected that to cost. Recorded rather than recomputed, so that
/// `explain` reports the numbers the choice was actually made on.
fn describe(
    allocator: std.mem.Allocator,
    facts: *relation_store.RelationStore,
    clause: syntax.Clause,
    origin: usize,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    policy: PlanPolicy,
) std.mem.Allocator.Error!Step {
    switch (clause) {
        .builtin => |expression| return .{
            .origin = origin,
            .kind = .filter,
            .predicate = expression.predicate,
            .arity = expression.terms.len,
            .mask = 0,
            .estimate = 0,
        },
        .relational, .negated => |expression| {
            const mask = boundMask(expression, bound);
            const measured = try facts.selectivity(syntax.predicateKey(expression), mask);
            return .{
                .origin = origin,
                .kind = if (clause == .negated) .anti_join else .join,
                .predicate = expression.predicate,
                .arity = expression.terms.len,
                .mask = mask,
                .estimate = measured.estimate(),
            };
        },
        .aggregate => |aggregate| {
            // The inner body sees the outer bindings, so it is planned from
            // them: that is what lets a correlated `setof` collect its members
            // through an index on the group key rather than by scanning.
            var inner_bound = try bound.clone(allocator);
            defer inner_bound.deinit(allocator);
            var inner_surface: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
            defer inner_surface.deinit(allocator);
            for (aggregate.body) |inner_clause|
                try syntax.collectClauseSurfaceVariables(allocator, inner_clause, &inner_surface);

            const inner = try allocator.create(Plan);
            errdefer allocator.destroy(inner);
            inner.* = try planBound(
                allocator,
                facts,
                aggregate.body,
                &inner_bound,
                &inner_surface,
                policy,
            );
            var estimate: usize = 0;
            for (inner.steps) |step| estimate +|= step.estimate;
            return .{
                .origin = origin,
                .kind = .aggregate,
                .predicate = null,
                .arity = 0,
                .mask = 0,
                .estimate = estimate,
                .inner = inner,
            };
        },
    }
}

/// Candidate facts a clause is expected to examine per input binding.
///
/// A built-in examines none, and a `setof` examines whatever its inner plan
/// does; neither multiplies its input, so both belong before any join that
/// would run them more times. Costing them by their own work rather than by
/// their kind is what puts them there without a special case.
fn clauseCost(
    allocator: std.mem.Allocator,
    facts: *relation_store.RelationStore,
    clause: syntax.Clause,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
) std.mem.Allocator.Error!usize {
    return switch (clause) {
        .builtin => 0,
        .relational, .negated => |expression| (try facts.selectivity(
            syntax.predicateKey(expression),
            boundMask(expression, bound),
        )).estimate(),
        .aggregate => |aggregate| blk: {
            var total: usize = 0;
            var inner_bound = try bound.clone(allocator);
            defer inner_bound.deinit(allocator);
            for (aggregate.body) |inner_clause| {
                total +|= try clauseCost(allocator, facts, inner_clause, &inner_bound);
                try bindClause(allocator, inner_clause, &inner_bound);
            }
            break :blk total;
        },
    };
}

/// Argument positions whose term the current bindings make ground, which is
/// exactly the set `Evaluator.lookupCandidates` will resolve and hand to the
/// store. Positions past the mask's width are left out there too, so a wide
/// goal is indexed on its first sixty-four arguments.
fn boundMask(expression: syntax.Expr, bound: *const std.AutoHashMapUnmanaged(syntax.Id, void)) u64 {
    var mask: u64 = 0;
    for (expression.terms, 0..) |term, position| {
        if (position >= 64) break;
        if (syntax.termVariablesBound(term, bound))
            mask |= @as(u64, 1) << @intCast(position);
    }
    return mask;
}

/// Whether a clause may be placed now: the same condition `validation`
/// admits it under, so a plan built from ready clauses is an order admission
/// would have accepted.
pub fn clauseReady(
    clause: syntax.Clause,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    surface: *const std.AutoHashMapUnmanaged(syntax.Id, void),
) bool {
    switch (clause) {
        .relational => return true,
        .negated => |expression| {
            for (expression.terms) |term|
                if (!syntax.termVariablesBound(term, bound)) return false;
            return true;
        },
        .builtin => |expression| {
            if (syntax.isArithmetic(expression)) {
                return expression.terms.len == 3 and
                    syntax.termVariablesBound(expression.terms[1], bound) and
                    syntax.termVariablesBound(expression.terms[2], bound);
            }
            if (syntax.isTypeTest(expression))
                return expression.terms.len == 1 and syntax.termVariablesBound(expression.terms[0], bound);
            if (expression.terms.len != 2) return false;
            const left = syntax.termVariablesBound(expression.terms[0], bound);
            const right = syntax.termVariablesBound(expression.terms[1], bound);
            if (expression.kind == .equality and !expression.negated) return left or right;
            return left and right;
        },
        .aggregate => |aggregate| return aggregateReady(aggregate, bound, surface),
    }
}

/// A `setof` is ready when every variable it shares with the surrounding body
/// is bound. That is what makes it correlated to one group: an unbound shared
/// variable would let the inner body range over members of other groups too.
fn aggregateReady(
    aggregate: syntax.Aggregate,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    surface: *const std.AutoHashMapUnmanaged(syntax.Id, void),
) bool {
    var ready = true;
    walkAggregateVariables(aggregate, bound, surface, &ready);
    return ready;
}

fn walkAggregateVariables(
    aggregate: syntax.Aggregate,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    surface: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    ready: *bool,
) void {
    checkTerm(aggregate.template, bound, surface, ready);
    for (aggregate.body) |clause| switch (clause) {
        .relational, .builtin, .negated => |expression| for (expression.terms) |term|
            checkTerm(term, bound, surface, ready),
        .aggregate => |nested| walkAggregateVariables(nested, bound, surface, ready),
    };
}

fn checkTerm(
    term: syntax.Term,
    bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    surface: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    ready: *bool,
) void {
    switch (term) {
        .variable => |variable| {
            if (surface.contains(variable) and !bound.contains(variable)) ready.* = false;
        },
        .cons => |pair| {
            checkTerm(pair.head, bound, surface, ready);
            checkTerm(pair.tail, bound, surface, ready);
        },
        else => {},
    }
}

/// Adds the variables placing this clause binds, mirroring what evaluation
/// leaves bound after it.
pub fn bindClause(
    allocator: std.mem.Allocator,
    clause: syntax.Clause,
    bound: *std.AutoHashMapUnmanaged(syntax.Id, void),
) !void {
    switch (clause) {
        .relational => |expression| for (expression.terms) |term|
            try syntax.bindTermVariables(allocator, term, bound),
        .negated => {},
        .builtin => |expression| {
            if (syntax.isArithmetic(expression)) {
                if (expression.terms.len == 3)
                    try syntax.bindTermVariables(allocator, expression.terms[0], bound);
                return;
            }
            if (expression.terms.len == 2 and expression.kind == .equality and !expression.negated) {
                try syntax.bindTermVariables(allocator, expression.terms[0], bound);
                try syntax.bindTermVariables(allocator, expression.terms[1], bound);
            }
        },
        .aggregate => |aggregate| try syntax.bindTermVariables(allocator, aggregate.output, bound),
    }
}

const testing = std.testing;

/// Interned ids for the variables the tests below use.
const x: syntax.Id = 1;
const y: syntax.Id = 2;

fn variables(comptime ids: []const syntax.Id) [ids.len]syntax.Term {
    var terms: [ids.len]syntax.Term = undefined;
    for (ids, &terms) |id, *term| term.* = .{ .variable = id };
    return terms;
}

test "readiness is the condition admission admits a clause under" {
    var bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer bound.deinit(testing.allocator);
    var surface: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer surface.deinit(testing.allocator);

    var pair = variables(&.{ x, y });
    const relational: syntax.Clause = .{ .relational = .{ .predicate = 10, .terms = &pair } };
    const negated: syntax.Clause = .{ .negated = .{ .predicate = 11, .terms = &pair, .negated = true } };
    const equality: syntax.Clause = .{ .builtin = .{ .predicate = 12, .terms = &pair, .kind = .equality } };
    const comparison: syntax.Clause = .{ .builtin = .{ .predicate = 13, .terms = &pair, .kind = .less_than } };

    // A positive relational goal consumes nothing and is always placeable; a
    // negation and a comparison consume both their arguments; an equality
    // needs one side, because it binds the other.
    try testing.expect(clauseReady(relational, &bound, &surface));
    try testing.expect(!clauseReady(negated, &bound, &surface));
    try testing.expect(!clauseReady(equality, &bound, &surface));
    try testing.expect(!clauseReady(comparison, &bound, &surface));

    try bound.put(testing.allocator, x, {});
    try testing.expect(!clauseReady(negated, &bound, &surface));
    try testing.expect(clauseReady(equality, &bound, &surface));
    try testing.expect(!clauseReady(comparison, &bound, &surface));

    // Placing the equality binds the other side, which is what makes the
    // negation and the comparison reachable at all.
    try bindClause(testing.allocator, equality, &bound);
    try testing.expect(clauseReady(negated, &bound, &surface));
    try testing.expect(clauseReady(comparison, &bound, &surface));
}

test "the cheapest ready clause is placed, and an unready one waits" {
    var store: relation_store.RelationStore = .init(testing.allocator);
    defer store.deinit();
    // `few` holds one fact and `many` holds four, so cost alone would place
    // `few` first. The comparison is cheaper than either and still may not go
    // first: it consumes variables neither it nor anything before it binds.
    _ = try store.insert(.{ .predicate = 20, .terms = try testing.allocator.dupe(ValueId, &.{7}) }, false);
    for (0..4) |value| _ = try store.insert(.{
        .predicate = 21,
        .terms = try testing.allocator.dupe(ValueId, &.{ @intCast(value), 7 }),
    }, false);

    var single = variables(&.{y});
    var pair = variables(&.{ x, y });
    const body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = 21, .terms = &pair } },
        .{ .builtin = .{ .predicate = 13, .terms = &pair, .kind = .less_than } },
        .{ .relational = .{ .predicate = 20, .terms = &single } },
    };

    var chosen = try plan(testing.allocator, &store, null, &body, &.{}, .cost_based);
    defer chosen.deinit();
    try testing.expectEqualSlices(
        usize,
        &.{ 2, 0, 1 },
        &.{ chosen.steps[0].origin, chosen.steps[1].origin, chosen.steps[2].origin },
    );
    // `many` is reached with `y` bound by `few`, so it is looked up on its
    // second argument rather than scanned.
    try testing.expectEqual(@as(u64, 0b10), chosen.steps[1].mask);
    try testing.expectEqual(StepKind.filter, chosen.steps[2].kind);

    // The stored order is what `.source_order` reproduces, clause for clause.
    var stored = try plan(testing.allocator, &store, null, &body, &.{}, .source_order);
    defer stored.deinit();
    try testing.expectEqualSlices(
        usize,
        &.{ 0, 1, 2 },
        &.{ stored.steps[0].origin, stored.steps[1].origin, stored.steps[2].origin },
    );
}

const ValueId = relation_store.ValueId;
