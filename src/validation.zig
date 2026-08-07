//! Rule admission: what a rule must satisfy before the database will store it.
//!
//! Three separable checks. Safety requires every head variable to be bound by
//! the body, with the seed argument of an admissible structural recursion as
//! the one documented exception. Admissibility bounds structural recursion so
//! it cannot generate infinitely many values. Stratification assigns each
//! predicate a level such that negation and aggregation only read strata below
//! their own, which is what makes the whole maintenance layer possible.
//!
//! Clause ordering belongs here too: it is not an optimisation but part of
//! admission, because it decides whether every consumer can be reached with
//! its bindings already made.

const std = @import("std");
const root = @import("root.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");

const Jatalog = root.Jatalog;
const PredicateKey = relation_store.PredicateKey;
const Id = syntax.Id;
const Expr = syntax.Expr;
const Clause = syntax.Clause;
const Rule = syntax.Rule;
const Aggregate = syntax.Aggregate;
const predicateKey = syntax.predicateKey;
const isBuiltin = syntax.isBuiltin;
const isArithmetic = syntax.isArithmetic;
const ruleContainsArithmetic = syntax.ruleContainsArithmetic;
const termContainsCons = syntax.termContainsCons;
const termEqual = syntax.termEqual;
const isTailDescendant = syntax.isTailDescendant;
const termVariablesBound = syntax.termVariablesBound;
const bindTermVariables = syntax.bindTermVariables;
const collectClauseSurfaceVariables = syntax.collectClauseSurfaceVariables;
const collectClauseAllVariables = syntax.collectClauseAllVariables;
const collectTermVariables = syntax.collectTermVariables;

pub fn validateRule(db: *Jatalog, head: Expr, body: []const Clause) !?usize {
    if (body.len == 0 or head.negated or isBuiltin(head)) return error.InvalidRule;
    const recursive_seed = try admissibleSeedArgument(head, body);
    var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
    defer outer_variables.deinit(db.allocator);
    for (head.terms) |term| try collectTermVariables(db.allocator, term, &outer_variables);
    for (body) |clause| try collectClauseSurfaceVariables(db.allocator, clause, &outer_variables);

    const ordered = try orderClauses(db, body);
    defer db.allocator.free(ordered);
    if (recursive_seed) |seed_argument| {
        try validateRuleSafety(db, head, ordered, &outer_variables, seed_argument);
        return seed_argument;
    }
    validateRuleSafety(db, head, ordered, &outer_variables, null) catch |err| switch (err) {
        error.InvalidRule => {
            const seed_argument = firstStructuralArgument(head) orelse
                return error.InvalidRule;
            try validateRuleSafety(db, head, ordered, &outer_variables, seed_argument);
            return seed_argument;
        },
        else => return err,
    };
    return null;
}
fn validateRuleSafety(
    db: *Jatalog,
    head: Expr,
    ordered: []const Clause,
    outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
    seed_argument: ?usize,
) !void {
    var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
    defer bound.deinit(db.allocator);
    if (seed_argument) |argument|
        try bindTermVariables(db.allocator, head.terms[argument], &bound);
    for (ordered) |clause| try validateClause(db, clause, &bound, outer_variables, error.InvalidRule);
    for (head.terms) |term| if (!termVariablesBound(term, &bound)) return error.InvalidRule;
}
fn admissibleSeedArgument(head: Expr, body: []const Clause) !?usize {
    var seed: ?usize = null;
    for (body) |clause| {
        const call = switch (clause) {
            .relational => |expression| expression,
            else => continue,
        };
        if (call.predicate != head.predicate or call.terms.len != head.terms.len) continue;

        var involves_cons = false;
        var call_seed: ?usize = null;
        for (head.terms, call.terms, 0..) |head_term, call_term, index| {
            if (!termContainsCons(head_term) and !termContainsCons(call_term)) continue;
            involves_cons = true;
            if (!termEqual(head_term, call_term) and !isTailDescendant(head_term, call_term))
                return error.NotAdmissible;
            if (isTailDescendant(head_term, call_term) and call_seed == null) call_seed = index;
        }
        if (!involves_cons) continue;
        const candidate = call_seed orelse return error.NotAdmissible;
        if (seed) |existing| {
            if (existing != candidate) return error.NotAdmissible;
        } else seed = candidate;
    }
    return seed;
}
fn firstStructuralArgument(head: Expr) ?usize {
    for (head.terms, 0..) |term, index|
        if (termContainsCons(term)) return index;
    return null;
}
pub fn validateRecursiveArithmetic(db: *Jatalog) !void {
    for (db.eval.rules.items) |rule| {
        if (!ruleContainsArithmetic(rule)) continue;
        const head = predicateKey(rule.head);
        for (rule.body) |clause| {
            const expression = switch (clause) {
                .relational => |value| value,
                else => continue,
            };
            var visited: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
            defer visited.deinit(db.allocator);
            const dependency = predicateKey(expression);
            const structurally_proven = rule.seed_argument != null and std.meta.eql(dependency, head);
            if (!structurally_proven and try predicateReaches(db, dependency, head, &visited))
                return error.NotAdmissible;
        }
    }
}
fn predicateReaches(
    db: *Jatalog,
    current: PredicateKey,
    target: PredicateKey,
    visited: *std.AutoHashMapUnmanaged(PredicateKey, void),
) !bool {
    if (std.meta.eql(current, target)) return true;
    if (visited.contains(current)) return false;
    try visited.put(db.allocator, current, {});
    for (db.eval.rules.items) |rule| {
        if (!std.meta.eql(predicateKey(rule.head), current)) continue;
        for (rule.body) |clause| {
            const expression = switch (clause) {
                .relational => |value| value,
                else => continue,
            };
            if (try predicateReaches(db, predicateKey(expression), target, visited)) return true;
        }
    }
    return false;
}
pub fn validateClause(
    db: *Jatalog,
    clause: Clause,
    bound: *std.AutoHashMapUnmanaged(Id, void),
    outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
    safety_error: anyerror,
) anyerror!void {
    switch (clause) {
        .relational => |expression| for (expression.terms) |term|
            try bindTermVariables(db.allocator, term, bound),
        .negated => |expression| for (expression.terms) |term|
            if (!termVariablesBound(term, bound)) return safety_error,
        .builtin => |expression| {
            if (isArithmetic(expression)) {
                if (expression.terms.len != 3 or
                    !termVariablesBound(expression.terms[1], bound) or
                    !termVariablesBound(expression.terms[2], bound)) return safety_error;
                try bindTermVariables(db.allocator, expression.terms[0], bound);
                return;
            }
            if (expression.terms.len != 2) return safety_error;
            const a_bound = termVariablesBound(expression.terms[0], bound);
            const b_bound = termVariablesBound(expression.terms[1], bound);
            if (expression.kind == .equality and !expression.negated) {
                if (!a_bound and !b_bound) return safety_error;
                try bindTermVariables(db.allocator, expression.terms[0], bound);
                try bindTermVariables(db.allocator, expression.terms[1], bound);
            } else if (!a_bound or !b_bound) return safety_error;
        },
        .aggregate => |aggregate| {
            try validateAggregate(db, aggregate, bound, outer_variables, safety_error);
            try bindTermVariables(db.allocator, aggregate.output, bound);
        },
    }
}
fn validateAggregate(
    db: *Jatalog,
    aggregate: Aggregate,
    outer_bound: *const std.AutoHashMapUnmanaged(Id, void),
    outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
    safety_error: anyerror,
) anyerror!void {
    if (aggregate.body.len == 0) return safety_error;
    var inner_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
    defer inner_variables.deinit(db.allocator);
    try collectTermVariables(db.allocator, aggregate.template, &inner_variables);
    for (aggregate.body) |clause| try collectClauseAllVariables(db.allocator, clause, &inner_variables);

    var inner_bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
    defer inner_bound.deinit(db.allocator);
    var iterator = inner_variables.keyIterator();
    while (iterator.next()) |variable| {
        if (!outer_variables.contains(variable.*)) continue;
        if (!outer_bound.contains(variable.*)) return safety_error;
        try inner_bound.put(db.allocator, variable.*, {});
    }

    var inner_outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
    defer inner_outer_variables.deinit(db.allocator);
    try collectTermVariables(db.allocator, aggregate.template, &inner_outer_variables);
    for (aggregate.body) |clause|
        try collectClauseSurfaceVariables(db.allocator, clause, &inner_outer_variables);

    const ordered = try orderClauses(db, aggregate.body);
    defer db.allocator.free(ordered);
    for (ordered) |clause|
        try validateClause(db, clause, &inner_bound, &inner_outer_variables, safety_error);
    if (!termVariablesBound(aggregate.template, &inner_bound)) return safety_error;
}
pub fn orderClauses(db: *Jatalog, clauses: []const Clause) ![]Clause {
    const result = try db.allocator.alloc(Clause, clauses.len);
    var index: usize = 0;
    for (clauses) |clause| switch (clause) {
        .relational => {
            result[index] = clause;
            index += 1;
        },
        .builtin => |expression| if (!expression.negated and expression.kind == .equality) {
            result[index] = clause;
            index += 1;
        },
        else => {},
    };
    for (clauses) |clause| switch (clause) {
        .builtin => |expression| {
            if (isArithmetic(expression)) {
                result[index] = clause;
                index += 1;
            }
        },
        else => {},
    };
    for (clauses) |clause| if (clause == .aggregate) {
        result[index] = clause;
        index += 1;
    };
    for (clauses) |clause| switch (clause) {
        .negated => {
            result[index] = clause;
            index += 1;
        },
        .builtin => |expression| if (expression.negated or
            (expression.kind != .equality and !isArithmetic(expression)))
        {
            result[index] = clause;
            index += 1;
        },
        else => {},
    };
    return result;
}
pub fn validateStratification(db: *Jatalog) !void {
    var levels = try db.eval.computeStrata();
    levels.deinit(db.allocator);
}
