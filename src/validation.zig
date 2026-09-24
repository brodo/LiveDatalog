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
const database = @import("database.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");

pub fn validateRule(db: *database.Database, head: syntax.Expr, body: []const syntax.Clause) !?usize {
    if (body.len == 0 or head.negated or syntax.isBuiltin(head)) return error.InvalidRule;
    const recursive_seed = try admissibleSeedArgument(head, body);
    var outer_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer outer_variables.deinit(db.allocator);
    for (head.terms) |term| try syntax.collectTermVariables(db.allocator, term, &outer_variables);
    for (body) |clause| try syntax.collectClauseSurfaceVariables(db.allocator, clause, &outer_variables);

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
    db: *database.Database,
    head: syntax.Expr,
    ordered: []const syntax.Clause,
    outer_variables: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    seed_argument: ?usize,
) !void {
    var bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer bound.deinit(db.allocator);
    if (seed_argument) |argument|
        try syntax.bindTermVariables(db.allocator, head.terms[argument], &bound);
    for (ordered) |clause| try validateClause(db, clause, &bound, outer_variables, error.InvalidRule);
    for (head.terms) |term| if (!syntax.termVariablesBound(term, &bound)) return error.InvalidRule;
}
fn admissibleSeedArgument(head: syntax.Expr, body: []const syntax.Clause) !?usize {
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
            if (!syntax.termContainsCons(head_term) and !syntax.termContainsCons(call_term)) continue;
            involves_cons = true;
            if (!syntax.termEqual(head_term, call_term) and !syntax.isTailDescendant(head_term, call_term))
                return error.NotAdmissible;
            if (syntax.isTailDescendant(head_term, call_term) and call_seed == null) call_seed = index;
        }
        if (!involves_cons) continue;
        const candidate = call_seed orelse return error.NotAdmissible;
        if (seed) |existing| {
            if (existing != candidate) return error.NotAdmissible;
        } else seed = candidate;
    }
    return seed;
}
fn firstStructuralArgument(head: syntax.Expr) ?usize {
    for (head.terms, 0..) |term, index|
        if (syntax.termContainsCons(term)) return index;
    return null;
}
/// Rejects a recursive dependency cycle that can generate new values: one
/// containing value-producing arithmetic or list construction. The only cycle
/// admitted is a rule's direct call to itself that the structural decrease
/// proof already covers. Mutual recursion through a generating rule is always
/// rejected, even where it would terminate: `admissibleSeedArgument` proves a
/// decrease only between a head and its own calls, and nothing proves one
/// across two predicates.
pub fn validateRecursiveGeneration(db: *database.Database) !void {
    for (db.eval.rules.items) |rule| {
        if (!syntax.ruleContainsArithmetic(rule) and !syntax.ruleConstructsLists(rule)) continue;
        const head = syntax.predicateKey(rule.head);
        for (rule.body) |clause| {
            const expression = switch (clause) {
                .relational => |value| value,
                else => continue,
            };
            var visited: std.AutoHashMapUnmanaged(relation_store.PredicateKey, void) = .empty;
            defer visited.deinit(db.allocator);
            const dependency = syntax.predicateKey(expression);
            const structurally_proven = rule.seed_argument != null and std.meta.eql(dependency, head);
            if (!structurally_proven and try predicateReaches(db, dependency, head, &visited))
                return error.NotAdmissible;
        }
    }
}
fn predicateReaches(
    db: *database.Database,
    current: relation_store.PredicateKey,
    target: relation_store.PredicateKey,
    visited: *std.AutoHashMapUnmanaged(relation_store.PredicateKey, void),
) !bool {
    if (std.meta.eql(current, target)) return true;
    if (visited.contains(current)) return false;
    try visited.put(db.allocator, current, {});
    for (db.eval.rules.items) |rule| {
        if (!std.meta.eql(syntax.predicateKey(rule.head), current)) continue;
        for (rule.body) |clause| {
            const expression = switch (clause) {
                .relational => |value| value,
                else => continue,
            };
            if (try predicateReaches(db, syntax.predicateKey(expression), target, visited)) return true;
        }
    }
    return false;
}
pub fn validateClause(
    db: *database.Database,
    clause: syntax.Clause,
    bound: *std.AutoHashMapUnmanaged(syntax.Id, void),
    outer_variables: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    safety_error: anyerror,
) anyerror!void {
    switch (clause) {
        .relational => |expression| for (expression.terms) |term|
            try syntax.bindTermVariables(db.allocator, term, bound),
        .negated => |expression| for (expression.terms) |term|
            if (!syntax.termVariablesBound(term, bound)) return safety_error,
        .builtin => |expression| {
            if (syntax.isArithmetic(expression)) {
                if (expression.terms.len != 3 or
                    !syntax.termVariablesBound(expression.terms[1], bound) or
                    !syntax.termVariablesBound(expression.terms[2], bound)) return safety_error;
                try syntax.bindTermVariables(db.allocator, expression.terms[0], bound);
                return;
            }
            if (syntax.isTypeTest(expression)) {
                if (expression.terms.len != 1 or !syntax.termVariablesBound(expression.terms[0], bound))
                    return safety_error;
                return;
            }
            if (syntax.isMembership(expression)) {
                if (expression.terms.len != 2 or
                    !syntax.termVariablesBound(expression.terms[1], bound)) return safety_error;
                try syntax.bindTermVariables(db.allocator, expression.terms[0], bound);
                return;
            }
            if (expression.terms.len != 2) return safety_error;
            const a_bound = syntax.termVariablesBound(expression.terms[0], bound);
            const b_bound = syntax.termVariablesBound(expression.terms[1], bound);
            if (expression.kind == .equality and !expression.negated) {
                if (!a_bound and !b_bound) return safety_error;
                try syntax.bindTermVariables(db.allocator, expression.terms[0], bound);
                try syntax.bindTermVariables(db.allocator, expression.terms[1], bound);
            } else if (!a_bound or !b_bound) return safety_error;
        },
        .aggregate => |aggregate| {
            try validateAggregate(db, aggregate, bound, outer_variables, safety_error);
            try syntax.bindTermVariables(db.allocator, aggregate.output, bound);
        },
    }
}
fn validateAggregate(
    db: *database.Database,
    aggregate: syntax.Aggregate,
    outer_bound: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    outer_variables: *const std.AutoHashMapUnmanaged(syntax.Id, void),
    safety_error: anyerror,
) anyerror!void {
    if (aggregate.body.len == 0) return safety_error;
    var inner_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer inner_variables.deinit(db.allocator);
    try syntax.collectTermVariables(db.allocator, aggregate.template, &inner_variables);
    for (aggregate.body) |clause| try syntax.collectClauseAllVariables(db.allocator, clause, &inner_variables);

    var inner_bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer inner_bound.deinit(db.allocator);
    var iterator = inner_variables.keyIterator();
    while (iterator.next()) |variable| {
        if (!outer_variables.contains(variable.*)) continue;
        if (!outer_bound.contains(variable.*)) return safety_error;
        try inner_bound.put(db.allocator, variable.*, {});
    }

    var inner_outer_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer inner_outer_variables.deinit(db.allocator);
    try syntax.collectTermVariables(db.allocator, aggregate.template, &inner_outer_variables);
    for (aggregate.body) |clause|
        try syntax.collectClauseSurfaceVariables(db.allocator, clause, &inner_outer_variables);

    const ordered = try orderClauses(db, aggregate.body);
    defer db.allocator.free(ordered);
    for (ordered) |clause|
        try validateClause(db, clause, &inner_bound, &inner_outer_variables, safety_error);
    if (!syntax.termVariablesBound(aggregate.template, &inner_bound)) return safety_error;
}
pub fn orderClauses(db: *database.Database, clauses: []const syntax.Clause) ![]syntax.Clause {
    const result = try db.allocator.alloc(syntax.Clause, clauses.len);
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
    // A membership goal reads a list something above bound and binds the
    // element, which an arithmetic goal after it may consume; the list itself
    // is never an arithmetic result.
    for (clauses) |clause| switch (clause) {
        .builtin => |expression| if (syntax.isMembership(expression)) {
            result[index] = clause;
            index += 1;
        },
        else => {},
    };
    for (clauses) |clause| switch (clause) {
        .builtin => |expression| {
            if (syntax.isArithmetic(expression)) {
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
            (expression.kind != .equality and !syntax.isArithmetic(expression) and
                !syntax.isMembership(expression)))
        {
            result[index] = clause;
            index += 1;
        },
        else => {},
    };
    return result;
}
pub fn validateStratification(db: *database.Database) !void {
    var levels = try db.eval.computeStrata();
    levels.deinit(db.allocator);
}
