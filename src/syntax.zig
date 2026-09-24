//! The compiled rule language: the terms, goals, clauses and rules a
//! database holds after parsing, and the pure operations over them —
//! cloning, freeing, variable collection, structural comparison and the
//! predicates that classify a goal.
//!
//! Nothing here touches a database. Keeping the language separable from the
//! engine that evaluates it is what lets the maintenance, aggregate and
//! parser layers share one definition of a rule without depending on each
//! other.

const std = @import("std");
const scalar = @import("scalar.zig");
const relation_store = @import("relation_store.zig");
const schema = @import("schema.zig");

/// Interned identifier for a name: predicate symbols and variable names.
pub const Id = u64;
/// Interned identifier for a ground value in the database's value table.
pub const ValueId = u64;

pub const Term = union(enum) {
    scalar: scalar.Id,
    variable: Id,
    nil,
    cons: *Cons,

    pub const Cons = struct {
        head: Term,
        tail: Term,
    };

    pub fn isGround(self: Term) bool {
        return switch (self) {
            .variable => false,
            .cons => |pair| pair.head.isGround() and pair.tail.isGround(),
            else => true,
        };
    }
};

pub const GoalKind = enum {
    relation,
    equality,
    inequality,
    less_than,
    less_or_equal,
    greater_than,
    greater_or_equal,
    add,
    subtract,
    /// `X : T`: one term, and the type it is tested against in `column_type`.
    type_test,
};

pub const Expr = struct {
    predicate: Id,
    terms: []Term,
    negated: bool = false,
    kind: GoalKind = .relation,
    /// The type a `type_test` tests for. Unused by every other kind.
    column_type: schema.ColumnType = .any,

    pub fn arity(self: Expr) usize {
        return self.terms.len;
    }

    pub fn isGround(self: Expr) bool {
        for (self.terms) |term| if (!term.isGround()) return false;
        return true;
    }
};

pub const Rule = struct {
    /// Stable database-local identifier; body occurrences are identified by
    /// `(id, clause index)`. Ids survive cloning and are never reused.
    id: u32 = 0,
    head: Expr,
    body: []Clause,
    seed_argument: ?usize = null,
};

/// Restricts one relational body occurrence to facts appended during the
/// previous semi-naive round.
pub const DeltaConstraint = struct {
    clause_index: usize,
    delta_start: usize,
    delta_end: usize,
};

/// The rule's body with the clause at `skip_index` removed: the outer goals
/// of an aggregate rule, or the body occurrences that remain to be joined
/// when over-deleting through one occurrence. The clauses themselves are
/// borrowed from the rule; the caller owns only the returned slice.
pub fn outerClauses(allocator: std.mem.Allocator, rule: Rule, skip_index: usize) ![]Clause {
    const result = try allocator.alloc(Clause, rule.body.len - 1);
    var count: usize = 0;
    for (rule.body, 0..) |clause, index| {
        if (index == skip_index) continue;
        result[count] = clause;
        count += 1;
    }
    return result;
}

/// Returns the body index of the single unnested `setof` occurrence a rule
/// can have maintained incrementally, or null when the rule falls outside
/// the maintainable class and needs the rebuild fallback: no aggregate,
/// several aggregates, a nested aggregate, or seeded structural recursion.
pub fn maintainableAggregateIndex(rule: Rule) ?usize {
    if (rule.seed_argument != null) return null;
    var found: ?usize = null;
    for (rule.body, 0..) |clause, index| {
        const aggregate = switch (clause) {
            .aggregate => |value| value,
            else => continue,
        };
        if (found != null) return null;
        for (aggregate.body) |inner| if (inner == .aggregate) return null;
        found = index;
    }
    return found;
}

pub fn bindingsEqual(left: *const Binding, right: *const Binding) bool {
    if (left.values.count() != right.values.count()) return false;
    for (left.values.keys(), left.values.values()) |variable, value| {
        const other = right.values.get(variable) orelse return false;
        if (other != value) return false;
    }
    return true;
}

pub const Aggregate = struct {
    template: Term,
    body: []Clause,
    output: Term,
};

pub const Clause = union(enum) {
    relational: Expr,
    builtin: Expr,
    negated: Expr,
    aggregate: Aggregate,
};

pub fn noteBodyDependencies(
    allocator: std.mem.Allocator,
    body: []const Clause,
    head_level: usize,
    first_dependent: *std.array_hash_map.Auto(relation_store.PredicateKey, usize),
) !void {
    for (body) |clause| switch (clause) {
        .relational, .negated => |expression| {
            const entry = try first_dependent.getOrPut(allocator, predicateKey(expression));
            if (!entry.found_existing or entry.value_ptr.* > head_level)
                entry.value_ptr.* = head_level;
        },
        .builtin => {},
        .aggregate => |aggregate| try noteBodyDependencies(
            allocator,
            aggregate.body,
            head_level,
            first_dependent,
        ),
    };
}

pub fn clausesReadGrownNonPositively(
    body: []const Clause,
    grown: *const std.AutoHashMapUnmanaged(relation_store.PredicateKey, void),
) bool {
    for (body) |clause| switch (clause) {
        .negated => |expression| if (grown.contains(predicateKey(expression))) return true,
        .aggregate => |aggregate| if (clausesReadGrownAnywhere(aggregate.body, grown)) return true,
        .relational, .builtin => {},
    };
    return false;
}

pub fn clausesReadGrownAnywhere(
    body: []const Clause,
    grown: *const std.AutoHashMapUnmanaged(relation_store.PredicateKey, void),
) bool {
    for (body) |clause| switch (clause) {
        .relational, .negated => |expression| if (grown.contains(predicateKey(expression))) return true,
        .aggregate => |aggregate| if (clausesReadGrownAnywhere(aggregate.body, grown)) return true,
        .builtin => {},
    };
    return false;
}

pub fn predicateKey(expression: Expr) relation_store.PredicateKey {
    return .{ .name = expression.predicate, .arity = expression.terms.len };
}

pub const Binding = struct {
    values: std.array_hash_map.Auto(Id, ValueId) = .empty,

    pub fn deinit(self: *Binding, allocator: std.mem.Allocator) void {
        self.values.deinit(allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const Binding, allocator: std.mem.Allocator) !Binding {
        return .{ .values = try self.values.clone(allocator) };
    }
};

pub fn freeExpr(allocator: std.mem.Allocator, value: Expr) void {
    for (value.terms) |term| freeTerm(allocator, term);
    allocator.free(value.terms);
}

pub fn freeRule(allocator: std.mem.Allocator, rule: Rule) void {
    freeExpr(allocator, rule.head);
    for (rule.body) |clause| freeClauseTree(allocator, clause);
    allocator.free(rule.body);
}

pub fn cloneTerm(allocator: std.mem.Allocator, term: Term) !Term {
    return switch (term) {
        .cons => |pair| blk: {
            const copy = try allocator.create(Term.Cons);
            errdefer allocator.destroy(copy);
            copy.head = try cloneTerm(allocator, pair.head);
            errdefer freeTerm(allocator, copy.head);
            copy.tail = try cloneTerm(allocator, pair.tail);
            break :blk .{ .cons = copy };
        },
        else => term,
    };
}

pub fn cloneExpr(allocator: std.mem.Allocator, expression: Expr) !Expr {
    const terms = try allocator.alloc(Term, expression.terms.len);
    var initialized: usize = 0;
    errdefer {
        for (terms[0..initialized]) |term| freeTerm(allocator, term);
        allocator.free(terms);
    }
    for (expression.terms, terms) |term, *copy| {
        copy.* = try cloneTerm(allocator, term);
        initialized += 1;
    }
    return .{
        .predicate = expression.predicate,
        .terms = terms,
        .negated = expression.negated,
        .kind = expression.kind,
        .column_type = expression.column_type,
    };
}

pub fn cloneClause(allocator: std.mem.Allocator, clause: Clause) !Clause {
    return switch (clause) {
        .relational => |expression| .{ .relational = try cloneExpr(allocator, expression) },
        .builtin => |expression| .{ .builtin = try cloneExpr(allocator, expression) },
        .negated => |expression| .{ .negated = try cloneExpr(allocator, expression) },
        .aggregate => |aggregate| blk: {
            const template = try cloneTerm(allocator, aggregate.template);
            errdefer freeTerm(allocator, template);
            const output = try cloneTerm(allocator, aggregate.output);
            errdefer freeTerm(allocator, output);
            const body = try allocator.alloc(Clause, aggregate.body.len);
            var initialized: usize = 0;
            errdefer {
                for (body[0..initialized]) |body_clause| freeClauseTree(allocator, body_clause);
                allocator.free(body);
            }
            for (aggregate.body, body) |body_clause, *copy| {
                copy.* = try cloneClause(allocator, body_clause);
                initialized += 1;
            }
            break :blk .{ .aggregate = .{ .template = template, .body = body, .output = output } };
        },
    };
}

pub fn cloneRule(allocator: std.mem.Allocator, rule: Rule) !Rule {
    const head = try cloneExpr(allocator, rule.head);
    errdefer freeExpr(allocator, head);
    const body = try allocator.alloc(Clause, rule.body.len);
    var initialized: usize = 0;
    errdefer {
        for (body[0..initialized]) |clause| freeClauseTree(allocator, clause);
        allocator.free(body);
    }
    for (rule.body, body) |clause, *copy| {
        copy.* = try cloneClause(allocator, clause);
        initialized += 1;
    }
    return .{ .id = rule.id, .head = head, .body = body, .seed_argument = rule.seed_argument };
}

pub fn freeClauseTree(allocator: std.mem.Allocator, clause: Clause) void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| freeExpr(allocator, expression),
        .aggregate => |aggregate| {
            freeTerm(allocator, aggregate.template);
            for (aggregate.body) |body_clause| freeClauseTree(allocator, body_clause);
            allocator.free(aggregate.body);
            freeTerm(allocator, aggregate.output);
        },
    }
}

pub fn freeTerm(allocator: std.mem.Allocator, term: Term) void {
    switch (term) {
        .cons => |pair| {
            freeTerm(allocator, pair.head);
            freeTerm(allocator, pair.tail);
            allocator.destroy(pair);
        },
        else => {},
    }
}

pub fn termVariablesBound(term: Term, bound: *const std.AutoHashMapUnmanaged(Id, void)) bool {
    return switch (term) {
        .variable => |variable| bound.contains(variable),
        .cons => |pair| termVariablesBound(pair.head, bound) and termVariablesBound(pair.tail, bound),
        else => true,
    };
}

pub fn bindTermVariables(
    allocator: std.mem.Allocator,
    term: Term,
    bound: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (term) {
        .variable => |variable| try bound.put(allocator, variable, {}),
        .cons => |pair| {
            try bindTermVariables(allocator, pair.head, bound);
            try bindTermVariables(allocator, pair.tail, bound);
        },
        else => {},
    }
}

pub fn collectTermVariables(
    allocator: std.mem.Allocator,
    term: Term,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    try bindTermVariables(allocator, term, variables);
}

pub fn collectExprVariables(
    allocator: std.mem.Allocator,
    expression: Expr,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    for (expression.terms) |term| try collectTermVariables(allocator, term, variables);
}

pub fn collectClauseSurfaceVariables(
    allocator: std.mem.Allocator,
    clause: Clause,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| try collectExprVariables(allocator, expression, variables),
        .aggregate => |aggregate| try collectTermVariables(allocator, aggregate.output, variables),
    }
}

pub fn collectClauseAllVariables(
    allocator: std.mem.Allocator,
    clause: Clause,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| try collectExprVariables(allocator, expression, variables),
        .aggregate => |aggregate| {
            try collectTermVariables(allocator, aggregate.template, variables);
            try collectTermVariables(allocator, aggregate.output, variables);
            for (aggregate.body) |body_clause|
                try collectClauseAllVariables(allocator, body_clause, variables);
        },
    }
}

pub fn isVariable(string: []const u8) bool {
    return string.len != 0 and std.ascii.isUpper(string[0]);
}

pub fn goalKind(operator: []const u8) ?GoalKind {
    if (std.mem.eql(u8, operator, "=")) return .equality;
    if (std.mem.eql(u8, operator, "!=") or std.mem.eql(u8, operator, "<>")) return .inequality;
    if (std.mem.eql(u8, operator, "<")) return .less_than;
    if (std.mem.eql(u8, operator, "<=")) return .less_or_equal;
    if (std.mem.eql(u8, operator, ">")) return .greater_than;
    if (std.mem.eql(u8, operator, ">=")) return .greater_or_equal;
    if (std.mem.eql(u8, operator, "+")) return .add;
    if (std.mem.eql(u8, operator, "-")) return .subtract;
    return null;
}

pub fn goalOperator(kind: GoalKind) []const u8 {
    return switch (kind) {
        .relation => unreachable,
        .equality => "=",
        .inequality => "<>",
        .less_than => "<",
        .less_or_equal => "<=",
        .greater_than => ">",
        .greater_or_equal => ">=",
        .add => "+",
        .subtract => "-",
        .type_test => ":",
    };
}

pub fn classifyExpr(expression: Expr) Clause {
    if (expression.negated) return .{ .negated = expression };
    if (isBuiltin(expression)) return .{ .builtin = expression };
    return .{ .relational = expression };
}

pub fn ruleContainsArithmetic(rule: Rule) bool {
    for (rule.body) |clause| switch (clause) {
        .builtin => |expression| if (isArithmetic(expression)) return true,
        else => {},
    };
    return false;
}

/// Whether a rule can produce a list no fact holds yet: a head argument built
/// with a cons, or an equality that builds one. A cons in a relational body
/// clause only takes an existing list apart, so it is not counted.
pub fn ruleConstructsLists(rule: Rule) bool {
    for (rule.head.terms) |term| if (termContainsCons(term)) return true;
    for (rule.body) |clause| switch (clause) {
        .builtin => |expression| for (expression.terms) |term| if (termContainsCons(term)) return true,
        else => {},
    };
    return false;
}

pub fn isBuiltin(value: Expr) bool {
    return value.kind != .relation;
}

pub fn isTypeTest(value: Expr) bool {
    return value.kind == .type_test;
}

pub fn isArithmetic(value: Expr) bool {
    return value.kind == .add or value.kind == .subtract;
}

pub fn termContainsCons(term: Term) bool {
    return switch (term) {
        .cons => true,
        else => false,
    };
}

pub fn termEqual(left: Term, right: Term) bool {
    return switch (left) {
        .scalar => |value| switch (right) {
            .scalar => |other| value == other,
            else => false,
        },
        .variable => |value| switch (right) {
            .variable => |other| value == other,
            else => false,
        },
        .nil => right == .nil,
        .cons => |pair| switch (right) {
            .cons => |other| termEqual(pair.head, other.head) and termEqual(pair.tail, other.tail),
            else => false,
        },
    };
}

pub fn isTailDescendant(ancestor: Term, candidate: Term) bool {
    var current = ancestor;
    while (current == .cons) {
        current = current.cons.tail;
        if (termEqual(current, candidate)) return true;
    }
    return false;
}
