//! The vocabulary a fold reasons in: terms, goals and rules that are *not*
//! the ones the evaluator runs, plus the symbol table that gives them
//! identities.
//!
//! `syntax` is the executable language. Everything expressible there can be
//! evaluated, which is exactly why folding cannot be written in it. Inverting
//! a view introduces terms naming a value some fact would have had — Skolem
//! terms — and equalities the caller never wrote, and neither has an
//! executable meaning until a later phase proves the plan runnable. A
//! representation for them in `syntax` would let an unproved plan reach the
//! evaluator by accident, so there is none: this IR is lowered *from* `syntax`
//! and never lifted back.
//!
//! Identity here is not spelling. A variable is an entry in a `Symbols` table
//! and its printed name is a lookup, so two variables spelled `X` in different
//! scopes are different variables, and a generated symbol cannot collide with
//! a user one — collision is a property of names, and names are not
//! identities. The renderer prints the identity alongside the spelling for the
//! same reason: dropping it would print two different variables the same way,
//! which is the confusion this module exists to prevent.
//!
//! Nothing here folds anything. This is the vocabulary the Inverse Method is
//! written in, and the renderer is how a plan holding generated symbols is
//! read at all, since such a plan is by construction not valid user input.

const std = @import("std");
const relation_store = @import("relation_store.zig");
const scalar = @import("scalar.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");

/// A variable's identity, unique across one `Symbols` table.
pub const Variable = enum(u32) { _ };

/// A generated function symbol: what a Skolem term applies to its arguments.
pub const Function = enum(u32) { _ };

/// The variables introduced together by one lowered rule, one query, or one
/// renamed copy. Two scopes may use the same spellings and mean different
/// variables by them.
pub const Scope = enum(u32) { _ };

/// A view's identity in a catalog. Declared here so a goal can name a view
/// without the IR having to know what a catalog is.
pub const ViewId = enum(u32) { _ };

/// The identities of every symbol an IR fragment mentions.
///
/// One table serves a catalog, the queries folded against it and the plans
/// that come back: an identity means the same thing in all of them because
/// they are handed out from one place. Fragments belonging to different tables
/// must never be mixed.
pub const Symbols = struct {
    allocator: std.mem.Allocator,
    scopes: std.ArrayList(ScopeInfo) = .empty,
    variables: std.ArrayList(VariableInfo) = .empty,
    functions: std.ArrayList(FunctionInfo) = .empty,
    /// The variable a user spelling denotes within a scope, so lowering the
    /// second occurrence of `X` in a rule reaches the first one's identity.
    interned: std.array_hash_map.Auto(UserName, Variable) = .empty,

    /// What a scope was opened for. Recorded for reading plans, not for
    /// deciding anything.
    pub const Purpose = enum { query, view_definition, generated };

    /// A variable's spelling, which is not its identity. A generated variable
    /// has none: it is printed from its identity alone.
    pub const Origin = union(enum) {
        /// A name interned in the string table the scope was lowered against.
        user: syntax.Id,
        generated,
    };

    pub const ScopeInfo = struct { purpose: Purpose };
    pub const VariableInfo = struct { scope: Scope, origin: Origin };
    pub const FunctionInfo = struct { scope: Scope };

    const UserName = struct { scope: Scope, name: syntax.Id };

    pub fn init(allocator: std.mem.Allocator) Symbols {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Symbols) void {
        self.scopes.deinit(self.allocator);
        self.variables.deinit(self.allocator);
        self.functions.deinit(self.allocator);
        self.interned.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn openScope(self: *Symbols, purpose: Purpose) !Scope {
        try self.scopes.append(self.allocator, .{ .purpose = purpose });
        return @enumFromInt(self.scopes.items.len - 1);
    }

    /// The variable `name` denotes in `scope`, added on its first occurrence.
    /// This is what makes a rule's repeated `X` one variable and another
    /// scope's `X` a different one.
    pub fn userVariable(self: *Symbols, scope: Scope, name: syntax.Id) !Variable {
        const key: UserName = .{ .scope = scope, .name = name };
        if (self.interned.get(key)) |existing| return existing;
        const variable = try self.addVariable(scope, .{ .user = name });
        // A failed interning leaves the variable in the table unreferenced
        // rather than popping it: identities are never reused, and the table
        // releases it either way.
        try self.interned.put(self.allocator, key, variable);
        return variable;
    }

    /// A variable with no user spelling, distinct from every other variable.
    pub fn freshVariable(self: *Symbols, scope: Scope) !Variable {
        return self.addVariable(scope, .generated);
    }

    /// A variable that prints like a user name but is distinct from every
    /// variable already in the table, including the one that name denotes in
    /// `scope`. This is how a renamed copy keeps a readable spelling without
    /// inheriting an identity.
    pub fn freshUserVariable(self: *Symbols, scope: Scope, name: syntax.Id) !Variable {
        return self.addVariable(scope, .{ .user = name });
    }

    pub fn freshFunction(self: *Symbols, scope: Scope) !Function {
        try self.functions.append(self.allocator, .{ .scope = scope });
        return @enumFromInt(self.functions.items.len - 1);
    }

    pub fn scopeOf(self: *const Symbols, variable: Variable) Scope {
        return self.variables.items[@intFromEnum(variable)].scope;
    }

    pub fn originOf(self: *const Symbols, variable: Variable) Origin {
        return self.variables.items[@intFromEnum(variable)].origin;
    }

    pub fn purposeOf(self: *const Symbols, scope: Scope) Purpose {
        return self.scopes.items[@intFromEnum(scope)].purpose;
    }

    fn addVariable(self: *Symbols, scope: Scope, origin: Origin) !Variable {
        try self.variables.append(self.allocator, .{ .scope = scope, .origin = origin });
        return @enumFromInt(self.variables.items.len - 1);
    }
};

pub const Term = union(enum) {
    /// A ground value interned in the database the IR was lowered from.
    constant: scalar.Id,
    variable: Variable,
    nil,
    cons: *Cons,
    /// A value the inverse of a view names but cannot produce: the value some
    /// fact must have had for the view's tuple to exist.
    skolem: *Skolem,

    pub const Cons = struct { head: Term, tail: Term };
    pub const Skolem = struct { function: Function, arguments: []Term };

    /// Whether this term can be evaluated at all. A Skolem term cannot, at any
    /// depth, which is what a later phase's elimination step has to remove
    /// before a plan can run.
    pub fn containsSkolem(self: Term) bool {
        return switch (self) {
            .skolem => true,
            .cons => |pair| pair.head.containsSkolem() or pair.tail.containsSkolem(),
            else => false,
        };
    }
};

/// What a relational goal reads. A view and a base relation spelled the same
/// way stay distinct because a view is named by its catalog identity; the name
/// it carries is for printing.
pub const Predicate = union(enum) {
    base: relation_store.PredicateKey,
    view: ViewRef,
    /// A relation a fold invented by splitting one of the query's off. It is
    /// not the relation it came from and must never be read as one: it holds
    /// the tuples whose columns were Skolem terms, spread across the arguments
    /// those terms were applied to.
    generated: GeneratedRef,
    /// A relation the fold defines itself, with a meaning of its own rather
    /// than one borrowed from a query or a view.
    auxiliary: Auxiliary,

    pub const ViewRef = struct { id: ViewId, name: syntax.Id, arity: usize };

    /// `origin` is what the split came from and is carried for reading only;
    /// `tag` is what distinguishes one split from another, and it means
    /// nothing outside the plan that handed it out.
    pub const GeneratedRef = struct {
        origin: relation_store.PredicateKey,
        tag: u32,
        arity: usize,
    };

    pub fn arity(self: Predicate) usize {
        return switch (self) {
            .base => |key| key.arity,
            .view => |reference| reference.arity,
            .generated => |reference| reference.arity,
            .auxiliary => |relation| relation.arity(),
        };
    }

    pub fn equals(self: Predicate, other: Predicate) bool {
        return switch (self) {
            .base => |key| switch (other) {
                .base => |other_key| key.name == other_key.name and key.arity == other_key.arity,
                else => false,
            },
            .view => |reference| switch (other) {
                .view => |other_reference| reference.id == other_reference.id,
                else => false,
            },
            .generated => |reference| switch (other) {
                .generated => |other_reference| reference.tag == other_reference.tag and
                    reference.origin.name == other_reference.origin.name and
                    reference.origin.arity == other_reference.origin.arity,
                else => false,
            },
            .auxiliary => |relation| switch (other) {
                .auxiliary => |other_relation| relation == other_relation,
                else => false,
            },
        };
    }
};

/// A relation a fold defines for itself. Unlike a split, it does not stand for
/// part of a relation the query named — it means the same thing in every plan,
/// and the fold supplies the rules that derive it.
pub const Auxiliary = enum {
    /// `member(X, L)`: `X` is one of the values in the list `L`. What reads a
    /// value back out of an aggregate output a view stored.
    member,

    pub fn arity(self: Auxiliary) usize {
        return switch (self) {
            .member => 2,
        };
    }

    /// The spelling it prints and executes under. The `$` is the hygiene rule:
    /// a program cannot name this relation, so a plan defining it cannot
    /// collide with one.
    pub fn text(self: Auxiliary) []const u8 {
        return switch (self) {
            .member => "$member",
        };
    }
};

/// Whether a goal is one the caller wrote or one a fold introduced. Recorded
/// so a rendered plan says which of its goals it invented.
pub const Provenance = enum { source, generated };

pub const Relation = struct {
    predicate: Predicate,
    terms: []Term,
    negated: bool = false,
    provenance: Provenance = .source,
};

/// A comparison, equality or arithmetic goal. `operator` is the executable
/// language's, because a fold neither adds operators nor changes what they
/// mean; the equalities a fold generates differ only in their provenance.
pub const Builtin = struct {
    operator: syntax.GoalKind,
    terms: []Term,
    negated: bool = false,
    provenance: Provenance = .source,
};

pub const Aggregate = struct {
    template: Term,
    body: []Goal,
    output: Term,
    provenance: Provenance = .source,
};

pub const Goal = union(enum) {
    relation: Relation,
    builtin: Builtin,
    aggregate: Aggregate,
};

pub const Rule = struct {
    /// The scope its variables were introduced in. A rule combined with
    /// another must be renamed into a scope of its own first.
    scope: Scope,
    head: Relation,
    body: []Goal,
    /// The head position a seeded structural rule recurses on, carried across
    /// from the executable rule rather than dropped: a fold that inverted such
    /// a rule without knowing what it was would be inverting recursion, which
    /// is the case F5 has to reject.
    seed_argument: ?usize = null,
};

pub fn freeTerm(allocator: std.mem.Allocator, term: Term) void {
    switch (term) {
        .cons => |pair| {
            freeTerm(allocator, pair.head);
            freeTerm(allocator, pair.tail);
            allocator.destroy(pair);
        },
        .skolem => |call| {
            freeTerms(allocator, call.arguments);
            allocator.destroy(call);
        },
        else => {},
    }
}

pub fn freeTerms(allocator: std.mem.Allocator, terms: []Term) void {
    for (terms) |term| freeTerm(allocator, term);
    allocator.free(terms);
}

pub fn freeGoal(allocator: std.mem.Allocator, goal: Goal) void {
    switch (goal) {
        .relation => |relation| freeTerms(allocator, relation.terms),
        .builtin => |builtin| freeTerms(allocator, builtin.terms),
        .aggregate => |aggregate| {
            freeTerm(allocator, aggregate.template);
            freeTerm(allocator, aggregate.output);
            freeGoals(allocator, aggregate.body);
        },
    }
}

pub fn freeGoals(allocator: std.mem.Allocator, goals: []Goal) void {
    for (goals) |goal| freeGoal(allocator, goal);
    allocator.free(goals);
}

pub fn freeRule(allocator: std.mem.Allocator, rule: Rule) void {
    freeTerms(allocator, rule.head.terms);
    freeGoals(allocator, rule.body);
}

pub fn cloneTerm(allocator: std.mem.Allocator, term: Term) std.mem.Allocator.Error!Term {
    return switch (term) {
        .cons => |pair| blk: {
            const copy = try allocator.create(Term.Cons);
            errdefer allocator.destroy(copy);
            copy.head = try cloneTerm(allocator, pair.head);
            errdefer freeTerm(allocator, copy.head);
            copy.tail = try cloneTerm(allocator, pair.tail);
            break :blk .{ .cons = copy };
        },
        .skolem => |call| blk: {
            const copy = try allocator.create(Term.Skolem);
            errdefer allocator.destroy(copy);
            copy.function = call.function;
            copy.arguments = try cloneTerms(allocator, call.arguments);
            break :blk .{ .skolem = copy };
        },
        else => term,
    };
}

pub fn cloneTerms(allocator: std.mem.Allocator, terms: []const Term) ![]Term {
    const copies = try allocator.alloc(Term, terms.len);
    var built: usize = 0;
    errdefer {
        for (copies[0..built]) |term| freeTerm(allocator, term);
        allocator.free(copies);
    }
    for (terms, copies) |term, *slot| {
        slot.* = try cloneTerm(allocator, term);
        built += 1;
    }
    return copies;
}

pub fn cloneRelation(allocator: std.mem.Allocator, relation: Relation) !Relation {
    return .{
        .predicate = relation.predicate,
        .terms = try cloneTerms(allocator, relation.terms),
        .negated = relation.negated,
        .provenance = relation.provenance,
    };
}

pub fn cloneGoal(allocator: std.mem.Allocator, goal: Goal) std.mem.Allocator.Error!Goal {
    return switch (goal) {
        .relation => |relation| .{ .relation = try cloneRelation(allocator, relation) },
        .builtin => |builtin| .{ .builtin = .{
            .operator = builtin.operator,
            .terms = try cloneTerms(allocator, builtin.terms),
            .negated = builtin.negated,
            .provenance = builtin.provenance,
        } },
        .aggregate => |aggregate| blk: {
            const template = try cloneTerm(allocator, aggregate.template);
            errdefer freeTerm(allocator, template);
            const output = try cloneTerm(allocator, aggregate.output);
            errdefer freeTerm(allocator, output);
            break :blk .{ .aggregate = .{
                .template = template,
                .body = try cloneGoals(allocator, aggregate.body),
                .output = output,
                .provenance = aggregate.provenance,
            } };
        },
    };
}

pub fn cloneGoals(allocator: std.mem.Allocator, goals: []const Goal) ![]Goal {
    const copies = try allocator.alloc(Goal, goals.len);
    var built: usize = 0;
    errdefer {
        for (copies[0..built]) |goal| freeGoal(allocator, goal);
        allocator.free(copies);
    }
    for (goals, copies) |goal, *slot| {
        slot.* = try cloneGoal(allocator, goal);
        built += 1;
    }
    return copies;
}

pub fn cloneRule(allocator: std.mem.Allocator, rule: Rule) !Rule {
    const head = try cloneRelation(allocator, rule.head);
    errdefer freeTerms(allocator, head.terms);
    return .{
        .scope = rule.scope,
        .head = head,
        .body = try cloneGoals(allocator, rule.body),
        .seed_argument = rule.seed_argument,
    };
}

/// What to put in place of a variable. The replacements are borrowed: a
/// substitution never owns them, and everything it produces is a fresh copy
/// owned by the caller.
pub const Substitution = struct {
    entries: std.array_hash_map.Auto(Variable, Term) = .empty,

    pub fn deinit(self: *Substitution, allocator: std.mem.Allocator) void {
        self.entries.deinit(allocator);
        self.* = undefined;
    }

    pub fn put(
        self: *Substitution,
        allocator: std.mem.Allocator,
        variable: Variable,
        term: Term,
    ) !void {
        try self.entries.put(allocator, variable, term);
    }

    pub fn get(self: *const Substitution, variable: Variable) ?Term {
        return self.entries.get(variable);
    }

    /// Withdraws a replacement, so that a scope which introduced one can end.
    pub fn remove(self: *Substitution, variable: Variable) void {
        _ = self.entries.swapRemove(variable);
    }
};

pub fn substituteTerm(
    allocator: std.mem.Allocator,
    term: Term,
    substitution: *const Substitution,
) std.mem.Allocator.Error!Term {
    return switch (term) {
        .variable => |variable| if (substitution.get(variable)) |replacement|
            cloneTerm(allocator, replacement)
        else
            term,
        .cons => |pair| blk: {
            const copy = try allocator.create(Term.Cons);
            errdefer allocator.destroy(copy);
            copy.head = try substituteTerm(allocator, pair.head, substitution);
            errdefer freeTerm(allocator, copy.head);
            copy.tail = try substituteTerm(allocator, pair.tail, substitution);
            break :blk .{ .cons = copy };
        },
        .skolem => |call| blk: {
            const copy = try allocator.create(Term.Skolem);
            errdefer allocator.destroy(copy);
            copy.function = call.function;
            copy.arguments = try substituteTerms(allocator, call.arguments, substitution);
            break :blk .{ .skolem = copy };
        },
        else => term,
    };
}

pub fn substituteTerms(
    allocator: std.mem.Allocator,
    terms: []const Term,
    substitution: *const Substitution,
) ![]Term {
    const copies = try allocator.alloc(Term, terms.len);
    var built: usize = 0;
    errdefer {
        for (copies[0..built]) |term| freeTerm(allocator, term);
        allocator.free(copies);
    }
    for (terms, copies) |term, *slot| {
        slot.* = try substituteTerm(allocator, term, substitution);
        built += 1;
    }
    return copies;
}

pub fn substituteGoal(
    allocator: std.mem.Allocator,
    goal: Goal,
    substitution: *const Substitution,
) std.mem.Allocator.Error!Goal {
    return switch (goal) {
        .relation => |relation| .{ .relation = .{
            .predicate = relation.predicate,
            .terms = try substituteTerms(allocator, relation.terms, substitution),
            .negated = relation.negated,
            .provenance = relation.provenance,
        } },
        .builtin => |builtin| .{ .builtin = .{
            .operator = builtin.operator,
            .terms = try substituteTerms(allocator, builtin.terms, substitution),
            .negated = builtin.negated,
            .provenance = builtin.provenance,
        } },
        .aggregate => |aggregate| blk: {
            const template = try substituteTerm(allocator, aggregate.template, substitution);
            errdefer freeTerm(allocator, template);
            const output = try substituteTerm(allocator, aggregate.output, substitution);
            errdefer freeTerm(allocator, output);
            break :blk .{ .aggregate = .{
                .template = template,
                .body = try substituteGoals(allocator, aggregate.body, substitution),
                .output = output,
                .provenance = aggregate.provenance,
            } };
        },
    };
}

pub fn substituteGoals(
    allocator: std.mem.Allocator,
    goals: []const Goal,
    substitution: *const Substitution,
) ![]Goal {
    const copies = try allocator.alloc(Goal, goals.len);
    var built: usize = 0;
    errdefer {
        for (copies[0..built]) |goal| freeGoal(allocator, goal);
        allocator.free(copies);
    }
    for (goals, copies) |goal, *slot| {
        slot.* = try substituteGoal(allocator, goal, substitution);
        built += 1;
    }
    return copies;
}

pub fn substituteRule(
    allocator: std.mem.Allocator,
    rule: Rule,
    substitution: *const Substitution,
) !Rule {
    const terms = try substituteTerms(allocator, rule.head.terms, substitution);
    errdefer freeTerms(allocator, terms);
    return .{
        .scope = rule.scope,
        .head = .{
            .predicate = rule.head.predicate,
            .terms = terms,
            .negated = rule.head.negated,
            .provenance = rule.head.provenance,
        },
        .body = try substituteGoals(allocator, rule.body, substitution),
        .seed_argument = rule.seed_argument,
    };
}

/// A copy of `rule` whose variables are its own: a fresh scope, and one fresh
/// variable per variable the original mentions, so two copies of one view
/// definition can be combined without their variables meeting.
///
/// A user spelling carries across for readability, but never an identity: the
/// copy's `X` is a different variable from the original's, which is what makes
/// this safe when the rule's variables came from more than one scope already.
pub fn renameRule(allocator: std.mem.Allocator, symbols: *Symbols, rule: Rule) !Rule {
    const scope = try symbols.openScope(.generated);
    var substitution: Substitution = .{};
    defer substitution.deinit(symbols.allocator);

    var variables: std.array_hash_map.Auto(Variable, void) = .empty;
    defer variables.deinit(symbols.allocator);
    try collectRelationVariables(symbols.allocator, rule.head, &variables);
    for (rule.body) |goal| try collectGoalVariables(symbols.allocator, goal, &variables);

    for (variables.keys()) |variable| {
        const replacement: Variable = switch (symbols.originOf(variable)) {
            .user => |name| try symbols.freshUserVariable(scope, name),
            .generated => try symbols.freshVariable(scope),
        };
        try substitution.put(symbols.allocator, variable, .{ .variable = replacement });
    }

    var renamed = try substituteRule(allocator, rule, &substitution);
    renamed.scope = scope;
    return renamed;
}

pub fn collectTermVariables(
    allocator: std.mem.Allocator,
    term: Term,
    variables: *std.array_hash_map.Auto(Variable, void),
) std.mem.Allocator.Error!void {
    switch (term) {
        .variable => |variable| try variables.put(allocator, variable, {}),
        .cons => |pair| {
            try collectTermVariables(allocator, pair.head, variables);
            try collectTermVariables(allocator, pair.tail, variables);
        },
        .skolem => |call| for (call.arguments) |argument|
            try collectTermVariables(allocator, argument, variables),
        else => {},
    }
}

pub fn collectRelationVariables(
    allocator: std.mem.Allocator,
    relation: Relation,
    variables: *std.array_hash_map.Auto(Variable, void),
) !void {
    for (relation.terms) |term| try collectTermVariables(allocator, term, variables);
}

pub fn collectGoalVariables(
    allocator: std.mem.Allocator,
    goal: Goal,
    variables: *std.array_hash_map.Auto(Variable, void),
) std.mem.Allocator.Error!void {
    switch (goal) {
        .relation => |relation| try collectRelationVariables(allocator, relation, variables),
        .builtin => |builtin| for (builtin.terms) |term|
            try collectTermVariables(allocator, term, variables),
        .aggregate => |aggregate| {
            try collectTermVariables(allocator, aggregate.template, variables);
            try collectTermVariables(allocator, aggregate.output, variables);
            for (aggregate.body) |inner| try collectGoalVariables(allocator, inner, variables);
        },
    }
}

/// Lowers an admitted rule into a scope of its own.
///
/// Every relational goal becomes a *base* predicate: pointing a goal at a view
/// is the catalog's business and inventing symbols is the folder's, so lowering
/// only translates. There is deliberately no inverse of this function.
pub fn lowerRule(
    allocator: std.mem.Allocator,
    symbols: *Symbols,
    scope: Scope,
    rule: syntax.Rule,
) !Rule {
    const head = try lowerExpr(allocator, symbols, scope, rule.head);
    errdefer freeTerms(allocator, head.terms);
    return .{
        .scope = scope,
        .head = head,
        .body = try lowerClauses(allocator, symbols, scope, rule.body),
        .seed_argument = rule.seed_argument,
    };
}

pub fn lowerClauses(
    allocator: std.mem.Allocator,
    symbols: *Symbols,
    scope: Scope,
    clauses: []const syntax.Clause,
) ![]Goal {
    const goals = try allocator.alloc(Goal, clauses.len);
    var built: usize = 0;
    errdefer {
        for (goals[0..built]) |goal| freeGoal(allocator, goal);
        allocator.free(goals);
    }
    for (clauses, goals) |clause, *slot| {
        slot.* = try lowerClause(allocator, symbols, scope, clause);
        built += 1;
    }
    return goals;
}

pub fn lowerClause(
    allocator: std.mem.Allocator,
    symbols: *Symbols,
    scope: Scope,
    clause: syntax.Clause,
) std.mem.Allocator.Error!Goal {
    return switch (clause) {
        .relational => |expression| .{ .relation = try lowerExpr(allocator, symbols, scope, expression) },
        .negated => |expression| blk: {
            var relation = try lowerExpr(allocator, symbols, scope, expression);
            relation.negated = true;
            break :blk .{ .relation = relation };
        },
        .builtin => |expression| .{ .builtin = .{
            .operator = expression.kind,
            .terms = try lowerTerms(allocator, symbols, scope, expression.terms),
            .negated = expression.negated,
        } },
        .aggregate => |aggregate| blk: {
            const template = try lowerTerm(allocator, symbols, scope, aggregate.template);
            errdefer freeTerm(allocator, template);
            const output = try lowerTerm(allocator, symbols, scope, aggregate.output);
            errdefer freeTerm(allocator, output);
            break :blk .{ .aggregate = .{
                .template = template,
                .body = try lowerClauses(allocator, symbols, scope, aggregate.body),
                .output = output,
            } };
        },
    };
}

fn lowerExpr(
    allocator: std.mem.Allocator,
    symbols: *Symbols,
    scope: Scope,
    expression: syntax.Expr,
) !Relation {
    return .{
        .predicate = .{ .base = syntax.predicateKey(expression) },
        .terms = try lowerTerms(allocator, symbols, scope, expression.terms),
    };
}

fn lowerTerms(
    allocator: std.mem.Allocator,
    symbols: *Symbols,
    scope: Scope,
    terms: []const syntax.Term,
) ![]Term {
    const lowered = try allocator.alloc(Term, terms.len);
    var built: usize = 0;
    errdefer {
        for (lowered[0..built]) |term| freeTerm(allocator, term);
        allocator.free(lowered);
    }
    for (terms, lowered) |term, *slot| {
        slot.* = try lowerTerm(allocator, symbols, scope, term);
        built += 1;
    }
    return lowered;
}

pub fn lowerTerm(
    allocator: std.mem.Allocator,
    symbols: *Symbols,
    scope: Scope,
    term: syntax.Term,
) std.mem.Allocator.Error!Term {
    return switch (term) {
        .scalar => |value| .{ .constant = value },
        .variable => |name| .{ .variable = try symbols.userVariable(scope, name) },
        .nil => .nil,
        .cons => |pair| blk: {
            const copy = try allocator.create(Term.Cons);
            errdefer allocator.destroy(copy);
            copy.head = try lowerTerm(allocator, symbols, scope, pair.head);
            errdefer freeTerm(allocator, copy.head);
            copy.tail = try lowerTerm(allocator, symbols, scope, pair.tail);
            break :blk .{ .cons = copy };
        },
    };
}

/// The tables an IR fragment's identifiers resolve against: the ones of the
/// database it was lowered from, plus the symbol table it was built with.
pub const Names = struct {
    symbols: *const Symbols,
    strings: *const string_table.StringTable,
    scalars: *const scalar.Store,
};

/// Whether `text` could be a name in user source.
///
/// Every symbol this module generates is printed so that this is false of it,
/// which is the second half of the hygiene rule: identities already cannot
/// collide, and a rendered plan additionally cannot be mistaken for a program
/// somebody wrote.
pub fn isUserSpellable(text: []const u8) bool {
    if (text.len == 0) return false;
    for (text) |character| {
        if (!std.ascii.isAlphanumeric(character) and character != '_') return false;
    }
    return true;
}

pub fn writeVariable(
    writer: *std.Io.Writer,
    names: Names,
    variable: Variable,
) std.Io.Writer.Error!void {
    return writeVariableName(writer, names.symbols, names.strings, variable);
}

/// A variable's spelling: its printed name and its identity together.
///
/// Kept separate from the renderer because a plan proved runnable is lowered
/// back into the executable language, and the name a variable runs under has
/// to be the name it reads under. Two variables printing alike would be one
/// variable to whoever reads the plan, and one variable to whatever runs it;
/// dropping the identity is exactly how that happens.
pub fn writeVariableName(
    writer: *std.Io.Writer,
    symbols: *const Symbols,
    strings: *const string_table.StringTable,
    variable: Variable,
) std.Io.Writer.Error!void {
    switch (symbols.originOf(variable)) {
        .user => |name| try writer.print("{s}#{d}", .{
            strings.resolve(name),
            @intFromEnum(variable),
        }),
        .generated => try writer.print("$V{d}", .{@intFromEnum(variable)}),
    }
}

pub fn writeTerm(writer: *std.Io.Writer, names: Names, term: Term) std.Io.Writer.Error!void {
    switch (term) {
        .constant => |value| names.scalars.write(writer, value) catch return error.WriteFailed,
        .variable => |variable| try writeVariable(writer, names, variable),
        .nil => try writer.writeAll("[]"),
        .cons => try writeList(writer, names, term),
        .skolem => |call| {
            try writer.print("$f{d}(", .{@intFromEnum(call.function)});
            for (call.arguments, 0..) |argument, index| {
                if (index != 0) try writer.writeAll(", ");
                try writeTerm(writer, names, argument);
            }
            try writer.writeByte(')');
        },
    }
}

/// Renders a list the way the language spells one: `[a, b]` when it ends in
/// `nil`, and `[a, b!T]` when its tail is anything else.
fn writeList(writer: *std.Io.Writer, names: Names, term: Term) std.Io.Writer.Error!void {
    try writer.writeByte('[');
    var current = term;
    var first = true;
    while (current == .cons) {
        if (!first) try writer.writeAll(", ");
        try writeTerm(writer, names, current.cons.head);
        current = current.cons.tail;
        first = false;
    }
    if (current != .nil) {
        try writer.writeByte('!');
        try writeTerm(writer, names, current);
    }
    try writer.writeByte(']');
}

pub fn writePredicate(
    writer: *std.Io.Writer,
    names: Names,
    predicate: Predicate,
) std.Io.Writer.Error!void {
    switch (predicate) {
        .base => |key| try writer.writeAll(names.strings.resolve(key.name)),
        .view => |reference| try writer.print("{s}@{d}", .{
            names.strings.resolve(reference.name),
            @intFromEnum(reference.id),
        }),
        .generated => |reference| try writer.print("{s}${d}", .{
            names.strings.resolve(reference.origin.name),
            reference.tag,
        }),
        .auxiliary => |relation| try writer.writeAll(relation.text()),
    }
}

pub fn writeRelation(
    writer: *std.Io.Writer,
    names: Names,
    relation: Relation,
) std.Io.Writer.Error!void {
    if (relation.negated) try writer.writeAll("not ");
    try writePredicate(writer, names, relation.predicate);
    try writer.writeByte('(');
    for (relation.terms, 0..) |term, index| {
        if (index != 0) try writer.writeAll(", ");
        try writeTerm(writer, names, term);
    }
    try writer.writeByte(')');
}

pub fn writeGoal(writer: *std.Io.Writer, names: Names, goal: Goal) std.Io.Writer.Error!void {
    switch (goal) {
        .relation => |relation| {
            try writeRelation(writer, names, relation);
            try writeProvenance(writer, relation.provenance);
        },
        .builtin => |builtin| {
            try writeBuiltin(writer, names, builtin);
            try writeProvenance(writer, builtin.provenance);
        },
        .aggregate => |aggregate| {
            try writer.writeAll("setof(");
            try writeTerm(writer, names, aggregate.template);
            try writer.writeAll(", (");
            for (aggregate.body, 0..) |inner, index| {
                if (index != 0) try writer.writeAll(", ");
                try writeGoal(writer, names, inner);
            }
            try writer.writeAll("), ");
            try writeTerm(writer, names, aggregate.output);
            try writer.writeByte(')');
            try writeProvenance(writer, aggregate.provenance);
        },
    }
}

/// Arithmetic is written `Z = X + Y`, which is the shape the language stores:
/// the result first, then the two operands.
fn writeBuiltin(
    writer: *std.Io.Writer,
    names: Names,
    builtin: Builtin,
) std.Io.Writer.Error!void {
    if (builtin.negated) try writer.writeAll("not ");
    if (builtin.terms.len == 3) {
        try writeTerm(writer, names, builtin.terms[0]);
        try writer.writeAll(" = ");
        try writeTerm(writer, names, builtin.terms[1]);
        try writer.print(" {s} ", .{syntax.goalOperator(builtin.operator)});
        try writeTerm(writer, names, builtin.terms[2]);
        return;
    }
    for (builtin.terms, 0..) |term, index| {
        if (index != 0) try writer.print(" {s} ", .{syntax.goalOperator(builtin.operator)});
        try writeTerm(writer, names, term);
    }
}

/// A goal a fold invented is marked with a source comment, so a rendering
/// reads as the program it stands for and still says which goals were not
/// written by anybody.
fn writeProvenance(writer: *std.Io.Writer, provenance: Provenance) std.Io.Writer.Error!void {
    if (provenance == .generated) try writer.writeAll(" % generated");
}

pub fn writeRule(writer: *std.Io.Writer, names: Names, rule: Rule) std.Io.Writer.Error!void {
    try writeRelation(writer, names, rule.head);
    try writer.writeAll(" :- ");
    for (rule.body, 0..) |goal, index| {
        if (index != 0) try writer.writeAll(", ");
        try writeGoal(writer, names, goal);
    }
    try writer.writeByte('.');
}

const testing = std.testing;

/// The tables a rendering resolves against, built for one test.
const Tables = struct {
    strings: string_table.StringTable,
    scalars: scalar.Store,
    symbols: Symbols,

    fn init(allocator: std.mem.Allocator) Tables {
        return .{
            .strings = .init(allocator),
            .scalars = .init(allocator),
            .symbols = .init(allocator),
        };
    }

    fn deinit(self: *Tables) void {
        self.symbols.deinit();
        self.scalars.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    fn names(self: *const Tables) Names {
        return .{ .symbols = &self.symbols, .strings = &self.strings, .scalars = &self.scalars };
    }
};

fn renderGoal(allocator: std.mem.Allocator, names: Names, goal: Goal) ![]u8 {
    var text: std.Io.Writer.Allocating = .init(allocator);
    defer text.deinit();
    writeGoal(&text.writer, names, goal) catch return error.OutOfMemory;
    return text.toOwnedSlice();
}

test "a variable's identity is its entry, not its spelling" {
    var tables: Tables = .init(testing.allocator);
    defer tables.deinit();
    const name = try tables.strings.intern("X");

    const query = try tables.symbols.openScope(.query);
    const definition = try tables.symbols.openScope(.view_definition);

    // One spelling in one scope is one variable, however often it occurs.
    const first = try tables.symbols.userVariable(query, name);
    try testing.expectEqual(first, try tables.symbols.userVariable(query, name));

    // The same spelling in another scope, a fresh copy of it, and a generated
    // variable are three further variables, none equal to it or each other.
    const elsewhere = try tables.symbols.userVariable(definition, name);
    const renamed = try tables.symbols.freshUserVariable(query, name);
    const generated = try tables.symbols.freshVariable(query);
    try testing.expect(first != elsewhere);
    try testing.expect(first != renamed);
    try testing.expect(elsewhere != renamed);
    try testing.expect(generated != first);

    try testing.expectEqual(query, tables.symbols.scopeOf(first));
    try testing.expectEqual(definition, tables.symbols.scopeOf(elsewhere));
    try testing.expectEqual(Symbols.Purpose.view_definition, tables.symbols.purposeOf(definition));

    // Every one of them renders differently, and no generated spelling could
    // have come from a program: identities cannot collide, and neither can
    // what they print as.
    var printed: [4][]u8 = undefined;
    var written: usize = 0;
    defer for (printed[0..written]) |text| testing.allocator.free(text);
    for ([_]Variable{ first, elsewhere, renamed, generated }, &printed) |variable, *slot| {
        var terms = [_]Term{ .{ .variable = variable }, .nil };
        const goal: Goal = .{ .builtin = .{ .operator = .equality, .terms = &terms } };
        const rendered = try renderGoal(testing.allocator, tables.names(), goal);
        slot.* = rendered;
        written += 1;
        const name_end = std.mem.indexOfScalar(u8, rendered, ' ') orelse rendered.len;
        try testing.expect(!isUserSpellable(rendered[0..name_end]));
    }
    for (printed, 0..) |text, index| for (printed[index + 1 ..]) |other| {
        try testing.expect(!std.mem.eql(u8, text, other));
    };
}

test "cloning, substituting and renaming preserve structure, scope and ownership" {
    var tables: Tables = .init(testing.allocator);
    defer tables.deinit();
    const allocator = testing.allocator;
    const path = try tables.strings.intern("path");
    const edge = try tables.strings.intern("edge");
    const x_name = try tables.strings.intern("X");
    const y_name = try tables.strings.intern("Y");

    // path(X, Y) :- edge(X, $f0(X, Y)), Y = $f0(X, Y).
    const scope = try tables.symbols.openScope(.view_definition);
    const x = try tables.symbols.userVariable(scope, x_name);
    const y = try tables.symbols.userVariable(scope, y_name);
    const function = try tables.symbols.freshFunction(scope);

    const skolem = try allocator.create(Term.Skolem);
    skolem.* = .{
        .function = function,
        .arguments = try allocator.dupe(Term, &.{ .{ .variable = x }, .{ .variable = y } }),
    };
    const rule: Rule = .{
        .scope = scope,
        .head = .{
            .predicate = .{ .base = .{ .name = path, .arity = 2 } },
            .terms = try allocator.dupe(Term, &.{ .{ .variable = x }, .{ .variable = y } }),
        },
        .body = try allocator.dupe(Goal, &.{
            .{ .relation = .{
                .predicate = .{ .base = .{ .name = edge, .arity = 2 } },
                .terms = try allocator.dupe(Term, &.{ .{ .variable = x }, .{ .skolem = skolem } }),
            } },
            .{ .builtin = .{
                .operator = .equality,
                .terms = try allocator.dupe(Term, &.{ .{ .variable = y }, .{ .variable = x } }),
                .provenance = .generated,
            } },
        }),
    };
    defer freeRule(allocator, rule);

    // A clone is the same rule down to every identity, and owns its own
    // structure: freeing it leaves the original intact for the renderer below.
    const copy = try cloneRule(allocator, rule);
    try testing.expectEqual(rule.scope, copy.scope);
    // A Skolem term is what makes this rule unrunnable, at any depth.
    try testing.expect(copy.body[0].relation.terms[1].containsSkolem());
    try testing.expect(!copy.head.terms[0].containsSkolem());
    try testing.expectEqual(x, copy.body[0].relation.terms[0].variable);
    try testing.expect(copy.body[0].relation.terms[1].skolem != skolem);
    try testing.expectEqual(function, copy.body[0].relation.terms[1].skolem.function);
    freeRule(allocator, copy);

    // Substitution replaces the variables it names, at every depth, and copies
    // rather than aliasing what it puts there.
    var substitution: Substitution = .{};
    defer substitution.deinit(allocator);
    const seven = try tables.scalars.internInteger(7);
    const replacement: Term = .{ .constant = seven };
    try substitution.put(allocator, x, replacement);
    const substituted = try substituteRule(allocator, rule, &substitution);
    defer freeRule(allocator, substituted);
    try testing.expectEqual(seven, substituted.head.terms[0].constant);
    try testing.expectEqual(y, substituted.head.terms[1].variable);
    try testing.expectEqual(
        seven,
        substituted.body[0].relation.terms[1].skolem.arguments[0].constant,
    );

    // Renaming standardizes apart: a scope of its own, no variable in common
    // with the original, and every occurrence of one variable still one
    // variable.
    const renamed = try renameRule(allocator, &tables.symbols, rule);
    defer freeRule(allocator, renamed);
    try testing.expect(renamed.scope != rule.scope);
    const renamed_x = renamed.head.terms[0].variable;
    const renamed_y = renamed.head.terms[1].variable;
    try testing.expect(renamed_x != x);
    try testing.expect(renamed_y != y);
    try testing.expect(renamed_x != renamed_y);
    try testing.expectEqual(renamed_x, renamed.body[0].relation.terms[0].variable);
    try testing.expectEqual(renamed_x, renamed.body[1].builtin.terms[1].variable);
    try testing.expectEqual(renamed.scope, tables.symbols.scopeOf(renamed_x));
    // The spelling carries so a plan stays readable; the identity does not.
    try testing.expectEqual(x_name, tables.symbols.originOf(renamed_x).user);

    // The rendering shows the generated goal, the Skolem term, and the
    // identity behind each spelling.
    var text: std.Io.Writer.Allocating = .init(allocator);
    defer text.deinit();
    try writeRule(&text.writer, tables.names(), rule);
    try testing.expectEqualStrings(
        "path(X#0, Y#1) :- edge(X#0, $f0(X#0, Y#1)), Y#1 = X#0 % generated.",
        text.written(),
    );
}

test "lowering translates an admitted rule and invents nothing" {
    var tables: Tables = .init(testing.allocator);
    defer tables.deinit();
    const allocator = testing.allocator;
    const total = try tables.strings.intern("total");
    const score = try tables.strings.intern("score");
    const x_name = try tables.strings.intern("X");
    const s_name = try tables.strings.intern("S");

    // total(X, S) :- setof(V, score(X, V), S).
    var inner_terms = [_]syntax.Term{ .{ .variable = x_name }, .{ .variable = s_name } };
    var aggregate_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = score, .terms = &inner_terms } },
    };
    var head_terms = [_]syntax.Term{ .{ .variable = x_name }, .{ .variable = s_name } };
    var body = [_]syntax.Clause{.{ .aggregate = .{
        .template = .{ .variable = s_name },
        .body = &aggregate_body,
        .output = .{ .variable = s_name },
    } }};
    const source: syntax.Rule = .{
        .head = .{ .predicate = total, .terms = &head_terms },
        .body = &body,
    };

    const scope = try tables.symbols.openScope(.view_definition);
    var lowered = try lowerRule(allocator, &tables.symbols, scope, source);
    defer freeRule(allocator, lowered);

    // Lowering names relations as base relations and nothing else, and the
    // spelling shared across the head and the aggregate is one variable.
    try testing.expect(lowered.head.predicate.equals(.{ .base = .{ .name = total, .arity = 2 } }));
    const inner = lowered.body[0].aggregate.body[0].relation;
    try testing.expect(inner.predicate.equals(.{ .base = .{ .name = score, .arity = 2 } }));
    try testing.expectEqual(lowered.head.terms[0].variable, inner.terms[0].variable);
    try testing.expectEqual(lowered.head.terms[1].variable, lowered.body[0].aggregate.output.variable);
    try testing.expectEqual(Provenance.source, lowered.body[0].aggregate.provenance);
}
