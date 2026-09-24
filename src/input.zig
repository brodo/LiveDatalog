//! Allocation-free borrowed descriptors for the public embedding interface.

pub const Term = union(enum) {
    atom: []const u8,
    integer: i64,
    float: f64,
    variable: []const u8,
    list: []const Term,
    cons: *const Cons,

    pub const Cons = struct {
        head: *const Term,
        tail: *const Term,
    };
};

pub const Comparison = enum { less_than, less_or_equal, greater_than, greater_or_equal };
pub const Arithmetic = enum { add, subtract };

pub const Relation = struct {
    predicate: []const u8,
    terms: []const Term,
};

pub const Binary = struct {
    left: Term,
    right: Term,
};

/// One rule of a query program handed to a fold.
///
/// A fold's input is the goals to answer *and* the rules the query defines its
/// own predicates by, because a folded plan is the query's program together
/// with the inverse rules of the views it needs. This is that half of the
/// input, in the same borrowed descriptors everything else here uses. It is
/// not how a rule is added to the database — `addRule` is — because a query's
/// rules are part of one question rather than part of the program.
pub const Rule = struct {
    head: Relation,
    body: []const Goal,
};

pub const ComparisonGoal = struct { kind: Comparison, operands: Binary };

/// A built-in test under `not`, as in `not X < Y` or `not X = Y`. Only tests
/// can be negated: arithmetic binds its output, and a negated goal binds
/// nothing.
pub const NegatedBuiltin = union(enum) {
    equality: Binary,
    inequality: Binary,
    comparison: ComparisonGoal,
};

pub const Goal = union(enum) {
    relation: Relation,
    negation: Relation,
    negated_builtin: NegatedBuiltin,
    equality: Binary,
    inequality: Binary,
    comparison: ComparisonGoal,
    arithmetic: struct { kind: Arithmetic, output: Term, left: Term, right: Term },
    aggregate: struct { template: Term, body: []const Goal, output: Term },
};

/// One top-level item of a program: what a parsed program is a sequence of,
/// and what `Jatalog.executeStatements` runs. See "Statement" in CONTEXT.md.
pub const Statement = union(enum) {
    /// `p(a).` — asserts one ground base fact.
    fact: Relation,
    /// `h :- b.` — adds a rule to the program.
    rule: Rule,
    /// `b?` — answers the goals.
    query: []const Goal,
    /// `b~` — removes every base fact the goals' relational goals match.
    retraction: []const Goal,
};

pub fn atom(value: []const u8) Term {
    return .{ .atom = value };
}

pub fn integer(value: i64) Term {
    return .{ .integer = value };
}

pub fn float(value: f64) Term {
    return .{ .float = value };
}

pub fn variable(name: []const u8) Term {
    return .{ .variable = name };
}

pub fn list(items: []const Term) Term {
    return .{ .list = items };
}

pub fn cons(pair: *const Term.Cons) Term {
    return .{ .cons = pair };
}

pub fn relation(predicate: []const u8, terms: []const Term) Goal {
    return .{ .relation = .{ .predicate = predicate, .terms = terms } };
}

/// Describes one ground fact for the batch-update interface.
pub fn fact(predicate: []const u8, terms: []const Term) Relation {
    return .{ .predicate = predicate, .terms = terms };
}

/// Describes one rule of a query program for the folding interface.
pub fn rule(head: Relation, body: []const Goal) Rule {
    return .{ .head = head, .body = body };
}

pub fn not(predicate: []const u8, terms: []const Term) Goal {
    return .{ .negation = .{ .predicate = predicate, .terms = terms } };
}

/// `not` applied to a built-in test: `notBuiltin(.{ .comparison = ... })`.
pub fn notBuiltin(builtin: NegatedBuiltin) Goal {
    return .{ .negated_builtin = builtin };
}

pub fn equal(left: Term, right: Term) Goal {
    return .{ .equality = .{ .left = left, .right = right } };
}

pub fn notEqual(left: Term, right: Term) Goal {
    return .{ .inequality = .{ .left = left, .right = right } };
}

pub fn compare(kind: Comparison, left: Term, right: Term) Goal {
    return .{ .comparison = .{ .kind = kind, .operands = .{ .left = left, .right = right } } };
}

pub fn lessThan(left: Term, right: Term) Goal {
    return compare(.less_than, left, right);
}

pub fn lessOrEqual(left: Term, right: Term) Goal {
    return compare(.less_or_equal, left, right);
}

pub fn greaterThan(left: Term, right: Term) Goal {
    return compare(.greater_than, left, right);
}

pub fn greaterOrEqual(left: Term, right: Term) Goal {
    return compare(.greater_or_equal, left, right);
}

pub fn add(output: Term, left: Term, right: Term) Goal {
    return .{ .arithmetic = .{ .kind = .add, .output = output, .left = left, .right = right } };
}

pub fn subtract(output: Term, left: Term, right: Term) Goal {
    return .{ .arithmetic = .{ .kind = .subtract, .output = output, .left = left, .right = right } };
}

pub fn setof(template: Term, body: []const Goal, output: Term) Goal {
    return .{ .aggregate = .{ .template = template, .body = body, .output = output } };
}
