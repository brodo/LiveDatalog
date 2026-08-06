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

pub const Goal = union(enum) {
    relation: Relation,
    negation: Relation,
    equality: Binary,
    inequality: Binary,
    comparison: struct { kind: Comparison, operands: Binary },
    arithmetic: struct { kind: Arithmetic, output: Term, left: Term, right: Term },
    aggregate: struct { template: Term, body: []const Goal, output: Term },
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

pub fn not(predicate: []const u8, terms: []const Term) Goal {
    return .{ .negation = .{ .predicate = predicate, .terms = terms } };
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
