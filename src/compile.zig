//! Turning input into stored syntax: symbol interning, typed descriptors, and
//! the ground structures a statement mentions.
//!
//! Compilation always runs against whichever database it is pointed at, which
//! is what keeps a statement's query-local symbols and structures out of the
//! committed database — the statement transaction points it at a staging copy
//! and discards that copy unless the statement commits.

const std = @import("std");
const root = @import("root.zig");
const syntax = @import("syntax.zig");
const input = root.input;
const input_compiler = @import("input_compiler.zig");

const Jatalog = root.Jatalog;
const Id = syntax.Id;
const Term = syntax.Term;
const Expr = syntax.Expr;
const Clause = syntax.Clause;
const GoalKind = syntax.GoalKind;
const freeClauseTree = syntax.freeClauseTree;
const goalOperator = syntax.goalOperator;
const freeTerm = syntax.freeTerm;

/// Interns predicate and variable symbols used by a database. IDs are
/// insertion indexes, which makes `resolve` a reverse lookup into the ordered
/// keys of the same StringArrayHashMapUnmanaged.
pub const StringTable = struct {
    allocator: std.mem.Allocator,
    strings: std.StringArrayHashMapUnmanaged(Id) = .empty,

    pub fn init(allocator: std.mem.Allocator) StringTable {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *StringTable) void {
        for (self.strings.keys()) |string| self.allocator.free(string);
        self.strings.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const StringTable) !StringTable {
        var result: StringTable = .init(self.allocator);
        errdefer result.deinit();
        for (self.strings.keys()) |string| _ = try result.intern(string);
        return result;
    }

    pub fn intern(self: *StringTable, string: []const u8) !Id {
        if (self.strings.get(string)) |id| return id;
        const owned = try self.allocator.dupe(u8, string);
        errdefer self.allocator.free(owned);
        const id: Id = @intCast(self.strings.count());
        try self.strings.putNoClobber(self.allocator, owned, id);
        return id;
    }

    pub fn get(self: *const StringTable, string: []const u8) ?Id {
        return self.strings.get(string);
    }

    pub fn resolve(self: *const StringTable, id: Id) []const u8 {
        return self.strings.keys()[@intCast(id)];
    }
};
pub const InputBuilder = struct {
    database: *Jatalog,

    pub fn allocator(self: *InputBuilder) std.mem.Allocator {
        return self.database.allocator;
    }

    pub fn nilTerm(_: *InputBuilder) Term { // ziglint-ignore: Z012
        return .nil;
    }

    pub fn atomTerm(self: *InputBuilder, atom: []const u8) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.eval.scalars.internAtom(atom) };
    }

    pub fn integerTerm(self: *InputBuilder, integer: i64) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.eval.scalars.internInteger(integer) };
    }

    pub fn floatTerm(self: *InputBuilder, float: f64) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.eval.scalars.internFloat(float) };
    }

    pub fn variableTerm(self: *InputBuilder, name: []const u8) !Term { // ziglint-ignore: Z012
        return .{ .variable = try self.database.strings.intern(name) };
    }

    pub fn consTerm(self: *InputBuilder, head: Term, tail: Term) !Term { // ziglint-ignore: Z012
        const pair = try self.database.allocator.create(Term.Cons);
        pair.* = .{ .head = head, .tail = tail };
        return .{ .cons = pair };
    }

    pub fn releaseTerm(self: *InputBuilder, term: Term) void { // ziglint-ignore: Z012
        freeTerm(self.database.allocator, term);
    }
};

pub fn compileRelation(
    db: *Jatalog,
    predicate: []const u8,
    descriptors: []const input.Term,
    negated: bool,
) !Expr {
    if (predicate.len == 0) return error.InvalidTerm;
    var builder: InputBuilder = .{ .database = db };
    return .{
        .predicate = try db.strings.intern(predicate),
        .terms = try input_compiler.compileTerms(&builder, descriptors),
        .negated = negated,
    };
}
pub fn compileGoals(db: *Jatalog, descriptors: []const input.Goal) anyerror![]Clause {
    try input_compiler.validateGoals(db.allocator, descriptors);
    return compileGoalsValidated(db, descriptors);
}
pub fn compileGoalsValidated(db: *Jatalog, descriptors: []const input.Goal) anyerror![]Clause {
    const clauses = try db.allocator.alloc(Clause, descriptors.len);
    var initialized: usize = 0;
    errdefer {
        for (clauses[0..initialized]) |clause| freeClauseTree(db.allocator, clause);
        db.allocator.free(clauses);
    }
    for (descriptors, clauses) |descriptor, *clause| {
        clause.* = try compileGoalValidated(db, descriptor);
        initialized += 1;
    }
    return clauses;
}
fn compileGoalValidated(db: *Jatalog, descriptor: input.Goal) anyerror!Clause {
    return switch (descriptor) {
        .relation => |relation| .{
            .relational = try compileRelation(db, relation.predicate, relation.terms, false),
        },
        .negation => |relation| .{ .negated = try compileRelation(db, relation.predicate, relation.terms, true) },
        .equality => |binary| .{ .builtin = try compileBuiltin(db, .equality, &.{ binary.left, binary.right }) },
        .inequality => |binary| .{
            .builtin = try compileBuiltin(db, .inequality, &.{ binary.left, binary.right }),
        },
        .comparison => |comparison| .{ .builtin = try compileBuiltin(db, switch (comparison.kind) {
            .less_than => .less_than,
            .less_or_equal => .less_or_equal,
            .greater_than => .greater_than,
            .greater_or_equal => .greater_or_equal,
        }, &.{ comparison.operands.left, comparison.operands.right }) },
        .arithmetic => |arithmetic| .{ .builtin = try compileBuiltin(db, switch (arithmetic.kind) {
            .add => .add,
            .subtract => .subtract,
        }, &.{ arithmetic.output, arithmetic.left, arithmetic.right }) },
        .aggregate => |aggregate| blk: {
            var builder: InputBuilder = .{ .database = db };
            const template = try input_compiler.compileTerm(&builder, aggregate.template);
            errdefer freeTerm(db.allocator, template);
            const output = try input_compiler.compileTerm(&builder, aggregate.output);
            errdefer freeTerm(db.allocator, output);
            const body = try compileGoalsValidated(db, aggregate.body);
            break :blk .{ .aggregate = .{ .template = template, .body = body, .output = output } };
        },
    };
}
pub fn compileBuiltin(db: *Jatalog, kind: GoalKind, terms: []const input.Term) !Expr {
    var result = try compileRelation(db, goalOperator(kind), terms, false);
    result.kind = kind;
    return result;
}
pub fn internGroundStructuresInExpr(db: *Jatalog, expression: Expr) !void {
    for (expression.terms) |term| try internGroundStructuresInTerm(db, term);
}
pub fn internGroundStructuresInClause(db: *Jatalog, clause: Clause) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| try internGroundStructuresInExpr(db, expression),
        .aggregate => |aggregate| {
            try internGroundStructuresInTerm(db, aggregate.template);
            for (aggregate.body) |body_clause|
                try internGroundStructuresInClause(db, body_clause);
            try internGroundStructuresInTerm(db, aggregate.output);
        },
    }
}
fn internGroundStructuresInTerm(db: *Jatalog, term: Term) !void {
    switch (term) {
        .nil => _ = try db.eval.termToValue(term, null),
        .cons => |pair| {
            if (term.isGround()) {
                _ = try db.eval.termToValue(term, null);
                return;
            }
            try internGroundStructuresInTerm(db, pair.head);
            try internGroundStructuresInTerm(db, pair.tail);
        },
        .scalar, .variable => {},
    }
}
