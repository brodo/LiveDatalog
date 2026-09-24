//! the ground structures a statement mentions.
//!
//! Compilation always runs against whichever database it is pointed at, which
//! is what keeps a statement's query-local symbols and structures out of the
//! committed database — the statement transaction points it at a staging copy
//! and discards that copy unless the statement commits.

const std = @import("std");
const database = @import("database.zig");
const input = @import("input.zig");
const syntax = @import("syntax.zig");
const input_compiler = @import("input_compiler.zig");
const schema = @import("schema.zig");

pub const InputBuilder = struct {
    database: *database.Database,

    pub fn allocator(self: *InputBuilder) std.mem.Allocator {
        return self.database.allocator;
    }

    pub fn nilTerm(_: *InputBuilder) syntax.Term { // ziglint-ignore: Z012
        return .nil;
    }

    pub fn atomTerm(self: *InputBuilder, atom: []const u8) !syntax.Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.eval.scalars.internAtom(atom) };
    }

    pub fn integerTerm(self: *InputBuilder, integer: i64) !syntax.Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.eval.scalars.internInteger(integer) };
    }

    pub fn floatTerm(self: *InputBuilder, float: f64) !syntax.Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.eval.scalars.internFloat(float) };
    }

    pub fn variableTerm(self: *InputBuilder, name: []const u8) !syntax.Term { // ziglint-ignore: Z012
        return .{ .variable = try self.database.strings.intern(name) };
    }

    pub fn consTerm(self: *InputBuilder, head: syntax.Term, tail: syntax.Term) !syntax.Term { // ziglint-ignore: Z012
        const pair = try self.database.allocator.create(syntax.Term.Cons);
        pair.* = .{ .head = head, .tail = tail };
        return .{ .cons = pair };
    }

    pub fn releaseTerm(self: *InputBuilder, term: syntax.Term) void { // ziglint-ignore: Z012
        syntax.freeTerm(self.database.allocator, term);
    }
};

pub fn compileRelation(
    db: *database.Database,
    predicate: []const u8,
    descriptors: []const input.Term,
    negated: bool,
) !syntax.Expr {
    if (predicate.len == 0) return error.InvalidTerm;
    var builder: InputBuilder = .{ .database = db };
    return .{
        .predicate = try db.strings.intern(predicate),
        .terms = try input_compiler.compileTerms(&builder, descriptors),
        .negated = negated,
    };
}
pub fn compileGoals(db: *database.Database, descriptors: []const input.Goal) anyerror![]syntax.Clause {
    try input_compiler.validateGoals(db.allocator, descriptors);
    return compileGoalsValidated(db, descriptors);
}
pub fn compileGoalsValidated(db: *database.Database, descriptors: []const input.Goal) anyerror![]syntax.Clause {
    const clauses = try db.allocator.alloc(syntax.Clause, descriptors.len);
    var initialized: usize = 0;
    errdefer {
        for (clauses[0..initialized]) |clause| syntax.freeClauseTree(db.allocator, clause);
        db.allocator.free(clauses);
    }
    for (descriptors, clauses) |descriptor, *clause| {
        clause.* = try compileGoalValidated(db, descriptor);
        initialized += 1;
    }
    return clauses;
}
fn compileGoalValidated(db: *database.Database, descriptor: input.Goal) anyerror!syntax.Clause {
    return switch (descriptor) {
        .relation => |relation| .{
            .relational = try compileRelation(db, relation.predicate, relation.terms, false),
        },
        .negation => |relation| .{ .negated = try compileRelation(db, relation.predicate, relation.terms, true) },
        .equality => |binary| .{ .builtin = try compileBuiltin(db, .equality, &.{ binary.left, binary.right }) },
        .inequality => |binary| .{
            .builtin = try compileBuiltin(db, .inequality, &.{ binary.left, binary.right }),
        },
        .negated_builtin => |builtin| blk: {
            var expression = switch (builtin) {
                .equality => |binary| try compileBuiltin(db, .equality, &.{ binary.left, binary.right }),
                .inequality => |binary| try compileBuiltin(db, .inequality, &.{ binary.left, binary.right }),
                .comparison => |comparison| try compileBuiltin(
                    db,
                    comparisonKind(comparison.kind),
                    &.{ comparison.operands.left, comparison.operands.right },
                ),
                .type_test => |type_test| try compileTypeTest(db, type_test),
            };
            expression.negated = true;
            break :blk .{ .negated = expression };
        },
        .comparison => |comparison| .{ .builtin = try compileBuiltin(
            db,
            comparisonKind(comparison.kind),
            &.{ comparison.operands.left, comparison.operands.right },
        ) },
        .arithmetic => |arithmetic| .{ .builtin = try compileBuiltin(db, switch (arithmetic.kind) {
            .add => .add,
            .subtract => .subtract,
        }, &.{ arithmetic.output, arithmetic.left, arithmetic.right }) },
        .type_test => |type_test| .{ .builtin = try compileTypeTest(db, type_test) },
        .aggregate => |aggregate| blk: {
            var builder: InputBuilder = .{ .database = db };
            const template = try input_compiler.compileTerm(&builder, aggregate.template);
            errdefer syntax.freeTerm(db.allocator, template);
            const output = try input_compiler.compileTerm(&builder, aggregate.output);
            errdefer syntax.freeTerm(db.allocator, output);
            const body = try compileGoalsValidated(db, aggregate.body);
            break :blk .{ .aggregate = .{ .template = template, .body = body, .output = output } };
        },
    };
}
fn comparisonKind(kind: input.Comparison) syntax.GoalKind {
    return switch (kind) {
        .less_than => .less_than,
        .less_or_equal => .less_or_equal,
        .greater_than => .greater_than,
        .greater_or_equal => .greater_or_equal,
    };
}
pub fn compileBuiltin(db: *database.Database, kind: syntax.GoalKind, terms: []const input.Term) !syntax.Expr {
    var result = try compileRelation(db, syntax.goalOperator(kind), terms, false);
    result.kind = kind;
    return result;
}
fn compileTypeTest(db: *database.Database, type_test: input.TypeTest) !syntax.Expr {
    const column_type = try compileColumnType(type_test.type);
    var result = try compileBuiltin(db, .type_test, &.{type_test.term});
    result.column_type = column_type;
    return result;
}

/// Lowers a described column type. One nested too deeply for a type to hold
/// is `InvalidTerm`, as a cyclic one is.
pub fn compileColumnType(descriptor: input.ColumnType) !schema.ColumnType {
    var lists: usize = 0;
    var current = descriptor;
    while (true) switch (current) {
        .list => |element| {
            lists += 1;
            if (lists > std.math.maxInt(u8)) return error.InvalidTerm;
            current = if (element) |inner| inner.* else .any;
        },
        else => break,
    };
    return .{ .lists = @intCast(lists), .element = switch (current) {
        .atom => .atom,
        .int => .int,
        .number => .number,
        .any => .any,
        .list => unreachable,
    } };
}

/// Lowers a schema declaration, interning its column names. The caller owns
/// the result.
pub fn compileSchema(db: *database.Database, descriptor: input.Schema) !schema.Schema {
    if (descriptor.predicate.len == 0) return error.InvalidTerm;
    const columns = try db.allocator.alloc(schema.ColumnType, descriptor.columns.len);
    errdefer db.allocator.free(columns);
    const names = try db.allocator.alloc(?u64, descriptor.columns.len);
    errdefer db.allocator.free(names);
    for (descriptor.columns, columns, names, 0..) |column, *column_type, *name, index| {
        column_type.* = try compileColumnType(column.type);
        name.* = if (column.name) |spelling| blk: {
            if (spelling.len == 0) return error.InvalidTerm;
            for (descriptor.columns[0..index]) |earlier| if (earlier.name) |other|
                if (std.mem.eql(u8, other, spelling)) return error.InvalidTerm;
            break :blk try db.strings.intern(spelling);
        } else null;
    }
    return .{ .columns = columns, .names = names };
}

pub fn internGroundStructuresInExpr(db: *database.Database, expression: syntax.Expr) !void {
    for (expression.terms) |term| try internGroundStructuresInTerm(db, term);
}
pub fn internGroundStructuresInClause(db: *database.Database, clause: syntax.Clause) !void {
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
fn internGroundStructuresInTerm(db: *database.Database, term: syntax.Term) !void {
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
