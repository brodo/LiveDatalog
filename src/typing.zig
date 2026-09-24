//! Static schema checking: the types a rule's variables can take, inferred
//! from its goals, and whether they fit the schemas it reads and derives into.
//! See "Schema" in CONTEXT.md and ADR 0004.
//!
//! A variable's type is the meet of everything its goals say about it: a
//! typed relation's columns, a comparison's `number`, a type test's type. A
//! variable whose type comes out empty makes its goal impossible, which is an
//! error rather than an empty answer. A rule's head must then fit its schema
//! on every binding the body can produce, which is what lets the database
//! skip checking the facts a rule derives.
//!
//! What a negated goal says is not a fact about any binding that passes it,
//! so negation narrows nothing. And an untyped predicate's values are `any`,
//! whatever its rules happen to produce.
//!
//! Goals that touch no typed predicate are not checked at all, so a program
//! without schemas behaves exactly as it did before schemas existed: a
//! comparison against an atom is still the runtime `NumericType` it always
//! was, not an `IllTyped` found by reading the literal.

const std = @import("std");
const database = @import("database.zig");
const scalar = @import("scalar.zig");
const schema = @import("schema.zig");
const syntax = @import("syntax.zig");
const errors = @import("errors.zig");

const ColumnType = schema.ColumnType;
const Env = std.AutoHashMapUnmanaged(syntax.Id, ColumnType);

/// Inference only ever narrows, and a narrowing is bounded by the terms it is
/// read from, so it reaches a fixpoint. This bounds the passes anyway; types
/// left wider than they could be make a check stricter, never unsound.
const max_passes = 64;

/// Checks a rule against the schemas: its body's goals, and that its head
/// fits its predicate's schema on every binding the body can produce.
pub fn checkRule(db: *const database.Database, head: syntax.Expr, body: []const syntax.Clause) !void {
    if (db.schemas.get(head.predicate) == null and !mentionsTyped(db, body)) return;
    var checker: Checker = .{ .db = db };
    var env: Env = .empty;
    defer env.deinit(db.allocator);
    try checker.body(&env, body);
    const declared = db.schemas.get(head.predicate) orelse return;
    if (declared.columns.len != head.terms.len) return errors.Error.IllTyped;
    for (head.terms, declared.columns) |term, column_type|
        if (!checker.typeOf(&env, term).isSubtype(column_type)) return errors.Error.IllTyped;
}

/// Checks a query's or a retraction's goals against the schemas.
pub fn checkGoals(db: *const database.Database, goals: []const syntax.Clause) !void {
    if (!mentionsTyped(db, goals)) return;
    var checker: Checker = .{ .db = db };
    var env: Env = .empty;
    defer env.deinit(db.allocator);
    try checker.body(&env, goals);
}

/// Checks every rule the database holds, as a new schema requires: a rule
/// that was fine while a predicate was untyped may not be once it is typed.
pub fn checkRules(db: *const database.Database) !void {
    for (db.eval.rules.items) |rule| try checkRule(db, rule.head, rule.body);
}

/// Whether any goal, at any depth, reads a predicate with a schema.
fn mentionsTyped(db: *const database.Database, clauses: []const syntax.Clause) bool {
    for (clauses) |clause| switch (clause) {
        .relational, .negated => |expression| if (!syntax.isBuiltin(expression) and
            db.schemas.get(expression.predicate) != null) return true,
        .builtin => {},
        .aggregate => |aggregate| if (mentionsTyped(db, aggregate.body)) return true,
    };
    return false;
}

const Checker = struct {
    db: *const database.Database,

    fn body(self: Checker, env: *Env, clauses: []const syntax.Clause) anyerror!void {
        for (0..max_passes) |_| {
            var changed = false;
            for (clauses) |goal| {
                if (try self.clause(env, goal)) changed = true;
            }
            if (!changed) return;
        }
    }

    /// Applies what one goal says about its variables, reporting whether any
    /// type narrowed.
    fn clause(self: Checker, env: *Env, value: syntax.Clause) anyerror!bool {
        switch (value) {
            .relational => |expression| {
                const declared = try self.schemaFor(expression) orelse return false;
                var changed = false;
                for (expression.terms, declared.columns) |term, column_type| {
                    if (try self.constrain(env, term, column_type)) changed = true;
                }
                return changed;
            },
            .negated => |expression| {
                if (syntax.isBuiltin(expression)) return false;
                const declared = try self.schemaFor(expression) orelse return false;
                for (expression.terms, declared.columns) |term, column_type|
                    if (self.typeOf(env, term).meet(column_type).isEmpty()) return errors.Error.IllTyped;
                return false;
            },
            .builtin => |expression| {
                if (expression.negated) return false;
                return self.builtin(env, expression);
            },
            .aggregate => |aggregate| {
                // What the inner body proves holds only for its own
                // solutions, so it is worked out on a copy and only the
                // collected list's type comes back out.
                var inner = try env.clone(self.db.allocator);
                defer inner.deinit(self.db.allocator);
                try self.body(&inner, aggregate.body);
                const collected = self.typeOf(&inner, aggregate.template).listOf() orelse ColumnType.any;
                return self.constrain(env, aggregate.output, collected);
            },
        }
    }

    fn builtin(self: Checker, env: *Env, expression: syntax.Expr) !bool {
        const terms = expression.terms;
        switch (expression.kind) {
            .relation, .inequality => return false,
            .equality => {
                if (terms.len != 2) return false;
                const shared = self.typeOf(env, terms[0]).meet(self.typeOf(env, terms[1]));
                if (shared.isEmpty()) return errors.Error.IllTyped;
                const left = try self.constrain(env, terms[0], shared);
                return try self.constrain(env, terms[1], shared) or left;
            },
            .less_than, .less_or_equal, .greater_than, .greater_or_equal => {
                if (terms.len != 2) return false;
                const left = try self.constrain(env, terms[0], .number);
                return try self.constrain(env, terms[1], .number) or left;
            },
            .add, .subtract => {
                if (terms.len != 3) return false;
                var changed = try self.constrain(env, terms[1], .number);
                if (try self.constrain(env, terms[2], .number)) changed = true;
                // Integer arithmetic stays integral; anything involving a
                // float may land on either.
                const integral = self.typeOf(env, terms[1]).isSubtype(.int) and
                    self.typeOf(env, terms[2]).isSubtype(.int);
                if (try self.constrain(env, terms[0], if (integral) .int else .number)) changed = true;
                return changed;
            },
            .type_test => {
                if (terms.len != 1) return false;
                return self.constrain(env, terms[0], expression.column_type);
            },
        }
    }

    /// The schema a relational goal's predicate has, checked against the
    /// goal's arity.
    fn schemaFor(self: Checker, expression: syntax.Expr) !?schema.Schema {
        const declared = self.db.schemas.get(expression.predicate) orelse return null;
        if (declared.columns.len != expression.terms.len) return errors.Error.IllTyped;
        return declared;
    }

    /// Narrows `term`'s variables to what having `column_type` requires,
    /// reporting whether any narrowed. A constant or a structure that cannot
    /// have the type makes the goal impossible.
    fn constrain(self: Checker, env: *Env, term: syntax.Term, column_type: ColumnType) !bool {
        switch (term) {
            .variable => |variable| {
                const current = env.get(variable) orelse ColumnType.any;
                const narrowed = current.meet(column_type);
                if (narrowed.isEmpty()) return errors.Error.IllTyped;
                if (narrowed.eql(current)) return false;
                try env.put(self.db.allocator, variable, narrowed);
                return true;
            },
            .scalar => |id| {
                if (!self.scalarType(id).isSubtype(column_type)) return errors.Error.IllTyped;
                return false;
            },
            .nil => {
                if (!column_type.holdsNil()) return errors.Error.IllTyped;
                return false;
            },
            .cons => |pair| {
                if (column_type.lists == 0) {
                    if (column_type.element == .any) return false;
                    return errors.Error.IllTyped;
                }
                const head = try self.constrain(env, pair.head, column_type.elements());
                return try self.constrain(env, pair.tail, column_type) or head;
            },
        }
    }

    /// The narrowest type `term` is known to have.
    fn typeOf(self: Checker, env: *const Env, term: syntax.Term) ColumnType {
        return switch (term) {
            .variable => |variable| env.get(variable) orelse .any,
            .scalar => |id| self.scalarType(id),
            .nil => .empty_list,
            .cons => |pair| blk: {
                const head = self.typeOf(env, pair.head);
                const tail = self.typeOf(env, pair.tail);
                if (head.isEmpty() or tail.isEmpty()) break :blk .empty;
                // A tail that need not be a list makes a pair that need not
                // be one either.
                if (tail.lists == 0) break :blk .any;
                break :blk head.join(tail.elements()).listOf() orelse .any;
            },
        };
    }

    fn scalarType(self: Checker, id: scalar.Id) ColumnType {
        return switch (self.db.eval.scalars.get(id)) {
            .atom => .atom,
            .integer => .int,
            .float => .number,
        };
    }
};

const testing = std.testing;
const compile = @import("compile.zig");
const input = @import("input.zig");
const transaction = @import("transaction.zig");

/// Compiles `body` against `db` and checks it as a rule deriving `head`.
fn checkDescribed(db: *database.Database, head: input.Relation, body: []const input.Goal) !void {
    const compiled_head = try compile.compileRelation(db, head.predicate, head.terms, false);
    defer syntax.freeExpr(db.allocator, compiled_head);
    const compiled = try compile.compileGoals(db, body);
    defer {
        for (compiled) |clause| syntax.freeClauseTree(db.allocator, clause);
        db.allocator.free(compiled);
    }
    try checkRule(db, compiled_head, compiled);
}

fn declare(db: *database.Database, name: []const u8, columns: []const ColumnType) !void {
    const types = try db.allocator.dupe(ColumnType, columns);
    errdefer db.allocator.free(types);
    const names = try db.allocator.alloc(?u64, columns.len);
    @memset(names, null);
    try transaction.declareSchema(db, try db.strings.intern(name), .{ .columns = types, .names = names });
}

test "goals that touch no typed predicate are not checked" {
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    // Comparing an atom is the runtime's `NumericType`, as it was before
    // schemas, not something read off the literal.
    try checkDescribed(&db, input.fact("p", &.{input.variable("X")}), &.{
        input.relation("q", &.{input.variable("X")}),
        input.lessThan(input.atom("a"), input.integer(1)),
    });
}

test "what a setof body proves stays inside it" {
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try declare(&db, "num", &.{.int});
    try declare(&db, "out", &.{ .int, .any });
    const x = input.variable("X");
    const s = input.variable("S");
    // `num(X)` inside the setof says nothing about the outer `X`.
    try testing.expectError(errors.Error.IllTyped, checkDescribed(&db, input.fact("out", &.{ x, s }), &.{
        input.relation("q", &.{x}),
        input.setof(x, &.{input.relation("num", &.{x})}, s),
    }));
    // What it collects is typed, though.
    try declare(&db, "nums", &.{ColumnType.int.listOf().?});
    try checkDescribed(&db, input.fact("nums", &.{s}), &.{
        input.setof(x, &.{input.relation("num", &.{x})}, s),
    });
}
