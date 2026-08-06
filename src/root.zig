//! A small, embeddable Datalog engine modeled after Jatalog.
const std = @import("std");
const scalar = @import("scalar.zig");
pub const input = @import("input.zig");
const input_compiler = @import("input_compiler.zig");

const Id = u64;
const ValueId = u64;
pub const Error = error{
    InvalidFact,
    InvalidRule,
    InvalidQuery,
    InvalidTerm,
    InvalidSyntax,
    NotStratified,
    UnboundVariable,
    UnknownOperator,
    NumericType,
    NumericOverflow,
    NotAdmissible,
    UnknownVariable,
    TypeMismatch,
};

/// Interns predicate and variable symbols used by a database. IDs are
/// insertion indexes, which makes `resolve` a reverse lookup into the ordered
/// keys of the same StringArrayHashMapUnmanaged.
const StringTable = struct {
    allocator: std.mem.Allocator,
    strings: std.StringArrayHashMapUnmanaged(Id) = .empty,

    fn init(allocator: std.mem.Allocator) StringTable {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *StringTable) void {
        for (self.strings.keys()) |string| self.allocator.free(string);
        self.strings.deinit(self.allocator);
        self.* = undefined;
    }

    fn clone(self: *const StringTable) !StringTable {
        var result: StringTable = .init(self.allocator);
        errdefer result.deinit();
        for (self.strings.keys()) |string| _ = try result.intern(string);
        return result;
    }

    fn intern(self: *StringTable, string: []const u8) !Id {
        if (self.strings.get(string)) |id| return id;
        const owned = try self.allocator.dupe(u8, string);
        errdefer self.allocator.free(owned);
        const id: Id = @intCast(self.strings.count());
        try self.strings.putNoClobber(self.allocator, owned, id);
        return id;
    }

    fn get(self: *const StringTable, string: []const u8) ?Id {
        return self.strings.get(string);
    }

    fn resolve(self: *const StringTable, id: Id) []const u8 {
        return self.strings.keys()[@intCast(id)];
    }
};

const Value = union(enum) {
    scalar: scalar.Id,
    nil,
    cons: struct { head: ValueId, tail: ValueId },
};

const ValueTable = struct {
    allocator: std.mem.Allocator,
    values: std.ArrayList(Value) = .empty,

    fn init(allocator: std.mem.Allocator) ValueTable {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *ValueTable) void {
        self.values.deinit(self.allocator);
        self.* = undefined;
    }

    fn clone(self: *const ValueTable) !ValueTable {
        return .{
            .allocator = self.allocator,
            .values = try self.values.clone(self.allocator),
        };
    }

    fn intern(self: *ValueTable, value: Value) !ValueId {
        for (self.values.items, 0..) |existing, index| {
            if (std.meta.eql(existing, value)) return @intCast(index);
        }
        try self.values.append(self.allocator, value);
        return @intCast(self.values.items.len - 1);
    }

    fn get(self: *const ValueTable, id: ValueId) Value {
        return self.values.items[@intCast(id)];
    }

    fn internFrom(self: *ValueTable, source: *const ValueTable, id: ValueId) !ValueId {
        return switch (source.get(id)) {
            .scalar => |value| try self.intern(.{ .scalar = value }),
            .nil => try self.intern(.nil),
            .cons => |pair| try self.intern(.{ .cons = .{
                .head = try self.internFrom(source, pair.head),
                .tail = try self.internFrom(source, pair.tail),
            } }),
        };
    }
};

const InputBuilder = struct {
    database: *Jatalog,

    pub fn allocator(self: *InputBuilder) std.mem.Allocator {
        return self.database.allocator;
    }

    pub fn nilTerm(_: *InputBuilder) Term { // ziglint-ignore: Z012
        return .nil;
    }

    pub fn atomTerm(self: *InputBuilder, atom: []const u8) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.scalars.internAtom(atom) };
    }

    pub fn integerTerm(self: *InputBuilder, integer: i64) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.scalars.internInteger(integer) };
    }

    pub fn floatTerm(self: *InputBuilder, float: f64) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.scalars.internFloat(float) };
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

const Term = union(enum) {
    scalar: scalar.Id,
    variable: Id,
    nil,
    cons: *Cons,

    pub const Cons = struct {
        head: Term,
        tail: Term,
    };

    fn isGround(self: Term) bool {
        return switch (self) {
            .variable => false,
            .cons => |pair| pair.head.isGround() and pair.tail.isGround(),
            else => true,
        };
    }
};

const GoalKind = enum {
    relation,
    equality,
    inequality,
    less_than,
    less_or_equal,
    greater_than,
    greater_or_equal,
    add,
    subtract,
};

const Expr = struct {
    predicate: Id,
    terms: []Term,
    negated: bool = false,
    kind: GoalKind = .relation,

    fn arity(self: Expr) usize {
        return self.terms.len;
    }

    fn isGround(self: Expr) bool {
        for (self.terms) |term| if (!term.isGround()) return false;
        return true;
    }
};

const Rule = struct {
    head: Expr,
    body: []Clause,
    seed_argument: ?usize = null,
};

const Aggregate = struct {
    template: Term,
    body: []Clause,
    output: Term,
};

const Clause = union(enum) {
    relational: Expr,
    builtin: Expr,
    negated: Expr,
    aggregate: Aggregate,
};

const Fact = struct {
    predicate: Id,
    terms: []ValueId,
};

const PredicateKey = struct {
    name: Id,
    arity: usize,
};

fn predicateKey(expression: Expr) PredicateKey {
    return .{ .name = expression.predicate, .arity = expression.terms.len };
}

const Binding = struct {
    values: std.array_hash_map.Auto(Id, ValueId) = .empty,

    pub fn deinit(self: *Binding, allocator: std.mem.Allocator) void {
        self.values.deinit(allocator);
        self.* = undefined;
    }

    fn clone(self: *const Binding, allocator: std.mem.Allocator) !Binding {
        return .{ .values = try self.values.clone(allocator) };
    }
};

const ResultNode = union(enum) {
    atom: []u8,
    integer: i64,
    float: f64,
    nil,
    cons: *ResultCons,
};

const ResultCons = struct {
    head: *ResultNode,
    tail: *ResultNode,
};

pub const ResultValue = struct {
    node: *const ResultNode,

    pub const Kind = enum { atom, integer, float, nil, cons };

    pub fn kind(self: ResultValue) Kind {
        return switch (self.node.*) {
            .atom => .atom,
            .integer => .integer,
            .float => .float,
            .nil => .nil,
            .cons => .cons,
        };
    }

    pub fn getAtom(self: ResultValue) Error![]const u8 {
        return switch (self.node.*) {
            .atom => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn getInteger(self: ResultValue) Error!i64 {
        return switch (self.node.*) {
            .integer => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn getFloat(self: ResultValue) Error!f64 {
        return switch (self.node.*) {
            .float => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn head(self: ResultValue) Error!ResultValue {
        return switch (self.node.*) {
            .cons => |pair| .{ .node = pair.head },
            else => Error.TypeMismatch,
        };
    }

    pub fn tail(self: ResultValue) Error!ResultValue {
        return switch (self.node.*) {
            .cons => |pair| .{ .node = pair.tail },
            else => Error.TypeMismatch,
        };
    }

    pub fn formatAlloc(self: ResultValue, allocator: std.mem.Allocator) ![]u8 {
        var output: std.Io.Writer.Allocating = .init(allocator);
        defer output.deinit();
        self.write(&output.writer) catch return error.OutOfMemory;
        return output.toOwnedSlice();
    }

    pub fn write(self: ResultValue, writer: *std.Io.Writer) !void {
        switch (self.node.*) {
            .atom => |value| {
                try scalar.writeAtom(writer, value);
            },
            .integer => |value| try writer.print("{d}", .{value}),
            .float => |value| try scalar.writeFloat(writer, value),
            .nil => try writer.writeAll("[]"),
            .cons => |pair| if (isProperResultList(self.node)) {
                try writer.writeByte('[');
                var current = self.node;
                var first = true;
                while (current.* == .cons) {
                    if (!first) try writer.writeAll(", ");
                    try (ResultValue{ .node = current.cons.head }).write(writer);
                    current = current.cons.tail;
                    first = false;
                }
                try writer.writeByte(']');
            } else {
                try writer.writeAll("cons(");
                try (ResultValue{ .node = pair.head }).write(writer);
                try writer.writeAll(", ");
                try (ResultValue{ .node = pair.tail }).write(writer);
                try writer.writeByte(')');
            },
        }
    }
};

fn isProperResultList(root: *const ResultNode) bool {
    var current = root;
    while (true) switch (current.*) {
        .nil => return true,
        .cons => |pair| current = pair.tail,
        else => return false,
    };
}

fn freeResultNode(allocator: std.mem.Allocator, node: *ResultNode) void {
    switch (node.*) {
        .atom => |atom| allocator.free(atom),
        .integer, .float, .nil => {},
        .cons => |pair| {
            freeResultNode(allocator, pair.head);
            freeResultNode(allocator, pair.tail);
            allocator.destroy(pair);
        },
    }
    allocator.destroy(node);
}

pub const Answer = struct {
    allocator: std.mem.Allocator,
    bindings: std.ArrayList(ResultBinding) = .empty,

    pub const ResultBinding = struct {
        name: []u8,
        value: ResultValue,
    };

    fn deinit(self: *Answer) void {
        for (self.bindings.items) |binding| {
            self.allocator.free(binding.name);
            freeResultNode(self.allocator, @constCast(binding.value.node));
        }
        self.bindings.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn getValue(self: *const Answer, variable: []const u8) Error!ResultValue {
        for (self.bindings.items) |binding|
            if (std.mem.eql(u8, binding.name, variable)) return binding.value;
        return Error.UnknownVariable;
    }

    pub fn getAtom(self: *const Answer, variable: []const u8) Error![]const u8 {
        return (try self.getValue(variable)).getAtom();
    }

    pub fn getInteger(self: *const Answer, variable: []const u8) Error!i64 {
        return (try self.getValue(variable)).getInteger();
    }

    pub fn getFloat(self: *const Answer, variable: []const u8) Error!f64 {
        return (try self.getValue(variable)).getFloat();
    }
};

pub const QueryResult = struct {
    allocator: std.mem.Allocator,
    answers: std.ArrayList(Answer) = .empty,

    pub fn deinit(self: *QueryResult) void {
        for (self.answers.items) |*answer| answer.deinit();
        self.answers.deinit(self.allocator);
        self.* = undefined;
    }
};

pub const ExecutionResult = union(enum) {
    none,
    changed: bool,
    query: QueryResult,

    pub fn deinit(self: *ExecutionResult) void {
        switch (self.*) {
            .query => |*result| result.deinit(),
            else => {},
        }
        self.* = undefined;
    }
};

pub const Jatalog = struct {
    allocator: std.mem.Allocator,
    strings: StringTable,
    scalars: scalar.Store,
    values: ValueTable,
    facts: std.ArrayList(Fact) = .empty,
    rules: std.ArrayList(Rule) = .empty,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{
            .allocator = allocator,
            .strings = .init(allocator),
            .scalars = .init(allocator),
            .values = .init(allocator),
        };
    }

    pub fn deinit(self: *Jatalog) void {
        for (self.facts.items) |fact| self.allocator.free(fact.terms);
        self.facts.deinit(self.allocator);
        for (self.rules.items) |rule| {
            freeExpr(self.allocator, rule.head);
            for (rule.body) |clause| freeClauseTree(self.allocator, clause);
            self.allocator.free(rule.body);
        }
        self.rules.deinit(self.allocator);
        self.values.deinit();
        self.scalars.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    fn clone(self: *const Jatalog) !Jatalog {
        var result: Jatalog = .{
            .allocator = self.allocator,
            .strings = try self.strings.clone(),
            .scalars = undefined,
            .values = undefined,
        };
        errdefer result.strings.deinit();
        result.scalars = try self.scalars.clone();
        errdefer result.scalars.deinit();
        result.values = try self.values.clone();
        errdefer result.values.deinit();
        errdefer {
            for (result.facts.items) |fact| self.allocator.free(fact.terms);
            result.facts.deinit(self.allocator);
        }
        for (self.facts.items) |fact| {
            const terms = try self.allocator.dupe(ValueId, fact.terms);
            result.facts.append(self.allocator, .{
                .predicate = fact.predicate,
                .terms = terms,
            }) catch |err| {
                self.allocator.free(terms);
                return err;
            };
        }
        errdefer {
            for (result.rules.items) |rule| freeRule(self.allocator, rule);
            result.rules.deinit(self.allocator);
        }
        for (self.rules.items) |rule| {
            const copy = try cloneRule(self.allocator, rule);
            result.rules.append(self.allocator, copy) catch |err| {
                freeRule(self.allocator, copy);
                return err;
            };
        }
        return result;
    }

    fn commit(self: *Jatalog, staging: *Jatalog) void {
        const previous = self.*;
        self.* = staging.*;
        staging.* = previous;
    }

    fn commitRetraction(self: *Jatalog, staging: *const Jatalog) !void {
        var committed = try self.clone();
        defer committed.deinit();
        var index = committed.facts.items.len;
        while (index > 0) {
            index -= 1;
            if (containsFact(staging.facts.items, committed.facts.items[index])) continue;
            committed.allocator.free(committed.facts.items[index].terms);
            _ = committed.facts.orderedRemove(index);
        }
        self.commit(&committed);
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const input.Term) !void {
        var staging = try self.clone();
        defer staging.deinit();
        const expression = try staging.compileRelation(predicate, terms, false);
        defer freeExpr(staging.allocator, expression);
        try staging.addFactExpr(expression);
        self.commit(&staging);
    }

    pub fn addRule(self: *Jatalog, head: input.Goal, body: []const input.Goal) !void {
        var staging = try self.clone();
        defer staging.deinit();
        const compiled_head = switch (head) {
            .relation => |relation| try staging.compileRelation(relation.predicate, relation.terms, false),
            else => return Error.InvalidRule,
        };
        var head_owned = true;
        defer if (head_owned) freeExpr(staging.allocator, compiled_head);
        const compiled_body = try staging.compileGoals(body);
        var body_owned = true;
        defer {
            if (body_owned) for (compiled_body) |clause| freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled_body);
        }
        try staging.addRuleClauses(compiled_head, compiled_body);
        head_owned = false;
        body_owned = false;
        self.commit(&staging);
    }

    pub fn query(self: *Jatalog, goals: []const input.Goal) !QueryResult {
        var staging = try self.clone();
        defer staging.deinit();
        const compiled = try staging.compileGoals(goals);
        defer {
            for (compiled) |clause| freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        return staging.queryClauses(compiled);
    }

    pub fn retract(self: *Jatalog, goals: []const input.Goal) !bool {
        var staging = try self.clone();
        defer staging.deinit();
        const compiled = try staging.compileGoals(goals);
        defer {
            for (compiled) |clause| freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        const changed = try staging.deleteClauses(compiled);
        if (changed) try self.commitRetraction(&staging);
        return changed;
    }

    fn compileRelation(
        self: *Jatalog,
        predicate: []const u8,
        descriptors: []const input.Term,
        negated: bool,
    ) !Expr {
        if (predicate.len == 0) return Error.InvalidTerm;
        var builder: InputBuilder = .{ .database = self };
        return .{
            .predicate = try self.strings.intern(predicate),
            .terms = try input_compiler.compileTerms(&builder, descriptors),
            .negated = negated,
        };
    }

    fn compileGoals(self: *Jatalog, descriptors: []const input.Goal) anyerror![]Clause {
        try input_compiler.validateGoals(self.allocator, descriptors);
        return self.compileGoalsValidated(descriptors);
    }

    fn compileGoalsValidated(self: *Jatalog, descriptors: []const input.Goal) anyerror![]Clause {
        const clauses = try self.allocator.alloc(Clause, descriptors.len);
        var initialized: usize = 0;
        errdefer {
            for (clauses[0..initialized]) |clause| freeClauseTree(self.allocator, clause);
            self.allocator.free(clauses);
        }
        for (descriptors, clauses) |descriptor, *clause| {
            clause.* = try self.compileGoalValidated(descriptor);
            initialized += 1;
        }
        return clauses;
    }

    fn compileGoalValidated(self: *Jatalog, descriptor: input.Goal) anyerror!Clause {
        return switch (descriptor) {
            .relation => |relation| .{
                .relational = try self.compileRelation(relation.predicate, relation.terms, false),
            },
            .negation => |relation| .{ .negated = try self.compileRelation(relation.predicate, relation.terms, true) },
            .equality => |binary| .{ .builtin = try self.compileBuiltin(.equality, &.{ binary.left, binary.right }) },
            .inequality => |binary| .{
                .builtin = try self.compileBuiltin(.inequality, &.{ binary.left, binary.right }),
            },
            .comparison => |comparison| .{ .builtin = try self.compileBuiltin(switch (comparison.kind) {
                .less_than => .less_than,
                .less_or_equal => .less_or_equal,
                .greater_than => .greater_than,
                .greater_or_equal => .greater_or_equal,
            }, &.{ comparison.operands.left, comparison.operands.right }) },
            .arithmetic => |arithmetic| .{ .builtin = try self.compileBuiltin(switch (arithmetic.kind) {
                .add => .add,
                .subtract => .subtract,
            }, &.{ arithmetic.output, arithmetic.left, arithmetic.right }) },
            .aggregate => |aggregate| blk: {
                var builder: InputBuilder = .{ .database = self };
                const template = try input_compiler.compileTerm(&builder, aggregate.template);
                errdefer freeTerm(self.allocator, template);
                const output = try input_compiler.compileTerm(&builder, aggregate.output);
                errdefer freeTerm(self.allocator, output);
                const body = try self.compileGoalsValidated(aggregate.body);
                break :blk .{ .aggregate = .{ .template = template, .body = body, .output = output } };
            },
        };
    }

    fn compileBuiltin(self: *Jatalog, kind: GoalKind, terms: []const input.Term) !Expr {
        var result = try self.compileRelation(goalOperator(kind), terms, false);
        result.kind = kind;
        return result;
    }

    fn addFactExpr(self: *Jatalog, value: Expr) !void {
        if (!value.isGround() or value.negated) return Error.InvalidFact;
        const terms = try self.allocator.alloc(ValueId, value.terms.len);
        errdefer self.allocator.free(terms);
        for (value.terms, terms) |term, *id| id.* = try self.termToValue(term, null);
        const fact: Fact = .{ .predicate = value.predicate, .terms = terms };
        if (containsFact(self.facts.items, fact)) {
            self.allocator.free(terms);
            return;
        }
        try self.facts.append(self.allocator, fact);
    }

    /// Adds a rule whose body may contain aggregate clauses. On success the
    /// database owns `head` and every clause in `body`; on failure the caller
    /// retains ownership. The body slice itself is only borrowed.
    fn addRuleClauses(self: *Jatalog, head: Expr, body: []const Clause) !void {
        const seed_argument = try self.validateRule(head, body);
        const owned_body = try self.orderClauses(body);
        errdefer self.allocator.free(owned_body);
        try self.rules.append(self.allocator, .{
            .head = head,
            .body = owned_body,
            .seed_argument = seed_argument,
        });
        self.validateRecursiveArithmetic() catch |err| {
            _ = self.rules.pop();
            return err;
        };
        self.validateStratification() catch |err| {
            _ = self.rules.pop();
            return err;
        };
    }

    fn classifyExpr(self: *const Jatalog, expression: Expr) Clause {
        if (expression.negated) return .{ .negated = expression };
        if (isBuiltin(self, expression)) return .{ .builtin = expression };
        return .{ .relational = expression };
    }

    /// Evaluates relational, built-in, negated, or aggregate goals. Goals and
    /// their structural terms remain caller-owned and may be freed immediately
    /// after this function returns.
    fn queryClauses(self: *Jatalog, goals: []const Clause) !QueryResult {
        var internal_answers = try self.evaluateClauses(goals);
        defer {
            for (internal_answers.items) |*answer| answer.deinit(self.allocator);
            internal_answers.deinit(self.allocator);
        }
        return self.copyQueryResult(internal_answers.items);
    }

    fn evaluateClauses(self: *Jatalog, goals: []const Clause) !std.ArrayList(Binding) {
        if (goals.len == 0) return Error.InvalidQuery;
        var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (goals) |clause| try collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try self.orderClauses(goals);
        defer self.allocator.free(ordered);
        for (ordered) |clause|
            try self.validateClause(clause, &bound, &outer_variables, Error.InvalidQuery);
        for (goals) |clause| try self.internGroundStructuresInClause(clause);

        var expanded = try self.cloneFacts();
        defer deinitFacts(self.allocator, &expanded);
        try self.expand(&expanded);

        var internal_answers: std.ArrayList(Binding) = .empty;
        errdefer {
            for (internal_answers.items) |*answer| answer.deinit(self.allocator);
            internal_answers.deinit(self.allocator);
        }
        var initial: Binding = .{};
        defer initial.deinit(self.allocator);
        try self.matchClauses(ordered, expanded.items, 0, &initial, &internal_answers);
        return internal_answers;
    }

    fn copyQueryResult(self: *const Jatalog, bindings: []const Binding) !QueryResult {
        var result: QueryResult = .{ .allocator = self.allocator };
        errdefer result.deinit();
        for (bindings) |binding| {
            var answer: Answer = .{ .allocator = self.allocator };
            errdefer answer.deinit();
            for (binding.values.keys(), binding.values.values()) |variable, value| {
                const name = try self.allocator.dupe(u8, self.strings.resolve(variable));
                errdefer self.allocator.free(name);
                const owned_value = try self.copyResultNode(value);
                answer.bindings.append(self.allocator, .{
                    .name = name,
                    .value = .{ .node = owned_value },
                }) catch |err| {
                    freeResultNode(self.allocator, owned_value);
                    return err;
                };
            }
            try result.answers.append(self.allocator, answer);
        }
        return result;
    }

    fn copyResultNode(self: *const Jatalog, value: ValueId) !*ResultNode {
        const node = try self.allocator.create(ResultNode);
        errdefer self.allocator.destroy(node);
        node.* = switch (self.values.get(value)) {
            .scalar => |scalar_id| switch (self.scalars.get(scalar_id)) {
                .atom => |atom| .{ .atom = try self.allocator.dupe(u8, atom) },
                .integer => |integer| .{ .integer = integer },
                .float => |float| .{ .float = float },
            },
            .nil => .nil,
            .cons => |value_pair| blk: {
                const pair = try self.allocator.create(ResultCons);
                errdefer self.allocator.destroy(pair);
                pair.head = try self.copyResultNode(value_pair.head);
                errdefer freeResultNode(self.allocator, pair.head);
                pair.tail = try self.copyResultNode(value_pair.tail);
                break :blk .{ .cons = pair };
            },
        };
        return node;
    }

    pub fn execute(self: *Jatalog, source: []const u8) !ExecutionResult {
        var parser: Parser = .{ .jatalog = self, .source = source };
        return parser.executeAll();
    }

    fn cloneFacts(self: *Jatalog) !std.ArrayList(Fact) {
        var result: std.ArrayList(Fact) = .empty;
        errdefer deinitFacts(self.allocator, &result);
        for (self.facts.items) |fact| {
            const terms = try self.allocator.dupe(ValueId, fact.terms);
            result.append(self.allocator, .{
                .predicate = fact.predicate,
                .terms = terms,
            }) catch |err| {
                self.allocator.free(terms);
                return err;
            };
        }
        return result;
    }

    fn expand(self: *Jatalog, facts: *std.ArrayList(Fact)) !void {
        var levels = try self.computeStrata();
        defer levels.deinit(self.allocator);
        var max_level: usize = 0;
        for (levels.values()) |level| max_level = @max(max_level, level);

        for (0..max_level + 1) |level| {
            while (true) {
                const fact_count_before = facts.items.len;
                const value_count_before = self.values.values.items.len;
                for (self.rules.items) |rule| {
                    const rule_level = levels.get(predicateKey(rule.head)) orelse 0;
                    if (rule_level != level and (rule.seed_argument == null or rule_level > level)) continue;
                    var answers: std.ArrayList(Binding) = .empty;
                    defer {
                        for (answers.items) |*answer| answer.deinit(self.allocator);
                        answers.deinit(self.allocator);
                    }
                    if (rule.seed_argument) |argument| {
                        const value_count = self.values.values.items.len;
                        for (0..value_count) |value| {
                            var initial: Binding = .{};
                            defer initial.deinit(self.allocator);
                            const seeded = try self.unifyValueTerm(
                                @intCast(value),
                                rule.head.terms[argument],
                                &initial,
                            );
                            if (seeded) {
                                self.matchClauses(
                                    rule.body,
                                    facts.items,
                                    0,
                                    &initial,
                                    &answers,
                                ) catch |err| switch (err) {
                                    Error.NumericType, Error.NumericOverflow => continue,
                                    else => return err,
                                };
                            }
                        }
                    } else {
                        var initial: Binding = .{};
                        defer initial.deinit(self.allocator);
                        try self.matchClauses(rule.body, facts.items, 0, &initial, &answers);
                    }
                    for (answers.items) |*answer| {
                        const derived = try self.deriveFact(rule.head, answer);
                        if (containsFact(facts.items, derived)) {
                            self.allocator.free(derived.terms);
                        } else {
                            facts.append(self.allocator, derived) catch |err| {
                                self.allocator.free(derived.terms);
                                return err;
                            };
                        }
                    }
                }
                if (facts.items.len == fact_count_before and
                    self.values.values.items.len == value_count_before) break;
            }
        }
    }

    fn deriveFact(self: *Jatalog, head: Expr, bindings: *const Binding) !Fact {
        const terms = try self.allocator.alloc(ValueId, head.terms.len);
        errdefer self.allocator.free(terms);
        for (head.terms, terms) |term, *id| id.* = try self.termToValue(term, bindings);
        return .{ .predicate = head.predicate, .terms = terms };
    }

    fn termToValue(self: *Jatalog, term: Term, bindings: ?*const Binding) !ValueId {
        return switch (term) {
            .scalar => |value| try self.values.intern(.{ .scalar = value }),
            .nil => try self.values.intern(.nil),
            .variable => |variable| if (bindings) |bound|
                bound.values.get(variable) orelse Error.UnboundVariable
            else
                Error.UnboundVariable,
            .cons => |pair| try self.values.intern(.{ .cons = .{
                .head = try self.termToValue(pair.head, bindings),
                .tail = try self.termToValue(pair.tail, bindings),
            } }),
        };
    }

    // Structural recursion is seeded from interned values during expansion, so
    // ground structures supplied by a query must join that seed set first.
    fn internGroundStructuresInExpr(self: *Jatalog, expression: Expr) !void {
        for (expression.terms) |term| try self.internGroundStructuresInTerm(term);
    }

    fn internGroundStructuresInClause(self: *Jatalog, clause: Clause) !void {
        switch (clause) {
            .relational, .builtin, .negated => |expression| try self.internGroundStructuresInExpr(expression),
            .aggregate => |aggregate| {
                try self.internGroundStructuresInTerm(aggregate.template);
                for (aggregate.body) |body_clause|
                    try self.internGroundStructuresInClause(body_clause);
                try self.internGroundStructuresInTerm(aggregate.output);
            },
        }
    }

    fn internGroundStructuresInTerm(self: *Jatalog, term: Term) !void {
        switch (term) {
            .nil => _ = try self.termToValue(term, null),
            .cons => |pair| {
                if (term.isGround()) {
                    _ = try self.termToValue(term, null);
                    return;
                }
                try self.internGroundStructuresInTerm(pair.head);
                try self.internGroundStructuresInTerm(pair.tail);
            },
            .scalar, .variable => {},
        }
    }

    fn matchClauses(
        self: *Jatalog,
        clauses: []const Clause,
        facts: []const Fact,
        index: usize,
        bindings: *const Binding,
        answers: *std.ArrayList(Binding),
    ) !void {
        if (index == clauses.len) {
            var answer = try bindings.clone(self.allocator);
            answers.append(self.allocator, answer) catch |err| {
                answer.deinit(self.allocator);
                return err;
            };
            return;
        }
        if (clauses[index] == .aggregate) {
            const aggregate = clauses[index].aggregate;
            var inner_answers: std.ArrayList(Binding) = .empty;
            defer {
                for (inner_answers.items) |*answer| answer.deinit(self.allocator);
                inner_answers.deinit(self.allocator);
            }
            try self.matchClauses(aggregate.body, facts, 0, bindings, &inner_answers);

            var values: std.ArrayList(ValueId) = .empty;
            defer values.deinit(self.allocator);
            for (inner_answers.items) |*answer| {
                const value = try self.termToValue(aggregate.template, answer);
                var duplicate = false;
                for (values.items) |existing| {
                    if (existing == value) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) try values.append(self.allocator, value);
            }
            self.sortValues(values.items);

            var list = try self.values.intern(.nil);
            var value_index = values.items.len;
            while (value_index > 0) {
                value_index -= 1;
                list = try self.values.intern(.{ .cons = .{
                    .head = values.items[value_index],
                    .tail = list,
                } });
            }

            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unifyValueTerm(list, aggregate.output, &next))
                try self.matchClauses(clauses, facts, index + 1, &next, answers);
            return;
        }
        const expression = switch (clauses[index]) {
            .aggregate => unreachable,
            .relational => |value| value,
            .builtin => |value| value,
            .negated => |value| value,
        };
        if (isBuiltin(self, expression)) {
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            const matched = try self.evalBuiltin(expression, &next);
            if (matched != expression.negated)
                try self.matchClauses(clauses, facts, index + 1, &next, answers);
            return;
        }
        if (expression.negated) {
            for (facts) |fact| {
                if (fact.predicate != expression.predicate or fact.terms.len != expression.terms.len) continue;
                var next = try bindings.clone(self.allocator);
                defer next.deinit(self.allocator);
                if (try self.unify(fact, expression, &next)) return;
            }
            try self.matchClauses(clauses, facts, index + 1, bindings, answers);
            return;
        }
        for (facts) |fact| {
            if (fact.predicate != expression.predicate or fact.terms.len != expression.terms.len) continue;
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unify(fact, expression, &next))
                try self.matchClauses(clauses, facts, index + 1, &next, answers);
        }
    }

    fn unify(self: *Jatalog, fact: Fact, goal: Expr, bindings: *Binding) !bool {
        for (fact.terms, goal.terms) |value, term| {
            if (!try self.unifyValueTerm(value, term, bindings)) return false;
        }
        return true;
    }

    fn unifyValueTerm(self: *Jatalog, value: ValueId, term: Term, bindings: *Binding) !bool {
        return switch (term) {
            .variable => |variable| if (bindings.values.get(variable)) |bound|
                bound == value
            else blk: {
                try bindings.values.put(self.allocator, variable, value);
                break :blk true;
            },
            .scalar => |expected| switch (self.values.get(value)) {
                .scalar => |actual| actual == expected,
                else => false,
            },
            .nil => self.values.get(value) == .nil,
            .cons => |pair| switch (self.values.get(value)) {
                .cons => |actual| try self.unifyValueTerm(actual.head, pair.head, bindings) and
                    try self.unifyValueTerm(actual.tail, pair.tail, bindings),
                else => false,
            },
        };
    }

    fn evalBuiltin(self: *Jatalog, expr_value: Expr, bindings: *Binding) !bool {
        if (expr_value.kind == .add or expr_value.kind == .subtract) {
            if (expr_value.terms.len != 3) return Error.InvalidQuery;
            const left_id = try self.termToValue(expr_value.terms[1], bindings);
            const right_id = try self.termToValue(expr_value.terms[2], bindings);
            const result_scalar = if (expr_value.kind == .add)
                try self.scalars.add(try self.valueScalar(left_id), try self.valueScalar(right_id))
            else
                try self.scalars.subtract(try self.valueScalar(left_id), try self.valueScalar(right_id));
            const value = try self.values.intern(.{ .scalar = result_scalar });
            return self.unifyValueTerm(value, expr_value.terms[0], bindings);
        }
        if (expr_value.terms.len != 2) return Error.InvalidQuery;
        const left = expr_value.terms[0];
        const right = expr_value.terms[1];
        const left_id = self.termToValue(left, bindings) catch |err| switch (err) {
            Error.UnboundVariable => null,
            else => return err,
        };
        const right_id = self.termToValue(right, bindings) catch |err| switch (err) {
            Error.UnboundVariable => null,
            else => return err,
        };

        if (expr_value.kind == .equality) {
            if (left_id == null and right_id == null) return Error.UnboundVariable;
            if (left_id == null) return self.unifyValueTerm(right_id.?, left, bindings);
            if (right_id == null) return self.unifyValueTerm(left_id.?, right, bindings);
            return self.valuesEqual(left_id.?, right_id.?);
        }
        if (left_id == null or right_id == null) return Error.UnboundVariable;
        if (expr_value.kind == .inequality) return !self.valuesEqual(left_id.?, right_id.?);

        const order = try self.scalars.compareNumeric(
            try self.valueScalar(left_id.?),
            try self.valueScalar(right_id.?),
        );
        return switch (expr_value.kind) {
            .less_than => order == .lt,
            .less_or_equal => order != .gt,
            .greater_than => order == .gt,
            .greater_or_equal => order != .lt,
            else => Error.UnknownOperator,
        };
    }

    fn valueScalar(self: *const Jatalog, value: ValueId) !scalar.Id {
        return switch (self.values.get(value)) {
            .scalar => |scalar_id| scalar_id,
            else => Error.NumericType,
        };
    }

    fn valuesEqual(self: *const Jatalog, left: ValueId, right: ValueId) bool {
        const left_value = self.values.get(left);
        const right_value = self.values.get(right);
        return switch (left_value) {
            .scalar => |left_scalar| switch (right_value) {
                .scalar => |right_scalar| left_scalar == right_scalar,
                else => false,
            },
            .nil => right_value == .nil,
            .cons => |left_cons| switch (right_value) {
                .cons => |right_cons| self.valuesEqual(left_cons.head, right_cons.head) and
                    self.valuesEqual(left_cons.tail, right_cons.tail),
                else => false,
            },
        };
    }

    fn validateRule(self: *Jatalog, head: Expr, body: []const Clause) !?usize {
        if (body.len == 0 or head.negated or isBuiltin(self, head)) return Error.InvalidRule;
        const recursive_seed = try admissibleSeedArgument(head, body);
        var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (head.terms) |term| try collectTermVariables(self.allocator, term, &outer_variables);
        for (body) |clause| try collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);

        const ordered = try self.orderClauses(body);
        defer self.allocator.free(ordered);
        if (recursive_seed) |seed_argument| {
            try self.validateRuleSafety(head, ordered, &outer_variables, seed_argument);
            return seed_argument;
        }
        self.validateRuleSafety(head, ordered, &outer_variables, null) catch |err| switch (err) {
            Error.InvalidRule => {
                const seed_argument = firstStructuralArgument(head) orelse
                    return Error.InvalidRule;
                try self.validateRuleSafety(head, ordered, &outer_variables, seed_argument);
                return seed_argument;
            },
            else => return err,
        };
        return null;
    }

    fn validateRuleSafety(
        self: *Jatalog,
        head: Expr,
        ordered: []const Clause,
        outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
        seed_argument: ?usize,
    ) !void {
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        if (seed_argument) |argument|
            try bindTermVariables(self.allocator, head.terms[argument], &bound);
        for (ordered) |clause| try self.validateClause(clause, &bound, outer_variables, Error.InvalidRule);
        for (head.terms) |term| if (!termVariablesBound(term, &bound)) return Error.InvalidRule;
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
                    return Error.NotAdmissible;
                if (isTailDescendant(head_term, call_term) and call_seed == null) call_seed = index;
            }
            if (!involves_cons) continue;
            const candidate = call_seed orelse return Error.NotAdmissible;
            if (seed) |existing| {
                if (existing != candidate) return Error.NotAdmissible;
            } else seed = candidate;
        }
        return seed;
    }

    fn firstStructuralArgument(head: Expr) ?usize {
        for (head.terms, 0..) |term, index|
            if (termContainsCons(term)) return index;
        return null;
    }

    fn validateRecursiveArithmetic(self: *Jatalog) !void {
        for (self.rules.items) |rule| {
            if (!self.ruleContainsArithmetic(rule)) continue;
            const head = predicateKey(rule.head);
            for (rule.body) |clause| {
                const expression = switch (clause) {
                    .relational => |value| value,
                    else => continue,
                };
                var visited: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
                defer visited.deinit(self.allocator);
                const dependency = predicateKey(expression);
                const structurally_proven = rule.seed_argument != null and std.meta.eql(dependency, head);
                if (!structurally_proven and try self.predicateReaches(dependency, head, &visited))
                    return Error.NotAdmissible;
            }
        }
    }

    fn ruleContainsArithmetic(self: *const Jatalog, rule: Rule) bool {
        for (rule.body) |clause| switch (clause) {
            .builtin => |expression| if (isArithmetic(self, expression)) return true,
            else => {},
        };
        return false;
    }

    fn predicateReaches(
        self: *Jatalog,
        current: PredicateKey,
        target: PredicateKey,
        visited: *std.AutoHashMapUnmanaged(PredicateKey, void),
    ) !bool {
        if (std.meta.eql(current, target)) return true;
        if (visited.contains(current)) return false;
        try visited.put(self.allocator, current, {});
        for (self.rules.items) |rule| {
            if (!std.meta.eql(predicateKey(rule.head), current)) continue;
            for (rule.body) |clause| {
                const expression = switch (clause) {
                    .relational => |value| value,
                    else => continue,
                };
                if (try self.predicateReaches(predicateKey(expression), target, visited)) return true;
            }
        }
        return false;
    }

    fn validateClause(
        self: *Jatalog,
        clause: Clause,
        bound: *std.AutoHashMapUnmanaged(Id, void),
        outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
        safety_error: anyerror,
    ) anyerror!void {
        switch (clause) {
            .relational => |expression| for (expression.terms) |term|
                try bindTermVariables(self.allocator, term, bound),
            .negated => |expression| for (expression.terms) |term|
                if (!termVariablesBound(term, bound)) return safety_error,
            .builtin => |expression| {
                if (isArithmetic(self, expression)) {
                    if (expression.terms.len != 3 or
                        !termVariablesBound(expression.terms[1], bound) or
                        !termVariablesBound(expression.terms[2], bound)) return safety_error;
                    try bindTermVariables(self.allocator, expression.terms[0], bound);
                    return;
                }
                if (expression.terms.len != 2) return safety_error;
                const a_bound = termVariablesBound(expression.terms[0], bound);
                const b_bound = termVariablesBound(expression.terms[1], bound);
                if (expression.kind == .equality and !expression.negated) {
                    if (!a_bound and !b_bound) return safety_error;
                    try bindTermVariables(self.allocator, expression.terms[0], bound);
                    try bindTermVariables(self.allocator, expression.terms[1], bound);
                } else if (!a_bound or !b_bound) return safety_error;
            },
            .aggregate => |aggregate| {
                try self.validateAggregate(aggregate, bound, outer_variables, safety_error);
                try bindTermVariables(self.allocator, aggregate.output, bound);
            },
        }
    }

    fn validateAggregate(
        self: *Jatalog,
        aggregate: Aggregate,
        outer_bound: *const std.AutoHashMapUnmanaged(Id, void),
        outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
        safety_error: anyerror,
    ) anyerror!void {
        if (aggregate.body.len == 0) return safety_error;
        var inner_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer inner_variables.deinit(self.allocator);
        try collectTermVariables(self.allocator, aggregate.template, &inner_variables);
        for (aggregate.body) |clause| try collectClauseAllVariables(self.allocator, clause, &inner_variables);

        var inner_bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer inner_bound.deinit(self.allocator);
        var iterator = inner_variables.keyIterator();
        while (iterator.next()) |variable| {
            if (!outer_variables.contains(variable.*)) continue;
            if (!outer_bound.contains(variable.*)) return safety_error;
            try inner_bound.put(self.allocator, variable.*, {});
        }

        var inner_outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer inner_outer_variables.deinit(self.allocator);
        try collectTermVariables(self.allocator, aggregate.template, &inner_outer_variables);
        for (aggregate.body) |clause|
            try collectClauseSurfaceVariables(self.allocator, clause, &inner_outer_variables);

        const ordered = try self.orderClauses(aggregate.body);
        defer self.allocator.free(ordered);
        for (ordered) |clause|
            try self.validateClause(clause, &inner_bound, &inner_outer_variables, safety_error);
        if (!termVariablesBound(aggregate.template, &inner_bound)) return safety_error;
    }

    fn orderClauses(self: *Jatalog, clauses: []const Clause) ![]Clause {
        const result = try self.allocator.alloc(Clause, clauses.len);
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
                if (isArithmetic(self, expression)) {
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
                (expression.kind != .equality and !isArithmetic(self, expression)))
            {
                result[index] = clause;
                index += 1;
            },
            else => {},
        };
        return result;
    }

    fn validateStratification(self: *Jatalog) !void {
        var levels = try self.computeStrata();
        levels.deinit(self.allocator);
    }

    fn computeStrata(self: *Jatalog) !std.array_hash_map.Auto(PredicateKey, usize) {
        var levels: std.array_hash_map.Auto(PredicateKey, usize) = .empty;
        errdefer levels.deinit(self.allocator);
        for (self.rules.items) |rule| {
            try levels.put(self.allocator, predicateKey(rule.head), 0);
            for (rule.body) |clause| try self.collectDependencyPredicates(clause, &levels);
        }
        const predicate_count = levels.count();
        for (0..predicate_count + 1) |iteration| {
            var changed = false;
            for (self.rules.items) |rule| {
                var required: usize = 0;
                for (rule.body) |clause|
                    required = @max(required, self.clauseRequiredStratum(clause, &levels, false));
                const head = predicateKey(rule.head);
                const current = levels.get(head) orelse 0;
                if (required > current) {
                    try levels.put(self.allocator, head, required);
                    changed = true;
                }
            }
            if (!changed) return levels;
            if (iteration == predicate_count) return Error.NotStratified;
        }
        return levels;
    }

    fn collectDependencyPredicates(
        self: *Jatalog,
        clause: Clause,
        levels: *std.array_hash_map.Auto(PredicateKey, usize),
    ) !void {
        switch (clause) {
            .relational => |expression| try levels.put(self.allocator, predicateKey(expression), 0),
            .negated => |expression| if (!isBuiltin(self, expression))
                try levels.put(self.allocator, predicateKey(expression), 0),
            .builtin => {},
            .aggregate => |aggregate| for (aggregate.body) |body_clause|
                try self.collectDependencyPredicates(body_clause, levels),
        }
    }

    fn clauseRequiredStratum(
        self: *const Jatalog,
        clause: Clause,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        aggregate_context: bool,
    ) usize {
        return switch (clause) {
            .relational => |expression| (levels.get(predicateKey(expression)) orelse 0) +
                @intFromBool(aggregate_context),
            .negated => |expression| if (isBuiltin(self, expression))
                0
            else
                (levels.get(predicateKey(expression)) orelse 0) + 1,
            .builtin => 0,
            .aggregate => |aggregate| blk: {
                var required: usize = 0;
                for (aggregate.body) |body_clause|
                    required = @max(required, self.clauseRequiredStratum(body_clause, levels, true));
                break :blk required;
            },
        };
    }

    fn deleteClauses(self: *Jatalog, goals: []const Clause) !bool {
        var answers = try self.evaluateClauses(goals);
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        var changed = false;
        var index = self.facts.items.len;
        while (index > 0) {
            index -= 1;
            const fact = self.facts.items[index];
            var remove = false;
            for (answers.items) |*answer| {
                for (goals) |clause| {
                    const goal = switch (clause) {
                        .relational => |expression| expression,
                        else => continue,
                    };
                    if (goal.predicate != fact.predicate or goal.terms.len != fact.terms.len) continue;
                    var matched = try answer.clone(self.allocator);
                    defer matched.deinit(self.allocator);
                    if (try self.unify(fact, goal, &matched)) remove = true;
                }
            }
            if (remove) {
                self.allocator.free(fact.terms);
                _ = self.facts.orderedRemove(index);
                changed = true;
            }
        }
        return changed;
    }

    fn writeValue(self: *const Jatalog, writer: *std.Io.Writer, value: ValueId) !void {
        switch (self.values.get(value)) {
            .scalar => |scalar_id| try self.scalars.write(writer, scalar_id),
            .nil => try writer.writeAll("[]"),
            .cons => |pair| if (self.isProperList(value)) {
                try writer.writeByte('[');
                var current = value;
                var first = true;
                while (true) {
                    switch (self.values.get(current)) {
                        .cons => |cell| {
                            if (!first) try writer.writeAll(", ");
                            try self.writeValue(writer, cell.head);
                            current = cell.tail;
                            first = false;
                        },
                        .nil => break,
                        else => unreachable,
                    }
                }
                try writer.writeByte(']');
            } else {
                try writer.writeAll("cons(");
                try self.writeValue(writer, pair.head);
                try writer.writeAll(", ");
                try self.writeValue(writer, pair.tail);
                try writer.writeByte(')');
            },
        }
    }

    fn isProperList(self: *const Jatalog, value: ValueId) bool {
        var current = value;
        while (true) switch (self.values.get(current)) {
            .nil => return true,
            .cons => |pair| current = pair.tail,
            else => return false,
        };
    }

    /// Numbers by value, atoms by spelling, nil, then cons cells recursively.
    fn compareValues(self: *const Jatalog, left: ValueId, right: ValueId) std.math.Order {
        const a = self.values.get(left);
        const b = self.values.get(right);
        const a_rank: u2 = switch (a) {
            .scalar => 0,
            .nil => 1,
            .cons => 2,
        };
        const b_rank: u2 = switch (b) {
            .scalar => 0,
            .nil => 1,
            .cons => 2,
        };
        if (a_rank != b_rank) return std.math.order(a_rank, b_rank);
        return switch (a) {
            .scalar => |a_scalar| switch (b) {
                .scalar => |b_scalar| self.scalars.compare(a_scalar, b_scalar),
                else => unreachable,
            },
            .nil => .eq,
            .cons => |a_pair| switch (b) {
                .cons => |b_pair| blk: {
                    const head_order = self.compareValues(a_pair.head, b_pair.head);
                    break :blk if (head_order != .eq) head_order else self.compareValues(a_pair.tail, b_pair.tail);
                },
                else => unreachable,
            },
        };
    }

    fn sortValues(self: *const Jatalog, values: []ValueId) void {
        if (values.len < 2) return;
        for (values[1..], 1..) |value, index| {
            var insertion = index;
            while (insertion > 0 and self.compareValues(value, values[insertion - 1]) == .lt) {
                values[insertion] = values[insertion - 1];
                insertion -= 1;
            }
            values[insertion] = value;
        }
    }
};

fn freeExpr(allocator: std.mem.Allocator, value: Expr) void {
    for (value.terms) |term| freeTerm(allocator, term);
    allocator.free(value.terms);
}

fn freeRule(allocator: std.mem.Allocator, rule: Rule) void {
    freeExpr(allocator, rule.head);
    for (rule.body) |clause| freeClauseTree(allocator, clause);
    allocator.free(rule.body);
}

fn cloneTerm(allocator: std.mem.Allocator, term: Term) !Term {
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

fn cloneExpr(allocator: std.mem.Allocator, expression: Expr) !Expr {
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
    };
}

fn cloneClause(allocator: std.mem.Allocator, clause: Clause) !Clause {
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

fn cloneRule(allocator: std.mem.Allocator, rule: Rule) !Rule {
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
    return .{ .head = head, .body = body, .seed_argument = rule.seed_argument };
}

fn freeClauseTree(allocator: std.mem.Allocator, clause: Clause) void {
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

fn freeTerm(allocator: std.mem.Allocator, term: Term) void {
    switch (term) {
        .cons => |pair| {
            freeTerm(allocator, pair.head);
            freeTerm(allocator, pair.tail);
            allocator.destroy(pair);
        },
        else => {},
    }
}

fn termVariablesBound(term: Term, bound: *const std.AutoHashMapUnmanaged(Id, void)) bool {
    return switch (term) {
        .variable => |variable| bound.contains(variable),
        .cons => |pair| termVariablesBound(pair.head, bound) and termVariablesBound(pair.tail, bound),
        else => true,
    };
}

fn bindTermVariables(
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

fn collectTermVariables(
    allocator: std.mem.Allocator,
    term: Term,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    try bindTermVariables(allocator, term, variables);
}

fn collectExprVariables(
    allocator: std.mem.Allocator,
    expression: Expr,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    for (expression.terms) |term| try collectTermVariables(allocator, term, variables);
}

fn collectClauseSurfaceVariables(
    allocator: std.mem.Allocator,
    clause: Clause,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| try collectExprVariables(allocator, expression, variables),
        .aggregate => |aggregate| try collectTermVariables(allocator, aggregate.output, variables),
    }
}

fn collectClauseAllVariables(
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

fn isVariable(string: []const u8) bool {
    return string.len != 0 and std.ascii.isUpper(string[0]);
}

fn goalKind(operator: []const u8) ?GoalKind {
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

fn goalOperator(kind: GoalKind) []const u8 {
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
    };
}

fn isBuiltin(_: *const Jatalog, value: Expr) bool {
    return value.kind != .relation;
}

fn isArithmetic(_: *const Jatalog, value: Expr) bool {
    return value.kind == .add or value.kind == .subtract;
}

fn termContainsCons(term: Term) bool {
    return switch (term) {
        .cons => true,
        else => false,
    };
}

fn termEqual(left: Term, right: Term) bool {
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

fn isTailDescendant(ancestor: Term, candidate: Term) bool {
    var current = ancestor;
    while (current == .cons) {
        current = current.cons.tail;
        if (termEqual(current, candidate)) return true;
    }
    return false;
}

fn factsEqual(a: Fact, b: Fact) bool {
    return a.predicate == b.predicate and std.mem.eql(Id, a.terms, b.terms);
}

fn containsFact(facts: []const Fact, needle: Fact) bool {
    for (facts) |fact| if (factsEqual(fact, needle)) return true;
    return false;
}

fn deinitFacts(allocator: std.mem.Allocator, facts: *std.ArrayList(Fact)) void {
    for (facts.items) |fact| allocator.free(fact.terms);
    facts.deinit(allocator);
}

const Parser = struct {
    jatalog: *Jatalog,
    source: []const u8,
    index: usize = 0,

    fn executeAll(self: *Parser) !ExecutionResult {
        var last: ?ExecutionResult = null;
        errdefer if (last) |*result| result.deinit();
        while (true) {
            self.skipSpace();
            if (self.index == self.source.len) return last orelse .none;
            if (last) |*result| result.deinit();
            last = null;
            var staging = try self.jatalog.clone();
            defer staging.deinit();
            var statement_parser = self.*;
            statement_parser.jatalog = &staging;
            const statement_result = try statement_parser.executeStatement();
            self.index = statement_parser.index;
            switch (statement_result) {
                .query => {},
                .none => self.jatalog.commit(&staging),
                .changed => |changed| if (changed) try self.jatalog.commitRetraction(&staging),
            }
            last = statement_result;
        }
    }

    fn executeStatement(self: *Parser) !ExecutionResult {
        const first = try self.parseClause();
        var first_owned = true;
        errdefer if (first_owned) freeClauseTree(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.consume(":-")) {
            const head = switch (first) {
                .relational => |expression| expression,
                else => return Error.InvalidRule,
            };
            var body: std.ArrayList(Clause) = .empty;
            defer body.deinit(self.jatalog.allocator);
            errdefer for (body.items) |clause| freeClauseTree(self.jatalog.allocator, clause);
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    freeClauseTree(self.jatalog.allocator, clause);
                    return err;
                };
                self.skipSpace();
                if (!self.consume(",")) break;
            }
            try self.expect(".");
            try self.jatalog.addRuleClauses(head, body.items);
            first_owned = false;
            return .none;
        }
        self.skipSpace();
        if (self.consume(".")) {
            const fact = switch (first) {
                .relational => |expression| expression,
                else => return Error.InvalidFact,
            };
            try self.jatalog.addFactExpr(fact);
            freeClauseTree(self.jatalog.allocator, first);
            first_owned = false;
            return .none;
        }

        var goals: std.ArrayList(Clause) = .empty;
        defer {
            for (goals.items) |clause| freeClauseTree(self.jatalog.allocator, clause);
            goals.deinit(self.jatalog.allocator);
        }
        try goals.append(self.jatalog.allocator, first);
        first_owned = false;
        while (self.consume(",")) {
            const goal = try self.parseClause();
            goals.append(self.jatalog.allocator, goal) catch |err| {
                freeClauseTree(self.jatalog.allocator, goal);
                return err;
            };
        }
        if (self.consume("?")) return .{ .query = try self.jatalog.queryClauses(goals.items) };
        if (self.consume("~")) return .{ .changed = try self.jatalog.deleteClauses(goals.items) };
        return Error.InvalidSyntax;
    }

    fn parseClause(self: *Parser) anyerror!Clause {
        self.skipSpace();
        if (self.peekKeyword("setof")) return .{ .aggregate = try self.parseAggregate() };
        const expression = try self.parseExpr();
        return self.jatalog.classifyExpr(expression);
    }

    fn parseAggregate(self: *Parser) anyerror!Aggregate {
        const keyword = try self.parseBare();
        if (!std.mem.eql(u8, keyword, "setof")) return Error.InvalidSyntax;
        try self.expect("(");
        const template = try self.parseTerm();
        var template_owned = true;
        errdefer if (template_owned) freeTerm(self.jatalog.allocator, template);
        try self.expect(",");

        var body: std.ArrayList(Clause) = .empty;
        errdefer {
            for (body.items) |clause| freeClauseTree(self.jatalog.allocator, clause);
            body.deinit(self.jatalog.allocator);
        }
        if (self.consume("(")) {
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    freeClauseTree(self.jatalog.allocator, clause);
                    return err;
                };
                if (self.consume(")")) break;
                try self.expect(",");
            }
        } else {
            const clause = try self.parseClause();
            body.append(self.jatalog.allocator, clause) catch |err| {
                freeClauseTree(self.jatalog.allocator, clause);
                return err;
            };
        }
        try self.expect(",");
        const output = try self.parseTerm();
        errdefer freeTerm(self.jatalog.allocator, output);
        try self.expect(")");
        const owned_body = try body.toOwnedSlice(self.jatalog.allocator);
        template_owned = false;
        return .{
            .template = template,
            .body = owned_body,
            .output = output,
        };
    }

    fn parseExpr(self: *Parser) !Expr {
        self.skipSpace();
        var negated = false;
        if (self.peekKeyword("not")) {
            _ = try self.parseBare();
            negated = true;
        }
        const first = try self.parseTerm();
        var first_owned = true;
        errdefer if (first_owned) freeTerm(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.parseOperator()) |operator| {
            const second = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, second);
            if (std.mem.eql(u8, operator, "=")) {
                const arithmetic: ?GoalKind = if (self.consume("+"))
                    .add
                else if (self.consume("-"))
                    .subtract
                else
                    null;
                if (arithmetic) |arithmetic_kind| {
                    if (negated) return Error.InvalidSyntax;
                    const third = try self.parseTerm();
                    errdefer freeTerm(self.jatalog.allocator, third);
                    const predicate = try self.jatalog.strings.intern(goalOperator(arithmetic_kind));
                    const terms = try self.jatalog.allocator.alloc(Term, 3);
                    terms[0] = first;
                    terms[1] = second;
                    terms[2] = third;
                    first_owned = false;
                    return .{ .predicate = predicate, .terms = terms, .kind = arithmetic_kind };
                }
            }
            const kind = goalKind(operator) orelse return Error.UnknownOperator;
            const predicate = try self.jatalog.strings.intern(goalOperator(kind));
            const terms = try self.jatalog.allocator.alloc(Term, 2);
            terms[0] = first;
            terms[1] = second;
            first_owned = false;
            return .{
                .predicate = predicate,
                .terms = terms,
                .negated = negated,
                .kind = kind,
            };
        }
        if (!self.consume("(")) return Error.InvalidSyntax;
        const predicate = switch (first) {
            .scalar => |scalar_id| switch (self.jatalog.scalars.get(scalar_id)) {
                .atom => |atom| try self.jatalog.strings.intern(atom),
                .integer, .float => return Error.InvalidSyntax,
            },
            else => return Error.InvalidSyntax,
        };
        first_owned = false;
        var terms: std.ArrayList(Term) = .empty;
        errdefer {
            for (terms.items) |term| freeTerm(self.jatalog.allocator, term);
            terms.deinit(self.jatalog.allocator);
        }
        self.skipSpace();
        if (!self.consume(")")) {
            while (true) {
                const term = try self.parseTerm();
                terms.append(self.jatalog.allocator, term) catch |err| {
                    freeTerm(self.jatalog.allocator, term);
                    return err;
                };
                self.skipSpace();
                if (self.consume(")")) break;
                try self.expect(",");
            }
        }
        return .{ .predicate = predicate, .terms = try terms.toOwnedSlice(self.jatalog.allocator), .negated = negated };
    }

    fn parseTerm(self: *Parser) anyerror!Term {
        var head = try self.parseTermPrimary();
        errdefer freeTerm(self.jatalog.allocator, head);
        if (self.consumeConsBang()) {
            const tail = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, tail);
            head = try self.makeCons(head, tail);
        }
        return head;
    }

    fn parseTermPrimary(self: *Parser) anyerror!Term {
        self.skipSpace();
        if (self.index == self.source.len) return Error.InvalidSyntax;
        if (self.consume("[")) return self.parseListTail();
        if (self.source[self.index] == '"' or self.source[self.index] == '\'') {
            const quote = self.source[self.index];
            self.index += 1;
            var string: std.ArrayList(u8) = .empty;
            defer string.deinit(self.jatalog.allocator);
            while (self.index < self.source.len and self.source[self.index] != quote) {
                if (self.source[self.index] == '\\' and self.index + 1 < self.source.len) self.index += 1;
                try string.append(self.jatalog.allocator, self.source[self.index]);
                self.index += 1;
            }
            if (self.index == self.source.len) return Error.InvalidSyntax;
            self.index += 1;
            return .{ .scalar = try self.jatalog.scalars.internAtom(string.items) };
        }
        const value = try self.parseBare();
        if (std.mem.eql(u8, value, "cons") and self.consume("(")) {
            const head = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, head);
            try self.expect(",");
            const tail = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, tail);
            try self.expect(")");
            return self.makeCons(head, tail);
        }
        if (isVariable(value)) return .{ .variable = try self.jatalog.strings.intern(value) };
        return .{ .scalar = try self.jatalog.scalars.parseBare(value) };
    }

    fn parseListTail(self: *Parser) anyerror!Term {
        if (self.consume("]")) return .nil;
        const head = try self.parseTerm();
        errdefer freeTerm(self.jatalog.allocator, head);
        var tail: Term = undefined;
        if (self.consume("]")) {
            tail = .nil;
        } else if (self.consume(",")) {
            tail = try self.parseListTail();
        } else if (self.consumeConsBang()) {
            tail = try self.parseImproperListTail();
        } else return Error.InvalidSyntax;
        errdefer freeTerm(self.jatalog.allocator, tail);
        return self.makeCons(head, tail);
    }

    fn parseImproperListTail(self: *Parser) anyerror!Term {
        const tail = try self.parseTerm();
        errdefer freeTerm(self.jatalog.allocator, tail);
        try self.expect("]");
        return tail;
    }

    fn makeCons(self: *Parser, head: Term, tail: Term) !Term {
        const pair = try self.jatalog.allocator.create(Term.Cons);
        pair.* = .{ .head = head, .tail = tail };
        return .{ .cons = pair };
    }

    fn parseBare(self: *Parser) ![]const u8 {
        self.skipSpace();
        const start = self.index;
        while (self.index < self.source.len) : (self.index += 1) {
            const c = self.source[self.index];
            if (std.ascii.isAlphanumeric(c) or c == '_') continue;
            if (c == '.' and self.index > start and self.index + 1 < self.source.len and
                std.ascii.isDigit(self.source[self.index - 1]) and
                std.ascii.isDigit(self.source[self.index + 1])) continue;
            if ((c == '+' or c == '-') and (self.index == start or
                (self.index > start and (self.source[self.index - 1] == 'e' or
                    self.source[self.index - 1] == 'E')))) continue;
            break;
        }
        if (self.index == start) return Error.InvalidSyntax;
        return self.source[start..self.index];
    }

    fn parseOperator(self: *Parser) ?[]const u8 {
        self.skipSpace();
        const operators = [_][]const u8{ "!=", "<>", "<=", ">=", "=", "<", ">" };
        for (operators) |operator| if (self.consume(operator)) return operator;
        return null;
    }

    fn skipSpace(self: *Parser) void {
        while (self.index < self.source.len) {
            if (std.ascii.isWhitespace(self.source[self.index])) {
                self.index += 1;
            } else if (self.source[self.index] == '%') {
                while (self.index < self.source.len and self.source[self.index] != '\n') self.index += 1;
            } else if (std.mem.startsWith(u8, self.source[self.index..], "//")) {
                while (self.index < self.source.len and self.source[self.index] != '\n') self.index += 1;
            } else if (std.mem.startsWith(u8, self.source[self.index..], "/*")) {
                const end = std.mem.indexOfPos(u8, self.source, self.index + 2, "*/") orelse {
                    self.index = self.source.len;
                    return;
                };
                self.index = end + 2;
            } else return;
        }
    }

    fn consume(self: *Parser, token: []const u8) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], token)) return false;
        self.index += token.len;
        return true;
    }

    fn consumeConsBang(self: *Parser) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], "!") or
            std.mem.startsWith(u8, self.source[self.index..], "!=")) return false;
        self.index += 1;
        return true;
    }

    fn expect(self: *Parser, token: []const u8) !void {
        if (!self.consume(token)) return Error.InvalidSyntax;
    }

    fn peekKeyword(self: *Parser, keyword: []const u8) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], keyword)) return false;
        const end = self.index + keyword.len;
        return end == self.source.len or !(std.ascii.isAlphanumeric(self.source[end]) or self.source[end] == '_');
    }
};

test "string table maps strings to stable ids and back" {
    var table: StringTable = .init(std.testing.allocator);
    defer table.deinit();
    const alice = try table.intern("alice");
    try std.testing.expectEqual(alice, try table.intern("alice"));
    try std.testing.expectEqualStrings("alice", table.resolve(alice));
}

test "recursive query and numeric builtins" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\parent(alice, bob). parent(bob, carol).
        \\ancestor(X, Y) :- parent(X, Y).
        \\ancestor(X, Y) :- ancestor(X, Z), parent(Z, Y).
        \\ancestor(X, carol), X != carol?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
}

test "stratified negation and retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). employed(alice).
        \\idle(X) :- person(X), not employed(X).
        \\idle(X)?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();
    result = try db.execute("person(bob)~");
    defer result.deinit();
    try std.testing.expect(result.changed);
}

test "negative recursion is rejected" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NotStratified, db.execute(
        \\p(X) :- q(X).
        \\q(X) :- not p(X), seed(X).
    ));
}

test "a parse error after a query releases the previous result" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidSyntax, db.execute(
        \\p(a). p(X)?
        \\bad(X) :- q(X), X <>.
    ));
}

fn expectBindingValue(
    _: *const Jatalog,
    binding: *const Answer,
    variable: []const u8,
    expected: []const u8,
) !void {
    const value = try binding.getValue(variable);
    const formatted = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(formatted);
    try std.testing.expectEqualStrings(expected, formatted);
}

test "lists round trip through queries and nested terms unify structurally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\nested([a, [b, []]]).
        \\nested(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "X", "[a, [b, []]]");
}

test "head tail patterns work in rules and cons syntax is equivalent" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items(cons(a, cons(b, []))).
        \\tail(T) :- items(H!T).
        \\tail(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "X", "[b]");
}

test "repeated variables inside structures enforce equality" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\pair([a, [a]]). pair([a, [b]]).
        \\pair([X, [X]])?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));
}

test "facts reject variables at every structural depth" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidFact, db.execute("bad([a, X])."));
    try std.testing.expectError(Error.InvalidFact, db.execute("bad(a!T)."));

    var result = try db.execute("improper(a!b). improper(X)?");
    defer result.deinit();
    try expectBindingValue(&db, &result.query.answers.items[0], "X", "cons(a, b)");
}

test "structural equality binds variables recursively and parse errors clean up" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("seed(a). seed(X), [X] = [a]?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));

    try std.testing.expectError(Error.InvalidSyntax, db.execute("broken([a, [b])."));
}

test "ground values have a deterministic structural total order" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\value(z). value(a). value('1'). value(-2). value(10). value(2). value([]).
        \\value([-1]). value(cons(a, z)). value([a]). value([a, b]).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[-2, 2, 10, '1', a, z, [], [-1], cons(a, z), [a], [a, b]]",
    );
}

fn structuralAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items([a, [b], c]).
        \\tail(T) :- items(H!T).
        \\tail([X, c])?
    );
    defer result.deinit();
    const value = try result.query.answers.items[0].getValue("X");
    const formatted = try value.formatAlloc(allocator);
    defer allocator.free(formatted);
    try std.testing.expectEqualStrings("[b]", formatted);
}

test "structural parsing and evaluation release every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        structuralAllocationScenario,
        .{},
    );
}

test "correlated aggregate clauses parse and validate without evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). parent(alice, bob). passed(bob).
        \\children(X, S) :- person(X), setof([Y, X], (parent(X, Y), passed(Y)), S).
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.rules.items.len);
    try std.testing.expect(db.rules.items[0].body[0] == .relational);
    const aggregate = db.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), aggregate.body.len);
    try std.testing.expect(aggregate.body[0] == .relational);
    try std.testing.expect(aggregate.body[1] == .relational);
}

test "rule bodies classify every clause kind distinctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(a).
        \\classified(X, S) :- seed(X), X = X, not blocked(X), setof(Y, item(X, Y), S).
    );
    defer result.deinit();
    const body = db.rules.items[0].body;
    try std.testing.expect(body[0] == .relational);
    try std.testing.expect(body[1] == .builtin);
    try std.testing.expect(body[2] == .aggregate);
    try std.testing.expect(body[3] == .negated);
}

test "aggregate safety rejects unbound correlations and escaping locals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidRule, db.execute(
        "bad(X, S) :- setof(Y, parent(X, Y), S).",
    ));
    try std.testing.expectError(Error.InvalidRule, db.execute(
        "bad(Y, S) :- seed(k), setof(Y, parent(X, Y), S).",
    ));
}

test "aggregate output binds head variables and aggregate locals stay local" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\all_parents(S) :- seed(k), setof([X, Y], parent(X, Y), S).
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.rules.items.len);
}

test "nested aggregates are represented directly and validate recursively" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\grouped(S) :- seed(k), setof(T, (group(G), setof(Y, parent(G, Y), T)), S).
    );
    defer result.deinit();
    const outer = db.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), outer.body.len);
    try std.testing.expect(outer.body[1] == .aggregate);
}

test "direct and indirect recursion through aggregation are rejected" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(Error.NotStratified, direct.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, p(X), S).
    ));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(Error.NotStratified, indirect.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, q(X), S).
        \\q(X) :- p(X).
    ));
}

test "positive recursion may complete below an aggregate stratum" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all_reachable(S) :- seed(k), setof([X, Y], reachable(X, Y), S).
    );
    defer result.deinit();
    var levels = try db.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const reachable: PredicateKey = .{ .name = db.strings.get("reachable").?, .arity = 2 };
    const all_reachable: PredicateKey = .{ .name = db.strings.get("all_reachable").?, .arity = 1 };
    try std.testing.expectEqual(@as(usize, 0), levels.get(reachable).?);
    try std.testing.expectEqual(@as(usize, 1), levels.get(all_reachable).?);
}

test "negation and aggregate strict edges share one dependency graph" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(a). excluded(b).
        \\allowed(X) :- seed(X), not excluded(X).
        \\summary(S) :- seed(a), setof(X, allowed(X), S).
    );
    defer result.deinit();
    var levels = try db.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const allowed: PredicateKey = .{ .name = db.strings.get("allowed").?, .arity = 1 };
    const summary: PredicateKey = .{ .name = db.strings.get("summary").?, .arity = 1 };
    try std.testing.expectEqual(@as(usize, 1), levels.get(allowed).?);
    try std.testing.expectEqual(@as(usize, 2), levels.get(summary).?);
}

test "grouped setof is sorted, deduplicated, and includes empty groups" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(bob). person(alice). parent(alice, carol). parent(alice, bob).
        \\from_left(X, Y) :- parent(X, Y).
        \\from_right(X, Y) :- parent(X, Y).
        \\child(X, Y) :- from_left(X, Y).
        \\child(X, Y) :- from_right(X, Y).
        \\children(X, S) :- person(X), setof(Y, child(X, Y), S).
        \\children(X, S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    for (result.query.answers.items) |*answer| {
        const person = try answer.getAtom("X");
        if (std.mem.eql(u8, person, "alice")) {
            try expectBindingValue(&db, answer, "S", "[bob, carol]");
        } else if (std.mem.eql(u8, person, "bob")) {
            try expectBindingValue(&db, answer, "S", "[]");
        } else return error.UnexpectedPerson;
    }
}

test "setof evaluates directly in queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("item(c). item(a). setof(X, item(X), S)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[a, c]");
}

test "setof sees completed recursive strata and preserves structural templates" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all(S) :- seed(k), setof([Y, X], reachable(X, Y), S).
        \\all(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[[b, a], [c, a], [c, b], [d, a], [d, b], [d, c]]",
    );
}

test "nested and multiple setof goals evaluate from correlated bindings" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). group(g2). group(g1). item(g1, b). item(g1, a).
        \\summary(All, Groups) :- seed(k), setof(X, item(g1, X), All),
        \\  setof([G, S], (group(G), setof(X, item(G, X), S)), Groups).
        \\summary(All, Groups)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "All", "[a, b]");
    try expectBindingValue(&db, &result.query.answers.items[0], "Groups", "[[g1, [a, b]], [g2, []]]");
}

test "setof recomputes after retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). item(b). item(a).
        \\items(S) :- seed(k), setof(X, item(X), S).
        \\item(b)~
    );
    result.deinit();
    result = try db.execute("items(S)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[a]");
}

test "setof ordering is independent of insertion and rule order" {
    var first: Jatalog = .init(std.testing.allocator);
    defer first.deinit();
    var first_result = try first.execute(
        \\seed(k). base(c). base(a). base(b).
        \\value(X) :- base(X).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\values(S)?
    );
    defer first_result.deinit();

    var second: Jatalog = .init(std.testing.allocator);
    defer second.deinit();
    var second_result = try second.execute(
        \\base(b). base(c). base(a). seed(k).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\value(X) :- base(X).
        \\values(S)?
    );
    defer second_result.deinit();

    const first_value = try first_result.query.answers.items[0].getValue("S");
    const first_text = try first_value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(first_text);
    const second_value = try second_result.query.answers.items[0].getValue("S");
    const second_text = try second_value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(second_text);
    try std.testing.expectEqualStrings(first_text, second_text);
}

fn aggregateEvaluationAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\group(g1). group(g2). item(g1, b). item(g1, a).
        \\grouped(Groups) :- group(g1), setof([G, S], (group(G), setof(X, item(G, X), S)), Groups).
        \\grouped(Groups)?
    );
    defer result.deinit();
}

test "aggregate evaluation releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        aggregateEvaluationAllocationScenario,
        .{},
    );
}

fn aggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\nested(S) :- seed(k), setof(T, (group(G), setof([Y, G], parent(G, Y), T)), S).
    );
    result.deinit();
    var malformed = db.execute("broken(S) :- seed(k), setof(X, (parent(X, Y), bad([Y])), S.") catch |err| switch (err) {
        Error.InvalidSyntax => return,
        else => return err,
    };
    malformed.deinit();
    return error.ExpectedInvalidSyntax;
}

test "aggregate parser errors release all partial clause trees" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        aggregateAllocationScenario,
        .{},
    );
}

fn floatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 1e-3). measure(c, 4.0).
        \\small(X) :- measure(X, V), V < 3.
        \\setof([X, V], measure(X, V), S)?
    );
    result.deinit();
    var overflow = db.execute("measure(d, 1e400).") catch |err| switch (err) {
        Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "float parsing evaluation and overflow release every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        floatAllocationScenario,
        .{},
    );
}

fn mixedArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 0.5).
        \\shifted(X, S) :- measure(X, V), S = V + 0.5.
        \\setof([X, S], shifted(X, S), Out)?
    );
    result.deinit();
    var overflow = db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
    ) catch |err| switch (err) {
        Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "mixed arithmetic releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        mixedArithmeticAllocationScenario,
        .{},
    );
}

test "recursive list length and sum use checked integer arithmetic" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
        \\numbers([1, 2, 3]).
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\total(N) :- numbers(S), sum(S, N).
        \\numchildren(X, N)?
    );
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("total(N)?");
    try std.testing.expectEqual(@as(i64, 6), try result.query.answers.items[0].getInteger("N"));
    result.deinit();

    result = try db.execute("person(alice), 3 = 1 + 2, -2 = 1 - 3?");
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("person(alice), 4 = 1 + 2?");
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
    result.deinit();

    try std.testing.expectError(Error.NumericType, db.execute("person(alice), N = nope + 1?"));
    try std.testing.expectError(
        Error.NumericOverflow,
        db.execute("person(alice), N = 9223372036854775807 + 1?"),
    );
}

test "ground list query inputs seed recursive evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var result = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([3, 3, 3], Total)?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try result.query.answers.items[0].getInteger("Total"));
    result.deinit();

    result = try db.execute(
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\length([a, b, c], Count)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 3), try result.query.answers.items[0].getInteger("Count"));

    const value_count_before_typed_query = db.values.values.items.len;
    var query_result = try db.query(&.{input.relation("sum", &.{
        input.list(&.{ input.integer(4), input.integer(5) }),
        input.variable("total"),
    })});
    defer query_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), query_result.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try query_result.answers.items[0].getInteger("total"));
    try std.testing.expectEqual(value_count_before_typed_query, db.values.values.items.len);

    var open_result = try db.execute("sum(Input, Total)?");
    defer open_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), open_result.query.answers.items.len);
    try expectBindingValue(&db, &open_result.query.answers.items[0], "Input", "[]");
    try std.testing.expectEqual(@as(i64, 0), try open_result.query.answers.items[0].getInteger("Total"));

    var structural_result = try db.execute("Value = [a, b]?");
    defer structural_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), structural_result.query.answers.items.len);
    try expectBindingValue(&db, &structural_result.query.answers.items[0], "Value", "[a, b]");
}

test "member and collectfirst are ordinary admissible list relations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items([a, b, c]).
        \\member(X, H!T) :- X = H.
        \\member(X, H!T) :- member(X, T).
        \\collectfirst([], []).
        \\collectfirst([H, K]!T, H!R) :- collectfirst(T, R).
        \\score(s1, 10). score(s2, 10). score(s3, 20). seed(k).
        \\bag(S) :- seed(k), setof([Score, Student], score(Student, Score), Pairs), collectfirst(Pairs, S).
        \\items(S), member(X, S)?
    );
    try std.testing.expectEqual(@as(usize, 3), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("bag(S)?");
    const value = try result.query.answers.items[0].getValue("S");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[10, 10, 20]", text);
    result.deinit();
}

test "structurally growing recursion is not admissible" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NotAdmissible, db.execute(
        \\q([X]) :- q(X).
    ));
}

test "non-recursive rules may construct structural head values" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\item(a).
        \\wrapped([X]) :- item(X).
        \\wrapped(Value)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "Value", "[a]");
}

test "structurally recursive rules retain their proven input seed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\base(a).
        \\p([a]).
        \\p(H!T) :- base(H), p(T).
        \\p(Value)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "Value", "[a]");
}

test "recursive arithmetic generators are not admissible" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(Error.NotAdmissible, direct.execute(
        \\number(0).
        \\number(N) :- number(M), N = M + 1.
    ));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(Error.NotAdmissible, indirect.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    ));
}

fn recursiveArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = db.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    ) catch |err| switch (err) {
        Error.NotAdmissible => return,
        else => return err,
    };
    result.deinit();
    return error.ExpectedNotAdmissible;
}

test "recursive arithmetic rejection is allocation safe" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        recursiveArithmeticAllocationScenario,
        .{},
    );
}

test "stratification distinguishes predicate arities" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\p(a, b). seed(k).
        \\p(S) :- seed(k), setof([X, Y], p(X, Y), S).
        \\p(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[[a, b]]");
}

test "embedding API constructs structural aggregate rules and queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("person", &.{input.atom("alice")});
    try db.addFact("person", &.{input.atom("bob")});
    try db.addFact("parent", &.{ input.atom("alice"), input.atom("bob") });

    const x = input.variable("x");
    const y = input.variable("y");
    const children = input.variable("children");
    const aggregate_body = [_]input.Goal{input.relation("parent", &.{ x, y })};
    try db.addRule(
        input.relation("children", &.{ x, children }),
        &.{
            input.relation("person", &.{x}),
            input.setof(y, &aggregate_body, children),
        },
    );

    var result = try db.query(&.{input.relation("children", &.{ x, children })});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.answers.items.len);
    for (result.answers.items) |*answer| {
        const person_name = try answer.getAtom("x");
        if (std.mem.eql(u8, person_name, "alice")) {
            try expectBindingValue(&db, answer, "children", "[bob]");
        } else {
            try std.testing.expectEqualStrings("bob", person_name);
            try expectBindingValue(&db, answer, "children", "[]");
        }
    }
}

test "typed nested setof matches source aggregate semantics" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("group", &.{input.atom("g1")});
    try db.addFact("group", &.{input.atom("g2")});
    try db.addFact("item", &.{ input.atom("g1"), input.atom("a") });

    const group = input.variable("group");
    const item = input.variable("item");
    const values = input.variable("values");
    const groups = input.variable("groups");
    const inner_body = [_]input.Goal{input.relation("item", &.{ group, item })};
    const outer_body = [_]input.Goal{
        input.relation("group", &.{group}),
        input.setof(item, &inner_body, values),
    };
    var result = try db.query(&.{input.setof(
        input.list(&.{ group, values }),
        &outer_body,
        groups,
    )});
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.answers.items[0],
        "groups",
        "[[g1, [a]], [g2, []]]",
    );
}

fn embeddedAggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("item", &.{input.atom("b")});
    try db.addFact("item", &.{input.atom("a")});

    const x = input.variable("x");
    const output = input.variable("output");
    const body = [_]input.Goal{input.relation("item", &.{x})};
    var result = try db.query(&.{input.setof(input.list(&.{x}), &body, output)});
    defer result.deinit();
    try expectBindingValue(&db, &result.answers.items[0], "output", "[[a], [b]]");
}

test "embedding aggregate ownership is allocation safe" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        embeddedAggregateAllocationScenario,
        .{},
    );
}

test "aggregate retraction is correct across the complete language tour" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
        \\numchildren(X, N)?
    );
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("parent(alice, bob)~");
    try std.testing.expect(result.changed);
    result.deinit();

    result = try db.execute("children(alice, S), numchildren(alice, N)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[]");
    try std.testing.expectEqual(@as(i64, 0), try result.query.answers.items[0].getInteger("N"));
}

test "public errors distinguish each aggregation failure boundary" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidSyntax, db.execute("broken([a)."));
    try std.testing.expectError(
        Error.InvalidRule,
        db.execute("bad(X, S) :- setof(Y, parent(X, Y), S)."),
    );
    try std.testing.expectError(
        Error.NotStratified,
        db.execute("seed(k). cycle(S) :- seed(k), setof(X, cycle(X), S)."),
    );
    try std.testing.expectError(
        Error.InvalidQuery,
        db.query(&.{input.add(input.variable("x"), input.variable("y"), input.integer(1))}),
    );
    try std.testing.expectError(Error.NotAdmissible, db.execute("grow([X]) :- grow(X)."));
}

test "public source interface canonicalizes the complete i64 domain" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(0). number(-0). number(+0). number(00).
        \\number(1). number(01). number(+1).
        \\number(-9223372036854775808). number(9223372036854775807).
        \\setof(X, number(X), Values)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "Values",
        "[-9223372036854775808, 0, 1, 9223372036854775807]",
    );

    try std.testing.expectError(Error.NumericOverflow, db.execute("number(9223372036854775808)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("number(-9223372036854775809)."));
}

test "quoted numeric atoms remain distinct from numeric scalars" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("value(1). value('1'). value('1.0'). setof(X, value(X), S)?");
    defer result.deinit();
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[1, '1', '1.0']");

    var inequality = try db.execute("1 = '1'?");
    defer inequality.deinit();
    try std.testing.expectEqual(@as(usize, 0), inequality.query.answers.items.len);

    var quoted_float = try db.execute("1000 = '1e3'?");
    defer quoted_float.deinit();
    try std.testing.expectEqual(@as(usize, 0), quoted_float.query.answers.items.len);

    var nested = try db.execute("nested([1]). nested(['1']). nested([1.0]). nested([1])?");
    defer nested.deinit();
    try std.testing.expectEqual(@as(usize, 1), nested.query.answers.items.len);

    var quoted_setof = try db.execute("text('2.5'). text(2.5). setof(X, text(X), S)?");
    defer quoted_setof.deinit();
    try expectBindingValue(&db, &quoted_setof.query.answers.items[0], "S", "[2.5, '2.5']");

    var arithmetic = try db.execute("01 = +0 + 1?");
    defer arithmetic.deinit();
    try std.testing.expectEqual(@as(usize, 1), arithmetic.query.answers.items.len);

    try std.testing.expectError(Error.NumericType, db.execute("value(X), X < 2?"));
}

test "float literals parse and integral values canonicalize to integers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\value(2.5). value(0.5). value(-0.025). value(1.0).
        \\value(1). value(1e0). value(1e3). value(-0.0).
        \\value(0). value(1e-999).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[-0.025, 0, 0.5, 1, 2.5, 1000]",
    );

    var canonical = try db.execute("nested([1.0]). nested([1])?");
    defer canonical.deinit();
    try std.testing.expectEqual(@as(usize, 1), canonical.query.answers.items.len);

    var integral = try db.execute("value(X), X = 1e0?");
    defer integral.deinit();
    try std.testing.expectEqual(@as(usize, 1), integral.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 1),
        try integral.query.answers.items[0].getInteger("X"),
    );
}

test "float extremes format deterministically and round-trip" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\extreme(5e-324). extreme(2.2250738585072014e-308).
        \\extreme(1.7976931348623157e308). extreme(-1.7976931348623157e308).
        \\extreme(1e300).
        \\setof(X, extreme(X), S)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[-1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, 1e300, " ++
            "1.7976931348623157e308]",
    );

    for ([_][]const u8{
        "extreme(5e-324)?",
        "extreme(2.2250738585072014e-308)?",
        "extreme(1.7976931348623157e308)?",
        "extreme(-1.7976931348623157e308)?",
        "extreme(1e300)?",
    }) |query| {
        var ground = try db.execute(query);
        defer ground.deinit();
        try std.testing.expectEqual(@as(usize, 1), ground.query.answers.items.len);
    }

    var formatted = try db.execute("half(0.5). half(X)?");
    defer formatted.deinit();
    const value = try formatted.query.answers.items[0].getValue("X");
    const spelled = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("0.5", spelled);
    try std.testing.expectEqual(ResultValue.Kind.float, value.kind());
    try std.testing.expectError(Error.TypeMismatch, value.getInteger());
}

test "non-finite and malformed numeric source reports stable errors" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NumericOverflow, db.execute("value(1e400)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("value(-1e400)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("value(2e308)."));

    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1e)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1e+)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1.2.3)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(12abc)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1.)."));

    var absent = try db.execute("value(X)?");
    defer absent.deinit();
    try std.testing.expectEqual(@as(usize, 0), absent.query.answers.items.len);
}

test "mixed numeric comparison and query-local float literals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var less = try db.execute("1.5 < 2?");
    defer less.deinit();
    try std.testing.expectEqual(@as(usize, 1), less.query.answers.items.len);

    var greater = try db.execute("2 < 1.5?");
    defer greater.deinit();
    try std.testing.expectEqual(@as(usize, 0), greater.query.answers.items.len);

    const scalar_count = db.scalars.values.items.len;
    var bound = try db.execute("X = 2.5?");
    const spelled = try (try bound.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    bound.deinit();
    try std.testing.expectEqual(scalar_count, db.scalars.values.items.len);
}

fn expectAnswerCount(db: *Jatalog, source: []const u8, expected: usize) !void {
    var result = try db.execute(source);
    defer result.deinit();
    try std.testing.expectEqual(expected, result.query.answers.items.len);
}

test "mixed arithmetic promotes to f64 and canonicalizes integral results" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var promoted = try db.execute("X = 1.5 + 1?");
    const spelled = try (try promoted.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    promoted.deinit();

    var integral = try db.execute("X = 1.5 + 2.5?");
    defer integral.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try integral.query.answers.items[0].getInteger("X"),
    );

    var negative = try db.execute("X = -0.5 - 0.5?");
    defer negative.deinit();
    try std.testing.expectEqual(
        @as(i64, -1),
        try negative.query.answers.items[0].getInteger("X"),
    );

    // Bound-output success, mismatch, and subtraction with both signs.
    try expectAnswerCount(&db, "4 = 1.5 + 2.5?", 1);
    try expectAnswerCount(&db, "5 = 1.5 + 2?", 0);
    try expectAnswerCount(&db, "-2.5 = -1.5 - 1?", 1);
    try expectAnswerCount(&db, "2.5 = 1 - -1.5?", 1);

    // Gradual underflow keeps exact subnormal results.
    try expectAnswerCount(
        &db,
        "1.1125369292536007e-308 = 2.2250738585072014e-308 - 1.1125369292536007e-308?",
        1,
    );
    try expectAnswerCount(&db, "0 = 5e-324 - 5e-324?", 1);

    // A mixed operation on an i64 extreme produces the rounded f64, which
    // stays a float because its integral value is outside the i64 range.
    var extreme = try db.execute("X = 9223372036854775807 + 0.5?");
    const extreme_spelled = try (try extreme.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(extreme_spelled);
    try std.testing.expectEqualStrings("9.223372036854776e18", extreme_spelled);
    extreme.deinit();

    try std.testing.expectError(Error.NumericOverflow, db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
    ));
    try std.testing.expectError(Error.NumericOverflow, db.execute(
        "N = -1.7976931348623157e308 - 1.7976931348623157e308?",
    ));
    try std.testing.expectError(Error.NumericType, db.execute("N = nope + 0.5?"));

    // Integer-only overflow behavior is unchanged by promotion.
    try std.testing.expectError(Error.NumericOverflow, db.execute(
        "N = 9223372036854775807 + 1?",
    ));
}

test "mixed equality and ordering are exact at numeric boundaries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    // Around 2^53: float literals canonicalize to their exact integer, so
    // nearby odd integers stay distinct.
    try expectAnswerCount(&db, "9007199254740993 > 9.007199254740992e15?", 1);
    try expectAnswerCount(&db, "9007199254740993 = 9.007199254740993e15?", 0);
    try expectAnswerCount(&db, "9007199254740992 = 9.007199254740992e15?", 1);

    // Both i64 limits against the adjacent representable floats.
    try expectAnswerCount(&db, "9223372036854775807 < 9.223372036854776e18?", 1);
    try expectAnswerCount(&db, "-9223372036854775808 = -9.223372036854775808e18?", 1);
    try expectAnswerCount(&db, "-9223372036854775807 > -9.223372036854776e18?", 1);

    // Adjacent representable floats around 1.
    try expectAnswerCount(&db, "1.0000000000000002 > 1?", 1);
    try expectAnswerCount(&db, "0.9999999999999999 < 1?", 1);
    try expectAnswerCount(&db, "1.0000000000000002 = 1?", 0);

    var ordered = try db.execute(
        \\near(0.9999999999999999). near(1). near(1.0000000000000002).
        \\setof(X, near(X), S)?
    );
    defer ordered.deinit();
    try expectBindingValue(
        &db,
        &ordered.query.answers.items[0],
        "S",
        "[0.9999999999999999, 1, 1.0000000000000002]",
    );
}

test "canonical numeric identity holds inside lists and nested aggregates" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var dedup = try db.execute(
        \\one(1). one(1.0). one(01). one(1e0). one('1'). one('1.0').
        \\setof(X, one(X), S)?
    );
    defer dedup.deinit();
    try expectBindingValue(&db, &dedup.query.answers.items[0], "S", "[1, '1', '1.0']");

    try expectAnswerCount(&db, "nested([1.0, 2.5]). nested([1, 2.5])?", 1);
    try expectAnswerCount(&db, "pair(cons(0.5, 1.0)). pair(cons(0.5, 1))?", 1);

    var grouped = try db.execute(
        \\kind(g). kind(h). item(g, 0.5). item(g, 1.0). item(g, 1). item(h, 2.5).
        \\grouped(Out) :- kind(g), setof([G, S], (kind(G), setof(V, item(G, V), S)), Out).
        \\grouped(Out)?
    );
    defer grouped.deinit();
    try expectBindingValue(
        &db,
        &grouped.query.answers.items[0],
        "Out",
        "[[g, [0.5, 1]], [h, [2.5]]]",
    );

    var summed = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([1, 0.5, 2.5], Total)?
    );
    defer summed.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try summed.query.answers.items[0].getInteger("Total"),
    );
}

test "source and typed mixed numeric operations produce identical answers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute("measure(a, 2.5). measure(b, 3). measure(c, 0.5).");
    setup.deinit();

    const x = input.variable("x");
    const v = input.variable("v");
    const s = input.variable("s");
    const d = input.variable("d");
    var typed = try db.query(&.{
        input.relation("measure", &.{ x, v }),
        input.compare(.less_than, v, input.integer(3)),
        input.add(s, v, input.integer(1)),
        input.subtract(d, v, input.integer(2)),
    });
    defer typed.deinit();

    var source = try db.execute("measure(X, V), V < 3, S = V + 1, D = V - 2?");
    defer source.deinit();

    try std.testing.expectEqual(@as(usize, 2), typed.answers.items.len);
    try std.testing.expectEqual(
        typed.answers.items.len,
        source.query.answers.items.len,
    );
    for (typed.answers.items, source.query.answers.items) |*typed_answer, *source_answer| {
        for ([_][2][]const u8{
            .{ "v", "V" },
            .{ "s", "S" },
            .{ "d", "D" },
        }) |names| {
            const typed_value = try (try typed_answer.getValue(names[0]))
                .formatAlloc(std.testing.allocator);
            defer std.testing.allocator.free(typed_value);
            const source_value = try (try source_answer.getValue(names[1]))
                .formatAlloc(std.testing.allocator);
            defer std.testing.allocator.free(source_value);
            try std.testing.expectEqualStrings(source_value, typed_value);
        }
    }

    const typed_shifted = try (try typed.answers.items[0].getValue("s"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(typed_shifted);
    try std.testing.expectEqualStrings("3.5", typed_shifted);
}

test "typed float descriptors canonicalize and getters never coerce" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("measure", &.{ input.atom("a"), input.float(2.5) });
    try db.addFact("measure", &.{ input.atom("b"), input.float(1.0) });
    try db.addFact("measure", &.{ input.atom("c"), input.float(-0.0) });
    try db.addFact("items", &.{input.list(&.{ input.float(0.5), input.integer(2) })});

    var fractional = try db.query(&.{
        input.relation("measure", &.{ input.atom("a"), input.variable("v") }),
    });
    defer fractional.deinit();
    const value = try fractional.answers.items[0].getValue("v");
    try std.testing.expectEqual(ResultValue.Kind.float, value.kind());
    try std.testing.expectEqual(@as(f64, 2.5), try fractional.answers.items[0].getFloat("v"));
    try std.testing.expectError(Error.TypeMismatch, fractional.answers.items[0].getInteger("v"));
    try std.testing.expectError(Error.TypeMismatch, fractional.answers.items[0].getAtom("v"));
    try std.testing.expectError(Error.UnknownVariable, fractional.answers.items[0].getFloat("missing"));

    // Integral typed floats canonicalize to integers, so the float getter
    // reports TypeMismatch and the integer getter succeeds.
    var canonical = try db.query(&.{
        input.relation("measure", &.{ input.atom("b"), input.variable("v") }),
    });
    defer canonical.deinit();
    try std.testing.expectEqual(@as(i64, 1), try canonical.answers.items[0].getInteger("v"));
    try std.testing.expectError(Error.TypeMismatch, canonical.answers.items[0].getFloat("v"));

    // Identity across construction paths: source literals match typed facts.
    try expectAnswerCount(&db, "measure(a, 2.5)?", 1);
    try expectAnswerCount(&db, "measure(b, 1)?", 1);
    try expectAnswerCount(&db, "measure(c, 0)?", 1);
    try expectAnswerCount(&db, "items([0.5, 2])?", 1);

    // Typed retraction matches a fact added from source, and vice versa.
    var added = try db.execute("measure(d, 3.5).");
    added.deinit();
    try std.testing.expect(try db.retract(&.{
        input.relation("measure", &.{ input.atom("d"), input.float(3.5) }),
    }));
    try expectAnswerCount(&db, "measure(d, X)?", 0);
}

test "non-finite typed floats fail compilation transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const scalar_count = db.scalars.values.items.len;
    const fact_count = db.facts.items.len;

    try std.testing.expectError(
        Error.NumericType,
        db.addFact("bad", &.{input.float(std.math.nan(f64))}),
    );
    try std.testing.expectError(
        Error.NumericOverflow,
        db.addFact("bad", &.{input.float(std.math.inf(f64))}),
    );
    try std.testing.expectError(
        Error.NumericOverflow,
        db.addFact("bad", &.{input.float(-std.math.inf(f64))}),
    );
    try std.testing.expectError(
        Error.NumericOverflow,
        db.query(&.{input.relation("kept", &.{input.float(std.math.inf(f64))})}),
    );
    const v = input.variable("v");
    try std.testing.expectError(
        Error.NumericType,
        db.addRule(
            input.relation("derived", &.{v}),
            &.{input.equal(v, input.float(std.math.nan(f64)))},
        ),
    );

    try std.testing.expectEqual(scalar_count, db.scalars.values.items.len);
    try std.testing.expectEqual(fact_count, db.facts.items.len);
    try std.testing.expectEqual(@as(usize, 0), db.rules.items.len);
    try expectAnswerCount(&db, "kept(1)?", 1);
    try expectAnswerCount(&db, "bad(X)?", 0);
}

fn typedFloatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("measure", &.{ input.atom("a"), input.float(2.5) });
    try db.addFact("measure", &.{ input.atom("b"), input.float(1.0) });
    var result = try db.query(&.{
        input.relation("measure", &.{ input.variable("x"), input.variable("v") }),
        input.compare(.less_than, input.variable("v"), input.integer(3)),
        input.add(input.variable("s"), input.variable("v"), input.float(0.25)),
    });
    result.deinit();
    db.addFact("bad", &.{input.float(std.math.inf(f64))}) catch |err| switch (err) {
        error.NumericOverflow => return,
        else => return err,
    };
    return error.ExpectedNumericOverflow;
}

test "typed float input releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        typedFloatAllocationScenario,
        .{},
    );
}

test "integer identity is exact above 2^53 and recursive inside lists" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(9007199254740992). number(9007199254740993).
        \\nested([9007199254740992]). nested([9007199254740993]).
        \\number(X), X = 9007199254740993?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740993),
        try result.query.answers.items[0].getInteger("X"),
    );
    result.deinit();

    result = try db.execute("nested([X]), X = 9007199254740992?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740992),
        try result.query.answers.items[0].getInteger("X"),
    );
}

test "numeric comparisons reject every nonnumeric ground value kind" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). seed(X), X < 1?"));
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). [] < 1?"));
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). [1] < 2?"));
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). cons(1, 2) < 3?"));
}

test "typed descriptors cover scalars lists rules builtins negation and retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("age", &.{ input.atom("alice"), input.integer(20) });
    try db.addFact("age", &.{ input.atom("bob"), input.integer(17) });
    try db.addFact("banned", &.{input.atom("bob")});
    try db.addFact("payload", &.{input.atom("123")});

    const person = input.variable("person");
    const age = input.variable("age");
    try db.addRule(
        input.relation("adult", &.{person}),
        &.{
            input.relation("age", &.{ person, age }),
            input.compare(.greater_or_equal, age, input.integer(18)),
            input.not("banned", &.{person}),
        },
    );

    var result = try db.query(&.{input.relation("adult", &.{person})});
    try std.testing.expectEqual(@as(usize, 1), result.answers.items.len);
    try std.testing.expectEqualStrings("alice", try result.answers.items[0].getAtom("person"));
    result.deinit();

    const head = input.atom("head");
    const tail = input.atom("tail");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    try db.addFact("improper", &.{input.cons(&pair)});
    result = try db.query(&.{input.relation("improper", &.{input.variable("value")})});
    try expectBindingValue(&db, &result.answers.items[0], "value", "cons(head, tail)");
    result.deinit();

    try db.addFact("items", &.{input.list(&.{ input.integer(1), input.integer(2) })});
    const list_head = input.variable("list_head");
    const list_tail = input.variable("list_tail");
    const list_pair: input.Term.Cons = .{ .head = &list_head, .tail = &list_tail };
    try db.addRule(
        input.relation("tail", &.{list_tail}),
        &.{input.relation("items", &.{input.cons(&list_pair)})},
    );
    result = try db.query(&.{input.relation("tail", &.{input.variable("result")})});
    try expectBindingValue(&db, &result.answers.items[0], "result", "[2]");
    result.deinit();

    try std.testing.expect(try db.retract(&.{input.relation("age", &.{
        input.atom("bob"),
        input.integer(17),
    })}));
    result = try db.query(&.{input.relation("age", &.{ input.atom("bob"), input.variable("n") })});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
}

test "typed equality inequality and arithmetic use canonical integer identity" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const value = input.variable("value");
    const sum = input.variable("sum");
    var result = try db.query(&.{
        input.equal(value, input.integer(1)),
        input.notEqual(value, input.integer(2)),
        input.add(sum, value, input.integer(2)),
        input.equal(sum, input.integer(3)),
    });
    defer result.deinit();
    try std.testing.expectEqual(@as(i64, 1), try result.answers.items[0].getInteger("value"));
    try std.testing.expectEqual(@as(i64, 3), try result.answers.items[0].getInteger("sum"));

    try std.testing.expectError(
        Error.NumericOverflow,
        db.query(&.{input.add(
            sum,
            input.integer(std.math.maxInt(i64)),
            input.integer(1),
        )}),
    );
    try std.testing.expectError(
        Error.NumericType,
        db.query(&.{input.subtract(sum, input.atom("one"), input.integer(1))}),
    );

    var difference = try db.query(&.{input.subtract(
        input.variable("difference"),
        input.integer(-2),
        input.integer(3),
    )});
    try std.testing.expectEqual(
        @as(i64, -5),
        try difference.answers.items[0].getInteger("difference"),
    );
    difference.deinit();

    var mismatch = try db.query(&.{input.add(input.integer(0), input.integer(1), input.integer(2))});
    try std.testing.expectEqual(@as(usize, 0), mismatch.answers.items.len);
    mismatch.deinit();
    try std.testing.expectError(
        Error.NumericOverflow,
        db.query(&.{input.subtract(
            sum,
            input.integer(std.math.minInt(i64)),
            input.integer(1),
        )}),
    );
}

test "malformed and cyclic typed descriptors are rejected transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.atom("yes")});

    var cyclic: input.Term = undefined;
    var pair: input.Term.Cons = .{ .head = &cyclic, .tail = &cyclic };
    cyclic = input.cons(&pair);
    try std.testing.expectError(Error.InvalidTerm, db.addFact("broken", &.{cyclic}));

    var cyclic_items: [1]input.Term = undefined;
    cyclic_items[0] = input.list(&cyclic_items);
    try std.testing.expectError(Error.InvalidTerm, db.addFact("broken", &cyclic_items));

    var cyclic_goals: [1]input.Goal = undefined;
    cyclic_goals[0] = input.setof(input.integer(1), &cyclic_goals, input.variable("values"));
    try std.testing.expectError(Error.InvalidTerm, db.query(&cyclic_goals));

    try std.testing.expectError(Error.InvalidTerm, db.addFact("", &.{input.atom("value")}));
    try std.testing.expectError(
        Error.InvalidTerm,
        db.query(&.{input.relation("kept", &.{input.variable("")})}),
    );

    const shared_items = [_]input.Term{input.atom("shared")};
    const shared_list = input.list(&shared_items);
    try db.addFact("shared", &.{ shared_list, shared_list });

    var result = try db.query(&.{input.relation("kept", &.{input.variable("value")})});
    defer result.deinit();
    try std.testing.expectEqualStrings("yes", try result.answers.items[0].getAtom("value"));
}

test "query results own names scalars and structures after database destruction" {
    var db: Jatalog = .init(std.testing.allocator);
    var result = blk: {
        try db.addFact("answer", &.{input.list(&.{ input.atom("x"), input.integer(42) })});
        try db.addFact("scalars", &.{ input.atom("atom"), input.integer(7), input.float(2.5) });
        const query_result = try db.query(&.{
            input.relation("answer", &.{input.variable("value")}),
            input.relation("scalars", &.{
                input.variable("atom"),
                input.variable("integer"),
                input.variable("float"),
            }),
        });
        db.deinit();
        break :blk query_result;
    };
    defer result.deinit();

    const value = try result.answers.items[0].getValue("value");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[x, 42]", text);
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getAtom("value"));
    try std.testing.expectError(Error.UnknownVariable, result.answers.items[0].getInteger("missing"));
    try std.testing.expectEqualStrings("atom", try result.answers.items[0].getAtom("atom"));
    try std.testing.expectEqual(@as(i64, 7), try result.answers.items[0].getInteger("integer"));
    try std.testing.expectEqual(@as(f64, 2.5), try result.answers.items[0].getFloat("float"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getInteger("atom"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getAtom("integer"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getFloat("integer"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getInteger("float"));
    try std.testing.expectEqualStrings("x", try (try value.head()).getAtom());
    try std.testing.expectEqual(@as(i64, 42), try (try (try value.tail()).head()).getInteger());
}

test "novel typed queries release all query-local storage" {
    var tracking = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    var db: Jatalog = .init(tracking.allocator());
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const persistent_bytes = tracking.allocated_bytes - tracking.freed_bytes;

    for (0..100) |index| {
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "novel_{d}", .{index});
        var result = try db.query(&.{input.relation("missing", &.{input.atom(novel)})});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        const novel = @as(f64, @floatFromInt(index)) + 0.5;
        var result = try db.query(&.{input.relation("missing", &.{input.float(novel)})});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "retract_{d}", .{index});
        try std.testing.expect(!try db.retract(&.{input.relation("missing", &.{
            input.variable(novel),
        })}));
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    try db.addFact("temporary", &.{input.integer(1)});
    try std.testing.expect(try db.retract(&.{input.relation("temporary", &.{
        input.variable("warmup"),
    })}));
    const retracted_bytes = tracking.allocated_bytes - tracking.freed_bytes;
    for (0..100) |index| {
        try db.addFact("temporary", &.{input.integer(1)});
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "changed_{d}", .{index});
        try std.testing.expect(try db.retract(&.{input.relation("temporary", &.{
            input.variable(novel),
        })}));
        try std.testing.expectEqual(
            retracted_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }
}

test "source statements are atomic while prior statements remain committed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(
        Error.NumericOverflow,
        db.execute("kept(ok). rejected(9223372036854775808)."),
    );
    var result = try db.execute("kept(X)?");
    try std.testing.expectEqualStrings("ok", try result.query.answers.items[0].getAtom("X"));
    result.deinit();
    result = try db.execute("rejected(X)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
}

test "typed persistent operations roll back every allocation failure point" {
    var fact_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.addFact("added", &.{input.atom("fresh")});
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |_| {
            fact_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(fact_succeeded);

    var rule_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.addRule(
            input.relation("derived", &.{input.variable("x")}),
            &.{input.relation("kept", &.{input.variable("x")})},
        );
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |_| {
            rule_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var kept = try db.query(&.{input.relation("kept", &.{input.variable("x")})});
                defer kept.deinit();
                try std.testing.expectEqual(@as(i64, 1), try kept.answers.items[0].getInteger("x"));
                var absent = try db.query(&.{input.relation("derived", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(rule_succeeded);

    var retraction_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        try db.addFact("removed", &.{input.atom("value")});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.retract(&.{input.relation("removed", &.{input.variable("novel")})});
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |changed| {
            try std.testing.expect(changed);
            retraction_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var present = try db.query(&.{input.relation("removed", &.{input.variable("x")})});
                defer present.deinit();
                try std.testing.expectEqualStrings("value", try present.answers.items[0].getAtom("x"));
            },
            else => return err,
        }
    }
    try std.testing.expect(retraction_succeeded);
}

test "source persistent statements roll back every allocation failure point" {
    var observed_success = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.execute("added(fresh).");
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |result_value| {
            var result = result_value;
            result.deinit();
            observed_success = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(observed_success);
}
