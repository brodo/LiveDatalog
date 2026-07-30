//! A small, embeddable Datalog engine modeled after Jatalog.
const std = @import("std");

pub const Id = u64;
pub const ValueId = u64;
pub const Error = error{
    InvalidFact,
    InvalidRule,
    InvalidQuery,
    InvalidSyntax,
    NotStratified,
    UnboundVariable,
    UnknownOperator,
};

/// Interns every predicate, variable, and value used by a database. IDs are
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

const Value = union(enum) {
    atom: Id,
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
};

pub const Term = union(enum) {
    atom: Id,
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

pub const Expr = struct {
    predicate: Id,
    terms: []Term,
    negated: bool = false,

    pub fn arity(self: Expr) usize {
        return self.terms.len;
    }

    pub fn isGround(self: Expr) bool {
        for (self.terms) |term| if (!term.isGround()) return false;
        return true;
    }
};

pub const Rule = struct {
    head: Expr,
    body: []Clause,
};

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

const Fact = struct {
    predicate: Id,
    terms: []ValueId,
};

pub const Binding = struct {
    values: std.array_hash_map.Auto(Id, ValueId) = .empty,

    pub fn deinit(self: *Binding, allocator: std.mem.Allocator) void {
        self.values.deinit(allocator);
        self.* = undefined;
    }

    pub fn get(self: *const Binding, jatalog: *const Jatalog, variable: []const u8) ?[]const u8 {
        const variable_id = jatalog.strings.get(variable) orelse return null;
        const value_id = self.values.get(variable_id) orelse return null;
        return switch (jatalog.values.get(value_id)) {
            .atom => |atom| jatalog.strings.resolve(atom),
            else => null,
        };
    }

    pub fn getValue(self: *const Binding, jatalog: *const Jatalog, variable: []const u8) ?ValueId {
        const variable_id = jatalog.strings.get(variable) orelse return null;
        return self.values.get(variable_id);
    }

    fn clone(self: *const Binding, allocator: std.mem.Allocator) !Binding {
        return .{ .values = try self.values.clone(allocator) };
    }
};

pub const QueryResult = struct {
    allocator: std.mem.Allocator,
    answers: std.ArrayList(Binding) = .empty,

    pub fn deinit(self: *QueryResult) void {
        for (self.answers.items) |*answer| answer.deinit(self.allocator);
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
    values: ValueTable,
    facts: std.ArrayList(Fact) = .empty,
    rules: std.ArrayList(Rule) = .empty,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{ .allocator = allocator, .strings = .init(allocator), .values = .init(allocator) };
    }

    pub fn deinit(self: *Jatalog) void {
        for (self.facts.items) |fact| self.allocator.free(fact.terms);
        self.facts.deinit(self.allocator);
        for (self.rules.items) |rule| {
            freeExpr(self.allocator, rule.head);
            for (rule.body) |clause| freeClause(self.allocator, clause);
            self.allocator.free(rule.body);
        }
        self.rules.deinit(self.allocator);
        self.values.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    pub fn expr(self: *Jatalog, predicate: []const u8, terms: []const []const u8) !Expr {
        return self.makeExpr(predicate, terms, false);
    }

    pub fn not(self: *Jatalog, predicate: []const u8, terms: []const []const u8) !Expr {
        return self.makeExpr(predicate, terms, true);
    }

    pub fn freeExpression(self: *Jatalog, value: Expr) void {
        freeExpr(self.allocator, value);
    }

    fn makeExpr(self: *Jatalog, predicate: []const u8, terms: []const []const u8, negated: bool) !Expr {
        const predicate_id = try self.strings.intern(normalizeOperator(predicate));
        const result_terms = try self.allocator.alloc(Term, terms.len);
        var initialized: usize = 0;
        errdefer {
            for (result_terms[0..initialized]) |term| freeTerm(self.allocator, term);
            self.allocator.free(result_terms);
        }
        for (terms, result_terms) |source, *term| {
            var parser: Parser = .{ .jatalog = self, .source = source };
            term.* = try parser.parseTerm();
            initialized += 1;
            parser.skipSpace();
            if (parser.index != source.len) return Error.InvalidSyntax;
        }
        return .{ .predicate = predicate_id, .terms = result_terms, .negated = negated };
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const []const u8) !void {
        const value = try self.expr(predicate, terms);
        defer self.freeExpression(value);
        try self.addFactExpr(value);
    }

    pub fn addFactExpr(self: *Jatalog, value: Expr) !void {
        if (!value.isGround() or value.negated or isBuiltin(self, value)) return Error.InvalidFact;
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

    /// Takes ownership of `head` and every expression in `body` on success.
    pub fn addRule(self: *Jatalog, head: Expr, body: []Expr) !void {
        const clauses = try self.allocator.alloc(Clause, body.len);
        defer self.allocator.free(clauses);
        for (body, clauses) |expression, *clause| clause.* = self.classifyExpr(expression);
        try self.addRuleClauses(head, clauses);
    }

    fn addRuleClauses(self: *Jatalog, head: Expr, body: []Clause) !void {
        try self.validateRule(head, body);
        const owned_body = try self.orderClauses(body);
        errdefer self.allocator.free(owned_body);
        try self.rules.append(self.allocator, .{ .head = head, .body = owned_body });
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

    pub fn query(self: *Jatalog, goals: []const Expr) !QueryResult {
        if (goals.len == 0) return Error.InvalidQuery;
        try self.validateQuery(goals);

        var expanded = try self.cloneFacts();
        defer deinitFacts(self.allocator, &expanded);
        try self.expand(&expanded);

        const ordered = try self.orderGoals(goals);
        defer self.allocator.free(ordered);
        var result: QueryResult = .{ .allocator = self.allocator };
        errdefer result.deinit();
        var initial: Binding = .{};
        defer initial.deinit(self.allocator);
        try self.matchGoals(ordered, expanded.items, 0, &initial, &result.answers);
        return result;
    }

    fn queryClauses(self: *Jatalog, goals: []const Clause) !QueryResult {
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

        var expanded = try self.cloneFacts();
        defer deinitFacts(self.allocator, &expanded);
        try self.expand(&expanded);

        var result: QueryResult = .{ .allocator = self.allocator };
        errdefer result.deinit();
        var initial: Binding = .{};
        defer initial.deinit(self.allocator);
        try self.matchClauses(ordered, expanded.items, 0, &initial, &result.answers);
        return result;
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
                const before = facts.items.len;
                for (self.rules.items) |rule| {
                    if ((levels.get(rule.head.predicate) orelse 0) != level) continue;
                    var answers: std.ArrayList(Binding) = .empty;
                    defer {
                        for (answers.items) |*answer| answer.deinit(self.allocator);
                        answers.deinit(self.allocator);
                    }
                    var initial: Binding = .{};
                    defer initial.deinit(self.allocator);
                    try self.matchClauses(rule.body, facts.items, 0, &initial, &answers);
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
                if (facts.items.len == before) break;
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
            .atom => |atom| try self.values.intern(.{ .atom = atom }),
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

    fn matchGoals(
        self: *Jatalog,
        goals: []const Expr,
        facts: []const Fact,
        index: usize,
        bindings: *const Binding,
        answers: *std.ArrayList(Binding),
    ) !void {
        if (index == goals.len) {
            var answer = try bindings.clone(self.allocator);
            answers.append(self.allocator, answer) catch |err| {
                answer.deinit(self.allocator);
                return err;
            };
            return;
        }
        const goal = goals[index];
        if (isBuiltin(self, goal)) {
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            const matched = try self.evalBuiltin(goal, &next);
            if (matched != goal.negated) try self.matchGoals(goals, facts, index + 1, &next, answers);
            return;
        }
        if (goal.negated) {
            for (facts) |fact| {
                if (fact.predicate != goal.predicate or fact.terms.len != goal.terms.len) continue;
                var next = try bindings.clone(self.allocator);
                defer next.deinit(self.allocator);
                if (try self.unify(fact, goal, &next)) return;
            }
            try self.matchGoals(goals, facts, index + 1, bindings, answers);
            return;
        }
        for (facts) |fact| {
            if (fact.predicate != goal.predicate or fact.terms.len != goal.terms.len) continue;
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unify(fact, goal, &next))
                try self.matchGoals(goals, facts, index + 1, &next, answers);
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
            .atom => |atom| switch (self.values.get(value)) {
                .atom => |actual| actual == atom,
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
        if (expr_value.terms.len != 2) return Error.InvalidQuery;
        const operator = self.strings.resolve(expr_value.predicate);
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

        if (std.mem.eql(u8, operator, "=")) {
            if (left_id == null and right_id == null) return Error.UnboundVariable;
            if (left_id == null) return self.unifyValueTerm(right_id.?, left, bindings);
            if (right_id == null) return self.unifyValueTerm(left_id.?, right, bindings);
            return self.valuesEqual(left_id.?, right_id.?);
        }
        if (left_id == null or right_id == null) return Error.UnboundVariable;
        if (std.mem.eql(u8, operator, "<>")) return !self.valuesEqual(left_id.?, right_id.?);

        const left_number = parseNumber(self.atomString(left_id.?) orelse "") orelse 0;
        const right_number = parseNumber(self.atomString(right_id.?) orelse "") orelse 0;
        if (std.mem.eql(u8, operator, "<")) return left_number < right_number;
        if (std.mem.eql(u8, operator, "<=")) return left_number <= right_number;
        if (std.mem.eql(u8, operator, ">")) return left_number > right_number;
        if (std.mem.eql(u8, operator, ">=")) return left_number >= right_number;
        return Error.UnknownOperator;
    }

    fn atomString(self: *const Jatalog, value: ValueId) ?[]const u8 {
        return switch (self.values.get(value)) {
            .atom => |atom| self.strings.resolve(atom),
            else => null,
        };
    }

    fn valuesEqual(self: *const Jatalog, left: ValueId, right: ValueId) bool {
        const left_value = self.values.get(left);
        const right_value = self.values.get(right);
        return switch (left_value) {
            .atom => |left_atom| switch (right_value) {
                .atom => |right_atom| blk: {
                    const left_string = self.strings.resolve(left_atom);
                    const right_string = self.strings.resolve(right_atom);
                    const left_number = parseNumber(left_string);
                    const right_number = parseNumber(right_string);
                    if (left_number != null and right_number != null)
                        break :blk left_number.? == right_number.?;
                    break :blk std.mem.eql(u8, left_string, right_string);
                },
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

    fn validateRule(self: *Jatalog, head: Expr, body: []const Clause) !void {
        if (body.len == 0 or head.negated or isBuiltin(self, head)) return Error.InvalidRule;
        var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (head.terms) |term| try collectTermVariables(self.allocator, term, &outer_variables);
        for (body) |clause| try collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);

        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try self.orderClauses(body);
        defer self.allocator.free(ordered);
        for (ordered) |clause| try self.validateClause(clause, &bound, &outer_variables, Error.InvalidRule);
        for (head.terms) |term| if (!termVariablesBound(term, &bound)) return Error.InvalidRule;
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
                if (expression.terms.len != 2) return safety_error;
                const operator = self.strings.resolve(expression.predicate);
                const a_bound = termVariablesBound(expression.terms[0], bound);
                const b_bound = termVariablesBound(expression.terms[1], bound);
                if (std.mem.eql(u8, operator, "=") and !expression.negated) {
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
            .builtin => |expression| if (!expression.negated and
                std.mem.eql(u8, self.strings.resolve(expression.predicate), "="))
            {
                result[index] = clause;
                index += 1;
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
                !std.mem.eql(u8, self.strings.resolve(expression.predicate), "="))
            {
                result[index] = clause;
                index += 1;
            },
            else => {},
        };
        return result;
    }

    fn validateQuery(self: *Jatalog, goals: []const Expr) !void {
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try self.orderGoals(goals);
        defer self.allocator.free(ordered);
        for (ordered) |goal| {
            if (!goal.negated and !isBuiltin(self, goal)) {
                for (goal.terms) |term| try bindTermVariables(self.allocator, term, &bound);
                continue;
            }
            if (isBuiltin(self, goal) and std.mem.eql(u8, self.strings.resolve(goal.predicate), "=")) {
                if (goal.terms.len != 2) return Error.InvalidQuery;
                const a_bound = termVariablesBound(goal.terms[0], &bound);
                const b_bound = termVariablesBound(goal.terms[1], &bound);
                if (!a_bound and !b_bound) return Error.InvalidQuery;
                try bindTermVariables(self.allocator, goal.terms[0], &bound);
                try bindTermVariables(self.allocator, goal.terms[1], &bound);
            } else {
                for (goal.terms) |term| if (!termVariablesBound(term, &bound)) return Error.InvalidQuery;
            }
        }
    }

    fn orderGoals(self: *Jatalog, goals: []const Expr) ![]Expr {
        const result = try self.allocator.alloc(Expr, goals.len);
        var index: usize = 0;
        for (goals) |goal| {
            const late = goal.negated or (isBuiltin(self, goal) and
                !std.mem.eql(u8, self.strings.resolve(goal.predicate), "="));
            if (!late) {
                result[index] = goal;
                index += 1;
            }
        }
        for (goals) |goal| {
            const late = goal.negated or (isBuiltin(self, goal) and
                !std.mem.eql(u8, self.strings.resolve(goal.predicate), "="));
            if (late) {
                result[index] = goal;
                index += 1;
            }
        }
        return result;
    }

    fn validateStratification(self: *Jatalog) !void {
        var levels = try self.computeStrata();
        levels.deinit(self.allocator);
    }

    fn computeStrata(self: *Jatalog) !std.array_hash_map.Auto(Id, usize) {
        var levels: std.array_hash_map.Auto(Id, usize) = .empty;
        errdefer levels.deinit(self.allocator);
        for (self.rules.items) |rule| {
            try levels.put(self.allocator, rule.head.predicate, 0);
            for (rule.body) |clause| try self.collectDependencyPredicates(clause, &levels);
        }
        const predicate_count = levels.count();
        for (0..predicate_count + 1) |iteration| {
            var changed = false;
            for (self.rules.items) |rule| {
                var required: usize = 0;
                for (rule.body) |clause|
                    required = @max(required, self.clauseRequiredStratum(clause, &levels, false));
                const current = levels.get(rule.head.predicate) orelse 0;
                if (required > current) {
                    try levels.put(self.allocator, rule.head.predicate, required);
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
        levels: *std.array_hash_map.Auto(Id, usize),
    ) !void {
        switch (clause) {
            .relational => |expression| try levels.put(self.allocator, expression.predicate, 0),
            .negated => |expression| if (!isBuiltin(self, expression))
                try levels.put(self.allocator, expression.predicate, 0),
            .builtin => {},
            .aggregate => |aggregate| for (aggregate.body) |body_clause|
                try self.collectDependencyPredicates(body_clause, levels),
        }
    }

    fn clauseRequiredStratum(
        self: *const Jatalog,
        clause: Clause,
        levels: *const std.array_hash_map.Auto(Id, usize),
        aggregate_context: bool,
    ) usize {
        return switch (clause) {
            .relational => |expression| (levels.get(expression.predicate) orelse 0) +
                @intFromBool(aggregate_context),
            .negated => |expression| if (isBuiltin(self, expression))
                0
            else
                (levels.get(expression.predicate) orelse 0) + 1,
            .builtin => 0,
            .aggregate => |aggregate| blk: {
                var required: usize = 0;
                for (aggregate.body) |body_clause|
                    required = @max(required, self.clauseRequiredStratum(body_clause, levels, true));
                break :blk required;
            },
        };
    }

    fn delete(self: *Jatalog, goals: []const Expr) !bool {
        var result = try self.query(goals);
        defer result.deinit();
        var changed = false;
        var index = self.facts.items.len;
        while (index > 0) {
            index -= 1;
            const fact = self.facts.items[index];
            var remove = false;
            for (result.answers.items) |*answer| {
                for (goals) |goal| {
                    if (goal.negated or isBuiltin(self, goal) or
                        goal.predicate != fact.predicate or goal.terms.len != fact.terms.len) continue;
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

    fn deleteClauses(self: *Jatalog, goals: []const Clause) !bool {
        var result = try self.queryClauses(goals);
        defer result.deinit();
        var changed = false;
        var index = self.facts.items.len;
        while (index > 0) {
            index -= 1;
            const fact = self.facts.items[index];
            var remove = false;
            for (result.answers.items) |*answer| {
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

    pub fn formatValue(self: *const Jatalog, allocator: std.mem.Allocator, value: ValueId) ![]u8 {
        var output: std.Io.Writer.Allocating = .init(allocator);
        defer output.deinit();
        self.writeValue(&output.writer, value) catch return error.OutOfMemory;
        return output.toOwnedSlice();
    }

    pub fn writeValue(self: *const Jatalog, writer: *std.Io.Writer, value: ValueId) !void {
        switch (self.values.get(value)) {
            .atom => |atom| try writeAtom(writer, self.strings.resolve(atom)),
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

    /// Deterministic total order for canonical ground values: atoms by spelling,
    /// then nil, then cons cells lexicographically by head and tail.
    pub fn compareValues(self: *const Jatalog, left: ValueId, right: ValueId) std.math.Order {
        const a = self.values.get(left);
        const b = self.values.get(right);
        const a_rank: u2 = switch (a) {
            .atom => 0,
            .nil => 1,
            .cons => 2,
        };
        const b_rank: u2 = switch (b) {
            .atom => 0,
            .nil => 1,
            .cons => 2,
        };
        if (a_rank != b_rank) return std.math.order(a_rank, b_rank);
        return switch (a) {
            .atom => |a_atom| switch (b) {
                .atom => |b_atom| std.mem.order(u8, self.strings.resolve(a_atom), self.strings.resolve(b_atom)),
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

fn writeAtom(writer: *std.Io.Writer, atom: []const u8) !void {
    if (isBareAtom(atom)) return writer.writeAll(atom);
    try writer.writeByte('\'');
    for (atom) |byte| {
        if (byte == '\\' or byte == '\'') try writer.writeByte('\\');
        try writer.writeByte(byte);
    }
    try writer.writeByte('\'');
}

fn isBareAtom(atom: []const u8) bool {
    if (atom.len == 0 or isVariable(atom)) return false;
    for (atom, 0..) |byte, index| {
        if (std.ascii.isAlphanumeric(byte) or byte == '_') continue;
        if (byte == '.' and index > 0 and index + 1 < atom.len and
            std.ascii.isDigit(atom[index - 1]) and std.ascii.isDigit(atom[index + 1])) continue;
        if ((byte == '+' or byte == '-') and (index == 0 or
            (index > 0 and (atom[index - 1] == 'e' or atom[index - 1] == 'E')))) continue;
        return false;
    }
    return true;
}

fn freeExpr(allocator: std.mem.Allocator, value: Expr) void {
    for (value.terms) |term| freeTerm(allocator, term);
    allocator.free(value.terms);
}

fn freeClause(allocator: std.mem.Allocator, clause: Clause) void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| freeExpr(allocator, expression),
        .aggregate => |aggregate| {
            freeTerm(allocator, aggregate.template);
            for (aggregate.body) |body_clause| freeClause(allocator, body_clause);
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

fn normalizeOperator(operator: []const u8) []const u8 {
    return if (std.mem.eql(u8, operator, "!=")) "<>" else operator;
}

fn isBuiltin(jatalog: *const Jatalog, value: Expr) bool {
    const predicate = jatalog.strings.resolve(value.predicate);
    return std.mem.eql(u8, predicate, "=") or std.mem.eql(u8, predicate, "<>") or
        std.mem.eql(u8, predicate, "<") or std.mem.eql(u8, predicate, "<=") or
        std.mem.eql(u8, predicate, ">") or std.mem.eql(u8, predicate, ">=");
}

fn parseNumber(string: []const u8) ?f64 {
    return std.fmt.parseFloat(f64, string) catch null;
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
            last = try self.executeStatement();
        }
    }

    fn executeStatement(self: *Parser) !ExecutionResult {
        const first = try self.parseClause();
        var first_owned = true;
        errdefer if (first_owned) freeClause(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.consume(":-")) {
            const head = switch (first) {
                .relational => |expression| expression,
                else => return Error.InvalidRule,
            };
            var body: std.ArrayList(Clause) = .empty;
            defer body.deinit(self.jatalog.allocator);
            errdefer for (body.items) |clause| freeClause(self.jatalog.allocator, clause);
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    freeClause(self.jatalog.allocator, clause);
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
            freeClause(self.jatalog.allocator, first);
            first_owned = false;
            return .none;
        }

        var goals: std.ArrayList(Clause) = .empty;
        defer {
            for (goals.items) |clause| freeClause(self.jatalog.allocator, clause);
            goals.deinit(self.jatalog.allocator);
        }
        try goals.append(self.jatalog.allocator, first);
        first_owned = false;
        while (self.consume(",")) {
            const goal = try self.parseClause();
            goals.append(self.jatalog.allocator, goal) catch |err| {
                freeClause(self.jatalog.allocator, goal);
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
            for (body.items) |clause| freeClause(self.jatalog.allocator, clause);
            body.deinit(self.jatalog.allocator);
        }
        if (self.consume("(")) {
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    freeClause(self.jatalog.allocator, clause);
                    return err;
                };
                if (self.consume(")")) break;
                try self.expect(",");
            }
        } else {
            const clause = try self.parseClause();
            body.append(self.jatalog.allocator, clause) catch |err| {
                freeClause(self.jatalog.allocator, clause);
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
            const predicate = try self.jatalog.strings.intern(normalizeOperator(operator));
            const terms = try self.jatalog.allocator.alloc(Term, 2);
            terms[0] = first;
            terms[1] = second;
            first_owned = false;
            return .{
                .predicate = predicate,
                .terms = terms,
                .negated = negated,
            };
        }
        if (!self.consume("(")) return Error.InvalidSyntax;
        const predicate = switch (first) {
            .atom => |atom| atom,
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
            return .{ .atom = try self.jatalog.strings.intern(string.items) };
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
        const id = try self.jatalog.strings.intern(value);
        return if (isVariable(value)) .{ .variable = id } else .{ .atom = id };
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
    db: *const Jatalog,
    binding: *const Binding,
    variable: []const u8,
    expected: []const u8,
) !void {
    const value = binding.getValue(db, variable) orelse return error.MissingBinding;
    const formatted = try db.formatValue(std.testing.allocator, value);
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
    try std.testing.expectEqualStrings("a", result.query.answers.items[0].get(&db, "X").?);
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
    try std.testing.expectEqualStrings("a", result.query.answers.items[0].get(&db, "X").?);

    try std.testing.expectError(Error.InvalidSyntax, db.execute("broken([a, [b])."));
}

test "ground values have a deterministic structural total order" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const expression = try db.expr("values", &.{ "z", "a", "[]", "[a]", "[a, b]" });
    defer db.freeExpression(expression);
    var ids: [5]ValueId = undefined;
    for (expression.terms, &ids) |term, *id| id.* = try db.termToValue(term, null);
    try std.testing.expectEqual(std.math.Order.gt, db.compareValues(ids[0], ids[1]));
    try std.testing.expectEqual(std.math.Order.lt, db.compareValues(ids[1], ids[2]));
    try std.testing.expectEqual(std.math.Order.lt, db.compareValues(ids[2], ids[3]));
    try std.testing.expectEqual(std.math.Order.lt, db.compareValues(ids[3], ids[4]));
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
    const value = result.query.answers.items[0].getValue(&db, "X").?;
    const formatted = try db.formatValue(allocator, value);
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
    const reachable = db.strings.get("reachable").?;
    const all_reachable = db.strings.get("all_reachable").?;
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
    try std.testing.expectEqual(@as(usize, 1), levels.get(db.strings.get("allowed").?).?);
    try std.testing.expectEqual(@as(usize, 2), levels.get(db.strings.get("summary").?).?);
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
        const person = answer.get(&db, "X").?;
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

    const first_value = first_result.query.answers.items[0].getValue(&first, "S").?;
    const first_text = try first.formatValue(std.testing.allocator, first_value);
    defer std.testing.allocator.free(first_text);
    const second_value = second_result.query.answers.items[0].getValue(&second, "S").?;
    const second_text = try second.formatValue(std.testing.allocator, second_value);
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
