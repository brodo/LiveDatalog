//! A small, embeddable Datalog engine modeled after Jatalog.
const std = @import("std");

pub const Id = u64;
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

pub const Term = struct {
    id: Id,
    variable: bool,
};

pub const Expr = struct {
    predicate: Id,
    terms: []Term,
    negated: bool = false,

    pub fn arity(self: Expr) usize {
        return self.terms.len;
    }

    pub fn isGround(self: Expr) bool {
        for (self.terms) |term| if (term.variable) return false;
        return true;
    }
};

pub const Rule = struct {
    head: Expr,
    body: []Expr,
};

const Fact = struct {
    predicate: Id,
    terms: []Id,
};

pub const Binding = struct {
    values: std.array_hash_map.Auto(Id, Id) = .empty,

    pub fn deinit(self: *Binding, allocator: std.mem.Allocator) void {
        self.values.deinit(allocator);
        self.* = undefined;
    }

    pub fn get(self: *const Binding, jatalog: *const Jatalog, variable: []const u8) ?[]const u8 {
        const variable_id = jatalog.strings.get(variable) orelse return null;
        const value_id = self.values.get(variable_id) orelse return null;
        return jatalog.strings.resolve(value_id);
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
    facts: std.ArrayList(Fact) = .empty,
    rules: std.ArrayList(Rule) = .empty,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{ .allocator = allocator, .strings = .init(allocator) };
    }

    pub fn deinit(self: *Jatalog) void {
        for (self.facts.items) |fact| self.allocator.free(fact.terms);
        self.facts.deinit(self.allocator);
        for (self.rules.items) |rule| {
            freeExpr(self.allocator, rule.head);
            for (rule.body) |clause| freeExpr(self.allocator, clause);
            self.allocator.free(rule.body);
        }
        self.rules.deinit(self.allocator);
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
        errdefer self.allocator.free(result_terms);
        for (terms, result_terms) |string, *term| {
            term.* = .{
                .id = try self.strings.intern(string),
                .variable = isVariable(string),
            };
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
        const terms = try self.allocator.alloc(Id, value.terms.len);
        errdefer self.allocator.free(terms);
        for (value.terms, terms) |term, *id| id.* = term.id;
        const fact: Fact = .{ .predicate = value.predicate, .terms = terms };
        if (containsFact(self.facts.items, fact)) {
            self.allocator.free(terms);
            return;
        }
        try self.facts.append(self.allocator, fact);
    }

    /// Takes ownership of `head` and every expression in `body` on success.
    pub fn addRule(self: *Jatalog, head: Expr, body: []Expr) !void {
        try self.validateRule(head, body);
        const owned_body = try self.allocator.dupe(Expr, body);
        errdefer self.allocator.free(owned_body);
        try self.rules.append(self.allocator, .{ .head = head, .body = owned_body });
        self.validateStratification() catch |err| {
            _ = self.rules.pop();
            return err;
        };
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

    pub fn execute(self: *Jatalog, source: []const u8) !ExecutionResult {
        var parser: Parser = .{ .jatalog = self, .source = source };
        return parser.executeAll();
    }

    fn cloneFacts(self: *Jatalog) !std.ArrayList(Fact) {
        var result: std.ArrayList(Fact) = .empty;
        errdefer deinitFacts(self.allocator, &result);
        for (self.facts.items) |fact| {
            try result.append(self.allocator, .{
                .predicate = fact.predicate,
                .terms = try self.allocator.dupe(Id, fact.terms),
            });
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
                    try self.matchGoals(rule.body, facts.items, 0, &initial, &answers);
                    for (answers.items) |*answer| {
                        const derived = try self.deriveFact(rule.head, answer);
                        if (containsFact(facts.items, derived)) {
                            self.allocator.free(derived.terms);
                        } else {
                            try facts.append(self.allocator, derived);
                        }
                    }
                }
                if (facts.items.len == before) break;
            }
        }
    }

    fn deriveFact(self: *Jatalog, head: Expr, bindings: *const Binding) !Fact {
        const terms = try self.allocator.alloc(Id, head.terms.len);
        errdefer self.allocator.free(terms);
        for (head.terms, terms) |term, *id| {
            id.* = if (term.variable)
                bindings.values.get(term.id) orelse return Error.UnboundVariable
            else
                term.id;
        }
        return .{ .predicate = head.predicate, .terms = terms };
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
            try answers.append(self.allocator, try bindings.clone(self.allocator));
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
                if (try unify(self.allocator, fact, goal, &next)) return;
            }
            try self.matchGoals(goals, facts, index + 1, bindings, answers);
            return;
        }
        for (facts) |fact| {
            if (fact.predicate != goal.predicate or fact.terms.len != goal.terms.len) continue;
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try unify(self.allocator, fact, goal, &next))
                try self.matchGoals(goals, facts, index + 1, &next, answers);
        }
    }

    fn evalBuiltin(self: *Jatalog, expr_value: Expr, bindings: *Binding) !bool {
        if (expr_value.terms.len != 2) return Error.InvalidQuery;
        const operator = self.strings.resolve(expr_value.predicate);
        const left = expr_value.terms[0];
        const right = expr_value.terms[1];
        const left_id = if (left.variable) bindings.values.get(left.id) else left.id;
        const right_id = if (right.variable) bindings.values.get(right.id) else right.id;

        if (std.mem.eql(u8, operator, "=")) {
            if (left_id == null and right_id == null) return Error.UnboundVariable;
            if (left_id == null) {
                try bindings.values.put(self.allocator, left.id, right_id.?);
                return true;
            }
            if (right_id == null) {
                try bindings.values.put(self.allocator, right.id, left_id.?);
                return true;
            }
            return self.valuesEqual(left_id.?, right_id.?);
        }
        if (left_id == null or right_id == null) return Error.UnboundVariable;
        if (std.mem.eql(u8, operator, "<>")) return !self.valuesEqual(left_id.?, right_id.?);

        const left_number = parseNumber(self.strings.resolve(left_id.?)) orelse 0;
        const right_number = parseNumber(self.strings.resolve(right_id.?)) orelse 0;
        if (std.mem.eql(u8, operator, "<")) return left_number < right_number;
        if (std.mem.eql(u8, operator, "<=")) return left_number <= right_number;
        if (std.mem.eql(u8, operator, ">")) return left_number > right_number;
        if (std.mem.eql(u8, operator, ">=")) return left_number >= right_number;
        return Error.UnknownOperator;
    }

    fn valuesEqual(self: *const Jatalog, left: Id, right: Id) bool {
        const left_string = self.strings.resolve(left);
        const right_string = self.strings.resolve(right);
        const left_number = parseNumber(left_string);
        const right_number = parseNumber(right_string);
        if (left_number != null and right_number != null) return left_number.? == right_number.?;
        return std.mem.eql(u8, left_string, right_string);
    }

    fn validateRule(self: *Jatalog, head: Expr, body: []const Expr) !void {
        if (body.len == 0 or head.negated or isBuiltin(self, head)) return Error.InvalidRule;
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try self.orderGoals(body);
        defer self.allocator.free(ordered);
        for (ordered) |clause| {
            if (isBuiltin(self, clause)) {
                if (clause.terms.len != 2) return Error.InvalidRule;
                const operator = self.strings.resolve(clause.predicate);
                const a_bound = !clause.terms[0].variable or bound.contains(clause.terms[0].id);
                const b_bound = !clause.terms[1].variable or bound.contains(clause.terms[1].id);
                if (std.mem.eql(u8, operator, "=")) {
                    if (!a_bound and !b_bound) return Error.InvalidRule;
                    if (clause.terms[0].variable) try bound.put(self.allocator, clause.terms[0].id, {});
                    if (clause.terms[1].variable) try bound.put(self.allocator, clause.terms[1].id, {});
                } else if (!a_bound or !b_bound) return Error.InvalidRule;
            } else if (clause.negated) {
                for (clause.terms) |term| if (term.variable and !bound.contains(term.id)) return Error.InvalidRule;
            } else {
                for (clause.terms) |term| if (term.variable) try bound.put(self.allocator, term.id, {});
            }
        }
        for (head.terms) |term| {
            if (!term.variable or !bound.contains(term.id)) return Error.InvalidRule;
        }
    }

    fn validateQuery(self: *Jatalog, goals: []const Expr) !void {
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try self.orderGoals(goals);
        defer self.allocator.free(ordered);
        for (ordered) |goal| {
            if (!goal.negated and !isBuiltin(self, goal)) {
                for (goal.terms) |term| if (term.variable) try bound.put(self.allocator, term.id, {});
                continue;
            }
            if (isBuiltin(self, goal) and std.mem.eql(u8, self.strings.resolve(goal.predicate), "=")) {
                if (goal.terms.len != 2) return Error.InvalidQuery;
                const a_bound = !goal.terms[0].variable or bound.contains(goal.terms[0].id);
                const b_bound = !goal.terms[1].variable or bound.contains(goal.terms[1].id);
                if (!a_bound and !b_bound) return Error.InvalidQuery;
                if (goal.terms[0].variable) try bound.put(self.allocator, goal.terms[0].id, {});
                if (goal.terms[1].variable) try bound.put(self.allocator, goal.terms[1].id, {});
            } else {
                for (goal.terms) |term| if (term.variable and !bound.contains(term.id)) return Error.InvalidQuery;
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
            for (rule.body) |clause| if (!isBuiltin(self, clause)) try levels.put(self.allocator, clause.predicate, 0);
        }
        const predicate_count = levels.count();
        for (0..predicate_count + 1) |iteration| {
            var changed = false;
            for (self.rules.items) |rule| {
                var required: usize = 0;
                for (rule.body) |clause| {
                    if (isBuiltin(self, clause)) continue;
                    const dependency = levels.get(clause.predicate) orelse 0;
                    required = @max(required, dependency + @intFromBool(clause.negated));
                }
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
                    var matches = true;
                    for (goal.terms, fact.terms) |term, value| {
                        const expected = if (term.variable) answer.values.get(term.id) else term.id;
                        if (expected == null or expected.? != value) {
                            matches = false;
                            break;
                        }
                    }
                    if (matches) remove = true;
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
};

fn freeExpr(allocator: std.mem.Allocator, value: Expr) void {
    allocator.free(value.terms);
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

fn unify(allocator: std.mem.Allocator, fact: Fact, goal: Expr, bindings: *Binding) !bool {
    for (fact.terms, goal.terms) |value, term| {
        if (term.variable) {
            if (bindings.values.get(term.id)) |bound| {
                if (bound != value) return false;
            } else try bindings.values.put(allocator, term.id, value);
        } else if (term.id != value) return false;
    }
    return true;
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
        const head = try self.parseExpr();
        var head_owned = true;
        errdefer if (head_owned) freeExpr(self.jatalog.allocator, head);
        self.skipSpace();
        if (self.consume(":-")) {
            var body: std.ArrayList(Expr) = .empty;
            defer body.deinit(self.jatalog.allocator);
            errdefer for (body.items) |expr_value| freeExpr(self.jatalog.allocator, expr_value);
            while (true) {
                try body.append(self.jatalog.allocator, try self.parseExpr());
                self.skipSpace();
                if (!self.consume(",")) break;
            }
            try self.expect(".");
            try self.jatalog.addRule(head, body.items);
            return .none;
        }
        self.skipSpace();
        if (self.consume(".")) {
            try self.jatalog.addFactExpr(head);
            freeExpr(self.jatalog.allocator, head);
            return .none;
        }

        var goals: std.ArrayList(Expr) = .empty;
        defer {
            for (goals.items) |expr_value| freeExpr(self.jatalog.allocator, expr_value);
            goals.deinit(self.jatalog.allocator);
        }
        try goals.append(self.jatalog.allocator, head);
        head_owned = false;
        while (self.consume(",")) try goals.append(self.jatalog.allocator, try self.parseExpr());
        if (self.consume("?")) return .{ .query = try self.jatalog.query(goals.items) };
        if (self.consume("~")) return .{ .changed = try self.jatalog.delete(goals.items) };
        return Error.InvalidSyntax;
    }

    fn parseExpr(self: *Parser) !Expr {
        self.skipSpace();
        var negated = false;
        if (self.peekKeyword("not")) {
            _ = try self.parseBare();
            negated = true;
        }
        const first = try self.parseTerm();
        self.skipSpace();
        if (self.parseOperator()) |operator| {
            const second = try self.parseTerm();
            const terms = try self.jatalog.allocator.alloc(Term, 2);
            terms[0] = first;
            terms[1] = second;
            return .{
                .predicate = try self.jatalog.strings.intern(normalizeOperator(operator)),
                .terms = terms,
                .negated = negated,
            };
        }
        if (!self.consume("(")) return Error.InvalidSyntax;
        var terms: std.ArrayList(Term) = .empty;
        errdefer terms.deinit(self.jatalog.allocator);
        self.skipSpace();
        if (!self.consume(")")) {
            while (true) {
                try terms.append(self.jatalog.allocator, try self.parseTerm());
                self.skipSpace();
                if (self.consume(")")) break;
                try self.expect(",");
            }
        }
        return .{ .predicate = first.id, .terms = try terms.toOwnedSlice(self.jatalog.allocator), .negated = negated };
    }

    fn parseTerm(self: *Parser) !Term {
        self.skipSpace();
        if (self.index == self.source.len) return Error.InvalidSyntax;
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
            return .{ .id = try self.jatalog.strings.intern(string.items), .variable = false };
        }
        const value = try self.parseBare();
        return .{ .id = try self.jatalog.strings.intern(value), .variable = isVariable(value) };
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
