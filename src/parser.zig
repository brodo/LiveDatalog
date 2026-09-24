//! The source syntax: text in, borrowed `input` descriptors out.
//!
//! Parsing needs no database and interns nothing. A parsed statement is the
//! same descriptor an embedder would build by hand, so everything that takes
//! one takes the other, and a statement's names become identifiers only when
//! it runs (`program.zig`). That is also what puts this module at the bottom
//! of the engine: it imports the descriptors and the literal classifier and
//! nothing that holds state.
//!
//! Parsing judges only what the text alone decides — the shape of a
//! statement, and whether a numeric literal fits its type. Anything needing
//! the program's meaning (a fact's groundness, a rule's safety, stratification)
//! is reported when the statement runs.

const std = @import("std");
const input = @import("input.zig");
const scalar = @import("scalar.zig");

pub const Error = error{
    InvalidSyntax,
    InvalidFact,
    InvalidRule,
    NumericOverflow,
    OutOfMemory,
};

/// A byte range of the source, `end` exclusive.
pub const Span = struct {
    start: usize,
    end: usize,
};

/// Where a parse or a program run failed. Filling one never allocates.
///
/// Passed as an optional out-parameter and written only when the operation
/// fails; on success it is left as it was.
pub const Diagnostic = struct {
    /// The index of the statement that failed, when one was reached. Set for
    /// syntax errors inside a program and for every error a run reports.
    statement: ?usize = null,
    /// The offending bytes: the token a parse stopped at, or the whole
    /// statement a run failed in. Null when there is no source to point into,
    /// as for statements built by hand.
    span: ?Span = null,
    /// 1-based line and byte column of `span.start`; 0 when `span` is null.
    line: u32 = 0,
    column: u32 = 0,
    /// What the parser was looking for, such as `"')'"`. Parse errors only.
    expected: ?[]const u8 = null,

    /// A diagnostic pointing at `span` of `source`.
    pub fn at(source: []const u8, span: Span, statement: ?usize, expected: ?[]const u8) Diagnostic {
        const location = locate(source, span.start);
        return .{
            .statement = statement,
            .span = span,
            .line = location.line,
            .column = location.column,
            .expected = expected,
        };
    }
};

pub const Location = struct {
    line: u32,
    column: u32,
};

/// The 1-based line and byte column of `offset` in `source`.
pub fn locate(source: []const u8, offset: usize) Location {
    const clamped = @min(offset, source.len);
    const line_start = if (std.mem.findScalarLast(u8, source[0..clamped], '\n')) |newline|
        newline + 1
    else
        0;
    return .{
        .line = @intCast(std.mem.count(u8, source[0..clamped], "\n") + 1),
        .column = @intCast(clamped - line_start + 1),
    };
}

/// A parse result and the memory its borrowed descriptors point into.
///
/// Everything `value` reaches — names, atoms, nested goals — lives in the
/// arena, including a copy of the source, so the caller's source may be freed
/// as soon as the parse returns.
pub fn Parsed(comptime T: type) type {
    return struct {
        const Self = @This();

        arena: *std.heap.ArenaAllocator,
        value: T,

        pub fn deinit(self: Self) void {
            const allocator = self.arena.child_allocator;
            self.arena.deinit();
            allocator.destroy(self.arena);
        }
    };
}

/// A parsed program: its statements, and where in the source each one was.
pub const Program = struct {
    statements: []const input.Statement,
    /// `spans[i]` covers `statements[i]`, terminator included.
    spans: []const Span,
};

/// Parses every statement of `source`. A syntax error anywhere fails the
/// whole parse, which is what lets a program be checked before any of it runs.
pub fn parseProgram(
    allocator: std.mem.Allocator,
    source: []const u8,
    diagnostic: ?*Diagnostic,
) Error!Parsed(Program) {
    return parseWith(Program, Parser.program, allocator, source, diagnostic);
}

/// Parses one rule, `head :- body`, with an optional trailing `.`.
pub fn parseRule(
    allocator: std.mem.Allocator,
    source: []const u8,
    diagnostic: ?*Diagnostic,
) Error!Parsed(input.Rule) {
    return parseWith(input.Rule, Parser.wholeRule, allocator, source, diagnostic);
}

/// Parses a comma-separated list of goals — a query's body — with an optional
/// trailing `?`.
pub fn parseGoals(
    allocator: std.mem.Allocator,
    source: []const u8,
    diagnostic: ?*Diagnostic,
) Error!Parsed([]const input.Goal) {
    return parseWith([]const input.Goal, Parser.wholeGoals, allocator, source, diagnostic);
}

fn parseWith(
    comptime T: type,
    comptime parse: fn (*Parser) Error!T,
    allocator: std.mem.Allocator,
    source: []const u8,
    diagnostic: ?*Diagnostic,
) Error!Parsed(T) {
    const arena = try allocator.create(std.heap.ArenaAllocator);
    errdefer allocator.destroy(arena);
    arena.* = .init(allocator);
    errdefer arena.deinit();
    var parser: Parser = .{
        .arena = arena.allocator(),
        .source = try arena.allocator().dupe(u8, source),
        .diagnostic = diagnostic,
    };
    const value = try parse(&parser);
    return .{ .arena = arena, .value = value };
}

/// A goal and the source it was written as, which is what a shape error
/// points at.
const Clause = struct {
    goal: input.Goal,
    span: Span,
};

const Parser = struct {
    arena: std.mem.Allocator,
    /// The arena's copy of the caller's source, so every name a descriptor
    /// borrows is a slice of memory the parse result owns.
    source: []const u8,
    index: usize = 0,
    diagnostic: ?*Diagnostic,
    /// The statement being parsed, when parsing a program.
    statement: ?usize = null,

    fn program(self: *Parser) Error!Program {
        var statements: std.ArrayList(input.Statement) = .empty;
        var spans: std.ArrayList(Span) = .empty;
        while (true) {
            self.skipSpace();
            if (self.index == self.source.len) break;
            self.statement = statements.items.len;
            const start = self.index;
            try statements.append(self.arena, try self.parseStatement());
            try spans.append(self.arena, .{ .start = start, .end = self.index });
        }
        return .{ .statements = statements.items, .spans = spans.items };
    }

    fn wholeRule(self: *Parser) Error!input.Rule {
        const head = try self.parseClause();
        const relation = switch (head.goal) {
            .relation => |relation| relation,
            else => return self.fail(error.InvalidRule, head.span, "a relation"),
        };
        if (!self.consume(":-")) return self.failHere(error.InvalidRule, "':-'");
        const body = try self.parseClauseList();
        _ = self.consume(".");
        try self.expectEnd();
        return .{ .head = relation, .body = body };
    }

    fn wholeGoals(self: *Parser) Error![]const input.Goal {
        const goals = try self.parseClauseList();
        _ = self.consume("?");
        try self.expectEnd();
        return goals;
    }

    fn parseStatement(self: *Parser) Error!input.Statement {
        const first = try self.parseClause();
        if (self.consume(":-")) {
            const head = switch (first.goal) {
                .relation => |relation| relation,
                else => return self.fail(error.InvalidRule, first.span, "a relation"),
            };
            const body = try self.parseClauseList();
            try self.expect(".");
            return .{ .rule = .{ .head = head, .body = body } };
        }
        if (self.consume(".")) {
            return switch (first.goal) {
                .relation => |relation| .{ .fact = relation },
                else => self.fail(error.InvalidFact, first.span, "a relation"),
            };
        }
        var goals: std.ArrayList(input.Goal) = .empty;
        try goals.append(self.arena, first.goal);
        const expected = if (self.consume(",")) blk: {
            try self.appendClauses(&goals);
            break :blk "',', 'order by', '?' or '~'";
        } else "':-', '.', ',', 'order by', '?' or '~'";
        if (try self.parseOrderBy()) |order| {
            try self.expect("?");
            return .{ .query = input.query(goals.items, order) };
        }
        if (self.consume("?")) return .{ .query = input.query(goals.items, &.{}) };
        if (self.consume("~")) return .{ .retraction = goals.items };
        return self.failHere(error.InvalidSyntax, expected);
    }

    /// `order by K, ...` after a query's goals, or null when there is none.
    /// `order` is a keyword only here, where no goal can follow a goal without
    /// a comma, so a relation named `order` stays legal everywhere else.
    fn parseOrderBy(self: *Parser) Error!?[]const input.SortKey {
        if (!self.peekKeyword("order")) return null;
        _ = try self.parseBare();
        if (!self.peekKeyword("by")) return self.failHere(error.InvalidSyntax, "'by'");
        _ = try self.parseBare();
        var keys: std.ArrayList(input.SortKey) = .empty;
        while (true) {
            self.skipSpace();
            if (self.index == self.source.len or !std.ascii.isUpper(self.source[self.index]))
                return self.failHere(error.InvalidSyntax, "a variable");
            const name = try self.parseBare();
            const direction: input.Direction = if (self.peekKeyword("desc")) blk: {
                _ = try self.parseBare();
                break :blk .descending;
            } else if (self.peekKeyword("asc")) blk: {
                _ = try self.parseBare();
                break :blk .ascending;
            } else .ascending;
            try keys.append(self.arena, .{ .variable = name, .direction = direction });
            if (!self.consume(",")) return keys.items;
        }
    }

    /// One or more clauses separated by commas.
    fn parseClauseList(self: *Parser) Error![]const input.Goal {
        var goals: std.ArrayList(input.Goal) = .empty;
        try self.appendClauses(&goals);
        return goals.items;
    }

    fn appendClauses(self: *Parser, goals: *std.ArrayList(input.Goal)) Error!void {
        while (true) {
            try goals.append(self.arena, (try self.parseClause()).goal);
            if (!self.consume(",")) return;
        }
    }

    fn parseClause(self: *Parser) Error!Clause {
        self.skipSpace();
        const start = self.index;
        const goal = if (self.peekKeyword("setof"))
            try self.parseAggregate()
        else
            try self.parseExpr();
        return .{ .goal = goal, .span = .{ .start = start, .end = self.index } };
    }

    fn parseAggregate(self: *Parser) Error!input.Goal {
        _ = try self.parseBare();
        try self.expect("(");
        const template = try self.parseTerm();
        try self.expect(",");
        var body: std.ArrayList(input.Goal) = .empty;
        if (self.consume("(")) {
            while (true) {
                try body.append(self.arena, (try self.parseClause()).goal);
                if (self.consume(")")) break;
                try self.expect(",");
            }
        } else {
            try body.append(self.arena, (try self.parseClause()).goal);
        }
        try self.expect(",");
        const output = try self.parseTerm();
        try self.expect(")");
        return input.setof(template, body.items, output);
    }

    fn parseExpr(self: *Parser) Error!input.Goal {
        self.skipSpace();
        const start = self.index;
        var negated = false;
        if (self.peekKeyword("not")) {
            _ = try self.parseBare();
            negated = true;
        }
        self.skipSpace();
        const first_start = self.index;
        const first = try self.parseTerm();
        const first_span: Span = .{ .start = first_start, .end = self.index };
        if (self.parseOperator()) |operator| {
            const second = try self.parseTerm();
            if (std.mem.eql(u8, operator, "=")) {
                const arithmetic: ?input.Arithmetic = if (self.consume("+"))
                    .add
                else if (self.consume("-"))
                    .subtract
                else
                    null;
                if (arithmetic) |kind| {
                    if (negated) return self.fail(
                        error.InvalidSyntax,
                        .{ .start = start, .end = self.index },
                        "a test after 'not'",
                    );
                    const third = try self.parseTerm();
                    return .{ .arithmetic = .{ .kind = kind, .output = first, .left = second, .right = third } };
                }
            }
            const operands: input.Binary = .{ .left = first, .right = second };
            const builtin: input.NegatedBuiltin = if (std.mem.eql(u8, operator, "="))
                .{ .equality = operands }
            else if (std.mem.eql(u8, operator, "!=") or std.mem.eql(u8, operator, "<>"))
                .{ .inequality = operands }
            else
                .{ .comparison = .{ .kind = comparisonKind(operator), .operands = operands } };
            if (negated) return input.notBuiltin(builtin);
            return switch (builtin) {
                .equality => |binary| .{ .equality = binary },
                .inequality => |binary| .{ .inequality = binary },
                .comparison => |comparison| .{ .comparison = comparison },
            };
        }
        if (!self.consume("(")) return self.failHere(error.InvalidSyntax, "'(' or an operator");
        const predicate = switch (first) {
            .atom => |atom| atom,
            else => return self.fail(error.InvalidSyntax, first_span, "a predicate name"),
        };
        var terms: std.ArrayList(input.Term) = .empty;
        self.skipSpace();
        if (!self.consume(")")) {
            while (true) {
                try terms.append(self.arena, try self.parseTerm());
                if (self.consume(")")) break;
                try self.expect(",");
            }
        }
        return if (negated)
            input.not(predicate, terms.items)
        else
            input.relation(predicate, terms.items);
    }

    fn parseTerm(self: *Parser) Error!input.Term {
        const head = try self.parseTermPrimary();
        if (self.consumeConsBang()) return self.makeCons(head, try self.parseTerm());
        return head;
    }

    fn parseTermPrimary(self: *Parser) Error!input.Term {
        self.skipSpace();
        if (self.index == self.source.len) return self.failHere(error.InvalidSyntax, "a term");
        if (self.consume("[")) return self.parseListTail();
        const quote = self.source[self.index];
        if (quote == '"' or quote == '\'') return self.parseQuoted();
        const start = self.index;
        const value = try self.parseBare();
        if (std.mem.eql(u8, value, "cons") and self.consume("(")) {
            const head = try self.parseTerm();
            try self.expect(",");
            const tail = try self.parseTerm();
            try self.expect(")");
            return self.makeCons(head, tail);
        }
        if (std.ascii.isUpper(value[0])) return input.variable(value);
        const literal = scalar.classifyBare(value) catch |err|
            return self.fail(err, .{ .start = start, .end = self.index }, null);
        return switch (literal) {
            .integer => |integer| input.integer(integer),
            .float => |float| input.float(float),
            .atom => |atom| input.atom(atom),
        };
    }

    fn parseQuoted(self: *Parser) Error!input.Term {
        const start = self.index;
        const quote = self.source[start];
        self.index += 1;
        const content_start = self.index;
        var escaped = false;
        while (self.index < self.source.len and self.source[self.index] != quote) {
            if (self.source[self.index] == '\\' and self.index + 1 < self.source.len) {
                escaped = true;
                self.index += 1;
            }
            self.index += 1;
        }
        if (self.index == self.source.len) return self.fail(
            error.InvalidSyntax,
            .{ .start = start, .end = self.index },
            "a closing quote",
        );
        const raw = self.source[content_start..self.index];
        self.index += 1;
        if (!escaped) return input.atom(raw);
        var text: std.ArrayList(u8) = .empty;
        var cursor: usize = 0;
        while (cursor < raw.len) : (cursor += 1) {
            if (raw[cursor] == '\\' and cursor + 1 < raw.len) cursor += 1;
            try text.append(self.arena, raw[cursor]);
        }
        return input.atom(text.items);
    }

    /// The rest of a list after its `[`. An element may itself be a pair —
    /// `[a, H!T]` is a two-element list whose second element is `H!T` —
    /// because `!` binds within a term, as it does everywhere else.
    fn parseListTail(self: *Parser) Error!input.Term {
        var items: std.ArrayList(input.Term) = .empty;
        while (!self.consume("]")) {
            try items.append(self.arena, try self.parseTerm());
            if (self.consume("]")) break;
            if (!self.consume(",")) return self.failHere(error.InvalidSyntax, "',' or ']'");
        }
        return input.list(items.items);
    }

    fn makeCons(self: *Parser, head: input.Term, tail: input.Term) Error!input.Term {
        const halves = try self.arena.alloc(input.Term, 2);
        halves[0] = head;
        halves[1] = tail;
        const pair = try self.arena.create(input.Term.Cons);
        pair.* = .{ .head = &halves[0], .tail = &halves[1] };
        return input.cons(pair);
    }

    fn parseBare(self: *Parser) Error![]const u8 {
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
        if (self.index == start) return self.failHere(error.InvalidSyntax, "a term");
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

    fn expect(self: *Parser, comptime token: []const u8) Error!void {
        if (!self.consume(token)) return self.failHere(error.InvalidSyntax, "'" ++ token ++ "'");
    }

    fn expectEnd(self: *Parser) Error!void {
        self.skipSpace();
        if (self.index != self.source.len) return self.failHere(error.InvalidSyntax, "the end of input");
    }

    fn peekKeyword(self: *Parser, keyword: []const u8) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], keyword)) return false;
        const end = self.index + keyword.len;
        return end == self.source.len or !(std.ascii.isAlphanumeric(self.source[end]) or self.source[end] == '_');
    }

    /// Fails at whatever comes next: the word there, or the one byte.
    fn failHere(self: *Parser, err: Error, expected: ?[]const u8) Error {
        self.skipSpace();
        var end = self.index;
        while (end < self.source.len and (std.ascii.isAlphanumeric(self.source[end]) or
            self.source[end] == '_')) end += 1;
        if (end == self.index and end < self.source.len) end += 1;
        return self.fail(err, .{ .start = self.index, .end = end }, expected);
    }

    fn fail(self: *Parser, err: Error, span: Span, expected: ?[]const u8) Error {
        if (self.diagnostic) |diagnostic|
            diagnostic.* = .at(self.source, span, self.statement, expected);
        return err;
    }
};

fn comparisonKind(operator: []const u8) input.Comparison {
    if (std.mem.eql(u8, operator, "<")) return .less_than;
    if (std.mem.eql(u8, operator, "<=")) return .less_or_equal;
    if (std.mem.eql(u8, operator, ">")) return .greater_than;
    std.debug.assert(std.mem.eql(u8, operator, ">="));
    return .greater_or_equal;
}

const testing = std.testing;

fn expectStatements(source: []const u8, expected: []const input.Statement) !void {
    const parsed = try parseProgram(testing.allocator, source, null);
    defer parsed.deinit();
    try testing.expectEqualDeep(expected, parsed.value.statements);
}

fn expectFailure(source: []const u8, err: Error, line: u32, column: u32, expected: ?[]const u8) !void {
    var diagnostic: Diagnostic = .{};
    try testing.expectError(err, parseProgram(testing.allocator, source, &diagnostic));
    try testing.expectEqual(line, diagnostic.line);
    try testing.expectEqual(column, diagnostic.column);
    if (expected) |text| {
        try testing.expectEqualStrings(text, diagnostic.expected.?);
    } else {
        try testing.expectEqual(@as(?[]const u8, null), diagnostic.expected);
    }
}

test "every kind of statement parses to the descriptors it names" {
    const x = input.variable("X");
    const y = input.variable("Y");
    try expectStatements(
        \\parent(alice, bob).
        \\grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
        \\parent(alice, X)?
        \\parent(X, bob)~
    , &.{
        .{ .fact = input.fact("parent", &.{ input.atom("alice"), input.atom("bob") }) },
        .{ .rule = input.rule(
            input.fact("grandparent", &.{ x, input.variable("Z") }),
            &.{
                input.relation("parent", &.{ x, y }),
                input.relation("parent", &.{ y, input.variable("Z") }),
            },
        ) },
        .{ .query = .{ .goals = &.{input.relation("parent", &.{ input.atom("alice"), x })} } },
        .{ .retraction = &.{input.relation("parent", &.{ x, input.atom("bob") })} },
    });
}

test "built-ins, negation and arithmetic parse without normalizing" {
    const x = input.variable("X");
    const y = input.variable("Y");
    try expectStatements(
        \\p(X), not q(X), X = Y, X != Y, X <> Y, X < Y, X >= Y, Z = X + Y, W = X - 1?
        \\p(X), not X < Y, not X = Y, not X != Y?
    , &.{
        .{ .query = .{ .goals = &.{
            input.relation("p", &.{x}),
            input.not("q", &.{x}),
            input.equal(x, y),
            input.notEqual(x, y),
            input.notEqual(x, y),
            input.lessThan(x, y),
            input.greaterOrEqual(x, y),
            input.add(input.variable("Z"), x, y),
            input.subtract(input.variable("W"), x, input.integer(1)),
        } } },
        .{ .query = .{ .goals = &.{
            input.relation("p", &.{x}),
            input.notBuiltin(.{ .comparison = .{
                .kind = .less_than,
                .operands = .{ .left = x, .right = y },
            } }),
            input.notBuiltin(.{ .equality = .{ .left = x, .right = y } }),
            input.notBuiltin(.{ .inequality = .{ .left = x, .right = y } }),
        } } },
    });
}

test "terms parse to atoms, numbers, lists and cons pairs" {
    const h = input.variable("H");
    const t = input.variable("T");
    const a = input.atom("a");
    const b = input.atom("b");
    const head_tail: input.Term.Cons = .{ .head = &h, .tail = &t };
    const b_tail: input.Term.Cons = .{ .head = &b, .tail = &t };
    try expectStatements(
        \\v(abc, 'quoted \' atom', "1", 42, -7, 2.5, 1e3, _x).
        \\v([], [a, b], [a,], H!T, cons(H, T), [a, b!T]).
    , &.{
        .{ .fact = input.fact("v", &.{
            input.atom("abc"),
            input.atom("quoted ' atom"),
            input.atom("1"),
            input.integer(42),
            input.integer(-7),
            input.float(2.5),
            input.float(1000),
            input.atom("_x"),
        }) },
        .{ .fact = input.fact("v", &.{
            input.list(&.{}),
            input.list(&.{ a, b }),
            input.list(&.{a}),
            input.cons(&head_tail),
            input.cons(&head_tail),
            input.list(&.{ a, input.cons(&b_tail) }),
        }) },
    });
}

test "aggregates parse with single and parenthesized bodies, and nest" {
    const g = input.variable("G");
    const y = input.variable("Y");
    try expectStatements(
        \\s(S) :- setof(Y, p(Y), S).
        \\n(S) :- seed(k), setof(T, (group(G), setof([Y, G], parent(G, Y), T)), S).
    , &.{
        .{ .rule = input.rule(input.fact("s", &.{input.variable("S")}), &.{
            input.setof(y, &.{input.relation("p", &.{y})}, input.variable("S")),
        }) },
        .{ .rule = input.rule(input.fact("n", &.{input.variable("S")}), &.{
            input.relation("seed", &.{input.atom("k")}),
            input.setof(input.variable("T"), &.{
                input.relation("group", &.{g}),
                input.setof(
                    input.list(&.{ y, g }),
                    &.{input.relation("parent", &.{ g, y })},
                    input.variable("T"),
                ),
            }, input.variable("S")),
        }) },
    });
}

test "order by parses to sort keys, and order stays a legal relation name" {
    const x = input.variable("X");
    const c = input.variable("C");
    try expectStatements(
        \\cost(X, C) order by C desc, X?
        \\cost(X, C), p(X) order by X asc, C?
        \\order(X), by(X)?
    , &.{
        .{ .query = input.query(
            &.{input.relation("cost", &.{ x, c })},
            &.{ input.descending("C"), input.ascending("X") },
        ) },
        .{ .query = input.query(
            &.{ input.relation("cost", &.{ x, c }), input.relation("p", &.{x}) },
            &.{ input.ascending("X"), input.ascending("C") },
        ) },
        .{ .query = input.query(
            &.{ input.relation("order", &.{x}), input.relation("by", &.{x}) },
            &.{},
        ) },
    });
}

test "a malformed order by reports what it expected, and a retraction has none" {
    try expectFailure("p(X) order X?", error.InvalidSyntax, 1, 12, "'by'");
    try expectFailure("p(X) order by a?", error.InvalidSyntax, 1, 15, "a variable");
    try expectFailure("p(X) order by X, ?", error.InvalidSyntax, 1, 18, "a variable");
    try expectFailure("p(X) order by X~", error.InvalidSyntax, 1, 16, "'?'");
}

test "comments and spans cover each statement" {
    const parsed = try parseProgram(testing.allocator,
        \\% a comment
        \\p(a). /* block */ p(X)?
        \\// trailing
    , null);
    defer parsed.deinit();
    try testing.expectEqual(@as(usize, 2), parsed.value.statements.len);
    try testing.expectEqualDeep(&[_]Span{
        .{ .start = 12, .end = 17 },
        .{ .start = 30, .end = 35 },
    }, parsed.value.spans);
}

test "the parse owns everything it returns" {
    const source = try testing.allocator.dupe(u8, "rule(X, 'y') :- body(X, [z]).");
    const parsed = try parseProgram(testing.allocator, source, null);
    defer parsed.deinit();
    @memset(source, 'q');
    testing.allocator.free(source);
    const rule = parsed.value.statements[0].rule;
    try testing.expectEqualStrings("rule", rule.head.predicate);
    try testing.expectEqualStrings("y", rule.head.terms[1].atom);
    try testing.expectEqualStrings("z", rule.body[0].relation.terms[1].list[0].atom);
}

test "syntax errors report where they are and what was expected" {
    try expectFailure("p(a)", error.InvalidSyntax, 1, 5, "':-', '.', ',', 'order by', '?' or '~'");
    try expectFailure("p(a), q(b)", error.InvalidSyntax, 1, 11, "',', 'order by', '?' or '~'");
    try expectFailure("p(a).\nq(a b).", error.InvalidSyntax, 2, 5, "','");
    try expectFailure("p(a) :- q(a)", error.InvalidSyntax, 1, 13, "'.'");
    try expectFailure("p([a b]).", error.InvalidSyntax, 1, 6, "',' or ']'");
    try expectFailure("p('open).", error.InvalidSyntax, 1, 3, "a closing quote");
    try expectFailure("p(X), X <>.", error.InvalidSyntax, 1, 11, "a term");
    try expectFailure("p(X), foo?", error.InvalidSyntax, 1, 10, "'(' or an operator");
    try expectFailure("X(a).", error.InvalidSyntax, 1, 1, "a predicate name");
    try expectFailure("p(12abc).", error.InvalidSyntax, 1, 3, null);
    try expectFailure("q(X) :- not X = Y + 1.", error.InvalidSyntax, 1, 9, "a test after 'not'");
}

test "shape errors are the statement's kind, located at the offending goal" {
    try expectFailure("p(a).\nX = a.", error.InvalidFact, 2, 1, "a relation");
    try expectFailure("not p(a).", error.InvalidFact, 1, 1, "a relation");
    try expectFailure("setof(X, p(X), S).", error.InvalidFact, 1, 1, "a relation");
    try expectFailure("not h(X) :- p(X).", error.InvalidRule, 1, 1, "a relation");
    try expectFailure("X < 1 :- p(X).", error.InvalidRule, 1, 1, "a relation");
}

test "numeric literals that do not fit are located" {
    try expectFailure("big(99999999999999999999).", error.NumericOverflow, 1, 5, null);
    try expectFailure("p(a).\nhuge(1e400).", error.NumericOverflow, 2, 6, null);
    var diagnostic: Diagnostic = .{};
    try testing.expectError(
        error.NumericOverflow,
        parseProgram(testing.allocator, "p(a). q(-2e308).", &diagnostic),
    );
    try testing.expectEqual(@as(?usize, 1), diagnostic.statement);
    try testing.expectEqualDeep(@as(?Span, .{ .start = 8, .end = 14 }), diagnostic.span);
}

test "a single rule or goal list parses on its own" {
    const x = input.variable("X");
    const rule = try parseRule(testing.allocator, "h(X) :- p(X), not q(X)", null);
    defer rule.deinit();
    try testing.expectEqualDeep(input.rule(input.fact("h", &.{x}), &.{
        input.relation("p", &.{x}),
        input.not("q", &.{x}),
    }), rule.value);

    const dotted = try parseRule(testing.allocator, "h(X) :- p(X).", null);
    dotted.deinit();

    const goals = try parseGoals(testing.allocator, "p(X), X > 1?", null);
    defer goals.deinit();
    try testing.expectEqualDeep(@as([]const input.Goal, &.{
        input.relation("p", &.{x}),
        input.greaterThan(x, input.integer(1)),
    }), goals.value);

    var diagnostic: Diagnostic = .{};
    try testing.expectError(error.InvalidRule, parseRule(testing.allocator, "p(a).", &diagnostic));
    try testing.expectEqualStrings("':-'", diagnostic.expected.?);
    try testing.expectError(error.InvalidSyntax, parseGoals(testing.allocator, "p(X)? q(X)?", &diagnostic));
    try testing.expectEqualStrings("the end of input", diagnostic.expected.?);
    try testing.expectEqual(@as(u32, 7), diagnostic.column);
    try testing.expectEqual(@as(?usize, null), diagnostic.statement);
}

test "an empty program has no statements" {
    const parsed = try parseProgram(testing.allocator, "  % nothing\n", null);
    defer parsed.deinit();
    try testing.expectEqual(@as(usize, 0), parsed.value.statements.len);
}

fn allocationScenario(allocator: std.mem.Allocator) !void {
    const parsed = try parseProgram(allocator,
        \\items([a, [b], c!T]).
        \\n(S) :- seed(k), setof(T, (group(G), setof([Y, G], parent(G, Y), T)), S).
        \\'q\'x'(X), not X < 2?
    , null);
    parsed.deinit();
    _ = parseProgram(allocator, "broken(S) :- setof(X, (p(X), bad([Y])), S.", null) catch |err| switch (err) {
        error.InvalidSyntax => return,
        else => return err,
    };
    return error.ExpectedInvalidSyntax;
}

test "parsing releases every allocation on failure" {
    try testing.checkAllAllocationFailures(testing.allocator, allocationScenario, .{});
}
