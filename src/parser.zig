//! The source syntax: tokenizer, term and clause parsing, and the statement
//! loop that drives a program's transactions.
//!
//! Parsing interns into whichever database it is pointed at, which is how a
//! statement's query-local symbols, scalars and structures stay out of the
//! committed database: the loop points each statement at a `Statement`'s
//! staging copy and commits only what the statement turned out to be.
//!
//! This module holds syntax only. It reaches the database through four
//! compiled-statement operations and the statement transaction, never through
//! the transaction primitives those are built from.

const std = @import("std");
const database = @import("database.zig");
const statement = @import("statement.zig");
const results = @import("results.zig");
const syntax = @import("syntax.zig");
const errors = @import("errors.zig");
const test_support = @import("test_support.zig");

pub const Parser = struct {
    jatalog: *database.Database,
    source: []const u8,
    index: usize = 0,

    pub fn executeAll(self: *Parser) !results.ExecutionResult {
        var last: ?results.ExecutionResult = null;
        errdefer if (last) |*result| result.deinit();
        while (true) {
            self.skipSpace();
            if (self.index == self.source.len) return last orelse .none;
            if (last) |*result| result.deinit();
            last = null;
            var transaction = try statement.Statement.begin(self.jatalog, self.peekStatementKind());
            defer transaction.deinit();
            var statement_parser = self.*;
            statement_parser.jatalog = transaction.target();
            const statement_result = try statement_parser.executeStatement(&transaction);
            self.index = statement_parser.index;
            try transaction.commit(statement_result);
            last = statement_result;
        }
    }

    /// Classifies the next statement by scanning for its terminator without
    /// interning anything, mirroring the tokenizer's comment, quote, and
    /// digit-dot-digit rules.
    fn peekStatementKind(self: *const Parser) statement.Statement.Kind {
        var index = self.index;
        while (index < self.source.len) : (index += 1) {
            const byte = self.source[index];
            if (byte == '%' or (byte == '/' and index + 1 < self.source.len and
                self.source[index + 1] == '/'))
            {
                while (index < self.source.len and self.source[index] != '\n') index += 1;
                continue;
            }
            if (byte == '/' and index + 1 < self.source.len and self.source[index + 1] == '*') {
                const end = std.mem.indexOfPos(u8, self.source, index + 2, "*/") orelse
                    return .end;
                index = end + 1;
                continue;
            }
            if (byte == '\'' or byte == '"') {
                index += 1;
                while (index < self.source.len and self.source[index] != byte) {
                    if (self.source[index] == '\\') index += 1;
                    index += 1;
                }
                if (index == self.source.len) return .end;
                continue;
            }
            if (byte == '?') return .query;
            if (byte == '~') return .retraction;
            if (byte == '.') {
                const digit_before = index > self.index and
                    std.ascii.isDigit(self.source[index - 1]);
                const digit_after = index + 1 < self.source.len and
                    std.ascii.isDigit(self.source[index + 1]);
                if (!(digit_before and digit_after)) return .assertion;
            }
        }
        return .end;
    }

    /// Runs one statement against `self.jatalog`, which is `transaction`'s
    /// staging copy. The transaction is named here only for the retraction,
    /// whose commit needs the facts its goals resolved to; every other
    /// statement is committed from the staging copy alone.
    fn executeStatement(self: *Parser, transaction: *statement.Statement) !results.ExecutionResult {
        const first = try self.parseClause();
        var first_owned = true;
        errdefer if (first_owned) syntax.freeClauseTree(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.consume(":-")) {
            const head = switch (first) {
                .relational => |expression| expression,
                else => return error.InvalidRule,
            };
            var body: std.ArrayList(syntax.Clause) = .empty;
            defer body.deinit(self.jatalog.allocator);
            errdefer for (body.items) |clause| syntax.freeClauseTree(self.jatalog.allocator, clause);
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    syntax.freeClauseTree(self.jatalog.allocator, clause);
                    return err;
                };
                self.skipSpace();
                if (!self.consume(",")) break;
            }
            try self.expect(".");
            try statement.addRuleClauses(self.jatalog, head, body.items);
            first_owned = false;
            return .none;
        }
        self.skipSpace();
        if (self.consume(".")) {
            const fact = switch (first) {
                .relational => |expression| expression,
                else => return error.InvalidFact,
            };
            try statement.addFactExpr(self.jatalog, fact);
            syntax.freeClauseTree(self.jatalog.allocator, first);
            first_owned = false;
            return .none;
        }

        var goals: std.ArrayList(syntax.Clause) = .empty;
        defer {
            for (goals.items) |clause| syntax.freeClauseTree(self.jatalog.allocator, clause);
            goals.deinit(self.jatalog.allocator);
        }
        try goals.append(self.jatalog.allocator, first);
        first_owned = false;
        while (self.consume(",")) {
            const goal = try self.parseClause();
            goals.append(self.jatalog.allocator, goal) catch |err| {
                syntax.freeClauseTree(self.jatalog.allocator, goal);
                return err;
            };
        }
        if (self.consume("?")) return .{ .query = try statement.queryClauses(self.jatalog, goals.items) };
        if (self.consume("~")) return .{ .changed = try transaction.retract(goals.items) };
        return error.InvalidSyntax;
    }

    fn parseClause(self: *Parser) anyerror!syntax.Clause {
        self.skipSpace();
        if (self.peekKeyword("setof")) return .{ .aggregate = try self.parseAggregate() };
        const expression = try self.parseExpr();
        return syntax.classifyExpr(expression);
    }

    fn parseAggregate(self: *Parser) anyerror!syntax.Aggregate {
        const keyword = try self.parseBare();
        if (!std.mem.eql(u8, keyword, "setof")) return error.InvalidSyntax;
        try self.expect("(");
        const template = try self.parseTerm();
        var template_owned = true;
        errdefer if (template_owned) syntax.freeTerm(self.jatalog.allocator, template);
        try self.expect(",");

        var body: std.ArrayList(syntax.Clause) = .empty;
        errdefer {
            for (body.items) |clause| syntax.freeClauseTree(self.jatalog.allocator, clause);
            body.deinit(self.jatalog.allocator);
        }
        if (self.consume("(")) {
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    syntax.freeClauseTree(self.jatalog.allocator, clause);
                    return err;
                };
                if (self.consume(")")) break;
                try self.expect(",");
            }
        } else {
            const clause = try self.parseClause();
            body.append(self.jatalog.allocator, clause) catch |err| {
                syntax.freeClauseTree(self.jatalog.allocator, clause);
                return err;
            };
        }
        try self.expect(",");
        const output = try self.parseTerm();
        errdefer syntax.freeTerm(self.jatalog.allocator, output);
        try self.expect(")");
        const owned_body = try body.toOwnedSlice(self.jatalog.allocator);
        template_owned = false;
        return .{
            .template = template,
            .body = owned_body,
            .output = output,
        };
    }

    fn parseExpr(self: *Parser) !syntax.Expr {
        self.skipSpace();
        var negated = false;
        if (self.peekKeyword("not")) {
            _ = try self.parseBare();
            negated = true;
        }
        const first = try self.parseTerm();
        var first_owned = true;
        errdefer if (first_owned) syntax.freeTerm(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.parseOperator()) |operator| {
            const second = try self.parseTerm();
            errdefer syntax.freeTerm(self.jatalog.allocator, second);
            if (std.mem.eql(u8, operator, "=")) {
                const arithmetic: ?syntax.GoalKind = if (self.consume("+"))
                    .add
                else if (self.consume("-"))
                    .subtract
                else
                    null;
                if (arithmetic) |arithmetic_kind| {
                    if (negated) return error.InvalidSyntax;
                    const third = try self.parseTerm();
                    errdefer syntax.freeTerm(self.jatalog.allocator, third);
                    const predicate = try self.jatalog.strings.intern(syntax.goalOperator(arithmetic_kind));
                    const terms = try self.jatalog.allocator.alloc(syntax.Term, 3);
                    terms[0] = first;
                    terms[1] = second;
                    terms[2] = third;
                    first_owned = false;
                    return .{ .predicate = predicate, .terms = terms, .kind = arithmetic_kind };
                }
            }
            const kind = syntax.goalKind(operator) orelse return error.UnknownOperator;
            const predicate = try self.jatalog.strings.intern(syntax.goalOperator(kind));
            const terms = try self.jatalog.allocator.alloc(syntax.Term, 2);
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
        if (!self.consume("(")) return error.InvalidSyntax;
        const predicate = switch (first) {
            .scalar => |scalar_id| switch (self.jatalog.eval.scalars.get(scalar_id)) {
                .atom => |atom| try self.jatalog.strings.intern(atom),
                .integer, .float => return error.InvalidSyntax,
            },
            else => return error.InvalidSyntax,
        };
        first_owned = false;
        var terms: std.ArrayList(syntax.Term) = .empty;
        errdefer {
            for (terms.items) |term| syntax.freeTerm(self.jatalog.allocator, term);
            terms.deinit(self.jatalog.allocator);
        }
        self.skipSpace();
        if (!self.consume(")")) {
            while (true) {
                const term = try self.parseTerm();
                terms.append(self.jatalog.allocator, term) catch |err| {
                    syntax.freeTerm(self.jatalog.allocator, term);
                    return err;
                };
                self.skipSpace();
                if (self.consume(")")) break;
                try self.expect(",");
            }
        }
        return .{ .predicate = predicate, .terms = try terms.toOwnedSlice(self.jatalog.allocator), .negated = negated };
    }

    fn parseTerm(self: *Parser) anyerror!syntax.Term {
        var head = try self.parseTermPrimary();
        errdefer syntax.freeTerm(self.jatalog.allocator, head);
        if (self.consumeConsBang()) {
            const tail = try self.parseTerm();
            errdefer syntax.freeTerm(self.jatalog.allocator, tail);
            head = try self.makeCons(head, tail);
        }
        return head;
    }

    fn parseTermPrimary(self: *Parser) anyerror!syntax.Term {
        self.skipSpace();
        if (self.index == self.source.len) return error.InvalidSyntax;
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
            if (self.index == self.source.len) return error.InvalidSyntax;
            self.index += 1;
            return .{ .scalar = try self.jatalog.eval.scalars.internAtom(string.items) };
        }
        const value = try self.parseBare();
        if (std.mem.eql(u8, value, "cons") and self.consume("(")) {
            const head = try self.parseTerm();
            errdefer syntax.freeTerm(self.jatalog.allocator, head);
            try self.expect(",");
            const tail = try self.parseTerm();
            errdefer syntax.freeTerm(self.jatalog.allocator, tail);
            try self.expect(")");
            return self.makeCons(head, tail);
        }
        if (syntax.isVariable(value)) return .{ .variable = try self.jatalog.strings.intern(value) };
        return .{ .scalar = try self.jatalog.eval.scalars.parseBare(value) };
    }

    fn parseListTail(self: *Parser) anyerror!syntax.Term {
        if (self.consume("]")) return .nil;
        const head = try self.parseTerm();
        errdefer syntax.freeTerm(self.jatalog.allocator, head);
        var tail: syntax.Term = undefined;
        if (self.consume("]")) {
            tail = .nil;
        } else if (self.consume(",")) {
            tail = try self.parseListTail();
        } else if (self.consumeConsBang()) {
            tail = try self.parseImproperListTail();
        } else return error.InvalidSyntax;
        errdefer syntax.freeTerm(self.jatalog.allocator, tail);
        return self.makeCons(head, tail);
    }

    fn parseImproperListTail(self: *Parser) anyerror!syntax.Term {
        const tail = try self.parseTerm();
        errdefer syntax.freeTerm(self.jatalog.allocator, tail);
        try self.expect("]");
        return tail;
    }

    fn makeCons(self: *Parser, head: syntax.Term, tail: syntax.Term) !syntax.Term {
        const pair = try self.jatalog.allocator.create(syntax.Term.Cons);
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
        if (self.index == start) return error.InvalidSyntax;
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
        if (!self.consume(token)) return error.InvalidSyntax;
    }

    fn peekKeyword(self: *Parser, keyword: []const u8) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], keyword)) return false;
        const end = self.index + keyword.len;
        return end == self.source.len or !(std.ascii.isAlphanumeric(self.source[end]) or self.source[end] == '_');
    }
};

/// Runs a source program against `db`, which is what `Jatalog.execute` does one
/// layer up. Spelled out here so the parser's own tests need nothing above the
/// parser to build the database they parse into.
fn execute(db: *database.Database, source: []const u8) !results.ExecutionResult {
    var statement_parser: Parser = .{ .jatalog = db, .source = source };
    return statement_parser.executeAll();
}

test "a parse error after a query releases the previous result" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db,
        \\p(a). p(X)?
        \\bad(X) :- q(X), X <>.
    ));
}

test "head tail patterns work in rules and cons syntax is equivalent" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try execute(&db,
        \\items(cons(a, cons(b, []))).
        \\tail(T) :- items(H!T).
        \\tail(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "[b]");
}

test "structural equality binds variables recursively and parse errors clean up" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try execute(&db, "seed(a). seed(X), [X] = [a]?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));

    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db, "broken([a, [b])."));
}

fn structuralAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var result = try execute(&db,
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
    try test_support.expectEveryAllocationFailureReleased(structuralAllocationScenario);
}

fn aggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var result = try execute(&db,
        \\seed(k).
        \\nested(S) :- seed(k), setof(T, (group(G), setof([Y, G], parent(G, Y), T)), S).
    );
    result.deinit();
    const malformed_source = "broken(S) :- seed(k), setof(X, (parent(X, Y), bad([Y])), S.";
    var malformed = execute(&db, malformed_source) catch |err| switch (err) {
        errors.Error.InvalidSyntax => return,
        else => return err,
    };
    malformed.deinit();
    return error.ExpectedInvalidSyntax;
}

test "aggregate parser errors release all partial clause trees" {
    try test_support.expectEveryAllocationFailureReleased(aggregateAllocationScenario);
}

test "quoted numeric atoms remain distinct from numeric scalars" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try execute(&db, "value(1). value('1'). value('1.0'). setof(X, value(X), S)?");
    defer result.deinit();
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[1, '1', '1.0']");

    var inequality = try execute(&db, "1 = '1'?");
    defer inequality.deinit();
    try std.testing.expectEqual(@as(usize, 0), inequality.query.answers.items.len);

    var quoted_float = try execute(&db, "1000 = '1e3'?");
    defer quoted_float.deinit();
    try std.testing.expectEqual(@as(usize, 0), quoted_float.query.answers.items.len);

    var nested = try execute(&db, "nested([1]). nested(['1']). nested([1.0]). nested([1])?");
    defer nested.deinit();
    try std.testing.expectEqual(@as(usize, 1), nested.query.answers.items.len);

    var quoted_setof = try execute(&db, "text('2.5'). text(2.5). setof(X, text(X), S)?");
    defer quoted_setof.deinit();
    try test_support.expectBindingValue(&quoted_setof.query.answers.items[0], "S", "[2.5, '2.5']");

    var arithmetic = try execute(&db, "01 = +0 + 1?");
    defer arithmetic.deinit();
    try std.testing.expectEqual(@as(usize, 1), arithmetic.query.answers.items.len);

    try std.testing.expectError(errors.Error.NumericType, execute(&db, "value(X), X < 2?"));
}

test "non-finite and malformed numeric source reports stable errors" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NumericOverflow, execute(&db, "value(1e400)."));
    try std.testing.expectError(errors.Error.NumericOverflow, execute(&db, "value(-1e400)."));
    try std.testing.expectError(errors.Error.NumericOverflow, execute(&db, "value(2e308)."));

    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db, "value(1e)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db, "value(1e+)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db, "value(1.2.3)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db, "value(12abc)."));
    try std.testing.expectError(errors.Error.InvalidSyntax, execute(&db, "value(1.)."));

    var absent = try execute(&db, "value(X)?");
    defer absent.deinit();
    try std.testing.expectEqual(@as(usize, 0), absent.query.answers.items.len);
}

test "float literals parse and integral values canonicalize to integers" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try execute(&db,
        \\value(2.5). value(0.5). value(-0.025). value(1.0).
        \\value(1). value(1e0). value(1e3). value(-0.0).
        \\value(0). value(1e-999).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "S",
        "[-0.025, 0, 0.5, 1, 2.5, 1000]",
    );

    var canonical = try execute(&db, "nested([1.0]). nested([1])?");
    defer canonical.deinit();
    try std.testing.expectEqual(@as(usize, 1), canonical.query.answers.items.len);

    var integral = try execute(&db, "value(X), X = 1e0?");
    defer integral.deinit();
    try std.testing.expectEqual(@as(usize, 1), integral.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 1),
        try integral.query.answers.items[0].getInteger("X"),
    );
}

test "float extremes format deterministically and round-trip" {
    var db: database.Database = .init(std.testing.allocator);
    defer db.deinit();
    var result = try execute(&db,
        \\extreme(5e-324). extreme(2.2250738585072014e-308).
        \\extreme(1.7976931348623157e308). extreme(-1.7976931348623157e308).
        \\extreme(1e300).
        \\setof(X, extreme(X), S)?
    );
    defer result.deinit();
    try test_support.expectBindingValue(
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
        var ground = try execute(&db, query);
        defer ground.deinit();
        try std.testing.expectEqual(@as(usize, 1), ground.query.answers.items.len);
    }

    var formatted = try execute(&db, "half(0.5). half(X)?");
    defer formatted.deinit();
    const value = try formatted.query.answers.items[0].getValue("X");
    const spelled = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("0.5", spelled);
    try std.testing.expectEqual(results.ResultValue.Kind.float, value.kind());
    try std.testing.expectError(errors.Error.TypeMismatch, value.getInteger());
}
