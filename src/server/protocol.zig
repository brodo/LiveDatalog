//! The line protocol spoken over TCP. See
//! docs/adr/0008-counted-tab-separated-protocol.md for why it looks like this.
//!
//! A client sends one request per line: a query (`path(a, X)?`, or without
//! the `?`), or a command starting with `.`. Every response starts with a
//! status line that says how many lines follow it:
//!
//!   ok table <rows>   a header line, then exactly <rows> rows
//!   ok text <lines>   exactly <lines> lines of text
//!   error <Name> <message>
//!                     nothing follows
//!
//! Header cells and row cells are separated by tabs. Every cell holds a value
//! in canonical Datalog syntax, which never contains a tab or a line break, so
//! a cell parses back to exactly the value it was written from. A cell left
//! empty holds no value. A query's header names its variables. A query
//! without variables has an empty header line and one empty row when it
//! holds, none when it does not.
//!
//! `.watch` turns the connection into a stream of `generation <n>` lines, one
//! now and one after every change to the database, and ends its requests.
//!
//! The data is read-only over the connection: facts, rules, retractions and
//! schemas belong in the watched `.dl` files.

const std = @import("std");
const LiveDatalog = @import("LiveDatalog");
const input = LiveDatalog.input;
const Engine = @import("Engine.zig");

pub const help_text =
    \\Send one request per line. Every response starts with 'ok table <rows>'
    \\(a tab-separated header, then that many rows), 'ok text <lines>' (then
    \\that many lines) or 'error <Name> <message>'.
    \\
    \\  path(a, X)?                 run a query (the trailing '?' is optional)
    \\  p(X), not q(X)?             goals may be combined as in a rule body
    \\  p(X, N) order by N desc?    list the answers in a chosen order
    \\  .predicates                 every predicate: name, arity, kind, facts, typed
    \\  .schema NAME                a predicate's schema: position, name, type
    \\  .rows NAME/ARITY [OFFSET [LIMIT]] [origin] [by POSITION [asc|desc] ...]
    \\                              a predicate's facts, headed by its schema;
    \\                              'origin' adds a $origin column: base or derived
    \\  .explain path(a, X)         show the join plan for the goals
    \\  .status                     directory, generation and counts
    \\  .errors                     what went wrong loading the files
    \\  .files                      list the loaded .dl files
    \\  .reload                     rescan the directory and rebuild
    \\  .watch                      stream 'generation <n>' after every change
    \\  .help                       this text
    \\  .quit                       close the connection
    \\
    \\Facts, rules, retractions and schemas come from the watched .dl files
    \\and are reloaded when those files change.
    \\
;

/// Answers one request line with one complete response.
pub fn handle(engine: *Engine, raw_line: []const u8, writer: *std.Io.Writer) !void {
    const line = std.mem.trim(u8, raw_line, &std.ascii.whitespace);
    if (line.len == 0) return writer.writeAll("error EmptyRequest send a query or a command; try .help\n");

    if (line[0] == '.' and line.len > 1 and std.ascii.isAlphabetic(line[1])) {
        const end = std.mem.findAny(u8, line, &std.ascii.whitespace) orelse line.len;
        const command = line[1..end];
        const argument = std.mem.trim(u8, line[end..], &std.ascii.whitespace);
        if (std.mem.eql(u8, command, "help")) return writeText(writer, help_text);
        if (std.mem.eql(u8, command, "status")) return status(engine, writer);
        if (std.mem.eql(u8, command, "errors")) return loadErrors(engine, writer);
        if (std.mem.eql(u8, command, "files")) return files(engine, writer);
        if (std.mem.eql(u8, command, "predicates")) return predicates(engine, writer);
        if (std.mem.eql(u8, command, "schema")) return schema(engine, argument, writer);
        if (std.mem.eql(u8, command, "rows")) return rows(engine, argument, writer);
        if (std.mem.eql(u8, command, "reload")) {
            engine.reloadAll();
            return status(engine, writer);
        }
        if (std.mem.eql(u8, command, "explain")) return explain(engine, argument, writer);
        return writer.print("error UnknownCommand .{s}; try .help\n", .{command});
    }

    // A line that does not end a statement is taken to be a query's goals.
    switch (line[line.len - 1]) {
        '.', '?', '~' => {},
        else => return queryGoals(engine, line, writer),
    }

    var diagnostic: LiveDatalog.Diagnostic = .{};
    const parsed = LiveDatalog.parseProgram(engine.gpa, line, &diagnostic) catch |err|
        return writeError(writer, err, diagnostic);
    defer parsed.deinit();
    const statements = parsed.value.statements;
    for (statements) |statement| switch (statement) {
        .query => {},
        .fact, .rule, .retraction, .schema => return writer.writeAll(
            "error ReadOnly facts, rules, retractions and schemas belong in the .dl files\n",
        ),
    };
    // One request, one response: only a single query can be answered.
    if (statements.len != 1) return writer.writeAll("error InvalidQuery send one query per line\n");
    const q = statements[0].query;
    try query(engine, q.goals, q.order, writer);
}

fn queryGoals(engine: *Engine, line: []const u8, writer: *std.Io.Writer) !void {
    var diagnostic: LiveDatalog.Diagnostic = .{};
    const parsed = LiveDatalog.parseGoals(engine.gpa, line, &diagnostic) catch |err|
        return writeError(writer, err, diagnostic);
    defer parsed.deinit();
    try query(engine, parsed.value, &.{}, writer);
}

fn query(
    engine: *Engine,
    goals: []const input.Goal,
    order: []const input.SortKey,
    writer: *std.Io.Writer,
) !void {
    var result = engine.db.query(goals, order) catch |err|
        return writer.print("error {s}\n", .{@errorName(err)});
    defer result.deinit();
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    for (result.variables.items) |name| try table.column(name);
    try writeAnswers(&table, result, 0, result.answers.items.len);
    try table.write(writer);
}

/// Answers `from..to` of `result` as rows, one cell per variable it lists.
fn writeAnswers(table: *Table, result: LiveDatalog.QueryResult, from: usize, to: usize) !void {
    for (result.answers.items[from..to]) |answer| {
        for (result.variables.items) |name| {
            const cell = try table.cell();
            const value = answer.getValue(name) catch continue;
            try value.write(cell);
        }
        try table.endRow();
    }
}

fn explain(engine: *Engine, source: []const u8, writer: *std.Io.Writer) !void {
    var diagnostic: LiveDatalog.Diagnostic = .{};
    const parsed = LiveDatalog.parseGoals(engine.gpa, source, &diagnostic) catch |err|
        return writeError(writer, err, diagnostic);
    defer parsed.deinit();
    const plan = engine.db.explainQuery(parsed.value) catch |err|
        return writer.print("error {s}\n", .{@errorName(err)});
    defer engine.gpa.free(plan);
    try writeText(writer, plan);
}

// ---------------------------------------------------------------------------
// Commands that describe the database

fn status(engine: *Engine, writer: *std.Io.Writer) !void {
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    try table.column("key");
    try table.column("value");
    try table.atoms(&.{ "directory", engine.root });
    const counts = [_]struct { []const u8, usize }{
        .{ "generation", engine.generation },
        .{ "files", engine.files.count() },
        .{ "facts", engine.db.state.facts.len() },
        .{ "errors", engine.errors.count() },
    };
    for (counts) |count| {
        try LiveDatalog.writeAtom(try table.cell(), count[0]);
        try (try table.cell()).print("{d}", .{count[1]});
        try table.endRow();
    }
    try table.write(writer);
}

fn loadErrors(engine: *Engine, writer: *std.Io.Writer) !void {
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    for ([_][]const u8{ "file", "line", "column", "error", "message" }) |name| try table.column(name);
    for (engine.errors.keys(), engine.errors.values()) |path, load_error| {
        try LiveDatalog.writeAtom(try table.cell(), engine.relative(path));
        const at = load_error.at;
        try (try table.cell()).print("{d}", .{if (at) |a| a.line + 1 else 0});
        try (try table.cell()).print("{d}", .{if (at) |a| a.start + 1 else 0});
        try LiveDatalog.writeAtom(try table.cell(), load_error.summary);
        try LiveDatalog.writeAtom(try table.cell(), load_error.message);
        try table.endRow();
    }
    try table.write(writer);
}

fn files(engine: *Engine, writer: *std.Io.Writer) !void {
    const paths = try engine.gpa.dupe([]const u8, engine.files.keys());
    defer engine.gpa.free(paths);
    std.mem.sort([]const u8, paths, {}, lessThan);
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    try table.column("path");
    for (paths) |path| try table.atoms(&.{engine.relative(path)});
    try table.write(writer);
}

fn predicates(engine: *Engine, writer: *std.Io.Writer) !void {
    const listed = engine.db.predicates(engine.gpa) catch |err|
        return writer.print("error {s}\n", .{@errorName(err)});
    defer engine.gpa.free(listed);
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    for ([_][]const u8{ "name", "arity", "kind", "facts", "typed" }) |name| try table.column(name);
    for (listed) |info| {
        try LiveDatalog.writeAtom(try table.cell(), info.name);
        try (try table.cell()).print("{d}", .{info.arity});
        try (try table.cell()).writeAll(@tagName(kindOf(info)));
        try (try table.cell()).print("{d}", .{info.facts.base + info.facts.derived});
        try (try table.cell()).writeAll(if (info.typed) "true" else "false");
        try table.endRow();
    }
    try table.write(writer);
}

/// Where a predicate's facts come from. See "Kind" in CONTEXT.md.
pub const Kind = enum { base, derived, mixed };

fn kindOf(info: LiveDatalog.PredicateInfo) Kind {
    if (!info.has_rules) return .base;
    return if (info.facts.base == 0) .derived else .mixed;
}

fn schema(engine: *Engine, argument: []const u8, writer: *std.Io.Writer) !void {
    if (argument.len == 0) return writer.writeAll("error MissingArgument .schema NAME\n");
    const columns = try engine.db.schemaColumns(engine.gpa, argument) orelse &.{};
    defer engine.gpa.free(columns);
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    for ([_][]const u8{ "position", "name", "type" }) |name| try table.column(name);
    for (columns, 1..) |column, position| {
        try (try table.cell()).print("{d}", .{position});
        const name_cell = try table.cell();
        if (column.name) |name| try LiveDatalog.writeAtom(name_cell, name);
        var type_text: [64]u8 = undefined;
        try LiveDatalog.writeAtom(
            try table.cell(),
            std.fmt.bufPrint(&type_text, "{f}", .{column.type}) catch "any",
        );
        try table.endRow();
    }
    try table.write(writer);
}

/// What `.rows` asks for.
pub const RowsRequest = struct {
    name: []const u8,
    arity: usize,
    offset: usize = 0,
    limit: usize = std.math.maxInt(usize),
    /// Positions to order by, 0-based, in precedence order.
    order: []const SortPosition = &.{},
    /// Whether to add a last column saying whether each fact is base or
    /// derived.
    origin: bool = false,

    pub const SortPosition = struct {
        position: usize,
        direction: input.Direction = .ascending,
    };

    /// Parses `NAME/ARITY [OFFSET [LIMIT]] [origin] [by POSITION [asc|desc] ...]`,
    /// with 1-based positions; `origin` may also come last. `order` is
    /// allocated in `arena`.
    pub fn parse(arena: std.mem.Allocator, argument: []const u8) !RowsRequest {
        var words = std.mem.tokenizeAny(u8, argument, &std.ascii.whitespace);
        const predicate = words.next() orelse return error.MissingArgument;
        const slash = std.mem.findScalarLast(u8, predicate, '/') orelse return error.InvalidArgument;
        if (slash == 0) return error.InvalidArgument;
        var request: RowsRequest = .{
            .name = predicate[0..slash],
            .arity = std.fmt.parseInt(usize, predicate[slash + 1 ..], 10) catch return error.InvalidArgument,
        };
        var numbers: usize = 0;
        var order: std.ArrayList(SortPosition) = .empty;
        while (words.next()) |word| {
            if (std.mem.eql(u8, word, "by")) break;
            if (std.mem.eql(u8, word, "origin")) {
                request.origin = true;
                continue;
            }
            const number = std.fmt.parseInt(usize, word, 10) catch return error.InvalidArgument;
            switch (numbers) {
                0 => request.offset = number,
                1 => request.limit = number,
                else => return error.InvalidArgument,
            }
            numbers += 1;
        } else return request;
        while (words.next()) |word| {
            if (std.mem.eql(u8, word, "origin")) {
                request.origin = true;
                continue;
            }
            if (std.mem.eql(u8, word, "asc") or std.mem.eql(u8, word, "desc")) {
                if (order.items.len == 0) return error.InvalidArgument;
                order.items[order.items.len - 1].direction =
                    if (word[0] == 'a') .ascending else .descending;
                continue;
            }
            const position = std.fmt.parseInt(usize, word, 10) catch return error.InvalidArgument;
            if (position == 0 or position > request.arity) return error.InvalidArgument;
            try order.append(arena, .{ .position = position - 1 });
        }
        if (order.items.len == 0) return error.InvalidArgument;
        request.order = order.items;
        return request;
    }
};

fn rows(engine: *Engine, argument: []const u8, writer: *std.Io.Writer) !void {
    var arena_state: std.heap.ArenaAllocator = .init(engine.gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const request = RowsRequest.parse(arena, argument) catch |err| switch (err) {
        error.OutOfMemory => |e| return e,
        else => return writer.print(
            "error {s} .rows NAME/ARITY [OFFSET [LIMIT]] [origin] [by POSITION [asc|desc] ...]\n",
            .{@errorName(err)},
        ),
    };

    const variables = try arena.alloc([]const u8, request.arity);
    const terms = try arena.alloc(input.Term, request.arity);
    for (variables, terms, 1..) |*name, *term, position| {
        name.* = try std.fmt.allocPrint(arena, "C{d}", .{position});
        term.* = input.variable(name.*);
    }
    const keys = try arena.alloc(input.SortKey, request.order.len);
    for (request.order, keys) |sort, *key| key.* = .{
        .variable = variables[sort.position],
        .direction = sort.direction,
    };
    var result = engine.db.query(&.{input.relation(request.name, terms)}, keys) catch |err|
        return writer.print("error {s}\n", .{@errorName(err)});
    defer result.deinit();

    const columns = try engine.db.schemaColumns(engine.gpa, request.name);
    defer if (columns) |c| engine.gpa.free(c);
    var table: Table = .init(engine.gpa);
    defer table.deinit();
    for (0..request.arity) |index| {
        const named = if (columns) |c| (if (index < c.len) c[index].name else null) else null;
        if (named) |name| {
            try table.column(name);
        } else {
            var position: [24]u8 = undefined;
            try table.column(try std.fmt.bufPrint(&position, "{d}", .{index + 1}));
        }
    }
    const total = result.answers.items.len;
    const from = @min(request.offset, total);
    const to = from + @min(request.limit, total - from);
    if (!request.origin) {
        try writeAnswers(&table, result, from, to);
        return table.write(writer);
    }

    // A fact is base when it is asserted, whether or not a rule derives it
    // too: the rows it is written as tell the two apart.
    try table.column("$origin");
    var base = engine.db.baseFacts(request.name, request.arity) catch |err|
        return writer.print("error {s}\n", .{@errorName(err)});
    defer base.deinit();
    var asserted: std.StringHashMapUnmanaged(void) = .empty;
    for (base.answers.items) |answer| {
        var row: std.Io.Writer.Allocating = .init(arena);
        try writeRow(&row.writer, base, answer);
        try asserted.put(arena, row.written(), {});
    }
    for (result.answers.items[from..to]) |answer| {
        var row: std.Io.Writer.Allocating = .init(arena);
        try writeRow(&row.writer, result, answer);
        for (result.variables.items) |name| {
            const cell = try table.cell();
            const value = answer.getValue(name) catch continue;
            try value.write(cell);
        }
        try (try table.cell()).writeAll(if (asserted.contains(row.written())) "base" else "derived");
        try table.endRow();
    }
    try table.write(writer);
}

/// Writes one answer's values, tab-separated, as a key to compare rows by.
fn writeRow(writer: *std.Io.Writer, result: LiveDatalog.QueryResult, answer: LiveDatalog.Answer) !void {
    for (result.variables.items, 0..) |name, index| {
        if (index != 0) try writer.writeByte('\t');
        const value = answer.getValue(name) catch continue;
        try value.write(writer);
    }
}

// ---------------------------------------------------------------------------
// Framing

/// A table response. Its row count comes first on the wire, so rows are
/// collected before anything is written.
pub const Table = struct {
    header: std.Io.Writer.Allocating,
    body: std.Io.Writer.Allocating,
    columns: usize = 0,
    rows: usize = 0,
    cells: usize = 0,

    pub fn init(gpa: std.mem.Allocator) Table {
        return .{ .header = .init(gpa), .body = .init(gpa) };
    }

    pub fn deinit(self: *Table) void {
        self.header.deinit();
        self.body.deinit();
        self.* = undefined;
    }

    /// Adds a column headed by `name`, which holds no tab or line break.
    pub fn column(self: *Table, name: []const u8) !void {
        std.debug.assert(std.mem.findAny(u8, name, "\t\r\n") == null);
        if (self.columns != 0) try self.header.writer.writeByte('\t');
        try self.header.writer.writeAll(name);
        self.columns += 1;
    }

    /// Starts the next cell of the current row and returns where to write it.
    pub fn cell(self: *Table) !*std.Io.Writer {
        if (self.cells != 0) try self.body.writer.writeByte('\t');
        self.cells += 1;
        return &self.body.writer;
    }

    pub fn endRow(self: *Table) !void {
        try self.body.writer.writeByte('\n');
        self.rows += 1;
        self.cells = 0;
    }

    /// Adds a row of atoms.
    pub fn atoms(self: *Table, values: []const []const u8) !void {
        for (values) |value| try LiveDatalog.writeAtom(try self.cell(), value);
        try self.endRow();
    }

    pub fn write(self: *Table, writer: *std.Io.Writer) !void {
        try writer.print("ok table {d}\n", .{self.rows});
        try writer.writeAll(self.header.written());
        try writer.writeByte('\n');
        try writer.writeAll(self.body.written());
    }
};

/// Writes `text` as a text response, as many lines as it has.
pub fn writeText(writer: *std.Io.Writer, text: []const u8) !void {
    const body = std.mem.trimEnd(u8, text, "\n");
    if (body.len == 0) return writer.writeAll("ok text 0\n");
    try writer.print("ok text {d}\n{s}\n", .{ std.mem.count(u8, body, "\n") + 1, body });
}

fn writeError(writer: *std.Io.Writer, err: anyerror, diagnostic: LiveDatalog.Diagnostic) !void {
    try writer.print("error {s}", .{@errorName(err)});
    if (diagnostic.span != null) try writer.print(" at column {d}", .{diagnostic.column});
    if (diagnostic.expected) |expected| try writer.print(", expected {s}", .{expected});
    try writer.writeByte('\n');
}

fn lessThan(_: void, a: []const u8, b: []const u8) bool {
    return std.mem.order(u8, a, b) == .lt;
}

/// `path:line:column: Error, expected ...` followed by the offending source
/// line and a caret under the column.
pub fn writeDiagnostic(
    writer: *std.Io.Writer,
    path: []const u8,
    source: []const u8,
    err: anyerror,
    diagnostic: LiveDatalog.Diagnostic,
) !void {
    try writer.print("{s}", .{path});
    if (diagnostic.span != null) try writer.print(":{d}:{d}", .{ diagnostic.line, diagnostic.column });
    try writer.print(": {s}", .{@errorName(err)});
    if (diagnostic.expected) |expected| try writer.print(", expected {s}", .{expected});
    const span = diagnostic.span orelse return;
    if (diagnostic.column == 0 or span.start + 1 < diagnostic.column) return;
    const line_start = span.start + 1 - diagnostic.column;
    const line_end = std.mem.findScalarPos(u8, source, line_start, '\n') orelse source.len;
    try writer.print("\n{s}\n", .{source[line_start..line_end]});
    try writer.splatByteAll(' ', diagnostic.column - 1);
    try writer.writeByte('^');
}

test "diagnostics point at the offending column" {
    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer out.deinit();
    const source = "p(a).\np(b";
    var diagnostic: LiveDatalog.Diagnostic = .{};
    const parsed = LiveDatalog.parseProgram(std.testing.allocator, source, &diagnostic);
    try std.testing.expectError(error.InvalidSyntax, parsed);
    try writeDiagnostic(&out.writer, "a.dl", source, error.InvalidSyntax, diagnostic);
    try std.testing.expect(std.mem.startsWith(u8, out.written(), "a.dl:2:"));
    try std.testing.expect(std.mem.endsWith(u8, out.written(), "^"));
}

test "text responses count their lines" {
    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer out.deinit();
    try writeText(&out.writer, "one\n\nthree\n");
    try writeText(&out.writer, "");
    try std.testing.expectEqualStrings("ok text 3\none\n\nthree\nok text 0\n", out.written());
}

test "rows requests parse paging and ordering" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const plain = try RowsRequest.parse(arena, "edge/2");
    try std.testing.expectEqualStrings("edge", plain.name);
    try std.testing.expectEqual(@as(usize, 2), plain.arity);
    try std.testing.expectEqual(@as(usize, 0), plain.offset);

    const paged = try RowsRequest.parse(arena, "born_in/3 100 50 by 3 desc 1");
    try std.testing.expectEqual(@as(usize, 100), paged.offset);
    try std.testing.expectEqual(@as(usize, 50), paged.limit);
    try std.testing.expectEqual(@as(usize, 2), paged.order.len);
    try std.testing.expectEqual(@as(usize, 2), paged.order[0].position);
    try std.testing.expectEqual(input.Direction.descending, paged.order[0].direction);
    try std.testing.expectEqual(input.Direction.ascending, paged.order[1].direction);

    try std.testing.expect(!paged.origin);
    try std.testing.expect((try RowsRequest.parse(arena, "edge/2 0 10 origin")).origin);
    try std.testing.expect((try RowsRequest.parse(arena, "edge/2 by 1 desc origin")).origin);

    try std.testing.expectError(error.InvalidArgument, RowsRequest.parse(arena, "edge"));
    try std.testing.expectError(error.InvalidArgument, RowsRequest.parse(arena, "edge/2 by 3"));
    try std.testing.expectError(error.InvalidArgument, RowsRequest.parse(arena, "edge/2 by"));
    try std.testing.expectError(error.MissingArgument, RowsRequest.parse(arena, ""));
}
