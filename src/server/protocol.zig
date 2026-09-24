//! The line protocol spoken over TCP.
//!
//! A client sends one request per line: a query (`path(a, X)?`, or without
//! the `?`), or a command starting with `.`. The server answers with zero or
//! more lines followed by an empty line, which never occurs inside a response.
//!
//! Query answers use the LiveDatalog REPL's format: one line of bindings per
//! answer (`X: a, Y: b`), `Yes.` for a ground query that holds, and `No.` for
//! one without answers. Failures are a single `Error: ...` line.
//!
//! The data is read-only over the connection: facts, rules, retractions and
//! schemas belong in the watched `.dl` files.

const std = @import("std");
const LiveDatalog = @import("LiveDatalog");
const Engine = @import("Engine.zig");

pub const help_text =
    \\Send one request per line; every response ends with an empty line.
    \\
    \\  path(a, X)?                 run a query (the trailing '?' is optional)
    \\  p(X), not q(X)?             goals may be combined as in a rule body
    \\  p(X, N) order by N desc?    list the answers in a chosen order
    \\  .explain path(a, X)         show the join plan for the goals
    \\  .status                     directory, generation, counts, load errors
    \\  .files                      list the loaded .dl files
    \\  .reload                     rescan the directory and rebuild
    \\  .help                       this text
    \\  .quit                       close the connection
    \\
    \\Facts, rules, retractions and schemas come from the watched .dl files
    \\and are reloaded when those files change.
    \\
;

/// Answers one request line. Always ends the response with an empty line.
pub fn handle(engine: *Engine, raw_line: []const u8, writer: *std.Io.Writer) !void {
    const line = std.mem.trim(u8, raw_line, &std.ascii.whitespace);
    defer writer.writeByte('\n') catch {};
    if (line.len == 0) return;

    if (line[0] == '.' and line.len > 1 and std.ascii.isAlphabetic(line[1])) {
        const end = std.mem.findAny(u8, line, &std.ascii.whitespace) orelse line.len;
        const command = line[1..end];
        const argument = std.mem.trim(u8, line[end..], &std.ascii.whitespace);
        if (std.mem.eql(u8, command, "help")) return writer.writeAll(help_text);
        if (std.mem.eql(u8, command, "status")) return engine.writeStatus(writer);
        if (std.mem.eql(u8, command, "files")) return engine.writeFiles(writer);
        if (std.mem.eql(u8, command, "reload")) {
            engine.reloadAll();
            return engine.writeStatus(writer);
        }
        if (std.mem.eql(u8, command, "explain")) return explain(engine, argument, writer);
        return writer.print("Error: unknown command .{s}; try .help\n", .{command});
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
    for (parsed.value.statements) |statement| switch (statement) {
        .query => |q| try query(engine, q.goals, q.order, writer),
        .fact, .rule, .retraction, .schema => return writer.writeAll(
            "Error: read-only; facts, rules, retractions and schemas belong in the .dl files\n",
        ),
    };
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
    goals: []const LiveDatalog.input.Goal,
    order: []const LiveDatalog.input.SortKey,
    writer: *std.Io.Writer,
) !void {
    var result = engine.db.query(goals, order) catch |err|
        return writer.print("Error: {s}\n", .{@errorName(err)});
    defer result.deinit();
    try writeAnswers(writer, result);
}

fn explain(engine: *Engine, source: []const u8, writer: *std.Io.Writer) !void {
    var diagnostic: LiveDatalog.Diagnostic = .{};
    const parsed = LiveDatalog.parseGoals(engine.gpa, source, &diagnostic) catch |err|
        return writeError(writer, err, diagnostic);
    defer parsed.deinit();
    const plan = engine.db.explainQuery(parsed.value) catch |err|
        return writer.print("Error: {s}\n", .{@errorName(err)});
    defer engine.gpa.free(plan);
    try writer.writeAll(plan);
    if (plan.len != 0 and plan[plan.len - 1] != '\n') try writer.writeByte('\n');
}

pub fn writeAnswers(writer: *std.Io.Writer, result: LiveDatalog.QueryResult) !void {
    if (result.answers.items.len == 0) return writer.writeAll("No.\n");
    if (result.answers.items[0].bindings.items.len == 0) return writer.writeAll("Yes.\n");
    for (result.answers.items) |answer| {
        for (answer.bindings.items, 0..) |binding, index| {
            if (index != 0) try writer.writeAll(", ");
            try writer.print("{s}: ", .{binding.name});
            try binding.value.write(writer);
        }
        try writer.writeByte('\n');
    }
}

fn writeError(writer: *std.Io.Writer, err: anyerror, diagnostic: LiveDatalog.Diagnostic) !void {
    try writer.print("Error: {s}", .{@errorName(err)});
    if (diagnostic.span != null) try writer.print(" at column {d}", .{diagnostic.column});
    if (diagnostic.expected) |expected| try writer.print(", expected {s}", .{expected});
    try writer.writeByte('\n');
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

/// Writes `text` with every line after the first indented, ending in a newline.
pub fn writeIndented(writer: *std.Io.Writer, text: []const u8) !void {
    var lines = std.mem.splitScalar(u8, text, '\n');
    var first = true;
    while (lines.next()) |line| {
        if (!first) try writer.writeAll("  ");
        try writer.print("{s}\n", .{line});
        first = false;
    }
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
