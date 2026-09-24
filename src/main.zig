const std = @import("std");
const LiveDatalog = @import("LiveDatalog");
const linenoise = @import("linenoise");

const help_text =
    \\LiveDatalog syntax reference
    \\
    \\% Fact
    \\predicate(atom, value).
    \\
    \\% Numbers: exact i64 integers and finite f64 floats.
    \\% 1, 1.0, and 1e0 are one value; quoted '1.0' is an atom.
    \\age(alice, 36).
    \\height(alice, 1.75).
    \\
    \\% Rule
    \\derived(X) :- source(X), condition(X).
    \\
    \\% Query
    \\derived(X)?
    \\
    \\% Query with an answer order (asc is the default)
    \\score(P, S) order by S desc, P?
    \\
    \\% Retraction
    \\source(X)~
    \\
    \\% Negation
    \\allowed(X) :- item(X), not blocked(X).
    \\
    \\% Equality, inequality, and numeric comparison
    \\X = value
    \\X != Y
    \\X <> Y
    \\N < 10
    \\N <= 10
    \\N > 10
    \\N >= 10
    \\
    \\% List terms (use them inside a statement)
    \\[]
    \\[a, b, c]
    \\H!T
    \\cons(H, T)
    \\
    \\% Aggregate
    \\setof(Template, Goal, Result)
    \\setof(Template, (Goal1, Goal2), Result)
    \\
    \\REPL commands: .help, .quit, .exit
    \\
;

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    const args = try init.minimal.args.toSlice(allocator);

    var database: LiveDatalog.Jatalog = .init(allocator);
    defer database.deinit();

    if (args.len > 1) {
        const source = try std.Io.Dir.cwd().readFileAlloc(init.io, args[1], allocator, .unlimited);
        return executeAndPrint(init.io, &database, source) catch std.process.exit(1);
    }

    if (!(std.Io.File.stdin().isTty(init.io) catch false)) {
        var buffer: [4096]u8 = undefined;
        var reader = std.Io.File.stdin().readerStreaming(init.io, &buffer);
        const source = try reader.interface.allocRemaining(allocator, .unlimited);
        return executeAndPrint(init.io, &database, source) catch std.process.exit(1);
    }

    return repl(allocator, init, &database);
}

fn repl(allocator: std.mem.Allocator, init: std.process.Init, database: *LiveDatalog.Jatalog) !void {
    var line_editor = linenoise.Linenoise.init(allocator, init.io, init.environ_map);
    defer line_editor.deinit();

    while (try line_editor.linenoise("datalog> ")) |line| {
        defer allocator.free(line);
        const command = std.mem.trim(u8, line, &std.ascii.whitespace);
        if (command.len == 0) continue;
        if (std.mem.eql(u8, command, ".quit") or std.mem.eql(u8, command, ".exit")) break;
        if (std.mem.eql(u8, command, ".help")) {
            try writeHelp(init.io);
            continue;
        }

        try line_editor.history.add(line);
        // The error has already been reported, with where it happened.
        executeAndPrint(init.io, database, line) catch continue;
    }
}

/// Runs `source` and prints its result, or reports why it failed and returns
/// the error.
fn executeAndPrint(io: std.Io, database: *LiveDatalog.Jatalog, source: []const u8) !void {
    var diagnostic: LiveDatalog.Diagnostic = .{};
    var result = database.execute(source, &diagnostic) catch |err| {
        try writeError(io, err, source, diagnostic);
        return err;
    };
    defer result.deinit();

    var output_buffer: [4096]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(io, &output_buffer);
    const writer = &file_writer.interface;
    switch (result) {
        .none => {},
        .changed => |changed| try writer.writeAll(if (changed) "Yes.\n" else "No.\n"),
        .query => |query_result| {
            if (query_result.answers.items.len == 0) {
                try writer.writeAll("No.\n");
            } else if (query_result.answers.items[0].bindings.items.len == 0) {
                try writer.writeAll("Yes.\n");
            } else {
                for (query_result.answers.items) |answer| {
                    for (answer.bindings.items, 0..) |binding, index| {
                        if (index != 0) try writer.writeAll(", ");
                        try writer.print("{s}: ", .{binding.name});
                        try binding.value.write(writer);
                    }
                    try writer.writeByte('\n');
                }
            }
        },
    }
    try writer.flush();
}

fn writeHelp(io: std.Io) !void {
    var output_buffer: [256]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(io, &output_buffer);
    const writer = &file_writer.interface;
    try writeHelpTo(writer);
    try writer.flush();
}

fn writeHelpTo(writer: *std.Io.Writer) !void {
    try writer.writeAll(help_text);
}

fn writeError(io: std.Io, err: anyerror, source: []const u8, diagnostic: LiveDatalog.Diagnostic) !void {
    var output_buffer: [256]u8 = undefined;
    var file_writer = std.Io.File.stderr().writer(io, &output_buffer);
    const writer = &file_writer.interface;
    try writeErrorTo(writer, err, source, diagnostic);
    try writer.flush();
}

/// Names the error, says where it was, and — when it points into the source —
/// shows the line with a caret under the offending bytes.
fn writeErrorTo(
    writer: *std.Io.Writer,
    err: anyerror,
    source: []const u8,
    diagnostic: LiveDatalog.Diagnostic,
) !void {
    try writer.print("Error: {s}", .{@errorName(err)});
    if (diagnostic.span != null) try writer.print(" at {d}:{d}", .{ diagnostic.line, diagnostic.column });
    if (diagnostic.expected) |expected| try writer.print(", expected {s}", .{expected});
    try writer.writeByte('\n');
    const span = diagnostic.span orelse return;
    const line_start = span.start + 1 - diagnostic.column;
    const line_end = std.mem.findScalarPos(u8, source, line_start, '\n') orelse source.len;
    try writer.print("  {s}\n  ", .{source[line_start..line_end]});
    try writer.splatByteAll(' ', span.start - line_start);
    const width = @max(1, @min(span.end, line_end) -| span.start);
    try writer.splatByteAll('^', width);
    try writer.writeByte('\n');
}

test {
    _ = LiveDatalog;
}

test "REPL help prints the syntax reference" {
    var output: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer output.deinit();

    try writeHelpTo(&output.writer);

    try std.testing.expectEqualStrings(help_text, output.written());
    try std.testing.expect(std.mem.indexOf(u8, output.written(), "% Fact") != null);
    try std.testing.expect(std.mem.indexOf(u8, output.written(), "% Aggregate") != null);
}

test "errors show the offending line with a caret" {
    var output: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer output.deinit();
    var database: LiveDatalog.Jatalog = .init(std.testing.allocator);
    defer database.deinit();

    const source = "p(a).\nq(a b).";
    var diagnostic: LiveDatalog.Diagnostic = .{};
    const err = if (database.execute(source, &diagnostic)) |_| unreachable else |err| err;
    try writeErrorTo(&output.writer, err, source, diagnostic);
    try std.testing.expectEqualStrings(
        \\Error: InvalidSyntax at 2:5, expected ','
        \\  q(a b).
        \\      ^
        \\
    , output.written());

    output.clearRetainingCapacity();
    const unsafe = "p(a).\nq(X) :- p(Y).";
    diagnostic = .{};
    const rule_err = if (database.execute(unsafe, &diagnostic)) |_| unreachable else |rule_err| rule_err;
    try writeErrorTo(&output.writer, rule_err, unsafe, diagnostic);
    try std.testing.expectEqualStrings(
        \\Error: InvalidRule at 2:1
        \\  q(X) :- p(Y).
        \\  ^^^^^^^^^^^^^
        \\
    , output.written());

    output.clearRetainingCapacity();
    try writeErrorTo(&output.writer, error.OutOfMemory, "", .{});
    try std.testing.expectEqualStrings("Error: OutOfMemory\n", output.written());
}
