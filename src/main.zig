const std = @import("std");
const LiveDatalog = @import("LiveDatalog");
const Linenoise = @import("linenoise").Linenoise;

const help_text =
    \\LiveDatalog syntax reference
    \\
    \\% Fact
    \\predicate(atom, value).
    \\
    \\% Rule
    \\derived(X) :- source(X), condition(X).
    \\
    \\% Query
    \\derived(X)?
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
        return executeAndPrint(init.io, &database, source);
    }

    if (!(std.Io.File.stdin().isTty(init.io) catch false)) {
        var buffer: [4096]u8 = undefined;
        var reader = std.Io.File.stdin().readerStreaming(init.io, &buffer);
        const source = try reader.interface.allocRemaining(allocator, .unlimited);
        return executeAndPrint(init.io, &database, source);
    }

    return repl(allocator, init, &database);
}

fn repl(allocator: std.mem.Allocator, init: std.process.Init, database: *LiveDatalog.Jatalog) !void {
    var line_editor = Linenoise.init(allocator, init.io, init.environ_map);
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
        executeAndPrint(init.io, database, line) catch |err| try writeError(init.io, err);
    }
}

fn executeAndPrint(io: std.Io, database: *LiveDatalog.Jatalog, source: []const u8) !void {
    var result = try database.execute(source);
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

fn writeError(io: std.Io, err: anyerror) !void {
    var output_buffer: [256]u8 = undefined;
    var file_writer = std.Io.File.stderr().writer(io, &output_buffer);
    const writer = &file_writer.interface;
    try writer.print("Error: {s}\n", .{@errorName(err)});
    try writer.flush();
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
