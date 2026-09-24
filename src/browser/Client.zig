//! The browser's side of the query listener's protocol: one connection,
//! requests written a line at a time, and responses read back whole. See
//! `src/server/protocol.zig` for the protocol itself.
//!
//! Nothing here draws anything, so it can be tested without a window.

const std = @import("std");
const Io = std.Io;

const Client = @This();

/// Longest line a response may hold.
pub const max_line = 1024 * 1024;

io: Io,
stream: Io.net.Stream,
reader: Io.net.Stream.Reader,
writer: Io.net.Stream.Writer,
read_buffer: []u8,
write_buffer: [1024]u8 = undefined,

/// Connects to the query listener at `address`. `self` must not move while
/// connected, since the reader and writer point into it.
pub fn connect(self: *Client, gpa: std.mem.Allocator, io: Io, address: Io.net.IpAddress) !void {
    const read_buffer = try gpa.alloc(u8, max_line);
    errdefer gpa.free(read_buffer);
    const stream = try address.connect(io, .{ .mode = .stream });
    self.* = .{
        .io = io,
        .stream = stream,
        .reader = undefined,
        .writer = undefined,
        .read_buffer = read_buffer,
    };
    self.reader = stream.reader(io, read_buffer);
    self.writer = stream.writer(io, &self.write_buffer);
}

pub fn close(self: *Client, gpa: std.mem.Allocator) void {
    self.stream.close(self.io);
    gpa.free(self.read_buffer);
    self.* = undefined;
}

/// Sends `line` and reads its response, allocated in `arena`.
pub fn request(self: *Client, arena: std.mem.Allocator, line: []const u8) !Response {
    try self.writer.interface.print("{s}\n", .{line});
    try self.writer.interface.flush();
    return readResponse(arena, &self.reader.interface);
}

/// Sends `.watch`, after which the connection only reads `nextGeneration`.
pub fn watch(self: *Client) !void {
    try self.writer.interface.writeAll(".watch\n");
    try self.writer.interface.flush();
}

/// The generation the next `generation <n>` line of a watched connection
/// reports.
pub fn nextGeneration(self: *Client) !u64 {
    const line = try takeLine(&self.reader.interface);
    const prefix = "generation ";
    if (!std.mem.startsWith(u8, line, prefix)) return error.UnexpectedResponse;
    return std.fmt.parseInt(u64, line[prefix.len..], 10) catch error.UnexpectedResponse;
}

// ---------------------------------------------------------------------------
// Responses

pub const Response = union(enum) {
    table: Table,
    text: []const []const u8,
    failure: Failure,

    /// The table, or `error.RequestFailed` for any other response.
    pub fn expectTable(self: Response) !Table {
        return switch (self) {
            .table => |table| table,
            else => error.RequestFailed,
        };
    }
};

pub const Table = struct {
    header: []const []const u8,
    /// Each row's cells, as the canonical text the server wrote.
    rows: []const []const []const u8,

    /// The index of the column headed `name`.
    pub fn column(self: Table, name: []const u8) ?usize {
        for (self.header, 0..) |heading, index| if (std.mem.eql(u8, heading, name)) return index;
        return null;
    }
};

pub const Failure = struct {
    name: []const u8,
    message: []const u8,
};

/// Reads one whole response. Everything returned is allocated in `arena`.
pub fn readResponse(arena: std.mem.Allocator, reader: *Io.Reader) !Response {
    const status = try arena.dupe(u8, try takeLine(reader));
    var words = std.mem.splitScalar(u8, status, ' ');
    const outcome = words.next().?;
    if (std.mem.eql(u8, outcome, "error")) {
        const name = words.next() orelse "";
        return .{ .failure = .{ .name = name, .message = words.rest() } };
    }
    if (!std.mem.eql(u8, outcome, "ok")) return error.UnexpectedResponse;
    const kind = words.next() orelse return error.UnexpectedResponse;
    const count = std.fmt.parseInt(usize, words.next() orelse "", 10) catch return error.UnexpectedResponse;

    if (std.mem.eql(u8, kind, "text")) {
        const lines = try arena.alloc([]const u8, count);
        for (lines) |*line| line.* = try arena.dupe(u8, try takeLine(reader));
        return .{ .text = lines };
    }
    if (!std.mem.eql(u8, kind, "table")) return error.UnexpectedResponse;
    const header = try splitCells(arena, try takeLine(reader));
    const rows = try arena.alloc([]const []const u8, count);
    for (rows) |*row| {
        row.* = try splitCells(arena, try takeLine(reader));
        // A header without columns has rows without cells.
        if (header.len == 0) row.* = &.{};
    }
    return .{ .table = .{ .header = header, .rows = rows } };
}

fn takeLine(reader: *Io.Reader) ![]const u8 {
    // A line may be empty, which `takeDelimiter` reports as a line, but the
    // end of the stream is null.
    return try reader.takeDelimiter('\n') orelse error.EndOfStream;
}

fn splitCells(arena: std.mem.Allocator, line: []const u8) ![]const []const u8 {
    if (line.len == 0) return &.{};
    const cells = try arena.alloc([]const u8, std.mem.count(u8, line, "\t") + 1);
    var parts = std.mem.splitScalar(u8, line, '\t');
    for (cells) |*cell| cell.* = try arena.dupe(u8, parts.next().?);
    return cells;
}

// ---------------------------------------------------------------------------
// Cells

/// A cell as the browser shows it.
pub const Cell = struct {
    kind: Kind,
    /// What to show: an atom without its quotes, anything else as written.
    text: []const u8,

    pub const Kind = enum { empty, atom, number, structure };
};

/// How to show a cell holding `canonical`, the server's text for a value.
/// Borrows from `canonical` unless a quoted atom has escapes to undo.
pub fn decodeCell(arena: std.mem.Allocator, canonical: []const u8) !Cell {
    if (canonical.len == 0) return .{ .kind = .empty, .text = "" };
    switch (canonical[0]) {
        '\'' => return .{ .kind = .atom, .text = try unquote(arena, canonical) },
        '[' => return .{ .kind = .structure, .text = canonical },
        '-', '0'...'9' => return .{ .kind = .number, .text = canonical },
        else => {},
    }
    // A pair that is not a proper list is written `cons(H, T)`.
    if (std.mem.startsWith(u8, canonical, "cons(")) return .{ .kind = .structure, .text = canonical };
    return .{ .kind = .atom, .text = canonical };
}

fn unquote(arena: std.mem.Allocator, quoted: []const u8) ![]const u8 {
    if (quoted.len < 2 or quoted[quoted.len - 1] != '\'') return quoted;
    const body = quoted[1 .. quoted.len - 1];
    if (std.mem.findScalar(u8, body, '\\') == null) return body;
    var text: std.ArrayList(u8) = .empty;
    var index: usize = 0;
    while (index < body.len) : (index += 1) {
        if (body[index] != '\\' or index + 1 == body.len) {
            try text.append(arena, body[index]);
            continue;
        }
        index += 1;
        try text.append(arena, switch (body[index]) {
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            else => |byte| byte,
        });
    }
    return text.items;
}

// ---------------------------------------------------------------------------
// Tests

const testing = std.testing;

test "reads tables, text and failures" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var reader: Io.Reader = .fixed(
        "ok table 2\nWho\tYear\nada\t1815\n'Grace Hopper'\t1906\n" ++
            "ok table 1\n\n\n" ++
            "ok text 2\none\n\n" ++
            "error InvalidSyntax at column 3, expected a term\n" ++
            "ok table 0\nname\n",
    );

    const table = (try readResponse(arena, &reader)).table;
    try testing.expectEqual(@as(usize, 2), table.header.len);
    try testing.expectEqual(@as(?usize, 1), table.column("Year"));
    try testing.expectEqualStrings("'Grace Hopper'", table.rows[1][0]);

    const ground = (try readResponse(arena, &reader)).table;
    try testing.expectEqual(@as(usize, 0), ground.header.len);
    try testing.expectEqual(@as(usize, 1), ground.rows.len);

    const text = (try readResponse(arena, &reader)).text;
    try testing.expectEqual(@as(usize, 2), text.len);
    try testing.expectEqualStrings("", text[1]);

    const failure = (try readResponse(arena, &reader)).failure;
    try testing.expectEqualStrings("InvalidSyntax", failure.name);
    try testing.expectEqualStrings("at column 3, expected a term", failure.message);

    const empty = (try readResponse(arena, &reader)).table;
    try testing.expectEqual(@as(usize, 0), empty.rows.len);
    try testing.expectError(error.EndOfStream, readResponse(arena, &reader));
}

test "cells show atoms without their quotes" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const quoted = try decodeCell(arena, "'two\\nlines \\'q\\' \\\\'");
    try testing.expectEqual(Cell.Kind.atom, quoted.kind);
    try testing.expectEqualStrings("two\nlines 'q' \\", quoted.text);
    try testing.expectEqual(Cell.Kind.atom, (try decodeCell(arena, "ada")).kind);
    try testing.expectEqual(Cell.Kind.number, (try decodeCell(arena, "-287")).kind);
    try testing.expectEqual(Cell.Kind.number, (try decodeCell(arena, "1.5e-7")).kind);
    try testing.expectEqual(Cell.Kind.structure, (try decodeCell(arena, "[a, 'b c']")).kind);
    try testing.expectEqual(Cell.Kind.structure, (try decodeCell(arena, "cons(a, b)")).kind);
    try testing.expectEqual(Cell.Kind.empty, (try decodeCell(arena, "")).kind);
}
