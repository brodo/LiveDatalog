//! The language listener: accepts editors' connections and speaks the
//! Language Server Protocol to each through a `LanguageSession`. See
//! docs/adr/0006-language-listener-in-process.md for why it runs here.

const std = @import("std");
const Io = std.Io;
const lsp = @import("lsp");
const Engine = @import("Engine.zig");
const LanguageSession = @import("LanguageSession.zig");

const LanguageListener = @This();
const log = std.log.scoped(.language);

engine: *Engine,
listener: Io.net.Server,

pub fn listen(engine: *Engine, address: Io.net.IpAddress) !LanguageListener {
    return .{
        .engine = engine,
        .listener = try address.listen(engine.io, .{ .reuse_address = true }),
    };
}

pub fn deinit(self: *LanguageListener) void {
    self.listener.deinit(self.engine.io);
    self.* = undefined;
}

/// The accept loop. Runs until canceled.
pub fn run(self: *LanguageListener) Io.Cancelable!void {
    const io = self.engine.io;
    var connections: Io.Group = .init;
    defer connections.cancel(io);

    while (true) {
        const stream = self.listener.accept(io) catch |err| switch (err) {
            error.Canceled => return error.Canceled,
            error.SocketNotListening => return,
            else => {
                log.err("accept failed: {s}", .{@errorName(err)});
                continue;
            },
        };
        connections.concurrent(io, serve, .{ self.engine, stream }) catch |err| {
            log.err("cannot serve editor: {s}", .{@errorName(err)});
            stream.close(io);
        };
    }
}

/// Speaks the protocol over `stream` until the editor exits or hangs up.
pub fn serve(engine: *Engine, stream: Io.net.Stream) Io.Cancelable!void {
    const io = engine.io;
    defer stream.close(io);

    var read_buffer: [4096]u8 = undefined;
    var write_buffer: [4096]u8 = undefined;
    var reader = stream.reader(io, &read_buffer);
    var writer = stream.writer(io, &write_buffer);
    var transport: StreamTransport = .init(&reader.interface, &writer.interface);

    var session: LanguageSession = undefined;
    session.init(engine, &transport.transport);
    defer session.deinit();
    if (!session.subscribe()) return;
    defer session.unsubscribe();

    var watcher = io.concurrent(LanguageSession.watch, .{&session}) catch |err| {
        log.err("cannot watch for changes: {s}", .{@errorName(err)});
        return;
    };
    defer {
        session.changes.close(io);
        watcher.cancel(io) catch {};
    }

    lsp.basic_server.run(io, engine.gpa, &transport.transport, &session, log.err) catch |err| switch (err) {
        error.Canceled => |e| return e,
        error.EndOfStream => {},
        else => log.err("editor connection failed: {s}", .{@errorName(err)}),
    };
}

/// An LSP transport over a reader and a writer, such as a TCP stream's.
/// Writes are serialized, since a session's handlers and its watcher both
/// write. A reader or writer that fails is taken for a closed connection.
pub const StreamTransport = struct {
    transport: lsp.Transport,
    reader: *Io.Reader,
    writer: *Io.Writer,
    write_mutex: Io.Mutex = .init,

    pub fn init(reader: *Io.Reader, writer: *Io.Writer) StreamTransport {
        return .{
            .transport = .{ .vtable = &.{
                .readJsonMessage = readJsonMessage,
                .writeJsonMessage = writeJsonMessage,
            } },
            .reader = reader,
            .writer = writer,
        };
    }

    // ziglint-ignore: Z023
    fn readJsonMessage(transport: *lsp.Transport, _: Io, allocator: std.mem.Allocator) lsp.Transport.ReadError![]u8 {
        const self: *StreamTransport = @fieldParentPtr("transport", transport);
        return lsp.readJsonMessage(self.reader, allocator) catch |err| switch (err) {
            error.ReadFailed => error.EndOfStream,
            else => |e| e,
        };
    }

    // ziglint-ignore: Z023
    fn writeJsonMessage(transport: *lsp.Transport, io: Io, json_message: []const u8) lsp.Transport.WriteError!void {
        const self: *StreamTransport = @fieldParentPtr("transport", transport);
        try self.write_mutex.lock(io);
        defer self.write_mutex.unlock(io);
        lsp.writeJsonMessage(self.writer, json_message) catch |err| switch (err) {
            error.WriteFailed => return error.BrokenPipe,
        };
    }
};

// ---------------------------------------------------------------------------
// Tests

const testing = std.testing;

/// The editor's end of a connection.
const TestClient = struct {
    reader: Io.net.Stream.Reader,
    writer: Io.net.Stream.Writer,
    arena: std.heap.ArenaAllocator,

    fn send(self: *TestClient, json: []const u8) !void {
        try lsp.writeJsonMessage(&self.writer.interface, json);
    }

    /// Reads messages until one contains every one of `needles`.
    fn expect(self: *TestClient, needles: []const []const u8) ![]const u8 {
        next: while (true) {
            const message = try lsp.readJsonMessage(&self.reader.interface, self.arena.allocator());
            for (needles) |needle| if (std.mem.find(u8, message, needle) == null) continue :next;
            return message;
        }
    }
};

test "an editor over TCP is told of load errors as they come and go" {
    const io = testing.io;
    var tmp = testing.tmpDir(.{ .iterate = true });
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "a.dl", .data = "p(a). p(b).\n" });
    try tmp.dir.writeFile(io, .{ .sub_path = "b.dl", .data = "q(\n" });
    var root_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const root = root_buffer[0..try tmp.dir.realPath(io, &root_buffer)];

    var engine: Engine = undefined;
    engine.init(testing.allocator, io, root);
    defer engine.deinit();
    engine.post(.reload);
    var engine_task = try io.concurrent(Engine.run, .{&engine});
    defer {
        engine.stop();
        engine_task.await(io);
    }

    var listener = try listen(&engine, try .parse("127.0.0.1", 0));
    defer listener.deinit();
    var listener_task = try io.concurrent(run, .{&listener});
    defer listener_task.cancel(io) catch {};

    const stream = try listener.listener.socket.address.connect(io, .{ .mode = .stream });
    defer stream.close(io);
    var read_buffer: [4096]u8 = undefined;
    var write_buffer: [4096]u8 = undefined;
    var client: TestClient = .{
        .reader = stream.reader(io, &read_buffer),
        .writer = stream.writer(io, &write_buffer),
        .arena = .init(testing.allocator),
    };
    defer client.arena.deinit();

    try client.send(
        \\{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}
    );
    _ = try client.expect(&.{ "\"id\":1", "\"hoverProvider\":true", "\"definitionProvider\":true" });
    try client.send(
        \\{"jsonrpc":"2.0","method":"initialized","params":{}}
    );
    _ = try client.expect(&.{ "publishDiagnostics", "b.dl", "InvalidSyntax, expected a term" });

    const arena = client.arena.allocator();
    const a_uri = try LanguageSession.pathToUri(arena, try std.fs.path.join(arena, &.{ root, "a.dl" }));
    try client.send(try std.fmt.allocPrint(arena,
        \\{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":
    ++
        \\{{"uri":"{s}","languageId":"datalog","version":1,"text":"p(a). p(b).\n"}}}}}}
    , .{a_uri}));
    try client.send(try std.fmt.allocPrint(arena,
        \\{{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":
    ++
        \\{{"textDocument":{{"uri":"{s}"}},"position":{{"line":0,"character":0}}}}}}
    , .{a_uri}));
    _ = try client.expect(&.{ "\"id\":2", "**p**/1 — base\\n\\n2 base facts" });

    // Fixing the file on disk clears its diagnostics.
    try tmp.dir.writeFile(io, .{ .sub_path = "b.dl", .data = "q(a).\n" });
    engine.post(.{ .changed = try std.fs.path.join(testing.allocator, &.{ root, "b.dl" }) });
    _ = try client.expect(&.{ "publishDiagnostics", "b.dl\",\"diagnostics\":[]" });

    try client.send(
        \\{"jsonrpc":"2.0","id":3,"method":"shutdown"}
    );
    _ = try client.expect(&.{"\"id\":3"});
    try client.send(
        \\{"jsonrpc":"2.0","method":"exit"}
    );
    // The server hangs up.
    try testing.expectError(error.EndOfStream, client.expect(&.{"never"}));
}
