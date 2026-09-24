//! The TCP front end. Accepts connections and relays each request line to
//! the engine, writing back the response. See `protocol.zig`.

const std = @import("std");
const Io = std.Io;
const Engine = @import("Engine.zig");

const Server = @This();
const log = std.log.scoped(.server);

/// Longest request line accepted.
const max_line = 64 * 1024;

engine: *Engine,
listener: Io.net.Server,

pub fn listen(engine: *Engine, address: Io.net.IpAddress) !Server {
    return .{
        .engine = engine,
        .listener = try address.listen(engine.io, .{ .reuse_address = true }),
    };
}

pub fn deinit(self: *Server) void {
    self.listener.deinit(self.engine.io);
    self.* = undefined;
}

/// The accept loop. Runs until canceled.
pub fn run(self: *Server) Io.Cancelable!void {
    const io = self.engine.io;
    // Each connection gets its own task so an idle client cannot block
    // others; all of them funnel into the single engine task.
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
        connections.concurrent(io, serve, .{ self, stream }) catch |err| {
            log.err("cannot serve connection: {s}", .{@errorName(err)});
            stream.close(io);
        };
    }
}

fn serve(self: *Server, stream: Io.net.Stream) Io.Cancelable!void {
    const io = self.engine.io;
    defer stream.close(io);

    const read_buffer = self.engine.gpa.alloc(u8, max_line) catch return;
    defer self.engine.gpa.free(read_buffer);
    var write_buffer: [4096]u8 = undefined;
    var reader = stream.reader(io, read_buffer);
    var writer = stream.writer(io, &write_buffer);

    while (true) {
        const line = reader.interface.takeDelimiter('\n') catch |err| switch (err) {
            error.StreamTooLong => {
                writer.interface.writeAll("Error: request too long\n\n") catch return;
                writer.interface.flush() catch return;
                return;
            },
            error.ReadFailed => return,
        } orelse return;

        const request_line = std.mem.trim(u8, line, &std.ascii.whitespace);
        if (std.mem.eql(u8, request_line, ".quit") or std.mem.eql(u8, request_line, ".exit")) return;
        if (std.mem.eql(u8, request_line, ".watch")) return self.watch(&writer.interface);

        var request: Engine.Request = .{
            .line = request_line,
            .response = .init(self.engine.gpa),
        };
        defer request.response.deinit();
        self.engine.post(.{ .request = &request });
        // Uncancelable: the engine holds a pointer to `request` until done.
        request.done.waitUncancelable(io);

        writer.interface.writeAll(request.response.written()) catch return;
        writer.interface.flush() catch return;
    }
}

/// Streams `generation <n>` to the client: the current generation now, then
/// one line after every change, until the client hangs up or the server
/// stops. The connection takes no more requests.
fn watch(self: *Server, writer: *Io.Writer) Io.Cancelable!void {
    const io = self.engine.io;
    var buffer: [1]u64 = undefined;
    var changes: Io.Queue(u64) = .init(&buffer);

    const Subscribe = struct {
        const Self = @This();
        call: Engine.Call = .{ .run = perform },
        changes: *Io.Queue(u64),
        generation: ?u64 = null,

        fn perform(call: *Engine.Call, engine: *Engine) void {
            const s: *Self = @fieldParentPtr("call", call);
            engine.subscribe(s.changes) catch return;
            s.generation = engine.generation;
        }
    };
    var subscription: Subscribe = .{ .changes = &changes };
    if (!subscription.call.perform(self.engine)) return;
    const first = subscription.generation orelse {
        writer.writeAll("error OutOfMemory\n") catch return;
        writer.flush() catch return;
        return;
    };
    defer {
        const Unsubscribe = struct {
            const Self = @This();
            call: Engine.Call = .{ .run = perform },
            changes: *Io.Queue(u64),

            fn perform(call: *Engine.Call, engine: *Engine) void {
                const u: *Self = @fieldParentPtr("call", call);
                engine.unsubscribe(u.changes);
            }
        };
        var unsubscription: Unsubscribe = .{ .changes = &changes };
        _ = unsubscription.call.perform(self.engine);
    }

    var generation = first;
    while (true) {
        writer.print("generation {d}\n", .{generation}) catch return;
        writer.flush() catch return;
        generation = changes.getOne(io) catch |err| switch (err) {
            error.Closed => return,
            error.Canceled => |e| return e,
        };
    }
}
