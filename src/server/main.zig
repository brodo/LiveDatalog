//! LiveDatalogServer, the development server: loads the `.dl` files of a
//! directory, keeps the database in step with them as they change, and serves
//! it on two TCP ports: queries on one, the Language Server Protocol on the
//! other.
//!
//! The engine task owns the database, nightwatch's thread reports file
//! changes, and one accept task per listener takes clients. Changes and
//! requests reach the engine through one queue, so the database is only ever
//! touched by the engine.

const std = @import("std");
const Io = std.Io;
const Engine = @import("Engine.zig");
const Watcher = @import("Watcher.zig");
const Server = @import("Server.zig");
const LanguageListener = @import("LanguageListener.zig");

const log = std.log.scoped(.main);

const usage =
    \\Usage: LiveDatalogServer [--host ADDRESS] [--port PORT] [--lsp-port PORT] [DIRECTORY]
    \\
    \\Loads every *.dl file under DIRECTORY (default: the current directory),
    \\reloads them when they change, answers queries over TCP, and speaks the
    \\Language Server Protocol to editors over TCP.
    \\
    \\  --host ADDRESS    address to listen on (default: 127.0.0.1)
    \\  --port PORT       port for queries (default: 7070)
    \\  --lsp-port PORT   port for editors (default: 7071)
    \\
    \\Connect with e.g. `nc 127.0.0.1 7070` and send `.help`.
    \\
;

const Options = struct {
    host: []const u8 = "127.0.0.1",
    port: u16 = 7070,
    lsp_port: u16 = 7071,
    directory: []const u8 = ".",
};

fn parseOptions(args: []const [:0]const u8) !Options {
    var options: Options = .{};
    var directory: ?[]const u8 = null;
    var index: usize = 1;
    while (index < args.len) : (index += 1) {
        const arg = args[index];
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) return error.Help;
        const port: ?*u16 = if (std.mem.eql(u8, arg, "--port"))
            &options.port
        else if (std.mem.eql(u8, arg, "--lsp-port"))
            &options.lsp_port
        else
            null;
        if (port != null or std.mem.eql(u8, arg, "--host")) {
            index += 1;
            if (index == args.len) return error.MissingValue;
            if (port) |p| {
                p.* = std.fmt.parseInt(u16, args[index], 10) catch return error.InvalidPort;
            } else {
                options.host = args[index];
            }
            continue;
        }
        if (arg.len > 0 and arg[0] == '-') return error.UnknownOption;
        if (directory != null) return error.TooManyArguments;
        directory = arg;
    }
    if (directory) |d| options.directory = d;
    return options;
}

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    const options = parseOptions(args) catch |err| {
        std.debug.print("{s}", .{usage});
        if (err == error.Help) return;
        std.debug.print("\nerror: {s}\n", .{@errorName(err)});
        std.process.exit(2);
    };

    // All concurrency goes through one thread-pool based Io: the engine and
    // the TCP accept loop are `concurrent` tasks, each on its own thread.
    // Nightwatch runs its own watcher thread.
    var threaded: Io.Threaded = .init(gpa, .{ .environ = init.minimal.environ });
    defer threaded.deinit();
    const io = threaded.io();

    var root_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const root = root: {
        var dir = Io.Dir.cwd().openDir(io, options.directory, .{}) catch |err| {
            log.err("cannot open {s}: {s}", .{ options.directory, @errorName(err) });
            std.process.exit(1);
        };
        defer dir.close(io);
        break :root root_buffer[0..try dir.realPath(io, &root_buffer)];
    };

    var engine: Engine = undefined;
    engine.init(gpa, io, root);
    defer engine.deinit();

    // Watch before the first load, so no change can fall between the two.
    var watcher: Watcher = undefined;
    try watcher.start(&engine);
    defer watcher.deinit();
    engine.post(.reload);

    var engine_task = try io.concurrent(Engine.run, .{&engine});
    defer {
        engine.stop();
        engine_task.await(io);
    }

    const address = Io.net.IpAddress.parse(options.host, options.port) catch |err| {
        log.err("invalid address {s}: {s}", .{ options.host, @errorName(err) });
        std.process.exit(2);
    };
    var server = Server.listen(&engine, address) catch |err| {
        log.err("cannot listen on {f}: {s}", .{ address, @errorName(err) });
        std.process.exit(1);
    };
    defer server.deinit();

    var lsp_address = address;
    lsp_address.setPort(options.lsp_port);
    var language = LanguageListener.listen(&engine, lsp_address) catch |err| {
        log.err("cannot listen on {f}: {s}", .{ lsp_address, @errorName(err) });
        std.process.exit(1);
    };
    defer language.deinit();
    log.info("watching {s}; queries on {f}, editors on {f}", .{ root, address, lsp_address });

    var language_task = try io.concurrent(LanguageListener.run, .{&language});
    defer language_task.cancel(io) catch {};

    var server_task = try io.concurrent(Server.run, .{&server});
    server_task.await(io) catch |err| log.err("server stopped: {s}", .{@errorName(err)});
}

test parseOptions {
    const parsed = try parseOptions(&.{ "server", "--port", "9000", "data" });
    try std.testing.expectEqual(@as(u16, 9000), parsed.port);
    try std.testing.expectEqualStrings("data", parsed.directory);
    try std.testing.expectEqualStrings("127.0.0.1", parsed.host);
    try std.testing.expectEqual(@as(u16, 7071), parsed.lsp_port);
    const lsp = try parseOptions(&.{ "server", "--lsp-port", "9001", "--host", "::1" });
    try std.testing.expectEqual(@as(u16, 9001), lsp.lsp_port);
    try std.testing.expectEqual(@as(u16, 7070), lsp.port);
    try std.testing.expectEqualStrings("::1", lsp.host);
    try std.testing.expectError(error.InvalidPort, parseOptions(&.{ "server", "--port", "x" }));
    try std.testing.expectError(error.TooManyArguments, parseOptions(&.{ "server", "a", "b" }));
}

test {
    _ = Engine;
    _ = Watcher;
    _ = Server;
    _ = LanguageListener;
    _ = @import("LanguageSession.zig");
    _ = @import("Source.zig");
    _ = @import("protocol.zig");
}
