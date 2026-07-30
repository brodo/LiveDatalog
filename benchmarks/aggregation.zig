const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const node_count = 25;
const iterations = 10;

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();

    var left_buffer: [16]u8 = undefined;
    var right_buffer: [16]u8 = undefined;
    for (0..node_count - 1) |index| {
        const left = try std.fmt.bufPrint(&left_buffer, "n{d}", .{index});
        const right = try std.fmt.bufPrint(&right_buffer, "n{d}", .{index + 1});
        try database.addFact("edge", &.{ left, right });
    }
    var setup = try database.execute(
        \\seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\summary(S) :- seed(k), setof([X, Y], reachable(X, Y), S).
    );
    setup.deinit();

    var warmup = try database.execute("summary(S)?");
    warmup.deinit();

    const start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..iterations) |_| {
        var result = try database.execute("summary(S)?");
        defer result.deinit();
        if (result.query.answers.items.len != 1) return error.UnexpectedResult;
    }
    const elapsed: u64 = @intCast(start.untilNow(init.io).raw.nanoseconds);

    var output_buffer: [256]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    try file_writer.interface.print(
        "{d} queries over a {d}-node chain: {d} ns ({d} ns/query)\n",
        .{ iterations, node_count, elapsed, elapsed / iterations },
    );
    try file_writer.interface.flush();
}
