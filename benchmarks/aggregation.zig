const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const node_count = 25;
const iterations = 10;

const program =
    \\seed(k).
    \\reachable(X, Y) :- edge(X, Y).
    \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
    \\summary(S) :- seed(k), setof([X, Y], reachable(X, Y), S).
;

fn buildDatabase(allocator: std.mem.Allocator) !LiveDatalog.Jatalog {
    var database = LiveDatalog.Jatalog.init(allocator);
    errdefer database.deinit();
    var left_buffer: [16]u8 = undefined;
    var right_buffer: [16]u8 = undefined;
    for (0..node_count - 1) |index| {
        const left = try std.fmt.bufPrint(&left_buffer, "n{d}", .{index});
        const right = try std.fmt.bufPrint(&right_buffer, "n{d}", .{index + 1});
        try database.addFact("edge", &.{ LiveDatalog.input.atom(left), LiveDatalog.input.atom(right) });
    }
    var setup = try database.execute(program, null);
    setup.deinit();
    var warmup = try database.execute("summary(S)?", null);
    warmup.deinit();
    return database;
}

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    const input = LiveDatalog.input;

    var output_buffer: [512]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;

    // Workload 1: repeated queries with no updates between them.
    {
        var database = try buildDatabase(allocator);
        defer database.deinit();
        const start = std.Io.Clock.Timestamp.now(init.io, .awake);
        for (0..iterations) |_| {
            var result = try database.execute("summary(S)?", null);
            defer result.deinit();
            if (result.query.answers.items.len != 1) return error.UnexpectedResult;
        }
        const elapsed: u64 = @intCast(start.untilNow(init.io).raw.nanoseconds);
        try writer.print(
            "{d} queries over a {d}-node chain: {d} ns ({d} ns/query)\n",
            .{ iterations, node_count, elapsed, elapsed / iterations },
        );
    }

    // Workloads 2 and 3 add the same sequence of shortcut edges, one per
    // query, and differ only in how the closure is brought up to date:
    // `applyChanges` maintains it incrementally, while `addFact` marks the
    // dependent strata dirty so the following query recomputes them.
    var shortcut_from: [16]u8 = undefined;
    var shortcut_to: [16]u8 = undefined;
    {
        var database = try buildDatabase(allocator);
        defer database.deinit();
        // Pinned so the two workloads isolate maintain versus recompute;
        // the automatic policy chooses maintenance here on its own.
        database.setMaintenancePolicy(.incremental);
        const start = std.Io.Clock.Timestamp.now(init.io, .awake);
        for (0..iterations) |index| {
            const from = try std.fmt.bufPrint(&shortcut_from, "n{d}", .{index});
            const to = try std.fmt.bufPrint(&shortcut_to, "n{d}", .{index + 10});
            const shortcut: [2]LiveDatalog.input.Term = .{ input.atom(from), input.atom(to) };
            _ = try database.applyChanges(&.{input.fact("edge", &shortcut)}, &.{});
            var result = try database.execute("summary(S)?", null);
            defer result.deinit();
            if (result.query.answers.items.len != 1) return error.UnexpectedResult;
        }
        const elapsed: u64 = @intCast(start.untilNow(init.io).raw.nanoseconds);
        const stats = database.maintenanceStats();
        try writer.print(
            "{d} edge changes with incremental maintenance: {d} ns ({d} ns/change), " ++
                "{d} rebuild fallbacks\n",
            .{ iterations, elapsed, elapsed / iterations, stats.rebuild_fallbacks },
        );
    }

    {
        var database = try buildDatabase(allocator);
        defer database.deinit();
        const start = std.Io.Clock.Timestamp.now(init.io, .awake);
        for (0..iterations) |index| {
            const from = try std.fmt.bufPrint(&shortcut_from, "n{d}", .{index});
            const to = try std.fmt.bufPrint(&shortcut_to, "n{d}", .{index + 10});
            try database.addFact("edge", &.{ input.atom(from), input.atom(to) });
            var result = try database.execute("summary(S)?", null);
            defer result.deinit();
            if (result.query.answers.items.len != 1) return error.UnexpectedResult;
        }
        const elapsed: u64 = @intCast(start.untilNow(init.io).raw.nanoseconds);
        try writer.print(
            "{d} edge changes with recomputation: {d} ns ({d} ns/change)\n",
            .{ iterations, elapsed, elapsed / iterations },
        );
    }

    try writer.flush();
}
