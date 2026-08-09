//! Query workloads that separate the join orders a planner can choose between.
//!
//! Each workload is run twice on identical databases, once with the clause
//! order admission stored and once with the order the planner chooses on cost,
//! and both are checked to answer the same number of rows. The five shapes are
//! the ones a cost-based order is expected to behave differently on: a sparse
//! join where one side is tiny, a dense join where neither side is, a
//! recursive closure whose rules are re-evaluated every delta round, an
//! aggregate whose groups are almost all empty, and an aggregate with few
//! groups and many members each.
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const iterations = 20;

const Workload = struct {
    name: []const u8,
    /// Facts and rules, loaded before timing starts.
    setup: []const u8,
    /// The question asked `iterations` times, timed.
    question: []const u8,
    /// Rows it must answer, so a plan that loses answers cannot look fast.
    answers: usize,
    /// Facts generated before `setup` runs, by shape.
    data: Data,
};

const Data = union(enum) {
    none,
    /// `wide(0..n)` and `narrow(n-1)`: a join whose second side is one fact.
    sparse: usize,
    /// `left(i, i+1)` and `right(i, i+1)` over the same range: every left fact
    /// joins exactly one right fact, and neither side is selective alone.
    dense: usize,
    /// A chain `edge(n0, n1), edge(n1, n2), ...`.
    chain: usize,
    /// `key(0..n)` with members for only the first `populated` of them.
    groups: struct { keys: usize, populated: usize, members: usize },
};

const workloads = [_]Workload{
    .{
        .name = "sparse join    ",
        .data = .{ .sparse = 2000 },
        .setup = "",
        .question = "wide(X), narrow(X)?",
        .answers = 1,
    },
    .{
        .name = "dense join     ",
        .data = .{ .dense = 400 },
        .setup = "",
        .question = "left(X, Y), right(Y, Z)?",
        .answers = 399,
    },
    .{
        .name = "recursive close",
        .data = .{ .chain = 40 },
        .setup =
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        ,
        .question = "path(n0, X)?",
        .answers = 39,
    },
    .{
        .name = "empty aggregate",
        .data = .{ .groups = .{ .keys = 400, .populated = 4, .members = 4 } },
        .setup = "collected(X, S) :- key(X), setof(Y, member(X, Y), S).",
        .question = "collected(X, S)?",
        .answers = 400,
    },
    .{
        .name = "large groups   ",
        .data = .{ .groups = .{ .keys = 4, .populated = 4, .members = 200 } },
        .setup = "collected(X, S) :- key(X), setof(Y, member(X, Y), S).",
        .question = "collected(X, S)?",
        .answers = 4,
    },
};

pub fn main(init: std.process.Init) !void {
    var output_buffer: [512]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;
    for (workloads) |workload| {
        const stored = try run(init, workload, .source_order);
        const planned = try run(init, workload, .cost_based);
        try writer.print(
            "{s}: {d} ns/query stored order, {d} ns/query planned ({d}.{d:0>2}x)\n",
            .{
                workload.name,
                stored / iterations,
                planned / iterations,
                stored / @max(1, planned),
                (stored * 100 / @max(1, planned)) % 100,
            },
        );
    }
    try writer.flush();
}

fn run(init: std.process.Init, workload: Workload, policy: LiveDatalog.PlanPolicy) !u64 {
    const allocator = init.arena.allocator();
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();
    database.setPlanPolicy(policy);
    try load(&database, workload.data);
    if (workload.setup.len != 0) {
        var setup = try database.execute(workload.setup);
        setup.deinit();
    }

    // Materialize before timing so the closure build is not charged to the
    // first query; what is measured is solving the question, repeatedly.
    var warmup = try database.execute(workload.question);
    const observed = warmup.query.answers.items.len;
    warmup.deinit();
    if (observed != workload.answers) return error.UnexpectedResult;

    const start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..iterations) |_| {
        var result = try database.execute(workload.question);
        defer result.deinit();
        if (result.query.answers.items.len != workload.answers) return error.UnexpectedResult;
    }
    return @intCast(start.untilNow(init.io).raw.nanoseconds);
}

fn load(database: *LiveDatalog.Jatalog, data: Data) !void {
    const input = LiveDatalog.input;
    var name_buffer: [16]u8 = undefined;
    var other_buffer: [16]u8 = undefined;
    switch (data) {
        .none => {},
        .sparse => |count| {
            for (0..count) |index|
                try database.addFact("wide", &.{input.integer(@intCast(index))});
            try database.addFact("narrow", &.{input.integer(@intCast(count - 1))});
        },
        .dense => |count| {
            for (0..count) |index| {
                try database.addFact("left", &.{
                    input.integer(@intCast(index)),
                    input.integer(@intCast(index + 1)),
                });
                try database.addFact("right", &.{
                    input.integer(@intCast(index)),
                    input.integer(@intCast(index + 1)),
                });
            }
        },
        .chain => |count| {
            for (0..count - 1) |index| {
                const from = try std.fmt.bufPrint(&name_buffer, "n{d}", .{index});
                const to = try std.fmt.bufPrint(&other_buffer, "n{d}", .{index + 1});
                try database.addFact("edge", &.{ input.atom(from), input.atom(to) });
            }
        },
        .groups => |shape| {
            for (0..shape.keys) |index| {
                const key = try std.fmt.bufPrint(&name_buffer, "k{d}", .{index});
                try database.addFact("key", &.{input.atom(key)});
                if (index >= shape.populated) continue;
                for (0..shape.members) |member| {
                    const value = try std.fmt.bufPrint(&other_buffer, "m{d}", .{member});
                    try database.addFact("member", &.{ input.atom(key), input.atom(value) });
                }
            }
        },
    }
}
