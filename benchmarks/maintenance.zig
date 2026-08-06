//! Insert, delete, and mixed update workloads with maintenance reporting.
//!
//! Each phase reports elapsed time per batch together with the maintenance
//! counters the engine exposes: derived facts added by insertion deltas,
//! facts removed by delete-and-rederive, aggregate groups recomputed, and
//! updates that fell back to a stratum rebuild. Memory is measured with a
//! counting allocator wrapped around the backing allocator.
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const node_count = 40;
const group_count = 40;
const members_per_group = 8;
const batches = 40;

/// Tracks outstanding and peak bytes so each phase can report memory.
const CountingAllocator = struct {
    child: std.mem.Allocator,
    current: usize = 0,
    peak: usize = 0,

    fn allocator(self: *CountingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn note(self: *CountingAllocator, added: usize, removed: usize) void {
        self.current = self.current + added - removed;
        if (self.current > self.peak) self.peak = self.current;
    }

    fn alloc(context: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        const result = self.child.rawAlloc(len, alignment, ret_addr);
        if (result != null) self.note(len, 0);
        return result;
    }

    fn resize(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        ret_addr: usize,
    ) bool {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        if (!self.child.rawResize(memory, alignment, new_len, ret_addr)) return false;
        self.note(new_len, memory.len);
        return true;
    }

    fn remap(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        ret_addr: usize,
    ) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        const result = self.child.rawRemap(memory, alignment, new_len, ret_addr);
        if (result != null) self.note(new_len, memory.len);
        return result;
    }

    fn free(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        self.child.rawFree(memory, alignment, ret_addr);
        self.note(0, memory.len);
    }
};

const program =
    \\path(X, Y) :- edge(X, Y).
    \\path(X, Z) :- edge(X, Y), path(Y, Z).
    \\collected(G, S) :- team(G), setof(M, member(G, M), S).
    \\length([], 0).
    \\length(H!T, N) :- length(T, M), N = M + 1.
    \\size(G, N) :- collected(G, S), length(S, N).
    \\quiet(G) :- team(G), not banned(G).
;

fn buildDatabase(allocator: std.mem.Allocator) !LiveDatalog.Jatalog {
    var database = LiveDatalog.Jatalog.init(allocator);
    errdefer database.deinit();
    const input = LiveDatalog.input;
    var left: [16]u8 = undefined;
    var right: [16]u8 = undefined;
    for (0..node_count - 1) |index| {
        const from = try std.fmt.bufPrint(&left, "n{d}", .{index});
        const to = try std.fmt.bufPrint(&right, "n{d}", .{index + 1});
        try database.addFact("edge", &.{ input.atom(from), input.atom(to) });
    }
    for (0..group_count) |group| {
        const name = try std.fmt.bufPrint(&left, "g{d}", .{group});
        try database.addFact("team", &.{input.atom(name)});
        for (0..members_per_group) |member| {
            const member_name = try std.fmt.bufPrint(&right, "m{d}", .{member});
            try database.addFact("member", &.{ input.atom(name), input.atom(member_name) });
        }
    }
    var setup = try database.execute(program);
    setup.deinit();
    try database.materialize();
    return database;
}

/// `negated` deliberately updates a predicate read under negation, which is
/// the documented category that cannot be maintained incrementally and
/// falls back to a stratum rebuild.
const Phase = enum { insert, delete, mixed, negated };

fn runPhase(
    io: std.Io,
    counting: *CountingAllocator,
    writer: *std.Io.Writer,
    phase: Phase,
    label: []const u8,
) !void {
    var database = try buildDatabase(counting.allocator());
    defer database.deinit();
    const input = LiveDatalog.input;
    const before = database.maintenanceStats();
    const memory_before = counting.current;
    counting.peak = counting.current;

    const start = std.Io.Clock.Timestamp.now(io, .awake);
    var group_name: [16]u8 = undefined;
    var member_name: [16]u8 = undefined;
    var node_name: [16]u8 = undefined;
    for (0..batches) |batch| {
        const group = try std.fmt.bufPrint(&group_name, "g{d}", .{batch % group_count});
        const member = try std.fmt.bufPrint(&member_name, "m{d}", .{batch % members_per_group});
        const node = try std.fmt.bufPrint(&node_name, "n{d}", .{batch % node_count});
        const member_fact: [2]LiveDatalog.input.Term = .{ input.atom(group), input.atom("extra") };
        const existing_member: [2]LiveDatalog.input.Term = .{ input.atom(group), input.atom(member) };
        const edge_fact: [2]LiveDatalog.input.Term = .{ input.atom(node), input.atom("sink") };
        switch (phase) {
            .insert => _ = try database.applyChanges(&.{
                input.fact("member", &member_fact),
                input.fact("edge", &edge_fact),
            }, &.{}),
            .delete => _ = try database.applyChanges(&.{}, &.{
                input.fact("member", &existing_member),
            }),
            .mixed => _ = try database.applyChanges(
                &.{input.fact("member", &member_fact)},
                &.{input.fact("member", &existing_member)},
            ),
            .negated => {
                const banned: [1]LiveDatalog.input.Term = .{input.atom(group)};
                if (batch % 2 == 0) {
                    _ = try database.applyChanges(&.{input.fact("banned", &banned)}, &.{});
                } else {
                    _ = try database.applyChanges(&.{}, &.{input.fact("banned", &banned)});
                }
            },
        }
    }
    const elapsed: u64 = @intCast(start.untilNow(io).raw.nanoseconds);
    const after = database.maintenanceStats();

    try writer.print(
        "{s}: {d} ns/batch, +{d} derived, -{d} removed, {d} groups, {d} rebuild fallbacks, " ++
            "{d} closure facts, {d} KiB live, {d} KiB peak\n",
        .{
            label,
            elapsed / batches,
            after.propagated_facts - before.propagated_facts,
            after.removed_facts - before.removed_facts,
            after.maintained_groups - before.maintained_groups,
            after.rebuild_fallbacks - before.rebuild_fallbacks,
            after.closure_facts,
            (counting.current - memory_before) / 1024,
            (counting.peak - memory_before) / 1024,
        },
    );
}

pub fn main(init: std.process.Init) !void {
    var counting: CountingAllocator = .{ .child = init.arena.allocator() };

    var output_buffer: [1024]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;

    try runPhase(init.io, &counting, writer, .insert, "insert-only     ");
    try runPhase(init.io, &counting, writer, .delete, "delete-only     ");
    try runPhase(init.io, &counting, writer, .mixed, "mixed           ");
    try runPhase(init.io, &counting, writer, .negated, "negation rebuild");
    try writer.flush();
}
