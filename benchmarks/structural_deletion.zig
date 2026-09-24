//! Deletion through a seeded structural rule: incremental over-deletion
//! against the stratum rebuild it used to fall back to.
//!
//! The two shapes differ in how much of the relation one deletion invalidates,
//! which is the whole question. `prefix(H!T, N) :- prefix(T, M), allowed(H),
//! N = M + 1` derives one fact per suffix of a long list. Deleting `allowed`
//! for the list's outermost element invalidates exactly the longest prefix;
//! deleting the rule's base case invalidates every one of them. Over-deleted
//! and rederived counts are reported next to the time so a win can be
//! attributed to the algorithm rather than to the shape.
//!
//! Deletion and restoration are timed separately: only the deletion half runs
//! the code this phase added, and the restoration is reported so the cycle is
//! not mistaken for it.
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const depth = 120;
const batches = 20;

const program =
    \\prefix([], 0).
    \\prefix(H!T, N) :- prefix(T, M), allowed(H), N = M + 1.
    \\deep(N) :- prefix(L, N), N > 1.
;

/// Element names, kept alive for the whole run because `input.atom` borrows
/// the spelling it is given.
const Names = struct {
    storage: [depth][8]u8 = undefined,
    slices: [depth][]const u8 = undefined,

    fn init(self: *Names) !void {
        for (&self.storage, &self.slices, 0..) |*buffer, *slice, index| {
            slice.* = try std.fmt.bufPrint(buffer, "e{d}", .{index});
        }
    }
};

fn buildDatabase(allocator: std.mem.Allocator, names: *const Names) !LiveDatalog.Jatalog {
    var database = LiveDatalog.Jatalog.init(allocator);
    errdefer database.deinit();
    const input = LiveDatalog.input;

    var elements: [depth]LiveDatalog.input.Term = undefined;
    for (&elements, names.slices) |*element, name| element.* = input.atom(name);
    try database.addFact("chain", &.{input.list(&elements)});
    for (names.slices) |name| try database.addFact("allowed", &.{input.atom(name)});

    var setup = try database.execute(program, null);
    setup.deinit();
    try database.materialize();
    return database;
}

/// `leaf` deletes the support of the single longest prefix; `base` deletes the
/// recursion's base case, which invalidates every prefix at once.
const Shape = enum { leaf, base };

fn runShape(
    allocator: std.mem.Allocator,
    io: std.Io,
    writer: *std.Io.Writer,
    names: *const Names,
    shape: Shape,
    policy: LiveDatalog.MaintenancePolicy,
    label: []const u8,
) !void {
    var database = try buildDatabase(allocator, names);
    defer database.deinit();
    database.setMaintenancePolicy(policy);
    const input = LiveDatalog.input;

    const leaf_terms: [1]LiveDatalog.input.Term = .{input.atom(names.slices[0])};
    const base_terms: [2]LiveDatalog.input.Term = .{ input.list(&.{}), input.integer(0) };
    const victim: LiveDatalog.input.Relation = switch (shape) {
        .leaf => input.fact("allowed", &leaf_terms),
        .base => input.fact("prefix", &base_terms),
    };

    const before = database.maintenanceStats();
    var delete_ns: u64 = 0;
    var restore_ns: u64 = 0;
    for (0..batches) |_| {
        const deletion_start = std.Io.Clock.Timestamp.now(io, .awake);
        _ = try database.applyChanges(&.{}, &.{victim});
        // Query inside the timed region so a recompute decision cannot defer
        // its work past the measurement.
        var deleted = try database.execute("deep(N)?", null);
        deleted.deinit();
        delete_ns += @intCast(deletion_start.untilNow(io).raw.nanoseconds);

        const restore_start = std.Io.Clock.Timestamp.now(io, .awake);
        _ = try database.applyChanges(&.{victim}, &.{});
        var restored = try database.execute("deep(N)?", null);
        restored.deinit();
        restore_ns += @intCast(restore_start.untilNow(io).raw.nanoseconds);
    }
    const after = database.maintenanceStats();

    try writer.print(
        "{s}: {d} ns/delete, {d} ns/restore, {d} over-deleted, {d} rederived, " ++
            "{d} fallbacks, {d} expansions, {d} closure facts\n",
        .{
            label,
            delete_ns / batches,
            restore_ns / batches,
            (after.overdeleted_facts - before.overdeleted_facts) / batches,
            (after.rederived_facts - before.rederived_facts) / batches,
            after.rebuild_fallbacks - before.rebuild_fallbacks,
            after.stratum_expansions - before.stratum_expansions,
            after.closure_facts,
        },
    );
}

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    var names: Names = .{};
    try names.init();

    var output_buffer: [1024]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;

    const shapes = [_]struct { shape: Shape, label: []const u8 }{
        .{ .shape = .leaf, .label = "leaf" },
        .{ .shape = .base, .label = "base" },
    };
    const policies = [_]struct { policy: LiveDatalog.MaintenancePolicy, label: []const u8 }{
        .{ .policy = .incremental, .label = "incremental" },
        .{ .policy = .recompute, .label = "recompute  " },
        .{ .policy = .automatic, .label = "automatic  " },
    };
    var label_buffer: [64]u8 = undefined;
    for (shapes) |entry| {
        for (policies) |selected| {
            const label = try std.fmt.bufPrint(
                &label_buffer,
                "{s} {s}",
                .{ entry.label, selected.label },
            );
            try runShape(allocator, init.io, writer, &names, entry.shape, selected.policy, label);
        }
    }
    try writer.flush();
}
