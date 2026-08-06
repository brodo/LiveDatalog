//! Update workload over a projected aggregate view.
//!
//! The view `v(X, S) :- p(X, Z), setof(Y, r(X, Y), S)` omits the outer
//! variable `Z` from its head, so every view tuple has as many derivations as
//! the key has `p` facts. Batches alternate between changing a group's member
//! set, which replaces the tuple and must carry its support across, and
//! changing one derivation, which must leave the visible tuple alone. Only
//! `applyChanges` is timed; the workload is verified afterwards.
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const key_count = 150;
const derivations_per_key = 20;
const members_per_key = 10;
const batches = 300;

pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();

    const input = LiveDatalog.input;
    var key_buffer: [16]u8 = undefined;
    var member_buffer: [16]u8 = undefined;
    for (0..key_count) |key_index| {
        const key = try std.fmt.bufPrint(&key_buffer, "k{d}", .{key_index});
        for (0..derivations_per_key) |derivation| {
            try database.addFact("p", &.{
                input.atom(key),
                input.integer(@intCast(derivation)),
            });
        }
        for (0..members_per_key) |member| {
            const name = try std.fmt.bufPrint(&member_buffer, "m{d}", .{member});
            try database.addFact("r", &.{ input.atom(key), input.atom(name) });
        }
    }
    var setup = try database.execute("v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).");
    setup.deinit();

    // Materialize before timing so the first batch is not charged for it.
    var warmup = try database.execute("v(X, S)?");
    if (warmup.query.answers.items.len != key_count) return error.UnexpectedResult;
    warmup.deinit();

    const start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..batches) |batch| {
        const key = try std.fmt.bufPrint(&key_buffer, "k{d}", .{batch % key_count});
        const member: [2]LiveDatalog.input.Term = .{ input.atom(key), input.atom("extra") };
        const derivation: [2]LiveDatalog.input.Term = .{
            input.atom(key),
            input.integer(derivations_per_key - 1),
        };
        // The first pass over the keys grows every group and drops one of
        // its derivations; the second pass restores both, so the workload
        // ends in its starting state.
        if (batch / key_count % 2 == 0) {
            _ = try database.applyChanges(
                &.{input.fact("r", &member)},
                &.{input.fact("p", &derivation)},
            );
        } else {
            _ = try database.applyChanges(
                &.{input.fact("p", &derivation)},
                &.{input.fact("r", &member)},
            );
        }
    }
    const elapsed: u64 = @intCast(start.untilNow(init.io).raw.nanoseconds);

    // Verify every group by key, because answer order is an implementation
    // detail that differs between rebuilt and incrementally kept closures.
    var verify = try database.execute("v(X, S)?");
    defer verify.deinit();
    if (verify.query.answers.items.len != key_count) return error.UnexpectedResult;
    for (verify.query.answers.items) |*answer| {
        const formatted = try (try answer.getValue("S")).formatAlloc(allocator);
        if (!std.mem.eql(u8, formatted, "[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]"))
            return error.UnexpectedAggregate;
    }

    var output_buffer: [256]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    try file_writer.interface.print(
        "{d} update batches over {d} projected groups: {d} ns ({d} ns/batch)\n",
        .{ batches, key_count, elapsed, elapsed / batches },
    );
    try file_writer.interface.flush();
}
