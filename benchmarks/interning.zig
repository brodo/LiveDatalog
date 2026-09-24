//! What interning costs, in time and in comparisons.
//!
//! Interning is on the path of every fact loaded and every value derived, and
//! P4 measured it as a linear scan of the whole table. The comparison counts
//! are reported next to the times because they are the same number on every
//! machine: a change to how a table is searched shows up in them directly,
//! while a time says only what it was worth on the machine that measured it.
//!
//! The three workloads are the two P4 counted, with the fact load reached
//! twice. `addFact` is the embedder's path; the parser opens a statement
//! transaction per fact and so clones the database 2000 times over the same
//! 4000 interns. The structural workload is the program
//! `benchmark-structural-deletion` runs, where a 242-entry table is walked
//! 22,500 times.
//!
//! Memory comes from a general-purpose allocator rather than the arena the
//! other benchmarks use, because loading facts one statement at a time clones
//! the database once per statement and an arena would hold every one of those
//! copies until the process exited.
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const fact_count = 2000;
const list_depth = 120;
const repeats = 5;

/// Names kept alive for the whole run, because `input.atom` borrows the
/// spelling it is given.
const Names = struct {
    storage: [fact_count + 1][8]u8 = undefined,
    slices: [fact_count + 1][]const u8 = undefined,

    fn init(self: *Names) !void {
        for (&self.storage, &self.slices, 0..) |*buffer, *slice, index| {
            slice.* = try std.fmt.bufPrint(buffer, "n{d}", .{index});
        }
    }
};

const Measurement = struct {
    elapsed: u64,
    scalar_calls: usize,
    scalar_compared: usize,
    scalar_entries: usize,
    value_calls: usize,
    value_compared: usize,
    value_entries: usize,

    fn between(
        elapsed: u64,
        before: LiveDatalog.InternStats,
        after: LiveDatalog.InternStats,
    ) Measurement {
        return .{
            .elapsed = elapsed,
            .scalar_calls = after.scalars.calls - before.scalars.calls,
            .scalar_compared = after.scalars.compared - before.scalars.compared,
            .scalar_entries = after.scalar_entries,
            .value_calls = after.values.calls - before.values.calls,
            .value_compared = after.values.compared - before.values.compared,
            .value_entries = after.value_entries,
        };
    }
};

/// `edge(n0, n1) … edge(n1999, n2000)` through the embedder's fact API.
fn loadWithAddFact(allocator: std.mem.Allocator, io: std.Io, names: *const Names) !Measurement {
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();
    const before = database.internStats();
    const start = std.Io.Clock.Timestamp.now(io, .awake);
    for (0..fact_count) |index| {
        try database.addFact("edge", &.{
            LiveDatalog.input.atom(names.slices[index]),
            LiveDatalog.input.atom(names.slices[index + 1]),
        });
    }
    const elapsed: u64 = @intCast(start.untilNow(io).raw.nanoseconds);
    return .between(elapsed, before, database.internStats());
}

/// The same facts in one batch, which clones the database once rather than
/// once per fact. Here for contrast: it is the same 4000 interns over the
/// same growing table, with the per-statement copying taken away.
fn loadWithBatch(
    allocator: std.mem.Allocator,
    io: std.Io,
    insertions: []const LiveDatalog.input.Relation,
) !Measurement {
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();
    const before = database.internStats();
    const start = std.Io.Clock.Timestamp.now(io, .awake);
    _ = try database.applyChanges(insertions, &.{});
    const elapsed: u64 = @intCast(start.untilNow(io).raw.nanoseconds);
    return .between(elapsed, before, database.internStats());
}

/// The same facts written out as source, one statement each.
fn loadWithParser(allocator: std.mem.Allocator, io: std.Io, source: []const u8) !Measurement {
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();
    const before = database.internStats();
    const start = std.Io.Clock.Timestamp.now(io, .awake);
    var loaded = try database.execute(source, null);
    loaded.deinit();
    const elapsed: u64 = @intCast(start.untilNow(io).raw.nanoseconds);
    return .between(elapsed, before, database.internStats());
}

/// Materializing a structural recursion over one 120-element list: one
/// `prefix` fact per suffix, each of which interns a fresh list value and a
/// fresh integer.
fn materializeStructural(allocator: std.mem.Allocator, io: std.Io, names: *const Names) !Measurement {
    var database = LiveDatalog.Jatalog.init(allocator);
    defer database.deinit();
    const input = LiveDatalog.input;

    var elements: [list_depth]LiveDatalog.input.Term = undefined;
    for (&elements, names.slices[0..list_depth]) |*element, name| element.* = input.atom(name);
    try database.addFact("chain", &.{input.list(&elements)});
    for (names.slices[0..list_depth]) |name| try database.addFact("allowed", &.{input.atom(name)});
    var setup = try database.execute(
        \\prefix([], 0).
        \\prefix(H!T, N) :- prefix(T, M), allowed(H), N = M + 1.
        \\deep(N) :- prefix(L, N), N > 1.
    , null);
    setup.deinit();

    const before = database.internStats();
    const start = std.Io.Clock.Timestamp.now(io, .awake);
    try database.materialize();
    const elapsed: u64 = @intCast(start.untilNow(io).raw.nanoseconds);
    return .between(elapsed, before, database.internStats());
}

fn report(writer: *std.Io.Writer, label: []const u8, measured: Measurement) !void {
    try writer.print(
        "{s}: {d} ns, scalars {d} calls {d} compared over {d} entries, " ++
            "values {d} calls {d} compared over {d} entries\n",
        .{
            label,
            measured.elapsed,
            measured.scalar_calls,
            measured.scalar_compared,
            measured.scalar_entries,
            measured.value_calls,
            measured.value_compared,
            measured.value_entries,
        },
    );
}

pub fn main(init: std.process.Init) !void {
    const allocator = std.heap.smp_allocator;
    var names: Names = .{};
    try names.init();

    var source: std.ArrayList(u8) = .empty;
    defer source.deinit(allocator);
    for (0..fact_count) |index| {
        try source.print(allocator, "edge({s}, {s}).\n", .{ names.slices[index], names.slices[index + 1] });
    }

    var output_buffer: [1024]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;

    const terms = try allocator.alloc([2]LiveDatalog.input.Term, fact_count);
    defer allocator.free(terms);
    const insertions = try allocator.alloc(LiveDatalog.input.Relation, fact_count);
    defer allocator.free(insertions);
    for (terms, insertions, 0..) |*pair, *insertion, index| {
        pair.* = .{
            LiveDatalog.input.atom(names.slices[index]),
            LiveDatalog.input.atom(names.slices[index + 1]),
        };
        insertion.* = LiveDatalog.input.fact("edge", pair);
    }

    var add_fact: ?Measurement = null;
    var parsed: ?Measurement = null;
    var batched: ?Measurement = null;
    var structural: ?Measurement = null;
    for (0..repeats) |_| {
        add_fact = best(add_fact, try loadWithAddFact(allocator, init.io, &names));
        parsed = best(parsed, try loadWithParser(allocator, init.io, source.items));
        batched = best(batched, try loadWithBatch(allocator, init.io, insertions));
        structural = best(structural, try materializeStructural(allocator, init.io, &names));
    }

    try report(writer, "addFact, 2000 facts   ", add_fact.?);
    try report(writer, "parsed, 2000 facts    ", parsed.?);
    try report(writer, "batched, 2000 facts   ", batched.?);
    try report(writer, "materialize, 120 deep ", structural.?);
    try writer.flush();
}

/// Best of the repeats, so that a scheduling accident does not become the
/// measurement. The counts are identical across repeats: each runs on its own
/// database.
fn best(previous: ?Measurement, current: Measurement) Measurement {
    const earlier = previous orelse return current;
    return if (current.elapsed < earlier.elapsed) current else earlier;
}
