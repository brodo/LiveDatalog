//! What folding costs, split into planning and execution, against the same
//! question answered directly.
//!
//! The comparison is only meaningful where the two sides provably answer the
//! same thing, so the view is a *canonical aggregate view* of the relation the
//! query reads: Lemma 6.4.2 makes reading its lists back out return the
//! relation itself, and the workload checks that both sides return the same
//! number of rows before either timing is believed. Under a view that
//! remembers less the folded side would be faster by answering less, which is
//! not a speedup.
//!
//! Three numbers per shape, and they measure different things on purpose.
//! *Planning* is `foldQuery`: inverting the view, eliminating the terms the
//! inversion invents, and lowering the result into the executable language. It
//! happens once per question. *Cached planning* is the same call once the plan
//! is in hand, which is what a repeated question actually costs. *Execution*
//! is running the plan. Loading the data is setup on both sides and is timed
//! on neither; what is compared is one call against one call.
//!
//! The two calls are not doing the same amount of work, and the difference is
//! the point rather than a flaw in the measurement. A direct query reuses the
//! materialized closure, so after the first one it only solves goals. A folded
//! plan cannot: its rules live in the plan and not in the database, so
//! `answerFolded` builds a copy holding what the catalog admits, installs them
//! there and derives the reconstruction from nothing, every time. That is what
//! folding costs today, and it is a property of where the plan is kept rather
//! than of the method.
//!
//! No list functions appear here, so nothing on either side needs the source
//! database seeded with the lists a structural rule derives over. That
//! asymmetry is real where it applies and would make a timing meaningless; it
//! does not apply to these shapes.
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

const input = LiveDatalog.input;
const iterations = 20;

const Workload = struct {
    name: []const u8,
    /// Keys in `r`, and values under each.
    keys: usize,
    values: usize,
    /// Which canonical aggregate view of `r` the plan reads: the relation
    /// copied, or the relation grouped by its first column.
    shape: enum { copied, grouped },
};

const workloads = [_]Workload{
    .{ .name = "copied   200x5 ", .keys = 200, .values = 5, .shape = .copied },
    .{ .name = "grouped  200x5 ", .keys = 200, .values = 5, .shape = .grouped },
    .{ .name = "grouped  50x40 ", .keys = 50, .values = 40, .shape = .grouped },
};

const Timings = struct {
    planning: u64,
    cached_planning: u64,
    execution: u64,
    direct: u64,
    rows: usize,
};

pub fn main(init: std.process.Init) !void {
    var output_buffer: [1024]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;
    for (workloads) |workload| {
        const timings = try run(init, workload);
        try writer.print(
            "{s}: plan {d} ns, cached plan {d} ns, folded run {d} ns/query, " ++
                "direct run {d} ns/query, {d} rows\n",
            .{
                workload.name,
                timings.planning,
                timings.cached_planning,
                timings.execution / iterations,
                timings.direct / iterations,
                timings.rows,
            },
        );
    }
    try writer.flush();
}

fn run(init: std.process.Init, workload: Workload) !Timings {
    const allocator = init.arena.allocator();
    var folded = LiveDatalog.Jatalog.init(allocator);
    defer folded.deinit();
    try declareView(&folded, workload);
    try loadExtension(&folded, workload);

    // Planning: everything between the question and a runnable plan. Timed on
    // its own because it happens once and execution happens per call.
    const planning_start = std.Io.Clock.Timestamp.now(init.io, .awake);
    const plan = try folded.foldQuery(&question, &.{});
    const planning: u64 = @intCast(planning_start.untilNow(init.io).raw.nanoseconds);
    if (plan.guarantee != .maximally_contained) return error.UnexpectedGuarantee;
    var reconstructed = try folded.foldReconstructions(plan);
    defer reconstructed.deinit();
    // A canonical view, so the reconstruction is the relation and the two
    // sides are comparable. Without this the folded side could be quick by
    // being wrong.
    if (reconstructed.items.len != 1 or !reconstructed.items[0].exact)
        return error.UnexpectedReconstruction;

    const cached_start = std.Io.Clock.Timestamp.now(init.io, .awake);
    const again = try folded.foldQuery(&question, &.{});
    const cached_planning: u64 = @intCast(cached_start.untilNow(init.io).raw.nanoseconds);
    if (!again.reused) return error.PlanNotReused;

    var warmup = try folded.answerFolded(plan);
    const rows = warmup.answers.items.len;
    warmup.deinit();
    if (rows == 0) return error.UnexpectedResult;

    const execution_start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..iterations) |_| {
        var answers = try folded.answerFolded(plan);
        defer answers.deinit();
        if (answers.answers.items.len != rows) return error.UnexpectedResult;
    }
    const execution: u64 = @intCast(execution_start.untilNow(init.io).raw.nanoseconds);

    // The same question against a database that still has `r`. Loading is
    // setup on both sides and is not timed on either; what is compared is one
    // call against one call.
    var plain = LiveDatalog.Jatalog.init(allocator);
    defer plain.deinit();
    try loadRelation(&plain, workload);
    var plain_warmup = try plain.query(&question);
    const plain_rows = plain_warmup.answers.items.len;
    plain_warmup.deinit();
    if (plain_rows != rows) return error.UnexpectedResult;

    const direct_start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..iterations) |_| {
        var answers = try plain.query(&question);
        defer answers.deinit();
        if (answers.answers.items.len != rows) return error.UnexpectedResult;
    }
    const direct: u64 = @intCast(direct_start.untilNow(init.io).raw.nanoseconds);

    return .{
        .planning = planning,
        .cached_planning = cached_planning,
        .execution = execution,
        .direct = direct,
        .rows = rows,
    };
}

/// The question both sides answer: every key holding the marked value.
const question = [_]input.Goal{input.relation("r", &.{
    input.variable("K"),
    input.atom("v0"),
})};

fn declareView(database: *LiveDatalog.Jatalog, workload: Workload) !void {
    const x1 = input.variable("X1");
    const x2 = input.variable("X2");
    const y2 = input.variable("Y2");
    const s = input.variable("S");
    switch (workload.shape) {
        .copied => _ = try database.defineView(
            input.fact("copied", &.{ x1, x2 }),
            &.{input.relation("r", &.{ x1, x2 })},
            .materialized,
        ),
        .grouped => _ = try database.defineView(input.fact("grouped", &.{ x1, s }), &.{
            input.relation("r", &.{ x1, x2 }),
            input.setof(y2, &.{input.relation("r", &.{ x1, y2 })}, s),
        }, .materialized),
    }
}

/// The view's stored extension, which is all the folded side has.
fn loadExtension(database: *LiveDatalog.Jatalog, workload: Workload) !void {
    var key_buffer: [16]u8 = undefined;
    // A descriptor borrows its text, and a list holds every element at once,
    // so each value needs a buffer that outlives the loop that fills it.
    var value_buffers: [64][16]u8 = undefined;
    var values: [64]input.Term = undefined;
    for (0..workload.values) |index|
        values[index] = input.atom(try std.fmt.bufPrint(&value_buffers[index], "v{d}", .{index}));

    for (0..workload.keys) |key_index| {
        const key = try std.fmt.bufPrint(&key_buffer, "k{d}", .{key_index});
        switch (workload.shape) {
            .copied => for (values[0..workload.values]) |value| {
                try database.addFact("copied", &.{ input.atom(key), value });
            },
            .grouped => try database.addFact("grouped", &.{
                input.atom(key),
                input.list(values[0..workload.values]),
            }),
        }
    }
}

/// The relation itself, which is what the direct side reads.
fn loadRelation(database: *LiveDatalog.Jatalog, workload: Workload) !void {
    var key_buffer: [16]u8 = undefined;
    var value_buffer: [16]u8 = undefined;
    for (0..workload.keys) |key_index| {
        const key = try std.fmt.bufPrint(&key_buffer, "k{d}", .{key_index});
        for (0..workload.values) |value_index| {
            const value = try std.fmt.bufPrint(&value_buffer, "v{d}", .{value_index});
            try database.addFact("r", &.{ input.atom(key), input.atom(value) });
        }
    }
}
