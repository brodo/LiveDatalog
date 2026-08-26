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
//! Four numbers per shape, and they measure different things on purpose.
//! *Planning* is `foldQuery`: inverting the view, eliminating the terms the
//! inversion invents, and lowering the result into the executable language. It
//! happens once per question. *Cached planning* is the same call once the plan
//! is in hand, which is what a repeated question actually costs. Then
//! execution, split in two: the *first* answer after the database changed,
//! which has to derive the reconstruction, and the *repeated* answer, which
//! finds it already derived and only solves goals. Loading the data is setup
//! on both sides and is timed on neither; what is compared is one call against
//! one call.
//!
//! The split is the measurement. A direct query reuses the materialized
//! closure, so after the first one it only solves goals. A folded plan's rules
//! live in the plan and not in the database, so `answerFolded` builds a copy
//! holding what the catalog admits, installs them there and derives the
//! reconstruction — and then keeps it, so the next call skips all of that.
//! What the first column costs is what folding costs on a database that
//! changes between every question; what the second costs is what it costs on
//! one that does not.
//!
//! Beside each time, candidate facts examined: the cost model's unit, the same
//! number on every machine, and the only one of these that says *why* a call
//! got cheaper. A reconstruction that is reused rather than made smaller shows
//! as a repeated call examining only the query's own candidates while the
//! first still examines the reconstruction's.
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
    /// Total nanoseconds over `iterations` calls of each kind.
    first: u64,
    repeated: u64,
    direct: u64,
    /// Candidate facts examined by one call of each kind.
    first_work: u64,
    repeated_work: u64,
    direct_work: u64,
    rows: usize,
};

pub fn main(init: std.process.Init) !void {
    var output_buffer: [1024]u8 = undefined;
    var file_writer = std.Io.File.stdout().writer(init.io, &output_buffer);
    const writer = &file_writer.interface;
    for (workloads) |workload| {
        const timings = try run(init, workload);
        try writer.print(
            "{s}: plan {d} ns, cached plan {d} ns, first run {d} ns/query " ++
                "({d} candidates), repeated run {d} ns/query ({d} candidates), " ++
                "direct run {d} ns/query ({d} candidates), {d} rows\n",
            .{
                workload.name,
                timings.planning,
                timings.cached_planning,
                timings.first / iterations,
                timings.first_work,
                timings.repeated / iterations,
                timings.repeated_work,
                timings.direct / iterations,
                timings.direct_work,
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

    // The first answer after a change. The fact goes under a name the plan
    // reads, so the reconstruction is stale and has to be derived again; it
    // holds a value the question does not ask for, so the answer does not
    // move and the two columns stay comparable. Making the change is not
    // timed — what is timed is one `answerFolded` that has to start from
    // nothing.
    var first: u64 = 0;
    var first_work: u64 = 0;
    for (0..iterations) |round| {
        try applyChange(&folded, workload, round);
        const work_before = folded.evaluationWork();
        const start = std.Io.Clock.Timestamp.now(init.io, .awake);
        var answers = try folded.answerFolded(plan);
        first += @intCast(start.untilNow(init.io).raw.nanoseconds);
        defer answers.deinit();
        first_work = folded.evaluationWork() - work_before;
        if (answers.answers.items.len != rows) return error.UnexpectedResult;
    }

    // And the same call with nothing changed in between, which finds the
    // reconstruction already derived.
    var repeated_warmup = try folded.answerFolded(plan);
    repeated_warmup.deinit();
    var repeated_work: u64 = 0;
    const repeated_start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..iterations) |_| {
        const work_before = folded.evaluationWork();
        var answers = try folded.answerFolded(plan);
        defer answers.deinit();
        repeated_work = folded.evaluationWork() - work_before;
        if (answers.answers.items.len != rows) return error.UnexpectedResult;
    }
    const repeated: u64 = @intCast(repeated_start.untilNow(init.io).raw.nanoseconds);

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

    var direct_work: u64 = 0;
    const direct_start = std.Io.Clock.Timestamp.now(init.io, .awake);
    for (0..iterations) |_| {
        const work_before = plain.evaluationWork();
        var answers = try plain.query(&question);
        defer answers.deinit();
        direct_work = plain.evaluationWork() - work_before;
        if (answers.answers.items.len != rows) return error.UnexpectedResult;
    }
    const direct: u64 = @intCast(direct_start.untilNow(init.io).raw.nanoseconds);

    return .{
        .planning = planning,
        .cached_planning = cached_planning,
        .first = first,
        .repeated = repeated,
        .direct = direct,
        .first_work = first_work,
        .repeated_work = repeated_work,
        .direct_work = direct_work,
        .rows = rows,
    };
}

/// One fact under the name the plan reads, put in and taken back out on
/// alternate rounds. It moves `Database.fact_generation` either way, and so
/// discards the kept reconstruction, without moving the answer: it holds a
/// value the question never asks for.
///
/// Alternating rather than adding a fresh fact each round is what keeps the
/// column measuring one thing. Twenty new keys is a 40% larger extension on
/// `grouped 50x40`, so a first-call time taken over twenty of them would be
/// reporting the workload growing under it.
fn applyChange(database: *LiveDatalog.Jatalog, workload: Workload, round: usize) !void {
    const terms = [_]input.Term{
        input.atom("kfresh"),
        switch (workload.shape) {
            .copied => input.atom("vfresh"),
            .grouped => input.list(&.{input.atom("vfresh")}),
        },
    };
    const name = switch (workload.shape) {
        .copied => "copied",
        .grouped => "grouped",
    };
    if (round % 2 == 0) {
        try database.addFact(name, &terms);
    } else if (!try database.retract(&.{input.relation(name, &terms)})) {
        return error.UnexpectedResult;
    }
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
