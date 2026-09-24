//! Assertions shared by the test suites of several modules.
//!
//! These take a `Database` rather than the public `Jatalog`, and reach no
//! higher than materialization, so a module's tests can use them without
//! importing anything above that module.
//!
//! Most check a database against a reference computed a different way, which
//! is the property the whole engine rests on: maintaining the closure
//! incrementally, rebuilding it from a dirty stratum and expanding it naively
//! must all produce the same database. The other property every module asserts
//! is that a failed allocation leaves nothing behind, which
//! `expectEveryAllocationFailureReleased` sweeps for.
//!
//! `defineRule` is the one helper that builds rather than asserts: it is how a
//! module below the program runner installs a rule without the parser.

const builtin = @import("builtin");
const std = @import("std");
const compile = @import("compile.zig");
const database = @import("database.zig");
const input = @import("input.zig");
const materialization = @import("materialization.zig");
const results = @import("results.zig");
const validation = @import("validation.zig");

/// Runs `scenario` once per allocation site with that allocation forced to
/// fail, which is the coverage `std.testing.checkAllAllocationFailures` gives,
/// but spreads the runs across the machine's cores.
///
/// The scenarios are quadratic — a scenario with a thousand allocation sites
/// is a thousand full runs — so they dominate the suite's wall clock, and the
/// runs share nothing: each gets its own database built from its own
/// allocator. The only reason they were serial is that the standard helper
/// loops.
pub fn expectEveryAllocationFailureReleased(
    comptime scenario: fn (std.mem.Allocator) anyerror!void,
) !void {
    // One unrestricted run says how many allocation sites there are to visit.
    const site_count = count: {
        var counting: std.testing.FailingAllocator = .init(std.testing.allocator, .{});
        try scenario(counting.allocator());
        break :count counting.alloc_index;
    };

    var sites: FailureSites = .{ .count = site_count };
    const shard = struct {
        /// Drains fail indices until they run out, on a private allocator so
        /// the shards never contend on allocator bookkeeping, and into a
        /// private failure slot so they never contend on reporting either.
        fn run(remaining: *FailureSites, failure: *?anyerror) void {
            var backing: std.heap.DebugAllocator(.{
                // A shard owns its allocator, so the thread-safety mutex would
                // be pure cost. Dropping the stack traces is what makes the
                // sweep cheap: `std.testing.allocator` captures ten frames per
                // allocation, and a sweep makes a whole run's worth of
                // allocations per allocation site. The trace that actually
                // names a leak here is the one `FailingAllocator` keeps for
                // the allocation it induced to fail.
                .thread_safe = false,
                .stack_trace_frames = 0,
            }) = .init;
            defer if (backing.deinit() == .leak and failure.* == null) {
                failure.* = error.MemoryLeakDetected;
            };
            while (remaining.claim()) |fail_index| {
                expectFailureReleased(
                    scenario,
                    backing.allocator(),
                    fail_index,
                    remaining.count,
                ) catch |err| {
                    failure.* = err;
                    return remaining.stop();
                };
            }
        }
    }.run;

    // Slot zero belongs to the calling thread, which sweeps alongside the
    // helpers rather than waiting on them.
    const shard_count = shardCount(site_count);
    const failures = try std.testing.allocator.alloc(?anyerror, shard_count);
    defer std.testing.allocator.free(failures);
    @memset(failures, null);
    const helpers = try std.testing.allocator.alloc(std.Thread, shard_count - 1);
    defer std.testing.allocator.free(helpers);

    var spawned: usize = 0;
    for (helpers, failures[1..]) |*helper, *failure| {
        // A thread we cannot spawn costs throughput, not coverage: whoever is
        // left keeps claiming until every index is done.
        helper.* = std.Thread.spawn(.{}, shard, .{ &sites, failure }) catch break;
        spawned += 1;
    }
    shard(&sites, &failures[0]);
    for (helpers[0..spawned]) |helper| helper.join();

    for (failures) |failure| if (failure) |err| return err;
}

/// The allocation sites of one scenario, handed out to the shards running it.
const FailureSites = struct {
    next: std.atomic.Value(usize) = .init(0),
    stopped: std.atomic.Value(bool) = .init(false),
    count: usize,

    /// Takes the next fail index, or null once they run out. A shard that has
    /// failed stops the sweep: the first leak is the one to fix, and letting
    /// the rest of the indices run only buries its report.
    fn claim(sites: *FailureSites) ?usize {
        if (sites.stopped.load(.acquire)) return null;
        const index = sites.next.fetchAdd(1, .monotonic);
        return if (index < sites.count) index else null;
    }

    fn stop(sites: *FailureSites) void {
        sites.stopped.store(true, .release);
    }
};

/// Runs `scenario` with allocation `fail_index` denied and holds it to what
/// `std.testing.checkAllAllocationFailures` demands of a single run: report
/// the induced failure, and give back everything allocated before it.
fn expectFailureReleased(
    comptime scenario: fn (std.mem.Allocator) anyerror!void,
    backing: std.mem.Allocator,
    fail_index: usize,
    site_count: usize,
) !void {
    var failing: std.testing.FailingAllocator = .init(backing, .{ .fail_index = fail_index });
    if (scenario(failing.allocator())) |_| {
        return if (failing.has_induced_failure)
            error.SwallowedOutOfMemoryError
        else
            error.NondeterministicMemoryUsage;
    } else |err| switch (err) {
        error.OutOfMemory => if (failing.allocated_bytes != failing.freed_bytes) {
            std.debug.print(
                "\nfail_index: {d}/{d}\nallocated bytes: {d}\nfreed bytes: {d}\n" ++
                    "allocations: {d}\ndeallocations: {d}\nallocation that was made to fail: {f}",
                .{
                    fail_index,
                    site_count,
                    failing.allocated_bytes,
                    failing.freed_bytes,
                    failing.allocations,
                    failing.deallocations,
                    std.debug.FormatStackTrace{ .stack_trace = failing.getStackTrace() },
                },
            );
            return error.MemoryLeakDetected;
        },
        else => |other| return other,
    }
}

/// How many shards to sweep a scenario's allocation sites with. More shards
/// than sites would just spawn threads that find nothing left to claim.
fn shardCount(site_count: usize) usize {
    if (builtin.single_threaded) return 1;
    const cpus = std.Thread.getCpuCount() catch return 1;
    return @max(1, @min(cpus, site_count));
}

/// Compares the maintained closure against a naive expansion of the same
/// base facts, on a clone so the database under test is left untouched.
/// Every incremental path must agree with this reference.
pub fn expectClosureMatchesRebuild(db: *database.Database) !void {
    var staging = try db.clone();
    defer staging.deinit();
    var rebuilt = try staging.facts.clone();
    defer rebuilt.deinit();
    try staging.eval.expandNaive(&rebuilt);
    const closure = &db.closure.?;
    try std.testing.expectEqual(rebuilt.len(), closure.len());
    for (0..rebuilt.len()) |index|
        try std.testing.expect(try closure.contains(rebuilt.factAt(index)));
}
/// Compares the semi-naive closure against the naive reference closure on a
/// staging clone, so the database under test is left untouched.
pub fn expectSemiNaiveMatchesNaive(db: *database.Database) !void {
    var staging = try db.clone();
    defer staging.deinit();
    var semi = try staging.facts.clone();
    defer semi.deinit();
    try materialization.expand(&staging, &semi);
    var naive = try staging.facts.clone();
    defer naive.deinit();
    try staging.eval.expandNaive(&naive);
    try std.testing.expectEqual(naive.len(), semi.len());
    for (0..naive.len()) |index|
        try std.testing.expect(try semi.contains(naive.factAt(index)));
}
/// Formats one answer binding and compares it with its source spelling.
pub fn expectBindingValue(
    binding: *const results.Answer,
    variable: []const u8,
    expected: []const u8,
) !void {
    const value = try binding.getValue(variable);
    const formatted = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(formatted);
    try std.testing.expectEqualStrings(expected, formatted);
}

/// Installs a rule from descriptors, which is the part of
/// `transaction.addRuleClauses` a test below that layer needs. That function
/// belongs to `transaction.zig`, above the maintenance and update layers
/// whose tests use this, so they cannot call it — and the parser is above it
/// too. Nothing this calls sits above materialization.
pub fn defineRule(
    db: *database.Database,
    head: input.Goal,
    body: []const input.Goal,
) !void {
    const compiled_head = try compile.compileRelation(db, head.relation.predicate, head.relation.terms, false);
    const compiled_body = try compile.compileGoals(db, body);
    defer db.allocator.free(compiled_body);
    const ordered = try validation.orderClauses(db, compiled_body);
    errdefer db.allocator.free(ordered);
    const id = db.eval.next_rule_id;
    db.eval.next_rule_id += 1;
    try db.eval.rules.append(db.allocator, .{ .id = id, .head = compiled_head, .body = ordered });
    materialization.invalidateAnalysis(db);
}
