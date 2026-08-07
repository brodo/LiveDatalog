//! Assertions shared by the test suites of several modules.
//!
//! Each checks a database against a reference computed a different way, which
//! is the property the whole engine rests on: maintaining the closure
//! incrementally, rebuilding it from a dirty stratum and expanding it naively
//! must all produce the same database.

const std = @import("std");
const root = @import("root.zig");
const materialization = @import("materialization.zig");

const Jatalog = root.Jatalog;
const Answer = root.Answer;

/// Compares the maintained closure against a naive expansion of the same
/// base facts, on a clone so the database under test is left untouched.
/// Every incremental path must agree with this reference.
pub fn expectClosureMatchesRebuild(db: *Jatalog) !void {
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
pub fn expectSemiNaiveMatchesNaive(db: *Jatalog) !void {
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
/// Runs one source query and asserts how many answers it produces.
pub fn expectAnswerCount(db: *Jatalog, source: []const u8, expected: usize) !void {
    var result = try db.execute(source);
    defer result.deinit();
    try std.testing.expectEqual(expected, result.query.answers.items.len);
}

/// Formats one answer binding and compares it with its source spelling.
pub fn expectBindingValue(
    binding: *const Answer,
    variable: []const u8,
    expected: []const u8,
) !void {
    const value = try binding.getValue(variable);
    const formatted = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(formatted);
    try std.testing.expectEqualStrings(expected, formatted);
}
