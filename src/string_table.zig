//! The symbol table a database interns its predicate and variable names in.

const std = @import("std");
const syntax = @import("syntax.zig");

/// Interns predicate and variable symbols used by a database. IDs are
/// insertion indexes, which makes `resolve` a reverse lookup into the ordered
/// keys of the same StringArrayHashMapUnmanaged.
pub const StringTable = struct {
    allocator: std.mem.Allocator,
    strings: std.StringArrayHashMapUnmanaged(syntax.Id) = .empty,

    pub fn init(allocator: std.mem.Allocator) StringTable {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *StringTable) void {
        for (self.strings.keys()) |string| self.allocator.free(string);
        self.strings.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const StringTable) !StringTable {
        var result: StringTable = .init(self.allocator);
        errdefer result.deinit();
        for (self.strings.keys()) |string| _ = try result.intern(string);
        return result;
    }

    pub fn intern(self: *StringTable, string: []const u8) !syntax.Id {
        if (self.strings.get(string)) |id| return id;
        const owned = try self.allocator.dupe(u8, string);
        errdefer self.allocator.free(owned);
        const id: syntax.Id = @intCast(self.strings.count());
        try self.strings.putNoClobber(self.allocator, owned, id);
        return id;
    }

    /// Drops every string interned at or after `count`, which is how a
    /// statement rolled back out of a shared transaction gives back the
    /// symbols it named. Identifiers are insertion indexes, so the strings
    /// below `count` keep the ones they had. Allocates nothing: a statement
    /// is usually being undone because an allocation failed.
    pub fn truncate(self: *StringTable, count: usize) void {
        if (count >= self.strings.count()) return;
        // The map wants the entries it discards still hashable while it takes
        // them out of its index, so they are freed afterwards. Shrinking keeps
        // the capacity that holds them, so the slice stays readable until then.
        const discarded = self.strings.keys()[count..];
        self.strings.shrinkRetainingCapacity(count);
        for (discarded) |string| self.allocator.free(string);
    }

    pub fn get(self: *const StringTable, string: []const u8) ?syntax.Id {
        return self.strings.get(string);
    }

    pub fn resolve(self: *const StringTable, id: syntax.Id) []const u8 {
        return self.strings.keys()[@intCast(id)];
    }
};

const testing = std.testing;

test "a table truncated to a savepoint interns like one that never held what it dropped" {
    // The symbols a rolled-back statement named have to go back, identifiers
    // and all: `resolve` reads the keys by position, so a dropped string left
    // findable would answer with an identifier past the end of the table.
    var table: StringTable = .init(testing.allocator);
    defer table.deinit();
    try testing.expectEqual(@as(syntax.Id, 0), try table.intern("kept"));
    try testing.expectEqual(@as(syntax.Id, 1), try table.intern("also_kept"));
    const mark = table.strings.count();

    _ = try table.intern("dropped");
    var buffer: [16]u8 = undefined;
    for (0..40) |index| _ = try table.intern(try std.fmt.bufPrint(&buffer, "s{d}", .{index}));
    table.truncate(mark);

    try testing.expectEqual(mark, table.strings.count());
    try testing.expectEqual(@as(?syntax.Id, null), table.get("dropped"));
    try testing.expectEqual(@as(syntax.Id, 0), try table.intern("kept"));
    try testing.expectEqual(@as(syntax.Id, 1), try table.intern("also_kept"));
    try testing.expectEqualStrings("also_kept", table.resolve(1));
    // And what was dropped is interned afresh, at the position it now has.
    try testing.expectEqual(@as(syntax.Id, 2), try table.intern("dropped"));
    try testing.expectEqualStrings("dropped", table.resolve(2));
}
