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

    pub fn get(self: *const StringTable, string: []const u8) ?syntax.Id {
        return self.strings.get(string);
    }

    pub fn resolve(self: *const StringTable, id: syntax.Id) []const u8 {
        return self.strings.keys()[@intCast(id)];
    }
};
