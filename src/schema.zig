//! Predicate schemas: the column types a schema declares, the order they form,
//! and the registry a database keeps them in. See "Schema" in CONTEXT.md.
//!
//! Every column type is some number of `list(...)` wrappers around one
//! element type, so a type is that pair rather than a tree: `list(list(int))`
//! is two lists around `int`, and `list` is one list around `any`. That makes
//! a type a plain value — nothing to allocate, clone or free — which is what
//! lets a type test sit inside a compiled goal like any other field.
//!
//! Nothing here reads a value. Whether a ground value has a type depends on
//! the value tables, so that check belongs to the evaluator that owns them.

const std = @import("std");

pub const Element = enum {
    /// The empty type. No value has it; `list(never)` is the type of `[]`.
    never,
    atom,
    int,
    number,
    any,
};

pub const ColumnType = struct {
    /// How many `list(...)` wrappers surround `element`.
    lists: u8 = 0,
    element: Element = .any,

    pub const any: ColumnType = .{};
    pub const atom: ColumnType = .{ .element = .atom };
    pub const int: ColumnType = .{ .element = .int };
    pub const number: ColumnType = .{ .element = .number };
    /// What no value has. An inference that arrives here has proven a goal
    /// can never match.
    pub const empty: ColumnType = .{ .element = .never };
    /// The type of `[]`, which every list type holds.
    pub const empty_list: ColumnType = .{ .lists = 1, .element = .never };

    pub fn isEmpty(self: ColumnType) bool {
        return self.lists == 0 and self.element == .never;
    }

    pub fn eql(self: ColumnType, other: ColumnType) bool {
        return self.lists == other.lists and self.element == other.element;
    }

    /// `list(self)`, or null when that nests deeper than a type can.
    pub fn listOf(self: ColumnType) ?ColumnType {
        if (self.isEmpty()) return empty_list;
        if (self.lists == std.math.maxInt(u8)) return null;
        return .{ .lists = self.lists + 1, .element = self.element };
    }

    /// The type of a list's elements, when every value of this type that is a
    /// list has elements of it: `any` for `any`, and nothing for a type that
    /// holds no lists at all.
    pub fn elements(self: ColumnType) ColumnType {
        if (self.lists > 0) return .{ .lists = self.lists - 1, .element = self.element };
        return if (self.element == .any) any else empty;
    }

    /// Whether `[]` has this type.
    pub fn holdsNil(self: ColumnType) bool {
        return self.lists > 0 or self.element == .any;
    }

    /// The type every value of both types has.
    pub fn meet(self: ColumnType, other: ColumnType) ColumnType {
        if (self.lists > 0 and other.lists > 0)
            return self.elements().meet(other.elements()).listOf().?;
        // At most one side is a list type from here on.
        if (self.lists == 0 and self.element == .any) return other;
        if (other.lists == 0 and other.element == .any) return self;
        if (self.lists > 0 or other.lists > 0) return empty;
        return .{ .element = meetElement(self.element, other.element) };
    }

    /// The narrowest type every value of either type has.
    pub fn join(self: ColumnType, other: ColumnType) ColumnType {
        if (self.isSubtype(other)) return other;
        if (other.isSubtype(self)) return self;
        if (self.lists > 0 and other.lists > 0)
            return self.elements().join(other.elements()).listOf() orelse any;
        if (self.lists == 0 and other.lists == 0 and numeric(self.element) and numeric(other.element))
            return number;
        return any;
    }

    /// Whether every value of this type has `other`.
    pub fn isSubtype(self: ColumnType, other: ColumnType) bool {
        return self.meet(other).eql(self);
    }

    pub fn format(self: ColumnType, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        for (0..self.lists) |_| try writer.writeAll("list(");
        try writer.writeAll(@tagName(self.element));
        for (0..self.lists) |_| try writer.writeByte(')');
    }
};

fn numeric(element: Element) bool {
    return element == .int or element == .number;
}

fn meetElement(left: Element, right: Element) Element {
    if (left == right) return left;
    if (left == .any) return right;
    if (right == .any) return left;
    if (left == .never or right == .never) return .never;
    if (numeric(left) and numeric(right)) return .int;
    return .never;
}

/// One predicate's declared shape.
pub const Schema = struct {
    columns: []ColumnType,
    /// The column names, as interned identifiers, or null where a column is
    /// unnamed. They are part of what a schema is, so a redeclaration that
    /// renames a column is a different schema.
    names: []?u64,

    pub fn deinit(self: Schema, allocator: std.mem.Allocator) void {
        allocator.free(self.columns);
        allocator.free(self.names);
    }

    pub fn clone(self: Schema, allocator: std.mem.Allocator) !Schema {
        const columns = try allocator.dupe(ColumnType, self.columns);
        errdefer allocator.free(columns);
        return .{ .columns = columns, .names = try allocator.dupe(?u64, self.names) };
    }

    pub fn eql(self: Schema, other: Schema) bool {
        if (self.columns.len != other.columns.len) return false;
        for (self.columns, other.columns) |left, right| if (!left.eql(right)) return false;
        for (self.names, other.names) |left, right| if (left != right) return false;
        return true;
    }
};

/// The schemas a database holds, by interned predicate name. A predicate
/// that has none is untyped.
pub const Registry = struct {
    schemas: std.array_hash_map.Auto(u64, Schema) = .empty,

    pub fn deinit(self: *Registry, allocator: std.mem.Allocator) void {
        for (self.schemas.values()) |value| value.deinit(allocator);
        self.schemas.deinit(allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const Registry, allocator: std.mem.Allocator) !Registry {
        var result: Registry = .{};
        errdefer result.deinit(allocator);
        try result.schemas.ensureTotalCapacity(allocator, self.schemas.count());
        for (self.schemas.keys(), self.schemas.values()) |name, value|
            result.schemas.putAssumeCapacity(name, try value.clone(allocator));
        return result;
    }

    pub fn get(self: *const Registry, name: u64) ?Schema {
        return self.schemas.get(name);
    }

    pub fn count(self: *const Registry) usize {
        return self.schemas.count();
    }

    /// Takes ownership of `value` on success.
    pub fn put(self: *Registry, allocator: std.mem.Allocator, name: u64, value: Schema) !void {
        std.debug.assert(!self.schemas.contains(name));
        try self.schemas.put(allocator, name, value);
    }

    /// Takes a schema back out, for a declaration that turned out not to hold.
    pub fn remove(self: *Registry, allocator: std.mem.Allocator, name: u64) void {
        const removed = self.schemas.fetchOrderedRemove(name) orelse return;
        removed.value.deinit(allocator);
    }
};

const testing = std.testing;

fn listOf(inner: ColumnType) ColumnType {
    return inner.listOf().?;
}

test "the order is the one the glossary states" {
    const list: ColumnType = listOf(.any);
    try testing.expect(ColumnType.int.isSubtype(.number));
    try testing.expect(ColumnType.number.isSubtype(.any));
    try testing.expect(!ColumnType.number.isSubtype(.int));
    try testing.expect(!ColumnType.atom.isSubtype(.number));
    try testing.expect(listOf(.int).isSubtype(listOf(.number)));
    try testing.expect(listOf(.int).isSubtype(list));
    try testing.expect(listOf(listOf(.int)).isSubtype(list));
    try testing.expect(list.isSubtype(.any));
    try testing.expect(!list.isSubtype(listOf(.int)));
    try testing.expect(!listOf(.int).isSubtype(.int));
    // `[]` is every list, and nothing else.
    try testing.expect(ColumnType.empty_list.isSubtype(listOf(listOf(.atom))));
    try testing.expect(!ColumnType.empty_list.isSubtype(.atom));
    // Every type is its own subtype, and the empty type is everyone's.
    for ([_]ColumnType{ .any, .atom, .int, .number, list, listOf(.int), .empty_list }) |t| {
        try testing.expect(t.isSubtype(t));
        try testing.expect(ColumnType.empty.isSubtype(t));
        try testing.expect(t.meet(.any).eql(t));
    }
}

test "meets that share nothing are empty, and lists of disjoint elements hold only []" {
    try testing.expect(ColumnType.int.meet(.atom).isEmpty());
    try testing.expect(listOf(.any).meet(.number).isEmpty());
    try testing.expect(ColumnType.int.meet(.number).eql(.int));
    try testing.expect(listOf(.int).meet(listOf(.atom)).eql(.empty_list));
    try testing.expect(listOf(.int).meet(listOf(listOf(.any))).eql(.empty_list));
    try testing.expect(ColumnType.empty_list.meet(.int).isEmpty());
}

test "joins widen to the narrowest common type" {
    try testing.expect(ColumnType.int.join(.number).eql(.number));
    try testing.expect(ColumnType.int.join(.atom).eql(.any));
    try testing.expect(listOf(.int).join(listOf(.atom)).eql(listOf(.any)));
    try testing.expect(ColumnType.empty_list.join(listOf(.int)).eql(listOf(.int)));
    try testing.expect(ColumnType.empty_list.join(.int).eql(.any));
}

test "types print as they are written" {
    var buffer: [32]u8 = undefined;
    const text = try std.fmt.bufPrint(&buffer, "{f}", .{listOf(listOf(.int))});
    try testing.expectEqualStrings("list(list(int))", text);
}
