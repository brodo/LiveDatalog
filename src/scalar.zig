const std = @import("std");
const intern_index = @import("intern_index.zig");

pub const Id = enum(u64) { _ };

pub const Value = union(enum) {
    atom: []u8,
    integer: i64,
    float: f64,
};

const two_pow_63: f64 = 9223372036854775808.0;

/// What a lookup is for: the three cases of `Value` with the atom borrowed
/// rather than owned, because a lookup has not decided to store anything yet.
const Key = union(enum) {
    atom: []const u8,
    integer: i64,
    float: f64,
};

fn keyOf(value: Value) Key {
    return switch (value) {
        .atom => |atom| .{ .atom = atom },
        .integer => |number| .{ .integer = number },
        .float => |number| .{ .float = number },
    };
}

/// Whether a stored value is what a lookup is for. This is exactly what the
/// three interning scans compared: values of different kinds are never equal,
/// atoms compare by their bytes, and numbers by their own equality.
fn matchesKey(value: Value, key: Key) bool {
    return switch (key) {
        .atom => |wanted| value == .atom and std.mem.eql(u8, value.atom, wanted),
        .integer => |wanted| value == .integer and value.integer == wanted,
        .float => |wanted| value == .float and value.float == wanted,
    };
}

/// A hash agreeing with `matchesKey`. Hashing a float by its bits agrees with
/// `==` here because the only two distinct bit patterns that compare equal are
/// the two zeroes, and both canonicalize to the integer zero in `internFloat`
/// before any float reaches the table.
fn hashKey(key: Key) u64 {
    return switch (key) {
        .atom => |atom| std.hash.Wyhash.hash(0, atom),
        .integer => |number| std.hash.Wyhash.hash(1, std.mem.asBytes(&number)),
        .float => |number| std.hash.Wyhash.hash(2, std.mem.asBytes(&number)),
    };
}

pub const Store = struct {
    allocator: std.mem.Allocator,
    values: std.ArrayList(Value) = .empty,
    /// Where a scalar equal to the one being interned already is. The ordered
    /// table above stays the source of truth and an identifier stays its
    /// position in it, so this accelerates the search and changes nothing
    /// about identity, ordering, or canonicalization.
    index: intern_index.Index = .empty,
    /// What interning this store has cost, machine-independently.
    counts: intern_index.Counts = .{},

    /// How the index reaches the store: what an entry hashes to, and whether
    /// the entry at an identifier is the scalar being looked for.
    const Lookup = struct {
        store: *const Store,
        key: Key,

        pub fn matches(self: Lookup, id: u32) bool { // ziglint-ignore: Z012
            return matchesKey(self.store.values.items[id], self.key);
        }

        pub fn hash(self: Lookup, id: u32) u64 { // ziglint-ignore: Z012
            return hashKey(keyOf(self.store.values.items[id]));
        }
    };

    pub fn init(allocator: std.mem.Allocator) Store {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Store) void {
        for (self.values.items) |value| switch (value) {
            .atom => |atom| self.allocator.free(atom),
            .integer, .float => {},
        };
        self.values.deinit(self.allocator);
        self.index.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const Store) !Store {
        var result: Store = .init(self.allocator);
        result.counts = self.counts;
        errdefer result.deinit();
        for (self.values.items) |value| switch (value) {
            .atom => |atom| {
                const owned = try self.allocator.dupe(u8, atom);
                result.values.append(self.allocator, .{ .atom = owned }) catch |err| {
                    self.allocator.free(owned);
                    return err;
                };
            },
            .integer, .float => try result.values.append(self.allocator, value),
        };
        result.index = try self.index.clone(self.allocator);
        return result;
    }

    /// The identifier of the scalar `key` names, if the store already holds
    /// it, counting the comparisons the search made.
    fn find(self: *Store, key: Key, hash: u64) ?Id {
        self.counts.calls += 1;
        const found = self.index.find(hash, Lookup{ .store = self, .key = key });
        self.counts.compared += found.compared;
        return if (found.id) |id| @enumFromInt(id) else null;
    }

    /// Records the value just appended to the table. The caller reserved room
    /// before appending, so this cannot fail and cannot leave the index
    /// disagreeing with the table.
    fn noteInterned(self: *Store, hash: u64) Id {
        const id: u32 = @intCast(self.values.items.len - 1);
        self.index.insertAssumeCapacity(hash, id);
        return @enumFromInt(id);
    }

    /// What the index needs to rehash an entry it is keeping when the table
    /// is truncated. Only `hash`, because nothing is being looked for.
    const Rehash = struct {
        store: *const Store,

        pub fn hash(self: Rehash, id: u32) u64 { // ziglint-ignore: Z012
            return hashKey(keyOf(self.store.values.items[id]));
        }
    };

    /// Drops every scalar interned at or after `count`, which is how a
    /// statement rolled back out of a shared transaction gives back what it
    /// interned. Identifiers are positions, so the scalars below `count` keep
    /// theirs and everything holding one still means what it meant. Allocates
    /// nothing: a statement is usually being undone because an allocation
    /// failed.
    pub fn truncate(self: *Store, count: usize) void {
        if (count >= self.values.items.len) return;
        for (self.values.items[count..]) |value| switch (value) {
            .atom => |atom| self.allocator.free(atom),
            .integer, .float => {},
        };
        self.values.shrinkRetainingCapacity(count);
        self.index.retainBelow(count, Rehash{ .store = self });
    }

    pub fn internAtom(self: *Store, atom: []const u8) !Id {
        const key: Key = .{ .atom = atom };
        const hash = hashKey(key);
        if (self.find(key, hash)) |id| return id;
        try self.index.reserve(self.allocator, Lookup{ .store = self, .key = key });
        const owned = try self.allocator.dupe(u8, atom);
        errdefer self.allocator.free(owned);
        try self.values.append(self.allocator, .{ .atom = owned });
        return self.noteInterned(hash);
    }

    pub fn internInteger(self: *Store, number: i64) !Id {
        const key: Key = .{ .integer = number };
        const hash = hashKey(key);
        if (self.find(key, hash)) |id| return id;
        try self.index.reserve(self.allocator, Lookup{ .store = self, .key = key });
        try self.values.append(self.allocator, .{ .integer = number });
        return self.noteInterned(hash);
    }

    /// Interns a float under the canonical numeric policy: NaN reports
    /// `NumericType`, infinities report `NumericOverflow`, and an integral
    /// value exactly representable as `i64` (including both zero signs)
    /// canonicalizes to the equal integer scalar.
    pub fn internFloat(self: *Store, number: f64) !Id {
        if (std.math.isNan(number)) return error.NumericType;
        if (std.math.isInf(number)) return error.NumericOverflow;
        const floored = @floor(number);
        if (floored == number and number >= -two_pow_63 and number < two_pow_63) {
            return self.internInteger(@intFromFloat(number));
        }
        const key: Key = .{ .float = number };
        const hash = hashKey(key);
        if (self.find(key, hash)) |id| return id;
        try self.index.reserve(self.allocator, Lookup{ .store = self, .key = key });
        try self.values.append(self.allocator, .{ .float = number });
        return self.noteInterned(hash);
    }

    pub fn parseBare(self: *Store, literal: []const u8) !Id {
        if (isIntegerSyntax(literal)) {
            const number = std.fmt.parseInt(i64, literal, 10) catch |err| switch (err) {
                error.Overflow => return error.NumericOverflow,
                else => unreachable,
            };
            return self.internInteger(number);
        }
        if (isFloatSyntax(literal)) {
            const number = std.fmt.parseFloat(f64, literal) catch unreachable;
            return self.internFloat(number);
        }
        if (isNumericLeading(literal)) return error.InvalidSyntax;
        return self.internAtom(literal);
    }

    pub fn get(self: *const Store, id: Id) Value {
        return self.values.items[@intFromEnum(id)];
    }

    /// Adds two numeric scalars. Integer-only operations stay on the checked
    /// `i64` path; an operation involving a float produces `f64` and interns
    /// the result under the canonical numeric policy.
    pub fn add(self: *Store, left: Id, right: Id) !Id {
        const a = self.get(left);
        const b = self.get(right);
        if (a == .integer and b == .integer) {
            const value = std.math.add(i64, a.integer, b.integer) catch
                return error.NumericOverflow;
            return self.internInteger(value);
        }
        const a_float = floatValue(a) orelse return error.NumericType;
        const b_float = floatValue(b) orelse return error.NumericType;
        return self.internFloat(a_float + b_float);
    }

    /// Subtracts two numeric scalars with the same promotion policy as `add`.
    pub fn subtract(self: *Store, left: Id, right: Id) !Id {
        const a = self.get(left);
        const b = self.get(right);
        if (a == .integer and b == .integer) {
            const value = std.math.sub(i64, a.integer, b.integer) catch
                return error.NumericOverflow;
            return self.internInteger(value);
        }
        const a_float = floatValue(a) orelse return error.NumericType;
        const b_float = floatValue(b) orelse return error.NumericType;
        return self.internFloat(a_float - b_float);
    }

    pub fn compareNumeric(self: *const Store, left: Id, right: Id) !std.math.Order {
        return numericOrder(self.get(left), self.get(right)) orelse error.NumericType;
    }

    pub fn compare(self: *const Store, left: Id, right: Id) std.math.Order {
        if (left == right) return .eq;
        const a = self.get(left);
        const b = self.get(right);
        if (numericOrder(a, b)) |order| return order;
        return switch (a) {
            .atom => |a_atom| switch (b) {
                .atom => |b_atom| std.mem.order(u8, a_atom, b_atom),
                .integer, .float => .gt,
            },
            .integer, .float => .lt,
        };
    }

    pub fn write(self: *const Store, writer: *std.Io.Writer, id: Id) !void {
        switch (self.get(id)) {
            .integer => |number| try writer.print("{d}", .{number}),
            .float => |number| try writeFloat(writer, number),
            .atom => |atom| try writeAtom(writer, atom),
        }
    }
};

fn floatValue(value: Value) ?f64 {
    return switch (value) {
        .integer => |number| @floatFromInt(number),
        .float => |number| number,
        .atom => null,
    };
}

fn numericOrder(a: Value, b: Value) ?std.math.Order {
    return switch (a) {
        .integer => |a_integer| switch (b) {
            .integer => |b_integer| std.math.order(a_integer, b_integer),
            .float => |b_float| orderIntegerFloat(a_integer, b_float),
            .atom => null,
        },
        .float => |a_float| switch (b) {
            .integer => |b_integer| orderIntegerFloat(b_integer, a_float).invert(),
            .float => |b_float| std.math.order(a_float, b_float),
            .atom => null,
        },
        .atom => null,
    };
}

/// Orders an exact `i64` against a finite float without rounding the integer
/// through `f64`. Floats in `[-2^63, 2^63)` floor to an exactly representable
/// `i64`, so the comparison reduces to integer order plus the fraction sign.
fn orderIntegerFloat(integer: i64, float: f64) std.math.Order {
    if (float >= two_pow_63) return .lt;
    if (float < -two_pow_63) return .gt;
    const floored = @floor(float);
    const floored_integer: i64 = @intFromFloat(floored);
    if (integer != floored_integer) return std.math.order(integer, floored_integer);
    return if (float == floored) .eq else .lt;
}

fn isIntegerSyntax(literal: []const u8) bool {
    if (literal.len == 0) return false;
    var index: usize = 0;
    if (literal[0] == '+' or literal[0] == '-') {
        index = 1;
        if (index == literal.len) return false;
    }
    for (literal[index..]) |byte| if (!std.ascii.isDigit(byte)) return false;
    return true;
}

fn isFloatSyntax(literal: []const u8) bool {
    if (literal.len == 0) return false;
    var index: usize = 0;
    if (literal[index] == '+' or literal[index] == '-') {
        index += 1;
        if (index == literal.len) return false;
    }
    const integer_start = index;
    while (index < literal.len and std.ascii.isDigit(literal[index])) index += 1;
    if (index == integer_start) return false;

    var has_marker = false;
    if (index < literal.len and literal[index] == '.') {
        has_marker = true;
        index += 1;
        const fraction_start = index;
        while (index < literal.len and std.ascii.isDigit(literal[index])) index += 1;
        if (index == fraction_start) return false;
    }
    if (index < literal.len and (literal[index] == 'e' or literal[index] == 'E')) {
        has_marker = true;
        index += 1;
        if (index < literal.len and (literal[index] == '+' or literal[index] == '-')) index += 1;
        const exponent_start = index;
        while (index < literal.len and std.ascii.isDigit(literal[index])) index += 1;
        if (index == exponent_start) return false;
    }
    return has_marker and index == literal.len;
}

fn isNumericLeading(literal: []const u8) bool {
    if (literal.len == 0) return false;
    var index: usize = 0;
    if (literal[0] == '+' or literal[0] == '-') index = 1;
    return index < literal.len and std.ascii.isDigit(literal[index]);
}

/// Formats a finite float deterministically with shortest round-trip digits:
/// plain decimal for non-integral magnitudes in `[1e-3, 1e16)`, scientific
/// notation otherwise. Both spellings reparse as float syntax.
pub fn writeFloat(writer: *std.Io.Writer, value: f64) !void {
    const magnitude = @abs(value);
    if (magnitude >= 1e-3 and magnitude < 1e16 and @floor(value) != value) {
        return writer.print("{d}", .{value});
    }
    return writer.print("{e}", .{value});
}

pub fn writeAtom(writer: *std.Io.Writer, atom: []const u8) !void {
    if (isBareAtom(atom)) return writer.writeAll(atom);
    try writer.writeByte('\'');
    for (atom) |byte| {
        if (byte == '\\' or byte == '\'') try writer.writeByte('\\');
        try writer.writeByte(byte);
    }
    try writer.writeByte('\'');
}

fn isBareAtom(atom: []const u8) bool {
    if (atom.len == 0 or std.ascii.isUpper(atom[0]) or isNumericLeading(atom)) return false;
    for (atom) |byte| if (!std.ascii.isAlphanumeric(byte) and byte != '_') return false;
    return true;
}

const testing = std.testing;

/// What `find` answers if the index is not consulted at all: the scan the
/// three interning functions used to make.
fn scanFor(store: *const Store, key: Key) ?Id {
    for (store.values.items, 0..) |value, index| {
        if (matchesKey(value, key)) return @enumFromInt(index);
    }
    return null;
}

/// The float one representation step above `value`, which is as close to it
/// as a distinct `f64` gets.
fn adjacent(value: f64) f64 {
    return @bitCast(@as(u64, @bitCast(value)) + 1);
}

test "interning through the index agrees with a linear scan over the same table" {
    var store: Store = .init(testing.allocator);
    defer store.deinit();

    const atoms = [_][]const u8{ "a", "alice", "n1000", "n1001", "", "1x", "alice " };
    for (atoms) |atom| {
        const id = try store.internAtom(atom);
        try testing.expectEqual(id, scanFor(&store, .{ .atom = atom }).?);
    }

    const integers = [_]i64{ 0, -1, 1, std.math.minInt(i64), std.math.maxInt(i64) };
    for (integers) |number| {
        const id = try store.internInteger(number);
        try testing.expectEqual(id, scanFor(&store, .{ .integer = number }).?);
    }

    const floats = [_]f64{
        0.5,
        adjacent(0.5),
        -0.5,
        std.math.floatMin(f64),
        std.math.floatTrueMin(f64),
        adjacent(std.math.floatTrueMin(f64)),
        1e300,
    };
    for (floats) |number| {
        const id = try store.internFloat(number);
        try testing.expectEqual(id, scanFor(&store, .{ .float = number }).?);
    }

    // A float that is exactly an in-range integer canonicalizes before any
    // table is searched, so the index never sees it and the two zeroes are
    // one scalar.
    const zero = try store.internInteger(0);
    try testing.expectEqual(zero, try store.internFloat(0.0));
    try testing.expectEqual(zero, try store.internFloat(-0.0));
    try testing.expectEqual(try store.internInteger(1), try store.internFloat(1.0));

    // Everything above is already there, so nothing more is stored and every
    // identifier comes back unchanged.
    const entries = store.values.items.len;
    for (atoms) |atom| try testing.expectEqual(
        scanFor(&store, .{ .atom = atom }).?,
        try store.internAtom(atom),
    );
    for (integers) |number| try testing.expectEqual(
        scanFor(&store, .{ .integer = number }).?,
        try store.internInteger(number),
    );
    for (floats) |number| try testing.expectEqual(
        scanFor(&store, .{ .float = number }).?,
        try store.internFloat(number),
    );
    try testing.expectEqual(entries, store.values.items.len);
    try testing.expectEqual(entries, store.index.filled);
}

test "a cloned store interns to the same identifiers as the store it came from" {
    var store: Store = .init(testing.allocator);
    defer store.deinit();
    for (0..200) |number| {
        var spelling: [16]u8 = undefined;
        _ = try store.internAtom(try std.fmt.bufPrint(&spelling, "n{d}", .{number}));
        _ = try store.internInteger(@intCast(number));
    }

    var copy = try store.clone();
    defer copy.deinit();
    for (0..200) |number| {
        var spelling: [16]u8 = undefined;
        const atom = try std.fmt.bufPrint(&spelling, "n{d}", .{number});
        try testing.expectEqual(try store.internAtom(atom), try copy.internAtom(atom));
        try testing.expectEqual(
            try store.internInteger(@intCast(number)),
            try copy.internInteger(@intCast(number)),
        );
    }
    try testing.expectEqual(store.values.items.len, copy.values.items.len);

    // The copy owns its own atoms, so the index it inherited has to be
    // reaching them through the copy's table rather than the original's.
    const fresh = try copy.internAtom("n200");
    try testing.expectEqual(@as(usize, @intFromEnum(fresh)), store.values.items.len);
    try testing.expectEqual(fresh, try copy.internAtom("n200"));
}

test "a store truncated to a savepoint interns like one that never held what it dropped" {
    // What undoing a statement in a shared transaction needs from the store:
    // the scalars below the savepoint keep their identifiers, and the ones
    // above it leave nothing behind for a later search to find them by.
    var store: Store = .init(testing.allocator);
    defer store.deinit();
    _ = try store.internAtom("kept");
    _ = try store.internInteger(7);
    _ = try store.internFloat(0.5);
    const mark = store.values.items.len;

    _ = try store.internAtom("dropped");
    _ = try store.internInteger(-9);
    _ = try store.internFloat(2.5);
    // Enough more to make the index grow past the slots the savepoint had.
    for (0..40) |number| _ = try store.internInteger(@intCast(1000 + number));
    store.truncate(mark);

    try testing.expectEqual(mark, store.values.items.len);
    try testing.expectEqual(mark, store.index.filled);
    try testing.expectEqual(@as(Id, @enumFromInt(0)), try store.internAtom("kept"));
    try testing.expectEqual(@as(Id, @enumFromInt(1)), try store.internInteger(7));
    try testing.expectEqual(@as(Id, @enumFromInt(2)), try store.internFloat(0.5));
    try testing.expectEqual(mark, store.values.items.len);

    // What was dropped is interned afresh at the position it now has, which is
    // also what the scan the index replaced would say.
    const revived = try store.internAtom("dropped");
    try testing.expectEqual(@as(Id, @enumFromInt(@as(u32, @intCast(mark)))), revived);
    try testing.expectEqual(revived, scanFor(&store, .{ .atom = "dropped" }).?);
    try testing.expectEqual(
        try store.internInteger(-9),
        scanFor(&store, .{ .integer = -9 }).?,
    );
}
