//! A hash index over an insertion-ordered table whose identifiers are its
//! positions.
//!
//! The table stays the source of truth and identifiers stay positions in it.
//! This holds positions and nothing else, so it can only say *where* an entry
//! equal to a key already is; the comparison itself belongs to the caller and
//! is made against the table. Two things follow, and both are why interning
//! uses this rather than a `std.HashMap`.
//!
//! A key is never copied. `scalar.Store` owns the bytes of its atoms, and an
//! index holding slices of them would have to re-point every one of them
//! whenever the store is cloned.
//!
//! And a clone is a `memcpy`. A slot means the same thing in a copy that it
//! means here — cloning a table preserves both its order and the content of
//! every entry, so the entry a slot points at hashes and compares in the copy
//! exactly as it did in the original. `RelationStore` answered the same
//! question two ways for the same reason: it carries the caches that describe
//! its entry list by position, and leaves `membership` lazy because a map
//! keyed by facts has to re-key them against the copy's own terms, which is
//! what building it costs. There are no keys here to re-key, and interning
//! happens on staging copies, so it is the copy that had to be cheap.
//!
//! An identifier must fit in a `u32`. The callers assert that where they
//! record one; a table of four billion values is beyond this engine for other
//! reasons first.
const std = @import("std");

/// What interning cost, in units that do not depend on the machine.
pub const Counts = struct {
    /// Searches of a table: one per value interned, plus none for a value
    /// canonicalized into another before any table was searched.
    calls: usize = 0,
    /// Table entries compared to answer those searches. A linear scan
    /// compares every entry in the table; an index compares only the entries
    /// its probe lands on.
    compared: usize = 0,
};

/// Positions of a table's entries, keyed by their content.
///
/// The caller supplies both halves of "same content" through a context: a
/// `matches(id)` that compares the entry at `id` with the key being looked
/// for, and a `hash(id)` that hashes the entry at `id`. Nothing here knows
/// what an entry is.
pub const Index = struct {
    /// Open addressing with linear probing. A slot holds one more than the
    /// identifier it records, so that zero means empty. The length is a power
    /// of two, or zero before anything has been inserted.
    slots: []u32 = &.{},
    /// Identifiers the slots hold, which is the table's length because the
    /// index records every entry.
    filled: usize = 0,

    pub const empty: Index = .{};

    /// Slots the first insertion allocates. Small: a database with two facts
    /// in it should not carry a page of empty slots through every clone.
    const initial_slots = 16;
    /// Grow at three quarters full, which is where `std.HashMap` grows too.
    const load_numerator = 3;
    const load_denominator = 4;

    pub fn deinit(self: *Index, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
        allocator.free(self.slots);
        self.* = undefined;
    }

    /// A copy over the copy of the table this indexes.
    pub fn clone(self: *const Index, allocator: std.mem.Allocator) !Index {
        return .{
            .slots = try allocator.dupe(u32, self.slots),
            .filled = self.filled,
        };
    }

    pub const Found = struct {
        id: ?u32,
        /// Entries the probe compared, for the caller's counts.
        compared: usize,
    };

    /// The identifier of the entry `context.matches` accepts, if there is one.
    pub fn find(self: *const Index, hash: u64, context: anytype) Found {
        if (self.slots.len == 0) return .{ .id = null, .compared = 0 };
        const mask = self.slots.len - 1;
        var slot = @as(usize, @truncate(hash)) & mask;
        var compared: usize = 0;
        while (self.slots[slot] != 0) {
            const id = self.slots[slot] - 1;
            compared += 1;
            if (context.matches(id)) return .{ .id = id, .compared = compared };
            slot = (slot + 1) & mask;
        }
        return .{ .id = null, .compared = compared };
    }

    /// Makes room for one more identifier, rehashing through `context.hash`
    /// when the slots would otherwise pass the load factor. Called before the
    /// entry is appended to the table, so that a table that fails to grow and
    /// an index that fails to grow both leave the pair as it was.
    pub fn reserve(self: *Index, allocator: std.mem.Allocator, context: anytype) !void {
        if ((self.filled + 1) * load_denominator <= self.slots.len * load_numerator) return;
        const capacity = if (self.slots.len == 0) initial_slots else self.slots.len * 2;
        const fresh = try allocator.alloc(u32, capacity);
        @memset(fresh, 0);
        for (self.slots) |stored| {
            if (stored == 0) continue;
            place(fresh, context.hash(stored - 1), stored);
        }
        allocator.free(self.slots);
        self.slots = fresh;
    }

    /// Records the entry at `id`, which the caller has just appended to the
    /// table under `hash`. `reserve` must have run since the last insertion.
    pub fn insertAssumeCapacity(self: *Index, hash: u64, id: u32) void {
        place(self.slots, hash, id + 1);
        self.filled += 1;
    }

    fn place(slots: []u32, hash: u64, stored: u32) void {
        const mask = slots.len - 1;
        var slot = @as(usize, @truncate(hash)) & mask;
        while (slots[slot] != 0) slot = (slot + 1) & mask;
        slots[slot] = stored;
    }
};

const testing = std.testing;

/// A table of integers standing in for the value tables, indexed the way they
/// index themselves.
const Numbers = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayList(u64) = .empty,
    index: Index = .empty,
    counts: Counts = .{},

    const Context = struct {
        table: *const Numbers,
        key: u64,

        pub fn matches(self: Context, id: u32) bool { // ziglint-ignore: Z012
            return self.table.entries.items[id] == self.key;
        }

        pub fn hash(self: Context, id: u32) u64 { // ziglint-ignore: Z012
            return hashNumber(self.table.entries.items[id]);
        }
    };

    /// Deliberately terrible above 64, so that the tests below cover probes
    /// that walk over entries they do not want.
    fn hashNumber(number: u64) u64 {
        return number % 64;
    }

    fn deinit(self: *Numbers) void {
        self.entries.deinit(self.allocator);
        self.index.deinit(self.allocator);
        self.* = undefined;
    }

    fn intern(self: *Numbers, number: u64) !u32 {
        const hash = hashNumber(number);
        const context: Context = .{ .table = self, .key = number };
        self.counts.calls += 1;
        const found = self.index.find(hash, context);
        self.counts.compared += found.compared;
        if (found.id) |id| return id;
        try self.index.reserve(self.allocator, context);
        try self.entries.append(self.allocator, number);
        const id: u32 = @intCast(self.entries.items.len - 1);
        self.index.insertAssumeCapacity(hash, id);
        return id;
    }

    /// What `intern` answers if the index is not consulted at all.
    fn scan(self: *const Numbers, number: u64) ?u32 {
        for (self.entries.items, 0..) |entry, id| {
            if (entry == number) return @intCast(id);
        }
        return null;
    }

    fn clone(self: *const Numbers) !Numbers {
        return .{
            .allocator = self.allocator,
            .entries = try self.entries.clone(self.allocator),
            .index = try self.index.clone(self.allocator),
            .counts = self.counts,
        };
    }
};

test "interning through the index agrees with a linear scan" {
    var numbers: Numbers = .{ .allocator = testing.allocator };
    defer numbers.deinit();

    var random: std.Random.DefaultPrng = .init(20260825);
    for (0..2000) |_| {
        const number = random.random().uintLessThan(u64, 500);
        const expected = numbers.scan(number);
        const id = try numbers.intern(number);
        if (expected) |already| {
            try testing.expectEqual(already, id);
        } else {
            try testing.expectEqual(numbers.entries.items.len - 1, id);
        }
        try testing.expectEqual(id, numbers.scan(number).?);
    }
    try testing.expectEqual(numbers.entries.items.len, numbers.index.filled);
}

test "a cloned index answers what the index it was copied from answers" {
    var numbers: Numbers = .{ .allocator = testing.allocator };
    defer numbers.deinit();
    for (0..300) |number| _ = try numbers.intern(number * 7);

    var copy = try numbers.clone();
    defer copy.deinit();
    for (0..300) |number| {
        try testing.expectEqual(
            try numbers.intern(number * 7),
            try copy.intern(number * 7),
        );
    }
    try testing.expectEqual(@as(usize, 300), copy.entries.items.len);

    // And the copy keeps interning where the original left off.
    try testing.expectEqual(@as(u32, 300), try copy.intern(1));
    try testing.expectEqual(@as(u32, 300), copy.scan(1).?);
}

test "an index whose slots never allocate finds nothing" {
    const numbers: Numbers = .{ .allocator = testing.allocator };
    const found = numbers.index.find(0, Numbers.Context{ .table = &numbers, .key = 1 });
    try testing.expectEqual(@as(?u32, null), found.id);
    try testing.expectEqual(@as(usize, 0), found.compared);
}
