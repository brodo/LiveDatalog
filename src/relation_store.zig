//! Indexed ownership of ground facts by predicate and arity.
//!
//! The ordered entry list is the source of truth: it preserves insertion
//! order, which keeps query answers deterministic. Exact membership, the
//! per-predicate buckets, and the bound-position pattern indexes are lazily
//! built caches over that list. A cache that fails to update during an insert
//! is destroyed and rebuilt on next use, so lookups never observe a stale or
//! partially updated cache. Pattern indexes are candidate prefilters keyed by
//! a hash of the bound values; callers must still unify every candidate, so a
//! hash collision can only add candidates, never hide a match.
//!
//! A pattern index keeps every group in one flat `[]u32`, beside an ordered
//! group list and an `intern_index.Index` of positions in it, so that a copy
//! is three `memcpy`s whatever number of groups it has. Groups reserve room
//! past their end and move to the end of the array when they outgrow it,
//! which is how a flat layout absorbs an insert; see `PatternIndex.append`.
const std = @import("std");
const intern_index = @import("intern_index.zig");

pub const Id = u64;
pub const ValueId = u64;

pub const Fact = struct {
    predicate: Id,
    terms: []ValueId,
};

pub const PredicateKey = struct {
    name: Id,
    arity: usize,
};

pub fn factsEqual(a: Fact, b: Fact) bool {
    return a.predicate == b.predicate and std.mem.eql(ValueId, a.terms, b.terms);
}

fn factHash(fact: Fact) u64 {
    var hasher = std.hash.Wyhash.init(0);
    hasher.update(std.mem.asBytes(&fact.predicate));
    hasher.update(std.mem.sliceAsBytes(fact.terms));
    return hasher.final();
}

fn tupleHash(values: []const ValueId) u64 {
    return std.hash.Wyhash.hash(1, std.mem.sliceAsBytes(values));
}

const FactContext = struct {
    pub fn hash(_: FactContext, fact: Fact) u64 { // ziglint-ignore: Z012
        return factHash(fact);
    }

    pub fn eql(_: FactContext, a: Fact, b: Fact) bool { // ziglint-ignore: Z012
        return factsEqual(a, b);
    }
};

const no_entries: [0]u32 = .{};

/// How many facts a relation holds and how many distinct keys an index on a
/// given mask projects them onto. A planner divides one by the other to
/// estimate what a lookup on that mask will return, without knowing the
/// values it will be given.
pub const Selectivity = struct {
    facts: usize,
    /// Distinct projected keys the index holds, or null when there is no index
    /// on that mask yet. An empty relation reports one (empty) key.
    groups: ?usize,

    /// Candidates a lookup on this mask is expected to return. An index that
    /// does not exist yet is assumed to give nothing away, so a mask no lookup
    /// has asked for yet rates no better than a scan. Building it to find out
    /// is what this deliberately does not do; the first lookup builds it, and
    /// the next plan sees what it is worth.
    pub fn estimate(self: Selectivity) usize {
        return self.facts / (self.groups orelse 1);
    }
};

pub const RelationStore = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayList(Entry) = .empty,
    membership: ?Membership = null,
    buckets: ?Buckets = null,
    patterns: Patterns = .empty,
    /// Patterns asked for once and answered with a scan. The second request
    /// is what builds the index; see `lookup`.
    requested: std.AutoHashMapUnmanaged(PatternId, void) = .empty,

    const Entry = struct {
        fact: Fact,
        derived: bool,
        /// Counts insertion attempts for the fact: one for the first
        /// insertion plus one per duplicate. This is internal support
        /// bookkeeping for deletion maintenance and is never exposed as a
        /// Datalog value; deletion phases refine its precision.
        support: u32,
    };

    const Membership = std.HashMapUnmanaged(Fact, u32, FactContext, std.hash_map.default_max_load_percentage);
    const Buckets = std.AutoHashMapUnmanaged(PredicateKey, std.ArrayList(u32));

    const PatternId = struct {
        name: Id,
        arity: usize,
        mask: u64,
    };

    /// One group of a pattern index: the key it collects, and where in the
    /// flat array its entry indices live — `len` of them starting at `start`,
    /// with room for `capacity` before the group has to move.
    const Group = struct {
        key: u64,
        start: u32,
        len: u32,
        capacity: u32,
    };

    /// Answers "same group" for `intern_index.Index`, which holds positions in
    /// the group list and nothing else. A group key is already a hash of the
    /// projected values, so it is its own hash and a rehash recomputes
    /// nothing.
    const GroupsByKey = struct {
        groups: []const Group,
        key: u64 = 0,

        pub fn matches(self: GroupsByKey, id: u32) bool { // ziglint-ignore: Z012
            return self.groups[id].key == self.key;
        }

        pub fn hash(self: GroupsByKey, id: u32) u64 { // ziglint-ignore: Z012
            return self.groups[id].key;
        }
    };

    /// Entry indices for one binding pattern: every group laid out end to end
    /// in a single array, an insertion-ordered list of the groups, and a hash
    /// index of *positions* in that list.
    ///
    /// This is what a group-per-`ArrayList` layout keyed by a `std.HashMap`
    /// could not be. All three parts are plain arrays, so a copy is three
    /// `memcpy`s however many groups there are, where copying used to cost an
    /// allocation per group and re-keying a map costs what building one costs.
    /// That is the same answer, for the same reason, that P4's first item gave
    /// for the value tables — see `intern_index` — and it is what retires the
    /// density gate that used to decide which indexes a clone could afford.
    ///
    /// A group reserves room past its end, so an insert is absorbed in place.
    /// When the room runs out the group is copied to the end of the array with
    /// twice as much, exactly as an `ArrayList` grows, and its old slots are
    /// abandoned. That bounds the array without compaction: a group at
    /// capacity `c` has ever occupied `2c - 1` slots and holds more than
    /// `c / 2`, so the array stays under four times the entries it holds
    /// however long it is grown, and equals them exactly when it is built
    /// rather than grown. A candidate slice stays valid until the next insert
    /// into its own index, which is the promise the per-group lists made too.
    const PatternIndex = struct {
        groups: std.ArrayList(Group) = .empty,
        directory: intern_index.Index = .empty,
        entries: std.ArrayList(u32) = .empty,

        fn deinit(self: *PatternIndex, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
            self.groups.deinit(allocator);
            self.directory.deinit(allocator);
            self.entries.deinit(allocator);
            self.* = undefined;
        }

        /// The position of the group collecting `key`, if it has one.
        fn find(self: *const PatternIndex, key: u64) ?u32 {
            return self.directory.find(key, GroupsByKey{
                .groups = self.groups.items,
                .key = key,
            }).id;
        }

        /// The entry indices grouped under `key`, in insertion order.
        fn group(self: *const PatternIndex, key: u64) []const u32 {
            const found = self.groups.items[self.find(key) orelse return &no_entries];
            return self.entries.items[found.start..][0..found.len];
        }

        /// Starts an empty group for `key` and returns its position. On
        /// failure nothing has changed.
        // ziglint-ignore: Z023
        fn addGroup(self: *PatternIndex, allocator: std.mem.Allocator, key: u64, start: u32, capacity: u32) !u32 {
            try self.groups.ensureUnusedCapacity(allocator, 1);
            try self.directory.reserve(allocator, GroupsByKey{ .groups = self.groups.items });
            const id: u32 = @intCast(self.groups.items.len);
            self.groups.appendAssumeCapacity(.{
                .key = key,
                .start = start,
                .len = 0,
                .capacity = capacity,
            });
            self.directory.insertAssumeCapacity(key, id);
            return id;
        }

        /// Adds `entry` to the group `key` names, in place when the group has
        /// room and by moving it to the end of the array with twice as much
        /// when it does not. On failure nothing has changed, which is what lets
        /// `noteInserted` treat a failure as a reason to drop the index rather
        /// than as a half-applied insert.
        // ziglint-ignore: Z023
        fn append(self: *PatternIndex, allocator: std.mem.Allocator, key: u64, entry: u32) !void {
            const existing = self.find(key) orelse {
                try self.entries.ensureUnusedCapacity(allocator, 1);
                const fresh = try self.addGroup(allocator, key, @intCast(self.entries.items.len), 1);
                self.entries.appendAssumeCapacity(entry);
                self.groups.items[fresh].len = 1;
                return;
            };
            const found = &self.groups.items[existing];
            if (found.len < found.capacity) {
                self.entries.items[found.start + found.len] = entry;
                found.len += 1;
                return;
            }
            const capacity = @max(found.capacity, 1) *| 2;
            try self.entries.ensureUnusedCapacity(allocator, capacity);
            const moved = found.*;
            const start: u32 = @intCast(self.entries.items.len);
            const slots = self.entries.addManyAsSliceAssumeCapacity(capacity);
            @memcpy(slots[0..moved.len], self.entries.items[moved.start..][0..moved.len]);
            slots[moved.len] = entry;
            // The reservation is inside `items`, and `copy` memcpys all of
            // `items`, so the room this group has not filled yet is written
            // rather than left undefined.
            @memset(slots[moved.len + 1 ..], 0);
            found.* = .{
                .key = moved.key,
                .start = start,
                .len = moved.len + 1,
                .capacity = capacity,
            };
        }

        /// A copy sharing nothing with this index, in three `memcpy`s. The
        /// abandoned slots come across with the rest, because a group's range
        /// means what it means only against the array it was measured in, and
        /// a directory slot means the same in a copy because the group list it
        /// points into is copied in order.
        fn copy(self: *const PatternIndex, allocator: std.mem.Allocator) !PatternIndex { // ziglint-ignore: Z023
            var result: PatternIndex = .{ .entries = try self.entries.clone(allocator) };
            errdefer result.deinit(allocator);
            result.groups = try self.groups.clone(allocator);
            result.directory = try self.directory.clone(allocator);
            return result;
        }
    };

    const Patterns = std.AutoHashMapUnmanaged(PatternId, PatternIndex);

    pub fn init(allocator: std.mem.Allocator) RelationStore {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *RelationStore) void {
        self.dropCaches();
        for (self.entries.items) |entry| self.allocator.free(entry.fact.terms);
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    fn dropCaches(self: *RelationStore) void {
        self.dropMembership();
        self.dropBuckets();
        self.dropPatterns();
    }

    fn dropMembership(self: *RelationStore) void {
        if (self.membership) |*membership| membership.deinit(self.allocator);
        self.membership = null;
    }

    fn dropBuckets(self: *RelationStore) void {
        if (self.buckets) |*buckets| {
            var iterator = buckets.valueIterator();
            while (iterator.next()) |bucket| bucket.deinit(self.allocator);
            buckets.deinit(self.allocator);
        }
        self.buckets = null;
    }

    fn dropPatterns(self: *RelationStore) void {
        var iterator = self.patterns.valueIterator();
        while (iterator.next()) |pattern| pattern.deinit(self.allocator);
        self.patterns.deinit(self.allocator);
        self.patterns = .empty;
        self.requested.deinit(self.allocator);
        self.requested = .empty;
    }

    /// A copy sharing nothing with this store.
    ///
    /// The lookup caches are copied rather than dropped. They describe the
    /// entry list by *position* — a bucket and an index group hold entry
    /// indices, and a group is keyed by a hash of interned value identifiers —
    /// and cloning preserves both order and identifiers, so every index and
    /// every hash means in the copy exactly what it meant here. Rebuilding
    /// them would cost a pass over the relation hashing each fact again, which
    /// is what a statement used to pay on every clone: the caches are the
    /// reason a query over a materialized closure did three passes over it
    /// instead of one.
    ///
    /// Membership is the exception and stays lazy. Its keys are facts rather
    /// than positions, so a copy has to re-key them against the copy's own
    /// terms — and a hash map cannot be copied without rehashing its keys, so
    /// copying one costs what building one costs. There is nothing to save,
    /// and a statement that never probes membership would pay it for nothing.
    ///
    /// `requested` does not carry over either, and must not: it records that a
    /// pattern was asked for once *here*, and `lookup` defers building an index
    /// until the second ask precisely so that a lookup happening once does not
    /// pay for one. A copy that inherited the record would build on its own
    /// first ask, which for a per-statement copy is every ask.
    pub fn clone(self: *const RelationStore) !RelationStore {
        var result: RelationStore = .init(self.allocator);
        errdefer result.deinit();
        try result.entries.ensureTotalCapacity(self.allocator, self.entries.items.len);
        for (self.entries.items) |entry| {
            const terms = try self.allocator.dupe(ValueId, entry.fact.terms);
            result.entries.appendAssumeCapacity(.{
                .fact = .{ .predicate = entry.fact.predicate, .terms = terms },
                .derived = entry.derived,
                .support = entry.support,
            });
        }
        try result.adoptCaches(self);
        return result;
    }

    /// Takes over the caches worth carrying from the store being cloned.
    fn adoptCaches(self: *RelationStore, source: *const RelationStore) !void {
        if (source.buckets) |*buckets| self.buckets = try cloneBuckets(self.allocator, buckets);
        self.patterns = try clonePatterns(self.allocator, &source.patterns);
    }

    fn cloneBuckets(allocator: std.mem.Allocator, source: *const Buckets) !Buckets {
        var result: Buckets = .empty;
        errdefer {
            var iterator = result.valueIterator();
            while (iterator.next()) |bucket| bucket.deinit(allocator);
            result.deinit(allocator);
        }
        try result.ensureTotalCapacity(allocator, source.count());
        var iterator = source.iterator();
        while (iterator.next()) |entry| {
            const bucket = try entry.value_ptr.clone(allocator);
            result.putAssumeCapacity(entry.key_ptr.*, bucket);
        }
        return result;
    }

    /// Copies every pattern index, whatever its shape.
    ///
    /// Density used to decide, because a group was a list of its own and
    /// copying an index cost an allocation per group: a near-unique index over
    /// a thousand facts was a thousand allocations to copy, which was slower
    /// than rebuilding it and was paid whether or not the copy ever looked at
    /// it. In the flat layout a copy is three `memcpy`s regardless of shape,
    /// so there is none it is cheaper to drop than to carry, and the rule that
    /// used to choose is gone.
    fn clonePatterns(allocator: std.mem.Allocator, source: *const Patterns) !Patterns {
        var result: Patterns = .empty;
        errdefer {
            var iterator = result.valueIterator();
            while (iterator.next()) |pattern| pattern.deinit(allocator);
            result.deinit(allocator);
        }
        try result.ensureTotalCapacity(allocator, source.count());
        var iterator = source.iterator();
        while (iterator.next()) |entry| {
            const pattern = try entry.value_ptr.copy(allocator);
            result.putAssumeCapacity(entry.key_ptr.*, pattern);
        }
        return result;
    }

    pub fn len(self: *const RelationStore) usize {
        return self.entries.items.len;
    }

    pub fn factAt(self: *const RelationStore, index: usize) Fact {
        return self.entries.items[index].fact;
    }

    pub fn isDerived(self: *const RelationStore, index: usize) bool {
        return self.entries.items[index].derived;
    }

    pub fn supportAt(self: *const RelationStore, index: usize) u32 {
        return self.entries.items[index].support;
    }

    pub fn contains(self: *RelationStore, fact: Fact) !bool {
        const membership = try self.ensureMembership();
        return membership.contains(fact);
    }

    /// Inserts a fact with set semantics. On success the store owns
    /// `fact.terms`, freeing them immediately when the fact is a duplicate
    /// (whose support count increments instead), and returns whether the
    /// fact was added. On error the caller retains ownership of `fact.terms`
    /// and the store is unchanged.
    pub fn insert(self: *RelationStore, fact: Fact, derived: bool) !bool {
        const membership = try self.ensureMembership();
        if (membership.get(fact)) |existing| {
            self.entries.items[existing].support += 1;
            self.allocator.free(fact.terms);
            return false;
        }
        const index: u32 = @intCast(self.entries.items.len);
        try self.entries.append(self.allocator, .{
            .fact = fact,
            .derived = derived,
            .support = 1,
        });
        self.noteInserted(index);
        return true;
    }

    /// Removes the exact fact when present, preserving entry order, and
    /// returns whether anything was removed.
    pub fn removeFact(self: *RelationStore, fact: Fact) !bool {
        const membership = try self.ensureMembership();
        const index = membership.get(fact) orelse return false;
        self.removeAt(index);
        return true;
    }

    /// Best-effort cache maintenance: a cache that cannot absorb the new
    /// entry is destroyed and rebuilt lazily instead of failing the insert.
    fn noteInserted(self: *RelationStore, index: u32) void {
        const fact = self.entries.items[index].fact;
        if (self.membership) |*membership| {
            membership.put(self.allocator, fact, index) catch self.dropMembership();
        }
        if (self.buckets) |*buckets| blk: {
            const key: PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
            const bucket = buckets.getOrPut(self.allocator, key) catch {
                self.dropBuckets();
                break :blk;
            };
            if (!bucket.found_existing) bucket.value_ptr.* = .empty;
            bucket.value_ptr.append(self.allocator, index) catch self.dropBuckets();
        }
        var failed_patterns = false;
        var iterator = self.patterns.iterator();
        while (iterator.next()) |pattern| {
            if (pattern.key_ptr.name != fact.predicate or
                pattern.key_ptr.arity != fact.terms.len) continue;
            const group_key = maskHash(fact.terms, pattern.key_ptr.mask);
            pattern.value_ptr.append(self.allocator, group_key, index) catch {
                failed_patterns = true;
            };
        }
        if (failed_patterns) self.dropPatterns();
    }

    /// Removes the entry at `index`, preserving the order of the remaining
    /// entries.
    pub fn removeAt(self: *RelationStore, index: usize) void {
        self.dropCaches();
        const entry = self.entries.orderedRemove(index);
        self.allocator.free(entry.fact.terms);
    }

    pub fn clear(self: *RelationStore) void {
        self.dropCaches();
        for (self.entries.items) |entry| self.allocator.free(entry.fact.terms);
        self.entries.clearRetainingCapacity();
    }

    /// Returns the indices of all facts with the given predicate and arity in
    /// insertion order.
    pub fn predicateEntries(self: *RelationStore, key: PredicateKey) ![]const u32 {
        const buckets = try self.ensureBuckets();
        const bucket = buckets.get(key) orelse return &no_entries;
        return bucket.items;
    }

    /// Returns candidate indices, in insertion order, for facts whose terms
    /// at the positions set in `mask` may equal `bound` (listed in ascending
    /// position order). Candidates are a superset of the exact matches, so
    /// callers must verify each candidate.
    ///
    /// The pattern index for `mask` is created on the *second* request, not
    /// the first, and the whole relation answers the first — a candidate set
    /// like any other, since the caller unifies every candidate.
    ///
    /// The flat layout made this cheap enough to reconsider and it was
    /// reconsidered, on the measurement rather than on the argument. Building
    /// on the first request cost `benchmark-join-planning`'s sparse join 1.30x
    /// and left every other shape where it was. That shape is what the rule is
    /// about: one goal binds a single value and the goal after it is looked up
    /// exactly once, on a staging copy that is discarded when the query ends.
    /// Two asks is a cheap proxy for a third, because the goal inside a join
    /// is looked up once per binding the goal outside it produced — a lookup
    /// that happens twice is one that is about to happen four hundred times.
    ///
    /// So this rule stayed and the density gate went. `requested` is set
    /// membership rather than a count: the question is only whether this is
    /// the first request, and a copy that inherited the answer would build on
    /// its own first ask, which for a per-statement copy is every ask.
    pub fn lookup(
        self: *RelationStore,
        key: PredicateKey,
        mask: u64,
        bound: []const ValueId,
    ) ![]const u32 {
        if (mask == 0) return self.predicateEntries(key);
        const id: PatternId = .{ .name = key.name, .arity = key.arity, .mask = mask };
        if (self.patterns.getPtr(id) == null) {
            const first = try self.requested.getOrPut(self.allocator, id);
            if (!first.found_existing) return self.predicateEntries(key);
        }
        const pattern = try self.ensurePattern(id);
        return pattern.group(tupleHash(bound));
    }

    /// The relation's size, and the number of groups an index on `mask` splits
    /// it into if such an index has already been built.
    ///
    /// This never builds one. An index costs a pass over the relation and one
    /// group per distinct key, which is a price worth paying for a lookup that
    /// is going to happen and pure loss for a plan that is not chosen — so a
    /// planner is told about the indexes that exist, and evaluating the plan it
    /// picks is what creates the rest.
    pub fn selectivity(self: *RelationStore, key: PredicateKey, mask: u64) !Selectivity {
        const facts = (try self.predicateEntries(key)).len;
        if (mask == 0 or facts == 0) return .{ .facts = facts, .groups = 1 };
        const pattern = self.patterns.getPtr(.{
            .name = key.name,
            .arity = key.arity,
            .mask = mask,
        }) orelse return .{ .facts = facts, .groups = null };
        return .{ .facts = facts, .groups = @max(1, pattern.groups.items.len) };
    }

    fn ensureMembership(self: *RelationStore) !*Membership {
        if (self.membership == null) {
            var membership: Membership = .empty;
            errdefer membership.deinit(self.allocator);
            for (self.entries.items, 0..) |entry, index| {
                try membership.put(self.allocator, entry.fact, @intCast(index));
            }
            self.membership = membership;
        }
        return &self.membership.?;
    }

    fn ensureBuckets(self: *RelationStore) !*Buckets {
        if (self.buckets == null) {
            var buckets: Buckets = .empty;
            errdefer {
                var iterator = buckets.valueIterator();
                while (iterator.next()) |bucket| bucket.deinit(self.allocator);
                buckets.deinit(self.allocator);
            }
            for (self.entries.items, 0..) |entry, index| {
                const key: PredicateKey = .{
                    .name = entry.fact.predicate,
                    .arity = entry.fact.terms.len,
                };
                const bucket = try buckets.getOrPut(self.allocator, key);
                if (!bucket.found_existing) bucket.value_ptr.* = .empty;
                try bucket.value_ptr.append(self.allocator, @intCast(index));
            }
            self.buckets = buckets;
        }
        return &self.buckets.?;
    }

    /// Builds the index for `id` if it does not exist, in two passes over the
    /// predicate's own entries: the first counts each group so that the flat
    /// array can be sized once and every group placed in it, the second writes
    /// the entry indices in insertion order, `len` serving as the cursor it
    /// ends up being the length of. A freshly built index reserves nothing, so
    /// its array is exactly as long as the entries it holds.
    ///
    /// The passes go over the predicate bucket rather than the whole entry
    /// list, so indexing one relation of a closure that holds many does not
    /// walk the others twice. The bucket is a cache of the same entry list and
    /// holds it in the same order, so the index it produces is the one a scan
    /// of everything would have produced.
    fn ensurePattern(self: *RelationStore, id: PatternId) !*PatternIndex {
        if (self.patterns.getPtr(id)) |pattern| return pattern;
        const bucket = try self.predicateEntries(.{ .name = id.name, .arity = id.arity });
        var pattern: PatternIndex = .{};
        errdefer pattern.deinit(self.allocator);
        for (bucket) |index| {
            const key = maskHash(self.entries.items[index].fact.terms, id.mask);
            const group = pattern.find(key) orelse try pattern.addGroup(self.allocator, key, 0, 0);
            pattern.groups.items[group].capacity += 1;
        }
        try pattern.entries.resize(self.allocator, bucket.len);
        var next_start: u32 = 0;
        for (pattern.groups.items) |*group| {
            group.start = next_start;
            next_start += group.capacity;
        }
        for (bucket) |index| {
            const key = maskHash(self.entries.items[index].fact.terms, id.mask);
            const group = &pattern.groups.items[pattern.find(key).?];
            pattern.entries.items[group.start + group.len] = index;
            group.len += 1;
        }
        try self.patterns.put(self.allocator, id, pattern);
        return self.patterns.getPtr(id).?;
    }

    fn maskHash(terms: []const ValueId, mask: u64) u64 {
        var projected: [64]ValueId = undefined;
        var count: usize = 0;
        for (terms, 0..) |term, position| {
            if (position >= 64) break;
            if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
            projected[count] = term;
            count += 1;
        }
        return tupleHash(projected[0..count]);
    }
};

fn testFact(allocator: std.mem.Allocator, predicate: Id, terms: []const ValueId) !Fact {
    return .{ .predicate = predicate, .terms = try allocator.dupe(ValueId, terms) };
}

/// Looks up through the pattern index rather than through the scan the first
/// request for a pattern is answered with. Both are valid candidate sets; a
/// test that pins the exact one has to ask twice to get it.
fn indexedLookup(store: *RelationStore, key: PredicateKey, mask: u64, bound: []const ValueId) ![]const u32 {
    _ = try store.lookup(key, mask, bound);
    return store.lookup(key, mask, bound);
}

test "insert duplicate insert membership and predicate buckets" {
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();

    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 20 }), false));
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 30 }), false));
    try std.testing.expect(!try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 20 }), true));
    try std.testing.expectEqual(@as(usize, 2), store.len());

    try std.testing.expect(try store.contains(.{ .predicate = 1, .terms = @constCast(&[_]ValueId{ 10, 20 }) }));
    try std.testing.expect(!try store.contains(.{ .predicate = 1, .terms = @constCast(&[_]ValueId{ 10, 40 }) }));
    try std.testing.expect(!try store.contains(.{ .predicate = 2, .terms = @constCast(&[_]ValueId{ 10, 20 }) }));

    const bucket = try store.predicateEntries(.{ .name = 1, .arity = 2 });
    try std.testing.expectEqualSlices(u32, &.{ 0, 1 }, bucket);
    try std.testing.expectEqual(@as(usize, 0), (try store.predicateEntries(.{ .name = 1, .arity = 1 })).len);
}

test "predicate names reused at different arities never share an index" {
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 7, &.{5}), false));
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 7, &.{ 5, 5 }), false));

    const unary = try indexedLookup(&store, .{ .name = 7, .arity = 1 }, 0b1, &.{5});
    try std.testing.expectEqualSlices(u32, &.{0}, unary);
    const binary = try indexedLookup(&store, .{ .name = 7, .arity = 2 }, 0b1, &.{5});
    try std.testing.expectEqualSlices(u32, &.{1}, binary);
    try std.testing.expectEqualSlices(u32, &.{0}, try store.predicateEntries(.{ .name = 7, .arity = 1 }));
    try std.testing.expectEqualSlices(u32, &.{1}, try store.predicateEntries(.{ .name = 7, .arity = 2 }));
}

test "pattern lookups stay consistent across inserts deletes and clear" {
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 3, &.{ 1, 100 }), false));
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 3, &.{ 2, 100 }), false));

    // Build the pattern index, then insert into it.
    try std.testing.expectEqualSlices(
        u32,
        &.{ 0, 1 },
        try indexedLookup(&store, .{ .name = 3, .arity = 2 }, 0b10, &.{100}),
    );
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 3, &.{ 3, 100 }), true));
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 3, &.{ 3, 200 }), true));
    try std.testing.expectEqualSlices(
        u32,
        &.{ 0, 1, 2 },
        try indexedLookup(&store, .{ .name = 3, .arity = 2 }, 0b10, &.{100}),
    );
    try std.testing.expectEqualSlices(
        u32,
        &.{2},
        try indexedLookup(&store, .{ .name = 3, .arity = 2 }, 0b11, &.{ 3, 100 }),
    );
    try std.testing.expect(!store.isDerived(0));
    try std.testing.expect(store.isDerived(2));

    store.removeAt(1);
    try std.testing.expectEqualSlices(
        u32,
        &.{ 0, 1 },
        try indexedLookup(&store, .{ .name = 3, .arity = 2 }, 0b10, &.{100}),
    );
    try std.testing.expect(!try store.contains(.{ .predicate = 3, .terms = @constCast(&[_]ValueId{ 2, 100 }) }));

    store.clear();
    try std.testing.expectEqual(@as(usize, 0), store.len());
    try std.testing.expectEqual(
        @as(usize, 0),
        (try store.lookup(.{ .name = 3, .arity = 2 }, 0b10, &.{100})).len,
    );
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 3, &.{ 2, 100 }), false));
    try std.testing.expectEqualSlices(
        u32,
        &.{0},
        try indexedLookup(&store, .{ .name = 3, .arity = 2 }, 0b11, &.{ 2, 100 }),
    );
}

test "a clone carries every pattern index whatever its density" {
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    // Eight facts whose first argument takes two values and whose second is
    // unique: an index on the first is dense, one on the second is not. That
    // difference used to decide which one a clone carried, because a group was
    // a list of its own and copying cost an allocation per group. Copying is
    // three `memcpy`s now, so there is no shape worth dropping and both come
    // across.
    for (0..8) |value| _ = try store.insert(
        try testFact(std.testing.allocator, 1, &.{ @intCast(value / 4), @intCast(value) }),
        false,
    );
    const key: PredicateKey = .{ .name = 1, .arity = 2 };
    try std.testing.expectEqualSlices(u32, &.{ 4, 5, 6, 7 }, try indexedLookup(&store, key, 0b01, &.{1}));
    try std.testing.expectEqualSlices(u32, &.{3}, try indexedLookup(&store, key, 0b10, &.{3}));
    try std.testing.expectEqual(@as(usize, 2), store.patterns.count());

    var copy = try store.clone();
    defer copy.deinit();

    // Both indexes and the buckets come across, and answer on the first ask —
    // they describe the entry list by position, and the position of every
    // entry is what a clone preserves.
    try std.testing.expectEqual(@as(usize, 2), copy.patterns.count());
    try std.testing.expect(copy.buckets != null);
    try std.testing.expectEqualSlices(u32, &.{ 4, 5, 6, 7 }, try copy.lookup(key, 0b01, &.{1}));
    try std.testing.expectEqualSlices(u32, &.{3}, try copy.lookup(key, 0b10, &.{3}));
    // Carrying the near-unique index is also what lets the copy report its
    // selectivity without having to rediscover it.
    try std.testing.expectEqual(@as(?usize, 8), (try copy.selectivity(key, 0b10)).groups);

    // A copied cache is a live cache: it absorbs the copy's own inserts, and
    // the store it came from is untouched by them.
    _ = try copy.insert(try testFact(std.testing.allocator, 1, &.{ 1, 99 }), true);
    try std.testing.expectEqualSlices(u32, &.{ 4, 5, 6, 7, 8 }, try copy.lookup(key, 0b01, &.{1}));
    try std.testing.expectEqualSlices(u32, &.{8}, try copy.lookup(key, 0b10, &.{99}));
    try std.testing.expectEqualSlices(u32, &.{ 4, 5, 6, 7 }, try store.lookup(key, 0b01, &.{1}));
    try std.testing.expectEqual(@as(usize, 0), (try store.lookup(key, 0b10, &.{99})).len);
    try std.testing.expectEqual(@as(usize, 8), store.len());
}

test "a pattern index is built on the second request, not the first" {
    // A single probe cannot repay a pass over the relation and a group per
    // distinct key, so the first request for a pattern is answered with the
    // relation instead. That is a candidate set like any other — the caller
    // unifies every candidate — and it is what keeps a query that touches a
    // large relation once from paying to index it. The flat layout made
    // building cheap enough to reconsider the rule; the sparse join in
    // `benchmark-join-planning` is what kept it.
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    for (0..4) |value| _ = try store.insert(
        try testFact(std.testing.allocator, 5, &.{ @intCast(value), 9 }),
        false,
    );

    const key: PredicateKey = .{ .name = 5, .arity = 2 };
    try std.testing.expectEqualSlices(u32, &.{ 0, 1, 2, 3 }, try store.lookup(key, 0b01, &.{2}));
    try std.testing.expectEqual(@as(usize, 0), store.patterns.count());
    try std.testing.expectEqualSlices(u32, &.{2}, try store.lookup(key, 0b01, &.{2}));
    try std.testing.expectEqual(@as(usize, 1), store.patterns.count());

    // Selectivity reports what the index says once it exists, and admits to
    // knowing nothing before that, so planning cannot mistake an unmeasured
    // pattern for a measured one.
    try std.testing.expectEqual(@as(?usize, 4), (try store.selectivity(key, 0b01)).groups);
    try std.testing.expectEqual(@as(?usize, null), (try store.selectivity(key, 0b10)).groups);
    try std.testing.expectEqual(@as(usize, 4), (try store.selectivity(key, 0b10)).estimate());
}

test "a group that outgrows its room moves without disturbing the others" {
    // The flat layout's one moving part. A group reserves room past its end
    // and is copied to the end of the array with twice as much when it runs
    // out, so what has to hold is that the move leaves every other group where
    // it was and the moved one in insertion order — and that the slots it
    // abandons stay bounded.
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    for (0..4) |value| _ = try store.insert(
        try testFact(std.testing.allocator, 5, &.{ @intCast(value), 9 }),
        false,
    );
    const key: PredicateKey = .{ .name = 5, .arity = 2 };
    // A built index reserves nothing, so the second argument's single group
    // has to move on the very next insert, and every insert after it.
    _ = try indexedLookup(&store, key, 0b10, &.{9});
    _ = try indexedLookup(&store, key, 0b01, &.{2});
    const built = store.patterns.getPtr(.{ .name = 5, .arity = 2, .mask = 0b10 }).?;
    try std.testing.expectEqual(@as(usize, 4), built.entries.items.len);

    for (4..12) |value| _ = try store.insert(
        try testFact(std.testing.allocator, 5, &.{ @intCast(value), 9 }),
        false,
    );
    try std.testing.expectEqualSlices(
        u32,
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 },
        try store.lookup(key, 0b10, &.{9}),
    );
    try std.testing.expectEqualSlices(u32, &.{2}, try store.lookup(key, 0b01, &.{2}));
    try std.testing.expectEqualSlices(u32, &.{11}, try store.lookup(key, 0b01, &.{11}));

    // A group at capacity `c` has ever occupied `2c - 1` slots and holds more
    // than `c / 2`, so the array cannot pass four times what it holds.
    const grown = store.patterns.getPtr(.{ .name = 5, .arity = 2, .mask = 0b10 }).?;
    try std.testing.expect(grown.entries.items.len < 4 * 12);

    // The same index survives a clone with the abandoned slots in place.
    var copy = try store.clone();
    defer copy.deinit();
    try std.testing.expectEqualSlices(
        u32,
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 },
        try copy.lookup(key, 0b10, &.{9}),
    );
    _ = try copy.insert(try testFact(std.testing.allocator, 5, &.{ 12, 9 }), false);
    try std.testing.expectEqualSlices(
        u32,
        &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 },
        try copy.lookup(key, 0b10, &.{9}),
    );
}

test "support counts duplicates and exact removal keeps indexes consistent" {
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 20 }), false));
    try std.testing.expect(!try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 20 }), true));
    try std.testing.expect(!try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 20 }), true));
    try std.testing.expectEqual(@as(u32, 3), store.supportAt(0));
    try std.testing.expect(!store.isDerived(0));

    try std.testing.expect(try store.insert(try testFact(std.testing.allocator, 1, &.{ 10, 30 }), true));
    try std.testing.expectEqual(@as(u32, 1), store.supportAt(1));

    try std.testing.expect(!try store.removeFact(.{ .predicate = 1, .terms = @constCast(&[_]ValueId{ 10, 40 }) }));
    try std.testing.expect(try store.removeFact(.{ .predicate = 1, .terms = @constCast(&[_]ValueId{ 10, 20 }) }));
    try std.testing.expectEqual(@as(usize, 1), store.len());
    try std.testing.expectEqualSlices(
        u32,
        &.{0},
        try store.lookup(.{ .name = 1, .arity = 2 }, 0b11, &.{ 10, 30 }),
    );
}

/// Exact matches for `mask`/`bound` found by scanning the store's own entry
/// list, which is the source of truth every cache is a cache of.
fn scanMatches(
    store: *const RelationStore,
    key: PredicateKey,
    mask: u64,
    bound: []const ValueId,
    into: *std.ArrayList(u32),
) !void {
    into.clearRetainingCapacity();
    for (0..store.len()) |index| {
        const fact = store.factAt(index);
        if (fact.predicate != key.name or fact.terms.len != key.arity) continue;
        var position: usize = 0;
        var taken: usize = 0;
        const matches = blk: {
            while (position < key.arity) : (position += 1) {
                if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
                if (fact.terms[position] != bound[taken]) break :blk false;
                taken += 1;
            }
            break :blk true;
        };
        if (matches) try into.append(std.testing.allocator, @intCast(index));
    }
}

/// Asks twice — so that a layout deferring construction has built whatever it
/// is going to build — verifies every candidate the way evaluation does, and
/// requires the survivors to be the scan's matches in the scan's order.
fn expectLookupAgreesWithScan(
    store: *RelationStore,
    key: PredicateKey,
    mask: u64,
    bound: []const ValueId,
    expected: *std.ArrayList(u32),
) !void {
    try scanMatches(store, key, mask, bound, expected);
    _ = try store.lookup(key, mask, bound);
    const candidates = try store.lookup(key, mask, bound);
    var found: usize = 0;
    for (candidates) |candidate| {
        const fact = store.factAt(candidate);
        if (fact.predicate != key.name or fact.terms.len != key.arity) continue;
        var position: usize = 0;
        var taken: usize = 0;
        const matches = blk: {
            while (position < key.arity) : (position += 1) {
                if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
                if (fact.terms[position] != bound[taken]) break :blk false;
                taken += 1;
            }
            break :blk true;
        };
        if (!matches) continue;
        try std.testing.expect(found < expected.items.len);
        try std.testing.expectEqual(expected.items[found], candidate);
        found += 1;
    }
    try std.testing.expectEqual(expected.items.len, found);
}

test "a clone and its original answer every pattern lookup as each keeps inserting" {
    // P4's pattern-index item is free to change how an index is laid out, when
    // it is built, and which ones a clone carries. What it is not free to
    // change is this: a lookup answers with the facts the entry list holds, in
    // the order the entry list holds them, on either side of a clone, and goes
    // on doing so as each side takes inserts the other never sees. The masks
    // below span a dense projection, a near-unique one, and every combination,
    // so a layout that copies some indexes and rebuilds others is measured on
    // all of them at once.
    var prng = std.Random.DefaultPrng.init(0x243f6a8885a308d3);
    const random = prng.random();
    const key: PredicateKey = .{ .name = 1, .arity = 3 };

    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    var expected: std.ArrayList(u32) = .empty;
    defer expected.deinit(std.testing.allocator);

    const freshTerms = struct {
        fn call(rng: std.Random) [3]ValueId {
            return .{
                rng.uintLessThan(u64, 2),
                rng.uintLessThan(u64, 40),
                rng.uintLessThan(u64, 7),
            };
        }
    }.call;

    for (0..120) |_| {
        const terms = freshTerms(random);
        _ = try store.insert(try testFact(std.testing.allocator, key.name, &terms), false);
    }
    // Ask on every mask before cloning, so that whatever the layout builds on
    // demand exists to be carried or dropped.
    for (1..8) |mask| {
        const terms = freshTerms(random);
        var bound: [3]ValueId = undefined;
        var count: usize = 0;
        for (0..3) |position| {
            if (mask & (@as(usize, 1) << @intCast(position)) == 0) continue;
            bound[count] = terms[position];
            count += 1;
        }
        try expectLookupAgreesWithScan(&store, key, @intCast(mask), bound[0..count], &expected);
    }

    var copy = try store.clone();
    defer copy.deinit();
    try std.testing.expectEqual(store.len(), copy.len());
    for (0..store.len()) |index|
        try std.testing.expect(factsEqual(store.factAt(index), copy.factAt(index)));

    for (0..400) |round| {
        const side = if (round % 3 == 0) &store else &copy;
        const terms = freshTerms(random);
        _ = try side.insert(try testFact(std.testing.allocator, key.name, &terms), false);
        for (1..8) |mask| {
            const probe = if (random.boolean()) terms else freshTerms(random);
            var bound: [3]ValueId = undefined;
            var count: usize = 0;
            for (0..3) |position| {
                if (mask & (@as(usize, 1) << @intCast(position)) == 0) continue;
                bound[count] = probe[position];
                count += 1;
            }
            try expectLookupAgreesWithScan(side, key, @intCast(mask), bound[0..count], &expected);
        }
    }
    try std.testing.expect(store.len() != copy.len());
}

test "random operation sequences agree with an unordered reference set" {
    var prng = std.Random.DefaultPrng.init(0x9e3779b97f4a7c15);
    const random = prng.random();
    var store: RelationStore = .init(std.testing.allocator);
    defer store.deinit();
    var reference: std.ArrayList(Fact) = .empty;
    defer {
        for (reference.items) |fact| std.testing.allocator.free(fact.terms);
        reference.deinit(std.testing.allocator);
    }

    for (0..2000) |_| {
        const predicate: Id = random.uintLessThan(u64, 4);
        const arity: usize = 1 + random.uintLessThan(usize, 3);
        var terms: [3]ValueId = undefined;
        for (terms[0..arity]) |*term| term.* = random.uintLessThan(u64, 6);
        const candidate: Fact = .{ .predicate = predicate, .terms = terms[0..arity] };

        switch (random.uintLessThan(u8, 10)) {
            0...5 => {
                const in_reference = blk: {
                    for (reference.items) |fact| if (factsEqual(fact, candidate)) break :blk true;
                    break :blk false;
                };
                const added = try store.insert(
                    try testFact(std.testing.allocator, predicate, terms[0..arity]),
                    false,
                );
                try std.testing.expectEqual(!in_reference, added);
                if (added) {
                    try reference.append(
                        std.testing.allocator,
                        try testFact(std.testing.allocator, predicate, terms[0..arity]),
                    );
                }
            },
            6 => {
                if (store.len() > 0) {
                    const index = random.uintLessThan(usize, store.len());
                    try std.testing.expect(factsEqual(store.factAt(index), reference.items[index]));
                    store.removeAt(index);
                    std.testing.allocator.free(reference.items[index].terms);
                    _ = reference.orderedRemove(index);
                }
            },
            else => {
                // Compare an indexed lookup against a reference scan.
                const mask: u64 = random.uintLessThan(u64, @as(u64, 1) << @intCast(arity));
                var bound: [3]ValueId = undefined;
                var bound_count: usize = 0;
                for (0..arity) |position| {
                    if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
                    bound[bound_count] = terms[position];
                    bound_count += 1;
                }
                const candidates = try store.lookup(
                    .{ .name = predicate, .arity = arity },
                    mask,
                    bound[0..bound_count],
                );
                var expected: std.ArrayList(u32) = .empty;
                defer expected.deinit(std.testing.allocator);
                for (reference.items, 0..) |fact, index| {
                    if (fact.predicate != predicate or fact.terms.len != arity) continue;
                    const matches = blk: {
                        for (0..arity) |position| {
                            if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
                            if (fact.terms[position] != terms[position]) break :blk false;
                        }
                        break :blk true;
                    };
                    if (matches) try expected.append(std.testing.allocator, @intCast(index));
                }
                // Candidates are a superset in insertion order; verify every
                // exact match is present and every candidate matches after
                // verification, mirroring how evaluation unifies candidates.
                var expected_index: usize = 0;
                for (candidates) |candidate_index| {
                    const fact = store.factAt(candidate_index);
                    const matches = blk: {
                        for (0..arity) |position| {
                            if (mask & (@as(u64, 1) << @intCast(position)) == 0) continue;
                            if (fact.terms[position] != terms[position]) break :blk false;
                        }
                        break :blk true;
                    };
                    if (!matches) continue;
                    try std.testing.expectEqual(expected.items[expected_index], candidate_index);
                    expected_index += 1;
                }
                try std.testing.expectEqual(expected.items.len, expected_index);
            },
        }
    }
    try std.testing.expectEqual(reference.items.len, store.len());
}

/// Inserts a copy of `fact` into `store`, which takes ownership of the copied
/// terms. The single place the database duplicates a fact between stores.
pub fn copyFactInto(
    allocator: std.mem.Allocator,
    store: *RelationStore,
    fact: Fact,
    derived: bool,
) !void {
    const terms = try allocator.dupe(ValueId, fact.terms);
    _ = store.insert(.{ .predicate = fact.predicate, .terms = terms }, derived) catch |err| {
        allocator.free(terms);
        return err;
    };
}

/// Appends a copy of `fact` to `list`, which takes ownership of the copied
/// terms. The `std.ArrayList` counterpart of `copyFactInto`, used where facts
/// are queued for later application rather than stored.
pub fn appendFactCopy(
    allocator: std.mem.Allocator,
    list: *std.ArrayList(Fact),
    fact: Fact,
) !void {
    const terms = try allocator.dupe(ValueId, fact.terms);
    list.append(allocator, .{ .predicate = fact.predicate, .terms = terms }) catch |err| {
        allocator.free(terms);
        return err;
    };
}

/// Collects the distinct predicate keys of `store[from..]`, the set the
/// stratum-impact analysis tests a batch's reach against.
pub fn collectPredicateKeys(
    allocator: std.mem.Allocator,
    store: *const RelationStore,
    from: usize,
    keys: *std.AutoHashMapUnmanaged(PredicateKey, void),
) !void {
    for (from..store.len()) |index| {
        const fact = store.factAt(index);
        try keys.put(allocator, .{ .name = fact.predicate, .arity = fact.terms.len }, {});
    }
}
