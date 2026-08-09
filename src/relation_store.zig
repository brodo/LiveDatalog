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
const std = @import("std");

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
    /// does not exist yet is assumed to give nothing away, so a mask whose
    /// index has never been built rates no better than a scan. Building it to
    /// find out is what this deliberately does not do; the first lookup builds
    /// it, and the next plan sees what it is worth.
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

    const PatternIndex = struct {
        groups: std.AutoHashMapUnmanaged(u64, std.ArrayList(u32)) = .empty,

        fn deinit(self: *PatternIndex, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
            var iterator = self.groups.valueIterator();
            while (iterator.next()) |group| group.deinit(allocator);
            self.groups.deinit(allocator);
            self.* = undefined;
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
            const group = pattern.value_ptr.groups.getOrPut(self.allocator, group_key) catch {
                failed_patterns = true;
                continue;
            };
            if (!group.found_existing) group.value_ptr.* = .empty;
            group.value_ptr.append(self.allocator, index) catch {
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
    /// the first. Building one costs a pass over the relation and a group per
    /// distinct key, which a single probe cannot repay — the whole relation is
    /// a valid candidate set and answering with it examines no more facts than
    /// building the index would touch, without allocating any. A pattern asked
    /// for twice will almost certainly be asked for again, so that is where
    /// the index is worth its construction. Set membership rather than a count
    /// is enough: the question is only whether this is the first request.
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
        const group = pattern.groups.get(tupleHash(bound)) orelse return &no_entries;
        return group.items;
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
        return .{ .facts = facts, .groups = @max(1, pattern.groups.count()) };
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

    fn ensurePattern(self: *RelationStore, id: PatternId) !*PatternIndex {
        if (self.patterns.getPtr(id)) |pattern| return pattern;
        var pattern: PatternIndex = .{};
        errdefer pattern.deinit(self.allocator);
        for (self.entries.items, 0..) |entry, index| {
            if (entry.fact.predicate != id.name or entry.fact.terms.len != id.arity) continue;
            const group_key = maskHash(entry.fact.terms, id.mask);
            const group = try pattern.groups.getOrPut(self.allocator, group_key);
            if (!group.found_existing) group.value_ptr.* = .empty;
            try group.value_ptr.append(self.allocator, @intCast(index));
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

test "a pattern index is built on the second request, not the first" {
    // A single probe cannot repay a pass over the relation and a group per
    // distinct key, so the first request for a pattern is answered with the
    // relation instead. That is a candidate set like any other — the caller
    // unifies every candidate — and it is what keeps a query that touches a
    // large relation once from paying to index it.
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
