//! Who asserts each base fact: the records behind "Contributor" in CONTEXT.md.
//!
//! A base fact is present while at least one contributor asserts it. Most
//! facts only ever have one — the implicit *direct* contributor that
//! statements, `addFact` and `applyChanges` assert for — and for those this
//! records nothing at all: a fact no named contributor asserts is asserted by
//! the direct contributor exactly when the database holds it, so the base
//! facts already say everything there is to say. A database no embedder has
//! named a contributor for therefore carries two empty maps, and copying one
//! costs nothing.
//!
//! Records begin with the first named contributor to assert a fact. From then
//! on the fact has a `Support` saying how many named contributors assert it
//! and whether the direct contributor does too, and each named contributor has
//! the set of facts it asserts. The support goes when the last named
//! contributor lets go of the fact, and with it the need to remember the direct
//! contributor separately: if the fact stays, it stays because the direct
//! contributor asserts it, which the base facts say again.
//!
//! Facts are identified by their interned values, which is what makes
//! sameness here the engine's scalar identity rather than a spelling: `1` and
//! `1.0`, or a cons chain and the list it spells, intern to one value and so
//! are one fact however each contributor wrote it. The identifiers survive
//! cloning, because a copy of a database has the same value tables in the same
//! order, so the records copy verbatim.
//!
//! This module holds the records and nothing else. When a fact enters or
//! leaves the base facts is the database's to say (`Database.adoptInsertion`
//! and `Database.applyRemoval` keep these records in step), and what a
//! replaced contribution does to the closure is the update path's.

const std = @import("std");
const relation_store = @import("relation_store.zig");

const Fact = relation_store.Fact;

/// Hashes a fact by its interned values, for the array hash maps below.
const FactContext = struct {
    pub fn hash(_: FactContext, fact: Fact) u32 { // ziglint-ignore: Z012
        return @truncate(relation_store.factHash(fact));
    }

    pub fn eql(_: FactContext, a: Fact, b: Fact, _: usize) bool { // ziglint-ignore: Z012
        return relation_store.factsEqual(a, b);
    }
};

/// A map keyed by facts, by value.
fn FactMap(comptime Value: type) type {
    return std.array_hash_map.Custom(Fact, Value, FactContext, true);
}

/// A set of facts, owning each key's terms.
const FactSet = FactMap(void);

/// What holds a fact up, for a fact at least one named contributor asserts.
pub const Support = struct {
    /// How many named contributors assert the fact. Never zero: a support
    /// whose last named contributor lets go is removed.
    named: u32,
    /// Whether the direct contributor asserts it too, which is what decides
    /// whether the fact outlives its last named contributor.
    direct: bool,
};

/// The contribution records of one database.
pub const Contributions = struct {
    /// Each named contributor's set of facts, by name. Names and fact terms
    /// are owned.
    named: std.array_hash_map.String(FactSet) = .empty,
    /// The support of every fact some named contributor asserts, with terms
    /// owned separately from any contributor's set, since the contributor a
    /// fact first came from may let go of it before the others do.
    support: FactMap(Support) = .empty,

    pub fn deinit(self: *Contributions, allocator: std.mem.Allocator) void {
        for (self.named.keys(), self.named.values()) |name, *facts| {
            freeSet(allocator, facts);
            allocator.free(name);
        }
        self.named.deinit(allocator);
        for (self.support.keys()) |fact| allocator.free(fact.terms);
        self.support.deinit(allocator);
        self.* = undefined;
    }

    /// A copy sharing nothing with this one. Free when nobody has named a
    /// contributor, which is the case every database starts in and most stay
    /// in.
    pub fn clone(self: *const Contributions, allocator: std.mem.Allocator) !Contributions {
        var result: Contributions = .{};
        errdefer result.deinit(allocator);
        result.support = try cloneOwning(Support, allocator, &self.support);
        try result.named.ensureTotalCapacity(allocator, self.named.count());
        for (self.named.keys(), self.named.values()) |name, *facts| {
            var copied = try cloneOwning(void, allocator, facts);
            const owned_name = allocator.dupe(u8, name) catch |err| {
                freeSet(allocator, &copied);
                return err;
            };
            result.named.putAssumeCapacityNoClobber(owned_name, copied);
        }
        return result;
    }

    /// How many facts some named contributor asserts. Taken by a savepoint:
    /// a statement either records its fact or leaves the records as they
    /// were, so a rollback checks this rather than restoring it.
    pub fn supported(self: *const Contributions) usize {
        return self.support.count();
    }

    /// Whether the contributor called `name` asserts `fact`.
    pub fn asserts(self: *const Contributions, name: []const u8, fact: Fact) bool {
        const facts = self.named.getPtr(name) orelse return false;
        return facts.contains(fact);
    }

    /// Records that the direct contributor asserts `fact`, which the base
    /// facts already hold. Only a fact some named contributor asserts has
    /// anything to record, so this allocates nothing and cannot fail.
    pub fn assertDirectly(self: *Contributions, fact: Fact) void {
        if (self.support.count() == 0) return;
        if (self.support.getPtr(fact)) |held| held.direct = true;
    }

    /// Records that the contributor called `name` asserts `fact`, which the
    /// base facts hold already when `present`. A fact nobody named asserted
    /// before was held up by the direct contributor alone, so it is present
    /// exactly when the direct contributor asserts it.
    ///
    /// All or nothing: on failure the records are as they were, save perhaps
    /// for a contributor that asserts nothing, which is no contributor at all.
    /// `fact` is only read.
    pub fn assertNamed(
        self: *Contributions,
        allocator: std.mem.Allocator,
        name: []const u8,
        fact: Fact,
        present: bool,
    ) !void {
        const facts = try self.contributor(allocator, name);
        if (facts.contains(fact)) return;
        const held = self.support.getPtr(fact);
        // Everything that can fail happens before anything is recorded.
        try facts.ensureUnusedCapacity(allocator, 1);
        if (held == null) try self.support.ensureUnusedCapacity(allocator, 1);
        const terms = try allocator.dupe(relation_store.ValueId, fact.terms);
        errdefer allocator.free(terms);
        if (held) |support| {
            support.named += 1;
        } else {
            const support_terms = try allocator.dupe(relation_store.ValueId, fact.terms);
            self.support.putAssumeCapacityNoClobber(
                .{ .predicate = fact.predicate, .terms = support_terms },
                .{ .named = 1, .direct = present },
            );
        }
        facts.putAssumeCapacityNoClobber(.{ .predicate = fact.predicate, .terms = terms }, {});
    }

    /// Takes `fact` from every contributor, named and direct: what a deletion
    /// means (see "Contributor" in CONTEXT.md). Called once the fact has left
    /// the base facts. A fact with no support has no named contributor to
    /// take it from, so the common case is one lookup in an empty map.
    pub fn retractEverywhere(self: *Contributions, allocator: std.mem.Allocator, fact: Fact) void {
        if (self.support.count() == 0) return;
        const removed = self.support.fetchSwapRemove(fact) orelse return;
        allocator.free(removed.key.terms);
        for (self.named.values()) |*facts| {
            if (facts.fetchSwapRemove(fact)) |taken| allocator.free(taken.key.terms);
        }
    }

    /// Replaces the contribution of `name` with `facts`, and says what that
    /// does to the base facts: the facts no contributor asserts any more go
    /// into `gone`, which `base` holds every one of, and the position in
    /// `facts` of each fact no contributor asserted before goes into
    /// `arriving`, which `base` holds none of. A fact `facts` names twice is
    /// one fact, arriving once.
    ///
    /// The records are updated before the base facts move. What arrives is
    /// recorded as held up by `name` alone, and nothing in `gone` has support
    /// left, so applying the two to the base facts afterwards finds nothing
    /// more to record. Staged work: on failure the records are left
    /// consistent enough to free, and not as they were, so the caller runs
    /// this on a copy it discards on failure.
    ///
    /// `facts` is only read, and interned against the database `base` is the
    /// base facts of. An empty `facts` withdraws the contributor. Returns
    /// whether the contributor's set of facts changed at all, which it can
    /// without `gone` or `arriving` holding anything.
    pub fn replace(
        self: *Contributions,
        allocator: std.mem.Allocator,
        name: []const u8,
        facts: []const Fact,
        base: *relation_store.RelationStore,
        gone: *relation_store.RelationStore,
        arriving: *std.ArrayList(usize),
    ) !bool {
        // The new contribution, borrowing its terms from `facts`, with the
        // position each fact first appears at.
        var next: FactMap(usize) = .empty;
        defer next.deinit(allocator);
        for (facts, 0..) |fact, position| {
            const entry = try next.getOrPut(allocator, fact);
            if (!entry.found_existing) entry.value_ptr.* = position;
        }

        const index = self.named.getIndex(name);
        const previous: ?*FactSet = if (index) |at| &self.named.values()[at] else null;
        var changed = false;
        if (previous) |old| for (old.keys()) |fact| {
            if (next.contains(fact)) continue;
            changed = true;
            const at = self.support.getIndex(fact).?;
            const held = &self.support.values()[at];
            held.named -= 1;
            if (held.named != 0) continue;
            if (!held.direct) try relation_store.copyFactInto(allocator, gone, fact, false);
            const key = self.support.keys()[at];
            self.support.swapRemoveAt(at);
            allocator.free(key.terms);
        };

        for (next.keys(), next.values()) |fact, position| {
            if (previous) |old| if (old.contains(fact)) continue;
            changed = true;
            if (self.support.getPtr(fact)) |held| {
                held.named += 1;
                continue;
            }
            const present = try base.contains(fact);
            try self.support.ensureUnusedCapacity(allocator, 1);
            if (!present) try arriving.append(allocator, position);
            const terms = try allocator.dupe(relation_store.ValueId, fact.terms);
            self.support.putAssumeCapacityNoClobber(
                .{ .predicate = fact.predicate, .terms = terms },
                .{ .named = 1, .direct = present },
            );
        }

        // The contributor's set becomes `next`, keeping the terms of every
        // fact it already held rather than copying them again.
        var replacement: FactSet = .empty;
        errdefer freeSet(allocator, &replacement);
        try replacement.ensureTotalCapacity(allocator, next.count());
        for (next.keys()) |fact| {
            const kept = if (previous) |old| old.fetchSwapRemove(fact) else null;
            const terms = if (kept) |taken| taken.key.terms else try allocator.dupe(relation_store.ValueId, fact.terms);
            replacement.putAssumeCapacityNoClobber(.{ .predicate = fact.predicate, .terms = terms }, {});
        }
        if (previous) |old| freeSet(allocator, old);
        if (replacement.count() == 0) {
            if (index) |at| {
                const owned_name = self.named.keys()[at];
                self.named.swapRemoveAt(at);
                allocator.free(owned_name);
            }
            replacement.deinit(allocator);
            return changed;
        }
        if (previous) |old| {
            old.* = replacement;
        } else {
            const owned_name = try allocator.dupe(u8, name);
            errdefer allocator.free(owned_name);
            try self.named.putNoClobber(allocator, owned_name, replacement);
        }
        return changed;
    }

    /// The set of facts `name` asserts, made empty if it has none yet.
    fn contributor(self: *Contributions, allocator: std.mem.Allocator, name: []const u8) !*FactSet {
        if (self.named.getPtr(name)) |facts| return facts;
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);
        const entry = try self.named.getOrPutValue(allocator, owned_name, .empty);
        return entry.value_ptr;
    }
};

fn freeSet(allocator: std.mem.Allocator, facts: *FactSet) void {
    for (facts.keys()) |fact| allocator.free(fact.terms);
    facts.deinit(allocator);
    facts.* = .empty;
}

/// Copies a map keyed by facts, giving the copy terms of its own. The keys
/// hash the same in the copy, since their values are the same, so the index
/// comes across as it is.
fn cloneOwning(
    comptime Value: type,
    allocator: std.mem.Allocator,
    source: *const FactMap(Value),
) !FactMap(Value) {
    var result = try source.clone(allocator);
    var owned: usize = 0;
    errdefer {
        for (result.keys()[0..owned]) |fact| allocator.free(fact.terms);
        result.deinit(allocator);
    }
    for (result.keys()) |*fact| {
        fact.terms = try allocator.dupe(relation_store.ValueId, fact.terms);
        owned += 1;
    }
    return result;
}
