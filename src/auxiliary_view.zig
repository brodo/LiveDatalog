//! The auxiliary view a maintained aggregate rule keeps when its head
//! projects outer variables away.

const std = @import("std");
const errors = @import("errors.zig");
const syntax = @import("syntax.zig");
const relation_store = @import("relation_store.zig");

/// CReaM-style auxiliary view for a maintained aggregate rule whose head
/// projects out some of its outer-goal variables. Each tuple retains those
/// projected values followed by the head values they derive, so the number
/// of auxiliary tuples carrying a head tuple is that tuple's derivation
/// count. A projected head tuple becomes visible on a zero-to-one count
/// transition and is deleted on a one-to-zero transition.
pub const AuxiliaryView = struct {
    rule_id: u32,
    /// Outer-goal variables omitted from the head, in ascending id order.
    projected: []syntax.Id,
    head_arity: usize,
    tuples: relation_store.RelationStore,

    pub fn deinit(self: *AuxiliaryView, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
        allocator.free(self.projected);
        self.tuples.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const AuxiliaryView, allocator: std.mem.Allocator) !AuxiliaryView { // ziglint-ignore: Z023
        const projected = try allocator.dupe(syntax.Id, self.projected);
        errdefer allocator.free(projected);
        return .{
            .rule_id = self.rule_id,
            .projected = projected,
            .head_arity = self.head_arity,
            .tuples = try self.tuples.clone(),
        };
    }

    pub fn arity(self: *const AuxiliaryView) usize {
        return self.projected.len + self.head_arity;
    }

    pub fn key(self: *const AuxiliaryView) relation_store.PredicateKey {
        return .{ .name = self.rule_id, .arity = self.arity() };
    }

    /// How many auxiliary tuples carry `head`, which is its derivation count:
    /// the head tuple is visible exactly while this is non-zero. Reports
    /// `NumericOverflow` rather than wrapping when it exceeds the counter.
    pub fn derivationCount(self: *AuxiliaryView, head: []const relation_store.ValueId) !u32 {
        var mask: u64 = 0;
        var bound: [64]relation_store.ValueId = undefined;
        for (head, 0..) |term, index| {
            mask |= @as(u64, 1) << @intCast(self.projected.len + index);
            bound[index] = term;
        }
        const candidates = try self.tuples.lookup(self.key(), mask, bound[0..head.len]);
        var count: usize = 0;
        for (candidates) |candidate| {
            const tuple = self.tuples.factAt(candidate);
            if (std.mem.eql(relation_store.ValueId, self.headTerms(tuple), head)) count += 1;
        }
        return std.math.cast(u32, count) orelse errors.Error.NumericOverflow;
    }

    pub fn headTerms(self: *const AuxiliaryView, tuple: relation_store.Fact) []const relation_store.ValueId {
        return tuple.terms[self.projected.len..];
    }
};
