//! Transactional lowering helpers for borrowed typed input.
//!
//! The caller supplies a staging builder. This module owns recursive descriptor
//! validation and never retains a pointer into caller memory.
const std = @import("std");
const input = @import("input.zig");

const TermSlice = struct {
    pointer: [*]const input.Term,
    length: usize,
};

const GoalSlice = struct {
    pointer: [*]const input.Goal,
    length: usize,
};

const Validator = struct {
    allocator: std.mem.Allocator,
    active_cons: std.AutoHashMapUnmanaged(*const input.Term.Cons, void) = .empty,
    active_lists: std.AutoHashMapUnmanaged(TermSlice, void) = .empty,
    active_goal_bodies: std.AutoHashMapUnmanaged(GoalSlice, void) = .empty,

    fn deinit(self: *Validator) void {
        self.active_cons.deinit(self.allocator);
        self.active_lists.deinit(self.allocator);
        self.active_goal_bodies.deinit(self.allocator);
        self.* = undefined;
    }

    fn term(self: *Validator, descriptor: input.Term) !void {
        switch (descriptor) {
            .atom, .integer, .float => {},
            .variable => |name| if (name.len == 0) return error.InvalidTerm,
            .list => |items| {
                if (items.len == 0) return;
                const key: TermSlice = .{ .pointer = items.ptr, .length = items.len };
                if (self.active_lists.contains(key)) return error.InvalidTerm;
                try self.active_lists.put(self.allocator, key, {});
                defer _ = self.active_lists.remove(key);
                for (items) |item| try self.term(item);
            },
            .cons => |pair| {
                if (self.active_cons.contains(pair)) return error.InvalidTerm;
                try self.active_cons.put(self.allocator, pair, {});
                defer _ = self.active_cons.remove(pair);
                try self.term(pair.head.*);
                try self.term(pair.tail.*);
            },
        }
    }

    fn goals(self: *Validator, descriptors: []const input.Goal) !void {
        if (descriptors.len == 0) return;
        const key: GoalSlice = .{ .pointer = descriptors.ptr, .length = descriptors.len };
        if (self.active_goal_bodies.contains(key)) return error.InvalidTerm;
        try self.active_goal_bodies.put(self.allocator, key, {});
        defer _ = self.active_goal_bodies.remove(key);
        for (descriptors) |descriptor| switch (descriptor) {
            .relation, .negation => |relation| {
                if (relation.predicate.len == 0) return error.InvalidTerm;
                for (relation.terms) |term_descriptor| try self.term(term_descriptor);
            },
            .equality, .inequality => |binary| {
                try self.term(binary.left);
                try self.term(binary.right);
            },
            .negated_builtin => |builtin| switch (builtin) {
                .equality, .inequality => |binary| {
                    try self.term(binary.left);
                    try self.term(binary.right);
                },
                .comparison => |comparison| {
                    try self.term(comparison.operands.left);
                    try self.term(comparison.operands.right);
                },
                .type_test => |type_test| try self.term(type_test.term),
            },
            .type_test => |type_test| try self.term(type_test.term),
            .comparison => |comparison| {
                try self.term(comparison.operands.left);
                try self.term(comparison.operands.right);
            },
            .arithmetic => |arithmetic| {
                try self.term(arithmetic.output);
                try self.term(arithmetic.left);
                try self.term(arithmetic.right);
            },
            .aggregate => |aggregate| {
                try self.term(aggregate.template);
                try self.goals(aggregate.body);
                try self.term(aggregate.output);
            },
        };
    }
};

pub fn validateGoals(allocator: std.mem.Allocator, descriptors: []const input.Goal) !void {
    var validator: Validator = .{ .allocator = allocator };
    defer validator.deinit();
    try validator.goals(descriptors);
}

pub fn compileTerm(builder: anytype, descriptor: input.Term) !@TypeOf(builder.nilTerm()) {
    var validator: Validator = .{ .allocator = builder.allocator() };
    defer validator.deinit();
    try validator.term(descriptor);
    var active: std.AutoHashMapUnmanaged(*const input.Term.Cons, void) = .empty;
    defer active.deinit(builder.allocator());
    return compileTermInner(builder, descriptor, &active);
}

pub fn compileTerms(builder: anytype, descriptors: []const input.Term) ![]@TypeOf(builder.nilTerm()) {
    var validator: Validator = .{ .allocator = builder.allocator() };
    defer validator.deinit();
    for (descriptors) |descriptor| try validator.term(descriptor);
    const terms = try builder.allocator().alloc(@TypeOf(builder.nilTerm()), descriptors.len);
    var initialized: usize = 0;
    errdefer {
        for (terms[0..initialized]) |term| builder.releaseTerm(term);
        builder.allocator().free(terms);
    }
    for (descriptors, terms) |descriptor, *term| {
        var active: std.AutoHashMapUnmanaged(*const input.Term.Cons, void) = .empty;
        defer active.deinit(builder.allocator());
        term.* = try compileTermInner(builder, descriptor, &active);
        initialized += 1;
    }
    return terms;
}

fn compileTermInner(
    builder: anytype,
    descriptor: input.Term,
    active: *std.AutoHashMapUnmanaged(*const input.Term.Cons, void),
) !@TypeOf(builder.nilTerm()) {
    return switch (descriptor) {
        .atom => |atom| builder.atomTerm(atom),
        .integer => |integer| builder.integerTerm(integer),
        .float => |float| builder.floatTerm(float),
        .variable => |name| if (name.len == 0) error.InvalidTerm else builder.variableTerm(name),
        .list => |items| blk: {
            var result = builder.nilTerm();
            var index = items.len;
            while (index > 0) {
                index -= 1;
                const head = compileTermInner(builder, items[index], active) catch |err| {
                    builder.releaseTerm(result);
                    return err;
                };
                result = builder.consTerm(head, result) catch |err| {
                    builder.releaseTerm(head);
                    builder.releaseTerm(result);
                    return err;
                };
            }
            break :blk result;
        },
        .cons => |pair| blk: {
            if (active.contains(pair)) return error.InvalidTerm;
            try active.put(builder.allocator(), pair, {});
            defer _ = active.remove(pair);
            const head = try compileTermInner(builder, pair.head.*, active);
            errdefer builder.releaseTerm(head);
            const tail = try compileTermInner(builder, pair.tail.*, active);
            errdefer builder.releaseTerm(tail);
            break :blk try builder.consTerm(head, tail);
        },
    };
}
