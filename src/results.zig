//! Query results and the values they carry.
//!
//! A result owns everything it exposes: names, scalars and structures are
//! copied out of the database when the answer is built, so results stay
//! valid after the database that produced them is destroyed. Nothing here
//! refers to a database, a rule or a term.

const std = @import("std");
const scalar = @import("scalar.zig");
// The database's error set. results.zig is a leaf otherwise; this is the
// one name it borrows back so public accessors share one error type.
const Error = @import("root.zig").Error;

pub const ResultNode = union(enum) {
    atom: []u8,
    integer: i64,
    float: f64,
    nil,
    cons: *ResultCons,
};

pub const ResultCons = struct {
    head: *ResultNode,
    tail: *ResultNode,
};

pub const ResultValue = struct {
    node: *const ResultNode,

    pub const Kind = enum { atom, integer, float, nil, cons };

    pub fn kind(self: ResultValue) Kind {
        return switch (self.node.*) {
            .atom => .atom,
            .integer => .integer,
            .float => .float,
            .nil => .nil,
            .cons => .cons,
        };
    }

    pub fn getAtom(self: ResultValue) Error![]const u8 {
        return switch (self.node.*) {
            .atom => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn getInteger(self: ResultValue) Error!i64 {
        return switch (self.node.*) {
            .integer => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn getFloat(self: ResultValue) Error!f64 {
        return switch (self.node.*) {
            .float => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn head(self: ResultValue) Error!ResultValue {
        return switch (self.node.*) {
            .cons => |pair| .{ .node = pair.head },
            else => Error.TypeMismatch,
        };
    }

    pub fn tail(self: ResultValue) Error!ResultValue {
        return switch (self.node.*) {
            .cons => |pair| .{ .node = pair.tail },
            else => Error.TypeMismatch,
        };
    }

    pub fn formatAlloc(self: ResultValue, allocator: std.mem.Allocator) ![]u8 {
        var output: std.Io.Writer.Allocating = .init(allocator);
        defer output.deinit();
        self.write(&output.writer) catch return error.OutOfMemory;
        return output.toOwnedSlice();
    }

    pub fn write(self: ResultValue, writer: *std.Io.Writer) !void {
        switch (self.node.*) {
            .atom => |value| {
                try scalar.writeAtom(writer, value);
            },
            .integer => |value| try writer.print("{d}", .{value}),
            .float => |value| try scalar.writeFloat(writer, value),
            .nil => try writer.writeAll("[]"),
            .cons => |pair| if (isProperResultList(self.node)) {
                try writer.writeByte('[');
                var current = self.node;
                var first = true;
                while (current.* == .cons) {
                    if (!first) try writer.writeAll(", ");
                    try (ResultValue{ .node = current.cons.head }).write(writer);
                    current = current.cons.tail;
                    first = false;
                }
                try writer.writeByte(']');
            } else {
                try writer.writeAll("cons(");
                try (ResultValue{ .node = pair.head }).write(writer);
                try writer.writeAll(", ");
                try (ResultValue{ .node = pair.tail }).write(writer);
                try writer.writeByte(')');
            },
        }
    }
};

pub fn isProperResultList(root: *const ResultNode) bool {
    var current = root;
    while (true) switch (current.*) {
        .nil => return true,
        .cons => |pair| current = pair.tail,
        else => return false,
    };
}

pub fn freeResultNode(allocator: std.mem.Allocator, node: *ResultNode) void {
    switch (node.*) {
        .atom => |atom| allocator.free(atom),
        .integer, .float, .nil => {},
        .cons => |pair| {
            freeResultNode(allocator, pair.head);
            freeResultNode(allocator, pair.tail);
            allocator.destroy(pair);
        },
    }
    allocator.destroy(node);
}

pub const Answer = struct {
    allocator: std.mem.Allocator,
    bindings: std.ArrayList(ResultBinding) = .empty,

    pub const ResultBinding = struct {
        name: []u8,
        value: ResultValue,
    };

    pub fn deinit(self: *Answer) void {
        for (self.bindings.items) |binding| {
            self.allocator.free(binding.name);
            freeResultNode(self.allocator, @constCast(binding.value.node));
        }
        self.bindings.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn getValue(self: *const Answer, variable: []const u8) Error!ResultValue {
        for (self.bindings.items) |binding|
            if (std.mem.eql(u8, binding.name, variable)) return binding.value;
        // Not inferrable: in an `Error!ResultValue` return the enum literal
        // resolves against the payload type, not the error set.
        return Error.UnknownVariable; // ziglint-ignore: Z010
    }

    pub fn getAtom(self: *const Answer, variable: []const u8) Error![]const u8 {
        return (try self.getValue(variable)).getAtom();
    }

    pub fn getInteger(self: *const Answer, variable: []const u8) Error!i64 {
        return (try self.getValue(variable)).getInteger();
    }

    pub fn getFloat(self: *const Answer, variable: []const u8) Error!f64 {
        return (try self.getValue(variable)).getFloat();
    }
};

pub const QueryResult = struct {
    allocator: std.mem.Allocator,
    answers: std.ArrayList(Answer) = .empty,

    pub fn deinit(self: *QueryResult) void {
        for (self.answers.items) |*answer| answer.deinit();
        self.answers.deinit(self.allocator);
        self.* = undefined;
    }
};

pub const ExecutionResult = union(enum) {
    none,
    changed: bool,
    query: QueryResult,

    pub fn deinit(self: *ExecutionResult) void {
        switch (self.*) {
            .query => |*result| result.deinit(),
            else => {},
        }
        self.* = undefined;
    }
};
