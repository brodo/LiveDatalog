const std = @import("std");

pub const Id = enum(u64) { _ };

pub const Value = union(enum) {
    atom: []u8,
    integer: i64,
    float: f64,
};

const two_pow_63: f64 = 9223372036854775808.0;

pub const Store = struct {
    allocator: std.mem.Allocator,
    values: std.ArrayList(Value) = .empty,

    pub fn init(allocator: std.mem.Allocator) Store {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Store) void {
        for (self.values.items) |value| switch (value) {
            .atom => |atom| self.allocator.free(atom),
            .integer, .float => {},
        };
        self.values.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const Store) !Store {
        var result: Store = .init(self.allocator);
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
        return result;
    }

    pub fn internAtom(self: *Store, atom: []const u8) !Id {
        for (self.values.items, 0..) |value, index| switch (value) {
            .atom => |existing| if (std.mem.eql(u8, existing, atom)) return @enumFromInt(index),
            .integer, .float => {},
        };
        const owned = try self.allocator.dupe(u8, atom);
        errdefer self.allocator.free(owned);
        try self.values.append(self.allocator, .{ .atom = owned });
        return @enumFromInt(self.values.items.len - 1);
    }

    pub fn internInteger(self: *Store, number: i64) !Id {
        for (self.values.items, 0..) |value, index| switch (value) {
            .integer => |existing| if (existing == number) return @enumFromInt(index),
            .atom, .float => {},
        };
        try self.values.append(self.allocator, .{ .integer = number });
        return @enumFromInt(self.values.items.len - 1);
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
        for (self.values.items, 0..) |value, index| switch (value) {
            .float => |existing| if (existing == number) return @enumFromInt(index),
            .atom, .integer => {},
        };
        try self.values.append(self.allocator, .{ .float = number });
        return @enumFromInt(self.values.items.len - 1);
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

    pub fn getInteger(self: *const Store, id: Id) !i64 {
        return switch (self.get(id)) {
            .integer => |value| value,
            .atom, .float => error.NumericType,
        };
    }

    pub fn add(self: *Store, left: Id, right: Id) !Id {
        const value = std.math.add(i64, try self.getInteger(left), try self.getInteger(right)) catch
            return error.NumericOverflow;
        return self.internInteger(value);
    }

    pub fn subtract(self: *Store, left: Id, right: Id) !Id {
        const value = std.math.sub(i64, try self.getInteger(left), try self.getInteger(right)) catch
            return error.NumericOverflow;
        return self.internInteger(value);
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
