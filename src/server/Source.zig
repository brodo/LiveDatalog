//! One loaded `.dl` file: its text, its parsed program, and what the engine
//! needs to decide whether a new version can be applied incrementally.

const std = @import("std");
const LiveDatalog = @import("LiveDatalog");
const input = LiveDatalog.input;

const Source = @This();

text: []u8,
parsed: LiveDatalog.Parsed(LiveDatalog.Program),
/// The program's statements minus its queries, which a data file has no use
/// for. `runnable_index[i]` is the index of `runnable[i]` in the program.
runnable: []input.Statement,
runnable_index: []usize,
/// The source text of every rule, retraction and schema, in order. Two
/// versions of a file with the same key differ only in their facts.
rules_key: []u8,
has_retraction: bool,

pub const ParseError = struct {
    err: anyerror,
    diagnostic: LiveDatalog.Diagnostic,
};

/// Parses `text`, taking ownership of it on success.
pub fn parse(gpa: std.mem.Allocator, text: []u8, parse_error: *ParseError) !Source {
    var diagnostic: LiveDatalog.Diagnostic = .{};
    const parsed = LiveDatalog.parseProgram(gpa, text, &diagnostic) catch |err| {
        parse_error.* = .{ .err = err, .diagnostic = diagnostic };
        return err;
    };
    errdefer parsed.deinit();

    const program = parsed.value;
    var runnable: std.ArrayList(input.Statement) = .empty;
    errdefer runnable.deinit(gpa);
    var runnable_index: std.ArrayList(usize) = .empty;
    errdefer runnable_index.deinit(gpa);
    var rules_key: std.ArrayList(u8) = .empty;
    errdefer rules_key.deinit(gpa);
    var has_retraction = false;

    for (program.statements, program.spans, 0..) |statement, span, index| {
        switch (statement) {
            .query => continue,
            .fact => {},
            .rule, .retraction, .schema => {
                if (statement == .retraction) has_retraction = true;
                try rules_key.appendSlice(gpa, text[span.start..span.end]);
                try rules_key.append(gpa, '\n');
            },
        }
        try runnable.append(gpa, statement);
        try runnable_index.append(gpa, index);
    }

    return .{
        .text = text,
        .parsed = parsed,
        .runnable = try runnable.toOwnedSlice(gpa),
        .runnable_index = try runnable_index.toOwnedSlice(gpa),
        .rules_key = try rules_key.toOwnedSlice(gpa),
        .has_retraction = has_retraction,
    };
}

pub fn deinit(self: *Source, gpa: std.mem.Allocator) void {
    gpa.free(self.rules_key);
    gpa.free(self.runnable_index);
    gpa.free(self.runnable);
    self.parsed.deinit();
    gpa.free(self.text);
    self.* = undefined;
}

/// Whether a changed file differs from its old version only in its facts,
/// so that the new version can replace the old one's contribution.
pub fn incrementalWith(old: ?*const Source, new: ?*const Source) bool {
    const old_rules: []const u8 = if (old) |o| o.rules_key else "";
    const new_rules: []const u8 = if (new) |n| n.rules_key else "";
    return std.mem.eql(u8, old_rules, new_rules);
}

/// Iterates the facts of the program.
pub fn facts(self: *const Source) FactIterator {
    return .{ .statements = self.parsed.value.statements };
}

/// The facts of the program, in order, as one slice the caller frees.
pub fn collectFacts(self: *const Source, gpa: std.mem.Allocator) ![]input.Relation {
    var collected: std.ArrayList(input.Relation) = .empty;
    errdefer collected.deinit(gpa);
    var it = self.facts();
    while (it.next()) |fact| try collected.append(gpa, fact);
    return collected.toOwnedSlice(gpa);
}

pub const FactIterator = struct {
    statements: []const input.Statement,
    index: usize = 0,

    pub fn next(self: *FactIterator) ?input.Relation {
        while (self.index < self.statements.len) {
            defer self.index += 1;
            switch (self.statements[self.index]) {
                .fact => |fact| return fact,
                else => {},
            }
        }
        return null;
    }
};

/// Where statement `runnable_position` came from, for error messages.
pub fn diagnosticFor(self: *const Source, runnable_position: usize) LiveDatalog.Diagnostic {
    const index = self.runnable_index[runnable_position];
    return LiveDatalog.Diagnostic.at(self.text, self.parsed.value.spans[index], index, null);
}

test "only fact changes are incremental" {
    const gpa = std.testing.allocator;
    var parse_error: ParseError = undefined;
    var a = try parse(gpa, try gpa.dupe(u8, "e(a, b). r(X) :- e(X, _). r(X)?"), &parse_error);
    defer a.deinit(gpa);
    var b = try parse(gpa, try gpa.dupe(u8, "e(a, c).\nr(X) :- e(X, _)."), &parse_error);
    defer b.deinit(gpa);
    var c = try parse(gpa, try gpa.dupe(u8, "e(a, c). r(Y) :- e(Y, _)."), &parse_error);
    defer c.deinit(gpa);

    try std.testing.expectEqual(@as(usize, 2), a.runnable.len);
    try std.testing.expect(incrementalWith(&a, &b));
    try std.testing.expect(!incrementalWith(&a, &c));
    try std.testing.expect(!incrementalWith(null, &a));
}
