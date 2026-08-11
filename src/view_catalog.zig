//! What a fold is allowed to read: the views whose definitions it may reason
//! about, what each one stores, and which relations a plan may name directly.
//!
//! Folding is not a rewrite that always applies. It answers a question about
//! availability — the query names relations, the plan may only name what is
//! actually there — so the catalog is the half of the input that says what is
//! there. A view carries three separate things because a later phase needs
//! them separately: its *definition*, which is what inversion works on; its
//! *schema*, which is what the stored extension holds and is not always the
//! head's shape, since an aggregate column holds a list; and its
//! *availability*, which is policy and can be withdrawn without the definition
//! becoming unknown. Withdrawing one is what turns a fold that had a plan into
//! one that has none.
//!
//! The catalog owns the symbol table every definition's variables live in, and
//! hands it to the queries folded against it, so an identity means one thing
//! everywhere. Its identifiers — predicate names and constants — are the
//! *database's*: a catalog outliving the database it was built from resolves
//! nothing, which is the same rule that keeps value identifiers out of stored
//! plans.

const std = @import("std");
const fold_ir = @import("fold_ir.zig");
const relation_store = @import("relation_store.zig");
const syntax = @import("syntax.zig");

/// Whether a plan may read a view's stored extension. The definition is known
/// either way: a withheld view still says what it would have contained, which
/// is what lets a fold explain what it was missing.
pub const Availability = enum { materialized, withheld };

/// What one stored column holds. A column is a list when the definition puts a
/// list there — literally, or as the output of an aggregate — because that is
/// the column a later phase reconstructs member facts from rather than reads a
/// value out of.
pub const Column = struct {
    kind: enum { value, list },
};

pub const Schema = struct {
    columns: []Column,

    pub fn arity(self: Schema) usize {
        return self.columns.len;
    }
};

pub const View = struct {
    id: fold_ir.ViewId,
    /// The spelling the view prints under. It may be the same as a base
    /// relation's; the two never become the same predicate, because a view is
    /// identified by `id`.
    name: syntax.Id,
    /// The rule the view is defined by, with its head pointed at the view
    /// itself and every body goal at a base relation.
    definition: fold_ir.Rule,
    schema: Schema,
    availability: Availability,

    /// A relational goal reading this view's stored extension.
    pub fn predicate(self: *const View) fold_ir.Predicate {
        return .{ .view = .{
            .id = self.id,
            .name = self.name,
            .arity = self.schema.arity(),
        } };
    }

    pub fn readable(self: *const View) bool {
        return self.availability == .materialized;
    }
};

pub const Catalog = struct {
    allocator: std.mem.Allocator,
    /// The identities of every symbol in this catalog's definitions, and of
    /// the queries and plans that mention them.
    symbols: fold_ir.Symbols,
    views: std.ArrayList(View) = .empty,
    /// The base relations a plan may read directly. Empty is the honest
    /// default for folding: a fold exists because the original relations are
    /// not there, and one that helped itself to them would prove nothing.
    available_base: std.array_hash_map.Auto(relation_store.PredicateKey, void) = .empty,

    pub fn init(allocator: std.mem.Allocator) Catalog {
        return .{ .allocator = allocator, .symbols = .init(allocator) };
    }

    pub fn deinit(self: *Catalog) void {
        for (self.views.items) |defined| {
            fold_ir.freeRule(self.allocator, defined.definition);
            self.allocator.free(defined.schema.columns);
        }
        self.views.deinit(self.allocator);
        self.available_base.deinit(self.allocator);
        self.symbols.deinit();
        self.* = undefined;
    }

    /// Records a view defined by an admitted rule. The rule is lowered into a
    /// scope of its own and its head becomes the view's own predicate, so a
    /// definition can never be confused with the base relation it is spelled
    /// like.
    pub fn define(self: *Catalog, rule: syntax.Rule, availability: Availability) !fold_ir.ViewId {
        const id: fold_ir.ViewId = @enumFromInt(self.views.items.len);
        const scope = try self.symbols.openScope(.view_definition);
        var definition = try fold_ir.lowerRule(self.allocator, &self.symbols, scope, rule);
        errdefer fold_ir.freeRule(self.allocator, definition);

        const columns = try self.allocator.alloc(Column, definition.head.terms.len);
        errdefer self.allocator.free(columns);
        for (definition.head.terms, columns) |term, *column| {
            column.* = .{ .kind = if (isListColumn(term, definition.body)) .list else .value };
        }

        definition.head.predicate = .{ .view = .{
            .id = id,
            .name = rule.head.predicate,
            .arity = definition.head.terms.len,
        } };
        try self.views.append(self.allocator, .{
            .id = id,
            .name = rule.head.predicate,
            .definition = definition,
            .schema = .{ .columns = columns },
            .availability = availability,
        });
        return id;
    }

    pub fn view(self: *const Catalog, id: fold_ir.ViewId) *const View {
        return &self.views.items[@intFromEnum(id)];
    }

    /// Declares that a plan may read this base relation directly. A caller
    /// that has the original data and only wants folding where it helps says
    /// so here; F6's hybrid plans are this permission taken further.
    pub fn declareBaseAvailable(self: *Catalog, key: relation_store.PredicateKey) !void {
        try self.available_base.put(self.allocator, key, {});
    }

    pub fn baseAvailable(self: *const Catalog, key: relation_store.PredicateKey) bool {
        return self.available_base.contains(key);
    }

    /// Whether some view's body reads this base relation, which is what makes
    /// it a candidate for reconstruction. Saying so is not saying it can be
    /// reconstructed — that is the Inverse Method's answer, not the catalog's.
    pub fn definedByView(self: *const Catalog, key: relation_store.PredicateKey) bool {
        for (self.views.items) |candidate| {
            if (goalsRead(candidate.definition.body, key)) return true;
        }
        return false;
    }
};

/// Whether a head position holds a list: written as one, or bound by an
/// aggregate's output in the body.
fn isListColumn(term: fold_ir.Term, body: []const fold_ir.Goal) bool {
    return switch (term) {
        .nil, .cons => true,
        .variable => |variable| boundByAggregate(variable, body),
        else => false,
    };
}

fn boundByAggregate(variable: fold_ir.Variable, body: []const fold_ir.Goal) bool {
    for (body) |goal| switch (goal) {
        .aggregate => |aggregate| {
            if (aggregate.output == .variable and aggregate.output.variable == variable) return true;
            if (boundByAggregate(variable, aggregate.body)) return true;
        },
        else => {},
    };
    return false;
}

fn goalsRead(goals: []const fold_ir.Goal, key: relation_store.PredicateKey) bool {
    for (goals) |goal| switch (goal) {
        .relation => |relation| if (relation.predicate.equals(.{ .base = key })) return true,
        .aggregate => |aggregate| if (goalsRead(aggregate.body, key)) return true,
        .builtin => {},
    };
    return false;
}

const testing = std.testing;
const string_table = @import("string_table.zig");

test "a view is its own predicate, whatever it is spelled like" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const path = try strings.intern("path");
    const edge = try strings.intern("edge");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");

    // path(X, Y) :- edge(X, Y). The view is spelled like a base relation that
    // also exists, which must not make the two one predicate.
    var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var body_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var body = [_]syntax.Clause{.{ .relational = .{ .predicate = path, .terms = &body_terms } }};
    const id = try catalog.define(.{
        .head = .{ .predicate = path, .terms = &head_terms },
        .body = &body,
    }, .materialized);

    const view = catalog.view(id);
    try testing.expect(view.readable());
    try testing.expect(!view.predicate().equals(.{ .base = .{ .name = path, .arity = 2 } }));
    try testing.expect(view.definition.head.predicate.equals(view.predicate()));
    // The body still reads the base relation of that name, which is exactly
    // the pair the identity rule keeps apart.
    try testing.expect(catalog.definedByView(.{ .name = path, .arity = 2 }));
    try testing.expect(!catalog.definedByView(.{ .name = edge, .arity = 2 }));

    // Availability is policy over an unchanged definition.
    try testing.expect(!catalog.baseAvailable(.{ .name = path, .arity = 2 }));
    try catalog.declareBaseAvailable(.{ .name = path, .arity = 2 });
    try testing.expect(catalog.baseAvailable(.{ .name = path, .arity = 2 }));
}

test "an aggregate output is a list column, whatever the head spells it" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const total = try strings.intern("total");
    const score = try strings.intern("score");
    const x = try strings.intern("X");
    const s = try strings.intern("S");

    // total(X, S) :- setof(X, score(X, V), S). The stored column S holds a
    // list although the head only shows a variable.
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = score, .terms = &inner_terms } }};
    var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    var body = [_]syntax.Clause{.{ .aggregate = .{
        .template = .{ .variable = x },
        .body = &inner,
        .output = .{ .variable = s },
    } }};
    const id = try catalog.define(.{
        .head = .{ .predicate = total, .terms = &head_terms },
        .body = &body,
    }, .withheld);

    const view = catalog.view(id);
    try testing.expectEqual(@as(usize, 2), view.schema.arity());
    try testing.expectEqual(Column{ .kind = .value }, view.schema.columns[0]);
    try testing.expectEqual(Column{ .kind = .list }, view.schema.columns[1]);
    try testing.expect(!view.readable());
    try testing.expect(catalog.definedByView(.{ .name = score, .arity = 2 }));
}
