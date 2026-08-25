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

/// Where a view's definition came from.
///
/// A definition the caller wrote down says what it says for as long as the
/// catalog lives. One taken from a rule the database maintains says what that
/// rule says, and a later rule addition can change what the predicate means —
/// so the rule generation it was read at is kept, and a fold against a catalog
/// that has fallen behind is refused rather than answered from a definition
/// the database no longer holds.
pub const Source = union(enum) {
    declared,
    materialized_rule: u32,
};

/// Two readable extensions a plan could not tell apart, because they store
/// under one name and arity.
pub const Ambiguity = struct {
    view: fold_ir.ViewId,
    rival: union(enum) { view: fold_ir.ViewId, base },
};

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
    source: Source,

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

    /// Whether this view is a *canonical aggregate view* of `key`, in the
    /// sense of Definition 6.4.3.
    ///
    /// It matters because of what such a view remembers. Inverting an ordinary
    /// view reconstructs a relation only as far as the view's tuples prove it,
    /// which is why a plan may not read the result under negation or inside an
    /// aggregate. A canonical view of a relation groups that relation by a
    /// subset of its columns and collects *everything* in each group, so
    /// reading its lists back out returns the relation itself — Lemma 6.4.2 —
    /// and there is then nothing incomplete left to ask about.
    ///
    /// There are two shapes and `2^n` of them for an n-ary relation. One is
    /// the relation copied: `v(X1, ..., Xn) :- r(X1, ..., Xn)`. The other
    /// keeps `k < n` of the columns and collects the rest:
    ///
    /// ```text
    /// v(Xi1, ..., Xik, S) :- r(X1, ..., Xn), setof(Ȳ, r(Z̄), S)
    /// ```
    ///
    /// where `i1 < ... < ik`, the collected `Z̄` writes `Xj` in a kept column
    /// and a variable of its own in every other, and `Ȳ` is those other
    /// variables in column order — one of them bare, several of them consed
    /// together, which is how Example 6.4.2 writes the pair case.
    pub fn isCanonicalFor(self: *const View, key: relation_store.PredicateKey) bool {
        const definition = self.definition;
        if (definition.seed_argument != null) return false;
        if (definition.body.len == 0 or definition.body.len > 2) return false;

        const outer = positiveRead(definition.body[0], key) orelse return false;
        if (!distinctVariables(outer)) return false;
        if (definition.body.len == 1) {
            // v(X1, ..., Xn) :- r(X1, ..., Xn): every column kept, in order.
            return sameVariables(definition.head.terms, outer);
        }

        const aggregate = switch (definition.body[1]) {
            .aggregate => |value| value,
            else => return false,
        };
        if (aggregate.body.len != 1) return false;
        const collected = positiveRead(aggregate.body[0], key) orelse return false;
        if (!distinctVariables(collected)) return false;
        // The head keeps the columns the aggregate did not collect, in their
        // own order, and the collected list last.
        if (definition.head.terms.len == 0) return false;
        const kept = definition.head.terms[0 .. definition.head.terms.len - 1];
        const output = definition.head.terms[definition.head.terms.len - 1];
        if (output != .variable) return false;
        if (aggregate.output != .variable or aggregate.output.variable != output.variable)
            return false;
        if (kept.len >= outer.len) return false;

        // Walk the relation's columns once: a kept column carries the outer
        // goal's variable in both goals, and every other carries a variable of
        // the aggregate's own, which the template collects in this same order.
        var template = aggregate.template;
        var next_kept: usize = 0;
        var collecting: usize = 0;
        const projected = outer.len - kept.len;
        for (outer, collected) |stored, gathered| {
            if (gathered == .variable and stored == .variable and
                gathered.variable == stored.variable)
            {
                if (next_kept == kept.len) return false;
                if (kept[next_kept] != .variable or kept[next_kept].variable != stored.variable)
                    return false;
                next_kept += 1;
                continue;
            }
            collecting += 1;
            // The last collected column ends the template; the others are the
            // heads of its cons cells.
            const element = if (collecting == projected) template else blk: {
                if (template != .cons) return false;
                const pair = template.cons;
                template = pair.tail;
                break :blk pair.head;
            };
            if (element != .variable or gathered != .variable) return false;
            if (element.variable != gathered.variable) return false;
        }
        return next_kept == kept.len;
    }
};

/// The terms of a positive goal reading `key`, or null for anything else.
fn positiveRead(goal: fold_ir.Goal, key: relation_store.PredicateKey) ?[]const fold_ir.Term {
    const relation = switch (goal) {
        .relation => |value| value,
        else => return null,
    };
    if (relation.negated) return null;
    if (!relation.predicate.equals(.{ .base = key })) return null;
    return relation.terms;
}

/// Whether these terms are variables, no two of them the same. A canonical
/// view reads the whole relation and nothing narrower, so a repeated column or
/// a constant is a different view.
fn distinctVariables(terms: []const fold_ir.Term) bool {
    for (terms, 0..) |term, index| {
        if (term != .variable) return false;
        for (terms[0..index]) |earlier| {
            if (earlier.variable == term.variable) return false;
        }
    }
    return true;
}

fn sameVariables(left: []const fold_ir.Term, right: []const fold_ir.Term) bool {
    if (left.len != right.len) return false;
    for (left, right) |one, other| {
        if (one != .variable or other != .variable) return false;
        if (one.variable != other.variable) return false;
    }
    return true;
}

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
    /// Counts every change to what a fold is allowed to read: a definition
    /// added, an availability withdrawn or restored, a base relation declared.
    ///
    /// The counter lives here because the thing it counts does. Nothing else
    /// can change a fold's input except the query itself, so one number is the
    /// whole of "these definitions under this policy" — which is what a plan
    /// cache above has to key on and what tells it, in one comparison, that
    /// every plan it holds was folded against something else.
    generation: u64 = 0,
    /// Where the views' stored extensions actually are, borrowed for as long
    /// as this catalog lives, or null when nobody said.
    ///
    /// A fold uses this for one thing: choosing between plans already proved
    /// to answer the same. Cost never decides *what* a plan may read — that is
    /// availability, above — so a catalog without a store folds to the same
    /// answers, only without preferring the smaller of two interchangeable
    /// views. It is a fact store rather than a `*Database` because sizes are
    /// all a fold has any business with, which is what keeps the folding
    /// modules where ADR 0002 put them.
    extensions: ?*relation_store.RelationStore = null,

    pub fn init(allocator: std.mem.Allocator) Catalog {
        return .{ .allocator = allocator, .symbols = .init(allocator) };
    }

    /// A copy sharing nothing with this one, for a database cloned out from
    /// under it. Identities survive because both tables hand out the same
    /// ones; the borrowed extension store does not, because it belonged to the
    /// original database and the copy's caller has to point this at its own.
    pub fn clone(self: *const Catalog) !Catalog {
        var result: Catalog = .{
            .allocator = self.allocator,
            .symbols = try self.symbols.clone(),
            .generation = self.generation,
        };
        errdefer result.deinit();
        try result.views.ensureTotalCapacityPrecise(self.allocator, self.views.items.len);
        for (self.views.items) |defined| {
            const definition = try fold_ir.cloneRule(self.allocator, defined.definition);
            errdefer fold_ir.freeRule(self.allocator, definition);
            const columns = try self.allocator.dupe(Column, defined.schema.columns);
            result.views.appendAssumeCapacity(.{
                .id = defined.id,
                .name = defined.name,
                .definition = definition,
                .schema = .{ .columns = columns },
                .availability = defined.availability,
                .source = defined.source,
            });
        }
        try result.available_base.ensureTotalCapacity(self.allocator, self.available_base.count());
        for (self.available_base.keys()) |key| result.available_base.putAssumeCapacity(key, {});
        return result;
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
        return self.defineFrom(rule, availability, .declared);
    }

    /// Records a view and where its definition came from. `define` is this
    /// with `.declared`; a definition read out of a database rule says so, so
    /// that a later rule addition can be noticed rather than folded against.
    pub fn defineFrom(
        self: *Catalog,
        rule: syntax.Rule,
        availability: Availability,
        source: Source,
    ) !fold_ir.ViewId {
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
            .source = source,
        });
        self.generation += 1;
        return id;
    }

    pub fn view(self: *const Catalog, id: fold_ir.ViewId) *const View {
        return &self.views.items[@intFromEnum(id)];
    }

    /// Withdraws or restores a view's extension. The definition is untouched:
    /// a withheld view still says what it would have contained, which is what
    /// lets a fold report what it was missing.
    pub fn setAvailability(self: *Catalog, id: fold_ir.ViewId, availability: Availability) void {
        const defined = &self.views.items[@intFromEnum(id)];
        if (defined.availability == availability) return;
        defined.availability = availability;
        self.generation += 1;
    }

    /// The first view whose definition was read out of a database rule that
    /// has since been added to, or null when every published definition is
    /// still the one the database holds.
    ///
    /// A rule addition can change what a predicate means, and a catalog cannot
    /// see it happen — so this is asked at the point a fold would otherwise
    /// reason from a definition the database has moved on from.
    pub fn staleAt(self: *const Catalog, rule_generation: u32) ?fold_ir.ViewId {
        for (self.views.items) |defined| switch (defined.source) {
            .declared => {},
            .materialized_rule => |generation| if (generation != rule_generation) return defined.id,
        };
        return null;
    }

    /// Two readable extensions storing under one name and arity, or null.
    ///
    /// A lowered plan names what it reads by the name the extension is stored
    /// under, so a selection holding two of them under one name cannot be
    /// executed whatever is asked of it. That makes it a property of the
    /// selection rather than of a fold, which is why it is answered here and
    /// before anything is folded.
    pub fn ambiguity(self: *const Catalog) ?Ambiguity {
        for (self.views.items, 0..) |defined, index| {
            if (!defined.readable()) continue;
            const key: relation_store.PredicateKey = .{
                .name = defined.name,
                .arity = defined.schema.arity(),
            };
            if (self.available_base.contains(key))
                return .{ .view = defined.id, .rival = .base };
            for (self.views.items[index + 1 ..]) |rival| {
                if (!rival.readable()) continue;
                if (rival.name != defined.name) continue;
                if (rival.schema.arity() != key.arity) continue;
                return .{ .view = defined.id, .rival = .{ .view = rival.id } };
            }
        }
        return null;
    }

    /// How many facts the store holds under this name and arity, or zero when
    /// no store was supplied. Only ever compared against another such number.
    pub fn cardinality(self: *const Catalog, key: relation_store.PredicateKey) !usize {
        const store = self.extensions orelse return 0;
        return (try store.predicateEntries(key)).len;
    }

    /// How many facts a view's stored extension holds.
    pub fn extent(self: *const Catalog, id: fold_ir.ViewId) !usize {
        const defined = self.view(id);
        return self.cardinality(.{ .name = defined.name, .arity = defined.schema.arity() });
    }

    /// Declares that a plan may read this base relation directly. A caller
    /// that has the original data and only wants folding where it helps says
    /// so here; F6's hybrid plans are this permission taken further.
    pub fn declareBaseAvailable(self: *Catalog, key: relation_store.PredicateKey) !void {
        const entry = try self.available_base.getOrPut(self.allocator, key);
        if (!entry.found_existing) self.generation += 1;
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

test "the canonical aggregate views of a binary relation are the four of Example 6.4.2" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const r = try strings.intern("r");
    const t = try strings.intern("t");
    const x1 = try strings.intern("X1");
    const x2 = try strings.intern("X2");
    const y1 = try strings.intern("Y1");
    const y2 = try strings.intern("Y2");
    const s = try strings.intern("S");
    const key: relation_store.PredicateKey = .{ .name = r, .arity = 2 };

    var outer = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = x2 } };
    var outer_goal = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &outer } },
    };

    // v1(S) :- r(X1, X2), setof(Y1!Y2, r(Y1, Y2), S). Every column collected,
    // so the whole relation is one stored list.
    var both = [_]syntax.Term{ .{ .variable = y1 }, .{ .variable = y2 } };
    var both_goal = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &both } }};
    var pair: syntax.Term.Cons = .{ .head = .{ .variable = y1 }, .tail = .{ .variable = y2 } };
    var v1_head = [_]syntax.Term{.{ .variable = s }};
    var v1_body = [_]syntax.Clause{
        outer_goal[0],
        .{ .aggregate = .{
            .template = .{ .cons = &pair },
            .body = &both_goal,
            .output = .{ .variable = s },
        } },
    };
    const v1 = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("v1"), .terms = &v1_head },
        .body = &v1_body,
    }, .materialized);
    try testing.expect(catalog.view(v1).isCanonicalFor(key));

    // v2(X1, S) :- r(X1, X2), setof(Y2, r(X1, Y2), S). Grouped by the first
    // column, collecting the second.
    var by_first = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = y2 } };
    var by_first_goal = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &by_first } },
    };
    var v2_head = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = s } };
    var v2_body = [_]syntax.Clause{
        outer_goal[0],
        .{ .aggregate = .{
            .template = .{ .variable = y2 },
            .body = &by_first_goal,
            .output = .{ .variable = s },
        } },
    };
    const v2 = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("v2"), .terms = &v2_head },
        .body = &v2_body,
    }, .materialized);
    try testing.expect(catalog.view(v2).isCanonicalFor(key));

    // v3(X2, S) :- r(X1, X2), setof(Y1, r(Y1, X2), S). The other grouping, and
    // the one that proves the kept column is found by position rather than by
    // being first.
    var by_second = [_]syntax.Term{ .{ .variable = y1 }, .{ .variable = x2 } };
    var by_second_goal = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &by_second } },
    };
    var v3_head = [_]syntax.Term{ .{ .variable = x2 }, .{ .variable = s } };
    var v3_body = [_]syntax.Clause{
        outer_goal[0],
        .{ .aggregate = .{
            .template = .{ .variable = y1 },
            .body = &by_second_goal,
            .output = .{ .variable = s },
        } },
    };
    const v3 = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("v3"), .terms = &v3_head },
        .body = &v3_body,
    }, .materialized);
    try testing.expect(catalog.view(v3).isCanonicalFor(key));

    // v4(X1, X2) :- r(X1, X2). The relation copied.
    const v4 = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("v4"), .terms = &outer },
        .body = outer_goal[0..1],
    }, .materialized);
    try testing.expect(catalog.view(v4).isCanonicalFor(key));

    // None of them is canonical for a relation they never read, which is the
    // condition that matters: a view mentioning a relation is not a view that
    // remembers all of it.
    const other: relation_store.PredicateKey = .{ .name = t, .arity = 2 };
    for ([_]fold_ir.ViewId{ v1, v2, v3, v4 }) |id|
        try testing.expect(!catalog.view(id).isCanonicalFor(other));
}

test "a view that collects less than the whole relation is not canonical for it" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const r = try strings.intern("r");
    const p = try strings.intern("p");
    const x1 = try strings.intern("X1");
    const x2 = try strings.intern("X2");
    const y2 = try strings.intern("Y2");
    const s = try strings.intern("S");
    const key: relation_store.PredicateKey = .{ .name = r, .arity = 2 };

    var outer = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = x2 } };
    var by_first = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = y2 } };
    var by_first_goal = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &by_first } },
    };
    var head = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = s } };

    // narrowed(X1, S) :- p(X1, X2), setof(Y2, r(X1, Y2), S). The list holds
    // every `r` for its key, but only the keys `p` admits have a list at all,
    // so what comes back is `r` restricted rather than `r`.
    var narrowed_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = p, .terms = &outer } },
        .{ .aggregate = .{
            .template = .{ .variable = y2 },
            .body = &by_first_goal,
            .output = .{ .variable = s },
        } },
    };
    const narrowed = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("narrowed"), .terms = &head },
        .body = &narrowed_body,
    }, .materialized);
    try testing.expect(!catalog.view(narrowed).isCanonicalFor(key));

    // filtered(X1, S) :- r(X1, X1), setof(Y2, r(X1, Y2), S). A repeated column
    // is a narrower read of the same relation, and narrower is not canonical.
    var repeated = [_]syntax.Term{ .{ .variable = x1 }, .{ .variable = x1 } };
    var filtered_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &repeated } },
        .{ .aggregate = .{
            .template = .{ .variable = y2 },
            .body = &by_first_goal,
            .output = .{ .variable = s },
        } },
    };
    const filtered = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("filtered"), .terms = &head },
        .body = &filtered_body,
    }, .materialized);
    try testing.expect(!catalog.view(filtered).isCanonicalFor(key));

    // grouped(X2, S) :- r(X1, X2), setof(Y2, r(X1, Y2), S). Grouped by one
    // column and collecting by another: the head does not name the column the
    // aggregate kept fixed, so a stored list says nothing about which key it
    // belongs to.
    var mismatched = [_]syntax.Term{ .{ .variable = x2 }, .{ .variable = s } };
    var grouped_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &outer } },
        .{ .aggregate = .{
            .template = .{ .variable = y2 },
            .body = &by_first_goal,
            .output = .{ .variable = s },
        } },
    };
    const grouped = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("grouped"), .terms = &mismatched },
        .body = &grouped_body,
    }, .materialized);
    try testing.expect(!catalog.view(grouped).isCanonicalFor(key));

    // copied(X1) :- r(X1, X2). A projection is not a copy.
    var narrow_head = [_]syntax.Term{.{ .variable = x1 }};
    var outer_goal = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &outer } }};
    const copied = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("copied"), .terms = &narrow_head },
        .body = &outer_goal,
    }, .materialized);
    try testing.expect(!catalog.view(copied).isCanonicalFor(key));
}

test "a catalog counts every change to what a fold may read" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const path = try strings.intern("path");
    const edge = try strings.intern("edge");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var body_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var body = [_]syntax.Clause{.{ .relational = .{ .predicate = edge, .terms = &body_terms } }};

    try testing.expectEqual(@as(u64, 0), catalog.generation);
    const id = try catalog.define(.{
        .head = .{ .predicate = path, .terms = &head_terms },
        .body = &body,
    }, .materialized);
    try testing.expectEqual(@as(u64, 1), catalog.generation);

    // Withdrawing an extension changes every plan folded under the policy, so
    // it counts; setting it to what it already was changes none, so it does
    // not, and a cache above is not asked to discard anything.
    catalog.setAvailability(id, .materialized);
    try testing.expectEqual(@as(u64, 1), catalog.generation);
    catalog.setAvailability(id, .withheld);
    try testing.expectEqual(@as(u64, 2), catalog.generation);
    try testing.expect(!catalog.view(id).readable());
    // The definition survives the withdrawal, which is what lets a fold report
    // the view it was missing rather than the relation.
    try testing.expect(catalog.definedByView(.{ .name = edge, .arity = 2 }));

    try catalog.declareBaseAvailable(.{ .name = edge, .arity = 2 });
    try testing.expectEqual(@as(u64, 3), catalog.generation);
    try catalog.declareBaseAvailable(.{ .name = edge, .arity = 2 });
    try testing.expectEqual(@as(u64, 3), catalog.generation);
}

test "two readable extensions under one name are found before anything is folded" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const v = try strings.intern("v");
    const edge = try strings.intern("edge");
    const other = try strings.intern("other");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    var terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var from_edge = [_]syntax.Clause{.{ .relational = .{ .predicate = edge, .terms = &terms } }};
    var from_other = [_]syntax.Clause{.{ .relational = .{ .predicate = other, .terms = &terms } }};

    const first = try catalog.define(.{
        .head = .{ .predicate = v, .terms = &terms },
        .body = &from_edge,
    }, .materialized);
    try testing.expect(catalog.ambiguity() == null);
    const second = try catalog.define(.{
        .head = .{ .predicate = v, .terms = &terms },
        .body = &from_other,
    }, .materialized);

    // Two stored extensions under `v/2`: a plan naming one of them names both.
    const clash = catalog.ambiguity().?;
    try testing.expectEqual(first, clash.view);
    try testing.expectEqual(second, clash.rival.view);

    // Withholding one leaves one readable extension of that name, and the
    // question a plan could not have answered no longer arises.
    catalog.setAvailability(second, .withheld);
    try testing.expect(catalog.ambiguity() == null);

    // A declared base relation of the same name and arity is the same clash
    // from the other side.
    try catalog.declareBaseAvailable(.{ .name = v, .arity = 2 });
    try testing.expectEqual(Ambiguity{ .view = first, .rival = .base }, catalog.ambiguity().?);
}

test "a published definition is only as current as the rule it was read from" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const two = try strings.intern("two");
    const edge = try strings.intern("edge");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    var terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var body = [_]syntax.Clause{.{ .relational = .{ .predicate = edge, .terms = &terms } }};
    const rule: syntax.Rule = .{
        .head = .{ .predicate = two, .terms = &terms },
        .body = &body,
    };

    const declared = try catalog.define(rule, .materialized);
    // A definition the caller wrote down says what it says forever, whatever
    // the database's rules do afterwards.
    try testing.expect(catalog.staleAt(7) == null);

    const published = try catalog.defineFrom(rule, .materialized, .{ .materialized_rule = 3 });
    try testing.expect(catalog.staleAt(3) == null);
    try testing.expectEqual(published, catalog.staleAt(4).?);
    try testing.expect(catalog.view(declared).source == .declared);
}

test "a cloned catalog resolves the identities the original handed out" {
    var strings: string_table.StringTable = .init(testing.allocator);
    defer strings.deinit();
    var catalog: Catalog = .init(testing.allocator);
    defer catalog.deinit();

    const path = try strings.intern("path");
    const edge = try strings.intern("edge");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    var terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var body = [_]syntax.Clause{.{ .relational = .{ .predicate = edge, .terms = &terms } }};
    const id = try catalog.define(.{
        .head = .{ .predicate = path, .terms = &terms },
        .body = &body,
    }, .materialized);
    try catalog.declareBaseAvailable(.{ .name = edge, .arity = 2 });

    var copy = try catalog.clone();
    defer copy.deinit();
    try testing.expectEqual(catalog.generation, copy.generation);
    try testing.expect(copy.view(id).predicate().equals(catalog.view(id).predicate()));
    try testing.expect(copy.baseAvailable(.{ .name = edge, .arity = 2 }));
    try testing.expect(copy.definedByView(.{ .name = edge, .arity = 2 }));
    // The two share nothing: a change to one is invisible in the other.
    copy.setAvailability(id, .withheld);
    try testing.expect(catalog.view(id).readable());
    try testing.expect(!copy.view(id).readable());
}
