//! What a fold returns: a plan and what it promises, or no plan and why.
//!
//! This is not the join planner. `planner.zig` reorders the goals of a body
//! that will be run either way and never changes which answers come back, so
//! it can be applied silently and cannot fail. Folding changes what is asked —
//! a query over relations that are gone becomes a query over the views that
//! remain — and Chapter 6 shows the general case producing a plan whose
//! answers are *not* those of the original query. A transformation that can do
//! that cannot be applied silently, so the result carries a guarantee, and the
//! caller decides whether that guarantee is enough.
//!
//! The four-valued vocabulary is one enum, but the fourth value is not shaped
//! like the other three: `unsupported` carries no plan at all. That is
//! deliberate. A fold that found nothing and a fold that produced a plan with
//! no goals in it are different answers, and a representation where both are
//! "a plan" would let the second be read as the first by anybody who forgot to
//! check a tag.
//!
//! Nothing here inverts anything yet. What this phase can answer is the
//! availability question folding is asked in the first place — whether the
//! query's relations are there — and it answers `unsupported` with the
//! precondition it could not meet whenever they are not. Reconstructing a
//! relation from the views that mention it is the Inverse Method, and it
//! arrives in the next phase.

const std = @import("std");
const fold_ir = @import("fold_ir.zig");
const view_catalog = @import("view_catalog.zig");

/// What a fold's answers are, relative to the query's.
pub const Guarantee = enum {
    /// The same answers as the query, over any database.
    equivalent,
    /// Contained in the query's answers, and no plan available under the same
    /// views returns more.
    maximally_contained,
    /// Contained in the query's answers, with nothing claimed about how much
    /// of them it returns.
    contained,
    /// No plan. Not an empty one — none.
    unsupported,

    pub fn text(self: Guarantee) []const u8 {
        return switch (self) {
            .equivalent => "equivalent",
            .maximally_contained => "maximally contained",
            .contained => "contained",
            .unsupported => "unsupported",
        };
    }
};

/// What a fold did to the query.
pub const TransformationKind = enum {
    /// Nothing was done. Every relation the query reads is available, so the
    /// query is its own plan.
    query_left_unchanged,

    pub fn text(self: TransformationKind) []const u8 {
        return switch (self) {
            .query_left_unchanged => "query reads only available relations",
        };
    }
};

/// Something a fold did to the query. Recorded so a plan can say how it came
/// to be, which is the only way to read one: its goals are not the caller's.
pub const Transformation = struct {
    kind: TransformationKind,
    subject: ?fold_ir.Predicate = null,
};

/// What a fold needed and did not have.
pub const PreconditionKind = enum {
    /// The query reads a relation that is neither available nor mentioned by
    /// any view. Nothing could reconstruct it.
    relation_unavailable,
    /// The query reads a relation only a view's definition mentions.
    /// Reconstructing it is inversion, which this phase does not do.
    view_inversion_unimplemented,
    /// The query reads a view whose extension the policy withholds.
    view_withheld,

    pub fn text(self: PreconditionKind) []const u8 {
        return switch (self) {
            .relation_unavailable => "unavailable, and no view mentions it",
            .view_inversion_unimplemented => "only a view defines it, and inversion is not implemented",
            .view_withheld => "the availability policy withholds this view's extension",
        };
    }
};

/// Something a fold needed and did not have, and what it needed it for.
pub const Precondition = struct {
    kind: PreconditionKind,
    subject: fold_ir.Predicate,
};

/// A query rewritten to run against what is available, and what that rewrite
/// promises.
///
/// A plan owns its goals, its rules and its notes; `deinit` releases them. Its
/// symbols are not its own — they belong to the catalog's table, which must
/// outlive it.
pub const Plan = struct {
    allocator: std.mem.Allocator,
    /// Never `.unsupported`: a plan that promises nothing is not a plan.
    guarantee: Guarantee,
    /// The goals to solve.
    goals: []fold_ir.Goal,
    /// Rules the plan needs solved alongside the program's own — where the
    /// inverses of the views it reads will go.
    rules: []fold_ir.Rule,
    transformations: []Transformation,

    pub fn deinit(self: *Plan) void {
        fold_ir.freeGoals(self.allocator, self.goals);
        for (self.rules) |rule| fold_ir.freeRule(self.allocator, rule);
        self.allocator.free(self.rules);
        self.allocator.free(self.transformations);
        self.* = undefined;
    }
};

/// Why there is no plan. The unmet preconditions are the report: each names
/// what the fold needed and could not get.
pub const Unsupported = struct {
    allocator: std.mem.Allocator,
    unmet: []Precondition,

    pub fn deinit(self: *Unsupported) void {
        self.allocator.free(self.unmet);
        self.* = undefined;
    }
};

/// The result of a fold: a plan, or no plan.
///
/// The tags are what keeps the two apart. There is no plan to read out of an
/// `unsupported` outcome, so an unsupported fold cannot be mistaken for one
/// that succeeded with nothing in it.
pub const Outcome = union(enum) {
    folded: Plan,
    unsupported: Unsupported,

    pub fn deinit(self: *Outcome) void {
        switch (self.*) {
            .folded => |*value| value.deinit(),
            .unsupported => |*reason| reason.deinit(),
        }
        self.* = undefined;
    }

    pub fn guarantee(self: *const Outcome) Guarantee {
        return switch (self.*) {
            .folded => |value| blk: {
                // A plan promising `unsupported` would be the one way back
                // into the confusion the two tags exist to prevent.
                std.debug.assert(value.guarantee != .unsupported);
                break :blk value.guarantee;
            },
            .unsupported => .unsupported,
        };
    }

    /// The plan, or null when there is none. The only way to reach one.
    pub fn plan(self: *const Outcome) ?*const Plan {
        return switch (self.*) {
            .folded => |*value| value,
            .unsupported => null,
        };
    }

    /// Renders the outcome: its guarantee first, then either the plan and what
    /// produced it, or the preconditions it could not meet. Order is the order
    /// the fold recorded, so the same fold renders the same text.
    pub fn write(
        self: *const Outcome,
        writer: *std.Io.Writer,
        names: fold_ir.Names,
    ) std.Io.Writer.Error!void {
        try writer.print("guarantee: {s}\n", .{self.guarantee().text()});
        switch (self.*) {
            .folded => |value| {
                try writer.writeAll("goals:\n");
                for (value.goals) |goal| {
                    try writer.writeAll("  ");
                    try fold_ir.writeGoal(writer, names, goal);
                    try writer.writeByte('\n');
                }
                if (value.rules.len != 0) {
                    try writer.writeAll("rules:\n");
                    for (value.rules) |rule| {
                        try writer.writeAll("  ");
                        try fold_ir.writeRule(writer, names, rule);
                        try writer.writeByte('\n');
                    }
                }
                try writer.writeAll("transformations:\n");
                for (value.transformations) |transformation| {
                    try writer.print("  {s}", .{transformation.kind.text()});
                    if (transformation.subject) |subject| {
                        try writer.writeAll(": ");
                        try writeSubject(writer, names, subject);
                    }
                    try writer.writeByte('\n');
                }
            },
            .unsupported => |reason| {
                try writer.writeAll("unmet preconditions:\n");
                for (reason.unmet) |precondition| {
                    try writer.writeAll("  ");
                    try writeSubject(writer, names, precondition.subject);
                    try writer.print(": {s}\n", .{precondition.kind.text()});
                }
            },
        }
    }

    /// Renders the outcome into a caller-owned string.
    pub fn explainAlloc(
        self: *const Outcome,
        allocator: std.mem.Allocator,
        names: fold_ir.Names,
    ) ![]u8 {
        var text: std.Io.Writer.Allocating = .init(allocator);
        defer text.deinit();
        self.write(&text.writer, names) catch return error.OutOfMemory;
        return text.toOwnedSlice();
    }
};

fn writeSubject(
    writer: *std.Io.Writer,
    names: fold_ir.Names,
    subject: fold_ir.Predicate,
) std.Io.Writer.Error!void {
    try fold_ir.writePredicate(writer, names, subject);
    try writer.print("/{d}", .{subject.arity()});
}

/// Folds `goals` against `catalog`.
///
/// The question this answers is availability: a plan may read a view's stored
/// extension and whichever base relations the catalog declares available, and
/// nothing else. A query already inside that boundary is its own plan, and the
/// guarantee is `equivalent` because nothing was done to it. A query outside it
/// is `unsupported`, naming each relation it could not get — including the ones
/// a view's definition mentions, which the Inverse Method will reconstruct in
/// the next phase and this one cannot.
///
/// The goals are borrowed; the outcome owns copies of everything it returns.
pub fn foldQuery(
    allocator: std.mem.Allocator,
    catalog: *const view_catalog.Catalog,
    goals: []const fold_ir.Goal,
) !Outcome {
    var unmet: std.ArrayList(Precondition) = .empty;
    defer unmet.deinit(allocator);
    try collectUnmet(allocator, catalog, goals, &unmet);

    if (unmet.items.len != 0) return .{ .unsupported = .{
        .allocator = allocator,
        .unmet = try unmet.toOwnedSlice(allocator),
    } };

    const copied = try fold_ir.cloneGoals(allocator, goals);
    errdefer fold_ir.freeGoals(allocator, copied);
    const transformations = try allocator.alloc(Transformation, 1);
    errdefer allocator.free(transformations);
    transformations[0] = .{ .kind = .query_left_unchanged };
    return .{ .folded = .{
        .allocator = allocator,
        .guarantee = .equivalent,
        .goals = copied,
        .rules = try allocator.alloc(fold_ir.Rule, 0),
        .transformations = transformations,
    } };
}

fn collectUnmet(
    allocator: std.mem.Allocator,
    catalog: *const view_catalog.Catalog,
    goals: []const fold_ir.Goal,
    unmet: *std.ArrayList(Precondition),
) std.mem.Allocator.Error!void {
    for (goals) |goal| switch (goal) {
        .relation => |relation| switch (relation.predicate) {
            .base => |key| {
                if (catalog.baseAvailable(key)) continue;
                try note(allocator, unmet, .{
                    .kind = if (catalog.definedByView(key))
                        .view_inversion_unimplemented
                    else
                        .relation_unavailable,
                    .subject = relation.predicate,
                });
            },
            .view => |reference| {
                if (catalog.view(reference.id).readable()) continue;
                try note(allocator, unmet, .{
                    .kind = .view_withheld,
                    .subject = relation.predicate,
                });
            },
        },
        .aggregate => |aggregate| try collectUnmet(allocator, catalog, aggregate.body, unmet),
        .builtin => {},
    };
}

/// Records one unmet precondition, once. A query reading the same missing
/// relation twice has one thing wrong with it, not two.
fn note(
    allocator: std.mem.Allocator,
    unmet: *std.ArrayList(Precondition),
    precondition: Precondition,
) !void {
    for (unmet.items) |existing| {
        if (existing.kind == precondition.kind and
            existing.subject.equals(precondition.subject)) return;
    }
    try unmet.append(allocator, precondition);
}

const testing = std.testing;
const scalar = @import("scalar.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");

/// A catalog holding `path(X, Y) :- edge(X, Y).` as a materialized view, and
/// the tables its names resolve against.
const Fixture = struct {
    strings: string_table.StringTable,
    scalars: scalar.Store,
    catalog: view_catalog.Catalog,
    path: syntax.Id,
    edge: syntax.Id,
    x: syntax.Id,
    y: syntax.Id,
    view: fold_ir.ViewId,

    fn init(allocator: std.mem.Allocator, availability: view_catalog.Availability) !Fixture {
        var fixture: Fixture = .{
            .strings = .init(allocator),
            .scalars = .init(allocator),
            .catalog = .init(allocator),
            .path = undefined,
            .edge = undefined,
            .x = undefined,
            .y = undefined,
            .view = undefined,
        };
        errdefer fixture.deinit();
        fixture.path = try fixture.strings.intern("path");
        fixture.edge = try fixture.strings.intern("edge");
        fixture.x = try fixture.strings.intern("X");
        fixture.y = try fixture.strings.intern("Y");

        var head_terms = [_]syntax.Term{ .{ .variable = fixture.x }, .{ .variable = fixture.y } };
        var body_terms = [_]syntax.Term{ .{ .variable = fixture.x }, .{ .variable = fixture.y } };
        var body = [_]syntax.Clause{
            .{ .relational = .{ .predicate = fixture.edge, .terms = &body_terms } },
        };
        fixture.view = try fixture.catalog.define(.{
            .head = .{ .predicate = fixture.path, .terms = &head_terms },
            .body = &body,
        }, availability);
        return fixture;
    }

    fn deinit(self: *Fixture) void {
        self.catalog.deinit();
        self.scalars.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    fn names(self: *const Fixture) fold_ir.Names {
        return .{
            .symbols = &self.catalog.symbols,
            .strings = &self.strings,
            .scalars = &self.scalars,
        };
    }

    /// One goal over the view, and one over the base relation it is defined
    /// from, sharing a scope and its variables. The caller owns both.
    fn queryGoals(self: *Fixture, allocator: std.mem.Allocator) ![]fold_ir.Goal {
        const scope = try self.catalog.symbols.openScope(.query);
        const a = try self.catalog.symbols.userVariable(scope, self.x);
        const b = try self.catalog.symbols.userVariable(scope, self.y);
        const view_terms = try allocator.dupe(
            fold_ir.Term,
            &.{ .{ .variable = a }, .{ .variable = b } },
        );
        errdefer allocator.free(view_terms);
        const base_terms = try allocator.dupe(
            fold_ir.Term,
            &.{ .{ .variable = b }, .{ .variable = a } },
        );
        errdefer allocator.free(base_terms);
        return allocator.dupe(fold_ir.Goal, &.{
            .{ .relation = .{
                .predicate = self.catalog.view(self.view).predicate(),
                .terms = view_terms,
            } },
            .{ .relation = .{
                .predicate = .{ .base = .{ .name = self.edge, .arity = 2 } },
                .terms = base_terms,
            } },
        });
    }
};

test "a query inside the availability boundary is its own equivalent plan" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .materialized);
    defer fixture.deinit();
    try fixture.catalog.declareBaseAvailable(.{ .name = fixture.edge, .arity = 2 });

    const goals = try fixture.queryGoals(allocator);
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try foldQuery(allocator, &fixture.catalog, goals);
    defer outcome.deinit();

    try testing.expectEqual(Guarantee.equivalent, outcome.guarantee());
    const plan = outcome.plan().?;
    try testing.expectEqual(@as(usize, 2), plan.goals.len);
    try testing.expectEqual(@as(usize, 0), plan.rules.len);
    // The plan owns its goals: they are equal to the query's and not the
    // same memory.
    try testing.expect(plan.goals.ptr != goals.ptr);
    try testing.expect(plan.goals[0].relation.predicate.equals(goals[0].relation.predicate));

    const rendered = try outcome.explainAlloc(allocator, fixture.names());
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\guarantee: equivalent
        \\goals:
        \\  path@0(X#2, Y#3)
        \\  edge(Y#3, X#2)
        \\transformations:
        \\  query reads only available relations
        \\
    , rendered);
}

test "an unsupported fold carries no plan to mistake for an empty one" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .withheld);
    defer fixture.deinit();

    const goals = try fixture.queryGoals(allocator);
    defer fold_ir.freeGoals(allocator, goals);

    // Neither relation is available: the view's extension is withheld, and
    // `edge` is only reachable by inverting that view.
    var outcome = try foldQuery(allocator, &fixture.catalog, goals);
    defer outcome.deinit();

    try testing.expectEqual(Guarantee.unsupported, outcome.guarantee());
    try testing.expectEqual(@as(?*const Plan, null), outcome.plan());
    try testing.expectEqual(@as(usize, 2), outcome.unsupported.unmet.len);
    try testing.expectEqual(
        PreconditionKind.view_withheld,
        outcome.unsupported.unmet[0].kind,
    );
    try testing.expectEqual(
        PreconditionKind.view_inversion_unimplemented,
        outcome.unsupported.unmet[1].kind,
    );

    const rendered = try outcome.explainAlloc(allocator, fixture.names());
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\guarantee: unsupported
        \\unmet preconditions:
        \\  path@0/2: the availability policy withholds this view's extension
        \\  edge/2: only a view defines it, and inversion is not implemented
        \\
    , rendered);

    // An empty *plan* renders as a plan, guarantee and all. Nothing about the
    // two readings can be confused: one has goals to run and the other has a
    // reason it has none.
    var empty: Outcome = .{ .folded = .{
        .allocator = allocator,
        .guarantee = .equivalent,
        .goals = try allocator.alloc(fold_ir.Goal, 0),
        .rules = try allocator.alloc(fold_ir.Rule, 0),
        .transformations = try allocator.alloc(Transformation, 0),
    } };
    defer empty.deinit();
    try testing.expect(empty.plan() != null);
    try testing.expectEqual(Guarantee.equivalent, empty.guarantee());
    const empty_text = try empty.explainAlloc(allocator, fixture.names());
    defer allocator.free(empty_text);
    try testing.expectEqualStrings(
        \\guarantee: equivalent
        \\goals:
        \\transformations:
        \\
    , empty_text);
}

test "a relation nothing defines is reported apart from one a view mentions" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .materialized);
    defer fixture.deinit();
    const missing = try fixture.strings.intern("colour");

    const scope = try fixture.catalog.symbols.openScope(.query);
    const variable = try fixture.catalog.symbols.userVariable(scope, fixture.x);
    var terms = [_]fold_ir.Term{.{ .variable = variable }};
    // The same missing relation twice, so the report is checked for being one
    // finding rather than two.
    const goals = [_]fold_ir.Goal{
        .{ .relation = .{
            .predicate = .{ .base = .{ .name = missing, .arity = 1 } },
            .terms = &terms,
        } },
        .{ .relation = .{
            .predicate = .{ .base = .{ .name = missing, .arity = 1 } },
            .terms = &terms,
        } },
    };

    var outcome = try foldQuery(allocator, &fixture.catalog, &goals);
    defer outcome.deinit();
    try testing.expectEqual(@as(usize, 1), outcome.unsupported.unmet.len);
    try testing.expectEqual(
        PreconditionKind.relation_unavailable,
        outcome.unsupported.unmet[0].kind,
    );
}

test "a plan renders the generated symbols no program could have written" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .materialized);
    defer fixture.deinit();

    // The shape F2 will produce, built by hand: an inverse rule reconstructing
    // `edge` from the view, with a Skolem term where the view projected a
    // value away, and a generated equality tying it down.
    const scope = try fixture.catalog.symbols.openScope(.generated);
    const a = try fixture.catalog.symbols.userVariable(scope, fixture.x);
    const hidden = try fixture.catalog.symbols.freshVariable(scope);
    const function = try fixture.catalog.symbols.freshFunction(scope);

    const skolem = try allocator.create(fold_ir.Term.Skolem);
    skolem.* = .{
        .function = function,
        .arguments = try allocator.dupe(fold_ir.Term, &.{.{ .variable = a }}),
    };
    const second_skolem = try fold_ir.cloneTerm(allocator, .{ .skolem = skolem });
    const rules = try allocator.alloc(fold_ir.Rule, 1);
    rules[0] = .{
        .scope = scope,
        .head = .{
            .predicate = .{ .base = .{ .name = fixture.edge, .arity = 2 } },
            .terms = try allocator.dupe(
                fold_ir.Term,
                &.{ .{ .variable = a }, .{ .skolem = skolem } },
            ),
            .provenance = .generated,
        },
        .body = try allocator.dupe(fold_ir.Goal, &.{
            .{ .relation = .{
                .predicate = fixture.catalog.view(fixture.view).predicate(),
                .terms = try allocator.dupe(
                    fold_ir.Term,
                    &.{ .{ .variable = a }, .{ .variable = hidden } },
                ),
            } },
            .{ .builtin = .{
                .operator = .equality,
                .terms = try allocator.dupe(
                    fold_ir.Term,
                    &.{ .{ .variable = hidden }, second_skolem },
                ),
                .provenance = .generated,
            } },
        }),
    };

    var outcome: Outcome = .{ .folded = .{
        .allocator = allocator,
        .guarantee = .maximally_contained,
        .goals = try allocator.alloc(fold_ir.Goal, 0),
        .rules = rules,
        .transformations = try allocator.alloc(Transformation, 0),
    } };
    defer outcome.deinit();

    const rendered = try outcome.explainAlloc(allocator, fixture.names());
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\guarantee: maximally contained
        \\goals:
        \\rules:
        \\  edge(X#2, $f0(X#2)) :- path@0(X#2, $V3), $V3 = $f0(X#2) % generated.
        \\transformations:
        \\
    , rendered);

    // Rendering a copy gives the same text, which is what makes the renderer
    // usable as the plan's identity while no executable form exists.
    var copy: Outcome = .{ .folded = .{
        .allocator = allocator,
        .guarantee = .maximally_contained,
        .goals = try allocator.alloc(fold_ir.Goal, 0),
        .rules = try allocator.alloc(fold_ir.Rule, 1),
        .transformations = try allocator.alloc(Transformation, 0),
    } };
    copy.folded.rules[0] = try fold_ir.cloneRule(allocator, rules[0]);
    defer copy.deinit();
    const copied_text = try copy.explainAlloc(allocator, fixture.names());
    defer allocator.free(copied_text);
    try testing.expectEqualStrings(rendered, copied_text);
}
