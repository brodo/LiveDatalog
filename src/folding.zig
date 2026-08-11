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
//! A relation the query reads and the catalog does not have is reconstructed
//! by inverting the views that read it — `inversion.zig` does that and removes
//! the terms it invents — and the result is the query's own rules combined
//! with the inverse rules, which is Chapter 6's `Q ∪ V⁻¹`. That plan is
//! maximally contained rather than equivalent, because a view remembers less
//! than the relations behind it.
//!
//! A plan that came back can be *lowered* into the executable language, and
//! only then. The IR exists because a Skolem term has no executable meaning,
//! so eliminating every one of them is precisely what earns the way back:
//! `lowerPlan` refuses a plan that still holds one, and there is no other
//! direction out of the IR.

const std = @import("std");
const fold_ir = @import("fold_ir.zig");
const inversion = @import("inversion.zig");
const relation_store = @import("relation_store.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");
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
    /// A view's definition was run backwards into rules that reconstruct what
    /// its body read.
    view_inverted,
    /// A relation the query reads is no longer read: the plan derives it.
    relation_reconstructed,
    /// The relations a reconstruction could not name a value in were split, so
    /// that every term the plan runs on is an ordinary value.
    skolem_terms_eliminated,
    /// Some instance of a rule was refused because a goal other than a
    /// positive relation would have had to read a reconstructed value. The
    /// plan is still sound and returns less.
    instances_dropped,

    pub fn text(self: TransformationKind) []const u8 {
        return switch (self) {
            .query_left_unchanged => "query reads only available relations",
            .view_inverted => "inverted into rules reconstructing what its body read",
            .relation_reconstructed => "reconstructed by the plan instead of read",
            .skolem_terms_eliminated => "relations split so that no reconstructed value stays unnameable",
            .instances_dropped => "instances that would have read a reconstructed value were dropped",
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
    /// The query reads a view whose extension the policy withholds.
    view_withheld,
    /// Every view mentioning this relation is withheld or outside the class
    /// the ordinary Inverse Method inverts, so nothing reconstructs it.
    relation_not_reconstructible,
    /// A view mentioning a relation the query needs reads what it defines.
    view_definition_recursive,
    /// A view mentioning a relation the query needs is not a conjunction of
    /// positive relations. Aggregates are F3's, and negation F4's.
    view_definition_not_conjunctive,
    /// A view mentioning a relation the query needs builds or reads a list,
    /// which is F5's.
    view_definition_uses_lists,
    /// The query reads a relation under negation or inside an aggregate that
    /// the plan would know only as far as the views prove it — a reconstructed
    /// relation, or one the query derives from one. Such a relation holds what
    /// the views prove existed, which can be less than it held; reading what is
    /// *not* in it, or counting what is, would then answer more than the query.
    relation_read_non_positively,
    /// Two relations a plan may read store under one name and arity, so a
    /// lowered plan could not tell them apart.
    predicate_name_ambiguous,

    pub fn text(self: PreconditionKind) []const u8 {
        return switch (self) {
            .relation_unavailable => "unavailable, and no view mentions it",
            .view_withheld => "the availability policy withholds this view's extension",
            .relation_not_reconstructible => "only views that cannot be inverted mention it",
            .view_definition_recursive => "its definition reads the relation it defines",
            .view_definition_not_conjunctive => "its definition is not a conjunction of positive relations",
            .view_definition_uses_lists => "its definition mentions a list",
            .relation_read_non_positively => "known only as far as the views prove it, " ++
                "and read under negation or inside an aggregate",
            .predicate_name_ambiguous => "another relation the plan may read stores under this name",
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

/// A query to fold: the goals to answer, and the rules the query defines its
/// own predicates by. The rules are part of the question — Chapter 6's plan is
/// `Q ∪ V⁻¹`, and a recursive `Q` is the case the Inverse Method exists for.
pub const Query = struct {
    goals: []const fold_ir.Goal,
    rules: []const fold_ir.Rule = &.{},
};

/// Folds `query` against `catalog`.
///
/// A plan may read a view's stored extension and whichever base relations the
/// catalog declares available, and nothing else. A query already inside that
/// boundary is its own plan and the guarantee is `equivalent`, because nothing
/// was done to it. Otherwise every relation it reads and cannot get must be
/// reconstructed by inverting the views that read it, and the plan is the
/// query's rules together with the inverse rules — maximally contained rather
/// than equivalent, because a view stores less than the relations behind it,
/// and only `contained` when eliminating Skolem terms had to drop instances.
/// A relation nothing can reconstruct makes the whole fold `unsupported`.
///
/// The query is borrowed; the outcome owns copies of everything it returns.
/// Its variables and functions are handed out by the catalog's symbol table,
/// which is why the catalog is not const.
pub fn foldQuery(
    allocator: std.mem.Allocator,
    catalog: *view_catalog.Catalog,
    query: Query,
) !Outcome {
    var reads: Reads = .{ .allocator = allocator };
    defer reads.deinit();
    try reads.walkGoals(query.goals, true);
    for (query.rules) |rule| {
        try reads.defined.put(allocator, headKey(rule), {});
        try reads.walkGoals(rule.body, true);
    }

    var unmet: std.ArrayList(Precondition) = .empty;
    defer unmet.deinit(allocator);
    var wanted: std.ArrayList(fold_ir.ViewId) = .empty;
    defer wanted.deinit(allocator);
    try examine(allocator, catalog, query.rules, &reads, &unmet, &wanted);
    if (unmet.items.len != 0) return .{ .unsupported = .{
        .allocator = allocator,
        .unmet = try unmet.toOwnedSlice(allocator),
    } };

    if (wanted.items.len == 0) {
        const copied = try fold_ir.cloneGoals(allocator, query.goals);
        errdefer fold_ir.freeGoals(allocator, copied);
        const rules = try cloneRules(allocator, query.rules);
        errdefer freeRules(allocator, rules);
        const transformations = try allocator.alloc(Transformation, 1);
        transformations[0] = .{ .kind = .query_left_unchanged };
        return .{ .folded = .{
            .allocator = allocator,
            .guarantee = .equivalent,
            .goals = copied,
            .rules = rules,
            .transformations = transformations,
        } };
    }

    var combined: std.ArrayList(fold_ir.Rule) = .empty;
    defer {
        for (combined.items) |rule| fold_ir.freeRule(allocator, rule);
        combined.deinit(allocator);
    }
    for (wanted.items) |id| {
        var inverted = try inversion.invert(allocator, &catalog.symbols, catalog.view(id));
        errdefer inverted.deinit();
        try combined.ensureUnusedCapacity(allocator, inverted.rules.len);
        combined.appendSliceAssumeCapacity(inverted.rules);
        allocator.free(inverted.take());
    }
    for (query.rules) |rule| {
        const copy = try fold_ir.cloneRule(allocator, rule);
        errdefer fold_ir.freeRule(allocator, copy);
        try combined.append(allocator, copy);
    }

    var eliminated = try inversion.eliminateSkolems(
        allocator,
        &catalog.symbols,
        catalog,
        combined.items,
    );
    errdefer eliminated.deinit();

    const goals = try fold_ir.cloneGoals(allocator, query.goals);
    errdefer fold_ir.freeGoals(allocator, goals);
    const transformations = try describe(allocator, catalog, &reads, wanted.items, eliminated);
    return .{ .folded = .{
        .allocator = allocator,
        .guarantee = if (eliminated.dropped) .contained else .maximally_contained,
        .goals = goals,
        .rules = eliminated.rules,
        .transformations = transformations,
    } };
}

/// What the query reads, and what it defines for itself.
///
/// A relation is recorded with whether the query ever reads it somewhere a
/// reconstruction cannot stand in for it — under negation, or inside an
/// aggregate — because that is what decides whether the fold is possible at
/// all, not how often it is read positively.
const Reads = struct {
    allocator: std.mem.Allocator,
    relations: std.array_hash_map.Auto(relation_store.PredicateKey, bool) = .empty,
    views: std.array_hash_map.Auto(fold_ir.ViewId, void) = .empty,
    defined: std.array_hash_map.Auto(relation_store.PredicateKey, void) = .empty,

    fn deinit(self: *Reads) void {
        self.defined.deinit(self.allocator);
        self.views.deinit(self.allocator);
        self.relations.deinit(self.allocator);
        self.* = undefined;
    }

    fn walkGoals(self: *Reads, goals: []const fold_ir.Goal, positive: bool) !void {
        for (goals) |goal| try self.walkGoal(goal, positive);
    }

    fn walkGoal(self: *Reads, goal: fold_ir.Goal, positive: bool) std.mem.Allocator.Error!void {
        switch (goal) {
            .relation => |relation| switch (relation.predicate) {
                .base => |key| {
                    const entry = try self.relations.getOrPut(self.allocator, key);
                    if (!entry.found_existing) entry.value_ptr.* = false;
                    if (!positive or relation.negated) entry.value_ptr.* = true;
                },
                .view => |reference| try self.views.put(self.allocator, reference.id, {}),
                // Nothing lowered from a query holds one, and a plan is not
                // folded a second time.
                .generated => unreachable,
            },
            // An aggregate reads its body to count what is in it, which a
            // reconstruction cannot stand in for however the body is written.
            .aggregate => |aggregate| try self.walkGoals(aggregate.body, false),
            .builtin => {},
        }
    }
};

fn headKey(rule: fold_ir.Rule) relation_store.PredicateKey {
    return switch (rule.head.predicate) {
        .base => |key| key,
        .view => |reference| .{ .name = reference.name, .arity = reference.arity },
        .generated => |reference| reference.origin,
    };
}

/// Decides, relation by relation, whether the plan can get what the query
/// reads: it is available, the query defines it, or some invertible view reads
/// it. Records the views to invert, and the preconditions of every relation
/// none of that covers.
fn examine(
    allocator: std.mem.Allocator,
    catalog: *const view_catalog.Catalog,
    rules: []const fold_ir.Rule,
    reads: *const Reads,
    unmet: *std.ArrayList(Precondition),
    wanted: *std.ArrayList(fold_ir.ViewId),
) !void {
    // What the plan will know only as far as the views prove it. A relation
    // reconstructed from a view starts here, and a predicate the query derives
    // joins it, because a rule is no more exact than what its body reads.
    var inexact: std.array_hash_map.Auto(relation_store.PredicateKey, void) = .empty;
    defer inexact.deinit(allocator);

    for (reads.views.keys()) |id| {
        const view = catalog.view(id);
        if (!view.readable()) try note(allocator, unmet, .{
            .kind = .view_withheld,
            .subject = view.predicate(),
        });
    }

    for (reads.relations.keys()) |key| {
        if (reads.defined.contains(key)) continue;
        if (catalog.baseAvailable(key)) continue;
        const subject: fold_ir.Predicate = .{ .base = key };

        var reconstructible = false;
        var mentioned = false;
        for (catalog.views.items) |*candidate| {
            if (!viewReads(candidate, key)) continue;
            mentioned = true;
            if (!candidate.readable()) {
                try note(allocator, unmet, .{
                    .kind = .view_withheld,
                    .subject = candidate.predicate(),
                });
                continue;
            }
            if (inversion.obstacle(candidate)) |blocker| {
                try note(allocator, unmet, .{
                    .kind = switch (blocker) {
                        .recursive => .view_definition_recursive,
                        .not_conjunctive => .view_definition_not_conjunctive,
                        .lists => .view_definition_uses_lists,
                    },
                    .subject = candidate.predicate(),
                });
                continue;
            }
            reconstructible = true;
            try noteView(allocator, wanted, candidate.id);
        }

        if (!mentioned) {
            try note(allocator, unmet, .{ .kind = .relation_unavailable, .subject = subject });
        } else if (!reconstructible) {
            try note(allocator, unmet, .{ .kind = .relation_not_reconstructible, .subject = subject });
        } else {
            try inexact.put(allocator, key, {});
        }
    }

    // Inexactness spreads along the query's own rules, and stopping at the
    // relations themselves would leave the hole open one step further on: a
    // rule reading a reconstruction derives less than the query's, so negating
    // *it* is the same unsound question asked about a different predicate.
    var spreading = true;
    while (spreading) {
        spreading = false;
        for (rules) |rule| {
            const head = headKey(rule);
            if (inexact.contains(head)) continue;
            if (!readsInexact(rule.body, &inexact)) continue;
            try inexact.put(allocator, head, {});
            spreading = true;
        }
    }

    for (reads.relations.keys(), reads.relations.values()) |key, non_positive| {
        if (!non_positive or !inexact.contains(key)) continue;
        try note(allocator, unmet, .{
            .kind = .relation_read_non_positively,
            .subject = .{ .base = key },
        });
    }

    // A lowered plan names a view by the name its extension is stored under,
    // so two relations it may read cannot share one. Checked over the views
    // the plan touches rather than the whole catalog: a name nothing reads
    // cannot be read wrongly.
    for (wanted.items) |id| {
        const view = catalog.view(id);
        const key: relation_store.PredicateKey = .{ .name = view.name, .arity = view.schema.arity() };
        var ambiguous = catalog.baseAvailable(key);
        for (wanted.items) |other| {
            if (other == id) continue;
            const rival = catalog.view(other);
            if (rival.name == view.name and rival.schema.arity() == key.arity) ambiguous = true;
        }
        if (ambiguous) try note(allocator, unmet, .{
            .kind = .predicate_name_ambiguous,
            .subject = view.predicate(),
        });
    }
}

/// Whether these goals read anything the plan will know incompletely. A view's
/// stored extension is exact whatever it was computed from, so only base
/// predicates can carry the doubt.
fn readsInexact(
    goals: []const fold_ir.Goal,
    inexact: *const std.array_hash_map.Auto(relation_store.PredicateKey, void),
) bool {
    for (goals) |goal| switch (goal) {
        .relation => |relation| switch (relation.predicate) {
            .base => |key| if (inexact.contains(key)) return true,
            .view, .generated => {},
        },
        .aggregate => |aggregate| if (readsInexact(aggregate.body, inexact)) return true,
        .builtin => {},
    };
    return false;
}

/// Whether a view's body reads this relation. The catalog answers the same
/// question over every view at once; a fold needs it per view, because which
/// view it was decides what gets inverted.
fn viewReads(view: *const view_catalog.View, key: relation_store.PredicateKey) bool {
    for (view.definition.body) |goal| switch (goal) {
        .relation => |relation| if (relation.predicate.equals(.{ .base = key })) return true,
        else => {},
    };
    return false;
}

fn noteView(
    allocator: std.mem.Allocator,
    wanted: *std.ArrayList(fold_ir.ViewId),
    id: fold_ir.ViewId,
) !void {
    for (wanted.items) |existing| if (existing == id) return;
    try wanted.append(allocator, id);
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

/// What the fold did, in the order it did it: the views it inverted, the
/// relations that made it worth inverting them, and what eliminating the
/// Skolem terms cost.
fn describe(
    allocator: std.mem.Allocator,
    catalog: *const view_catalog.Catalog,
    reads: *const Reads,
    wanted: []const fold_ir.ViewId,
    eliminated: inversion.Elimination,
) ![]Transformation {
    var notes: std.ArrayList(Transformation) = .empty;
    errdefer notes.deinit(allocator);
    for (wanted) |id| try notes.append(allocator, .{
        .kind = .view_inverted,
        .subject = catalog.view(id).predicate(),
    });
    for (reads.relations.keys()) |key| {
        if (reads.defined.contains(key) or catalog.baseAvailable(key)) continue;
        try notes.append(allocator, .{
            .kind = .relation_reconstructed,
            .subject = .{ .base = key },
        });
    }
    if (eliminated.split) try notes.append(allocator, .{ .kind = .skolem_terms_eliminated });
    if (eliminated.dropped) try notes.append(allocator, .{ .kind = .instances_dropped });
    return notes.toOwnedSlice(allocator);
}

fn cloneRules(allocator: std.mem.Allocator, rules: []const fold_ir.Rule) ![]fold_ir.Rule {
    const copies = try allocator.alloc(fold_ir.Rule, rules.len);
    var built: usize = 0;
    errdefer {
        for (copies[0..built]) |rule| fold_ir.freeRule(allocator, rule);
        allocator.free(copies);
    }
    for (rules, copies) |rule, *slot| {
        slot.* = try fold_ir.cloneRule(allocator, rule);
        built += 1;
    }
    return copies;
}

fn freeRules(allocator: std.mem.Allocator, rules: []fold_ir.Rule) void {
    for (rules) |rule| fold_ir.freeRule(allocator, rule);
    allocator.free(rules);
}

/// A plan in the executable language, ready to be installed and run.
///
/// It owns its rules and goals. A caller that installs a rule takes ownership
/// of that rule's head and clauses from it and says so with `takeRule`, since
/// the database it hands them to will free them itself.
pub const Executable = struct {
    allocator: std.mem.Allocator,
    rules: []syntax.Rule,
    goals: []syntax.Clause,

    pub fn deinit(self: *Executable) void {
        for (self.rules) |rule| syntax.freeRule(self.allocator, rule);
        self.allocator.free(self.rules);
        for (self.goals) |clause| syntax.freeClauseTree(self.allocator, clause);
        self.allocator.free(self.goals);
        self.* = undefined;
    }

    /// Hands rule `index` to the caller and leaves nothing of it behind, so
    /// that installing it and then releasing the rest does not release it
    /// twice. The body slice stays the caller's either way.
    pub fn takeRule(self: *Executable, index: usize) syntax.Rule {
        const rule = self.rules[index];
        self.rules[index] = .{ .head = .{ .predicate = 0, .terms = &.{} }, .body = &.{} };
        return rule;
    }
};

/// Lowers a plan into the executable language.
///
/// This is the only way back out of the folding IR, and it exists because a
/// plan that has been through Skolem elimination no longer needs one: every
/// term in it is a term the evaluator has a meaning for. A plan still holding
/// a Skolem term is refused rather than represented, which is what keeps the
/// IR's reason for existing intact — an unproved plan has no executable form
/// to reach the evaluator through.
///
/// Generated predicates are interned into `strings` under spellings no source
/// program could produce. A view goal is lowered to the view's own name, so
/// the database this runs against must hold that view's extension under it.
pub fn lowerPlan(
    allocator: std.mem.Allocator,
    strings: *string_table.StringTable,
    symbols: *const fold_ir.Symbols,
    plan: *const Plan,
) !Executable {
    var lowering: Lowering = .{ .allocator = allocator, .strings = strings, .symbols = symbols };
    const rules = try allocator.alloc(syntax.Rule, plan.rules.len);
    var built: usize = 0;
    errdefer {
        for (rules[0..built]) |rule| syntax.freeRule(allocator, rule);
        allocator.free(rules);
    }
    for (plan.rules, rules) |rule, *slot| {
        slot.* = try lowering.rule(rule);
        built += 1;
    }
    return .{
        .allocator = allocator,
        .rules = rules,
        .goals = try lowering.clauses(plan.goals),
    };
}

const Lowering = struct {
    allocator: std.mem.Allocator,
    strings: *string_table.StringTable,
    symbols: *const fold_ir.Symbols,

    fn rule(self: *Lowering, value: fold_ir.Rule) !syntax.Rule {
        const head = try self.expr(value.head);
        errdefer syntax.freeExpr(self.allocator, head);
        return .{
            .head = head,
            .body = try self.clauses(value.body),
            .seed_argument = value.seed_argument,
        };
    }

    fn clauses(self: *Lowering, goals: []const fold_ir.Goal) ![]syntax.Clause {
        const lowered = try self.allocator.alloc(syntax.Clause, goals.len);
        var built: usize = 0;
        errdefer {
            for (lowered[0..built]) |clause| syntax.freeClauseTree(self.allocator, clause);
            self.allocator.free(lowered);
        }
        for (goals, lowered) |goal, *slot| {
            slot.* = try self.goalClause(goal);
            built += 1;
        }
        return lowered;
    }

    fn goalClause(self: *Lowering, goal: fold_ir.Goal) anyerror!syntax.Clause {
        return switch (goal) {
            .relation => |relation| if (relation.negated)
                .{ .negated = try self.expr(relation) }
            else
                .{ .relational = try self.expr(relation) },
            .builtin => |builtin| blk: {
                var expression = syntax.Expr{
                    .predicate = try self.strings.intern(syntax.goalOperator(builtin.operator)),
                    .terms = try self.terms(builtin.terms),
                    .negated = builtin.negated,
                };
                expression.kind = builtin.operator;
                break :blk .{ .builtin = expression };
            },
            .aggregate => |aggregate| blk: {
                const template = try self.term(aggregate.template);
                errdefer syntax.freeTerm(self.allocator, template);
                const output = try self.term(aggregate.output);
                errdefer syntax.freeTerm(self.allocator, output);
                break :blk .{ .aggregate = .{
                    .template = template,
                    .body = try self.clauses(aggregate.body),
                    .output = output,
                } };
            },
        };
    }

    fn expr(self: *Lowering, relation: fold_ir.Relation) !syntax.Expr {
        return .{
            .predicate = try self.predicate(relation.predicate),
            .terms = try self.terms(relation.terms),
            .negated = relation.negated,
        };
    }

    fn predicate(self: *Lowering, value: fold_ir.Predicate) !syntax.Id {
        return switch (value) {
            .base => |key| key.name,
            .view => |reference| reference.name,
            .generated => |reference| blk: {
                var spelling: std.Io.Writer.Allocating = .init(self.allocator);
                defer spelling.deinit();
                spelling.writer.print("{s}${d}", .{
                    self.strings.resolve(reference.origin.name),
                    reference.tag,
                }) catch return error.OutOfMemory;
                break :blk self.strings.intern(spelling.written());
            },
        };
    }

    fn terms(self: *Lowering, values: []const fold_ir.Term) ![]syntax.Term {
        const lowered = try self.allocator.alloc(syntax.Term, values.len);
        var built: usize = 0;
        errdefer {
            for (lowered[0..built]) |value| syntax.freeTerm(self.allocator, value);
            self.allocator.free(lowered);
        }
        for (values, lowered) |value, *slot| {
            slot.* = try self.term(value);
            built += 1;
        }
        return lowered;
    }

    fn term(self: *Lowering, value: fold_ir.Term) anyerror!syntax.Term {
        return switch (value) {
            .constant => |constant| .{ .scalar = constant },
            .variable => |name| .{ .variable = try self.variableName(name) },
            .nil => .nil,
            .cons => |pair| blk: {
                const copy = try self.allocator.create(syntax.Term.Cons);
                errdefer self.allocator.destroy(copy);
                copy.head = try self.term(pair.head);
                errdefer syntax.freeTerm(self.allocator, copy.head);
                copy.tail = try self.term(pair.tail);
                break :blk .{ .cons = copy };
            },
            // What the IR exists for: there is no executable term this could
            // become, and inventing one is exactly what would let an unproved
            // plan run.
            .skolem => return error.PlanNotExecutable,
        };
    }

    /// A variable executes under the name it renders under — identity and all.
    /// Two distinct variables printing alike would be one variable to whoever
    /// reads the plan, and to whatever runs it.
    fn variableName(self: *Lowering, value: fold_ir.Variable) !syntax.Id {
        var spelling: std.Io.Writer.Allocating = .init(self.allocator);
        defer spelling.deinit();
        fold_ir.writeVariableName(&spelling.writer, self.symbols, self.strings, value) catch
            return error.OutOfMemory;
        return self.strings.intern(spelling.written());
    }
};

const testing = std.testing;
const scalar = @import("scalar.zig");

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

    var outcome = try foldQuery(allocator, &fixture.catalog, .{ .goals = goals });
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
    var outcome = try foldQuery(allocator, &fixture.catalog, .{ .goals = goals });
    defer outcome.deinit();

    try testing.expectEqual(Guarantee.unsupported, outcome.guarantee());
    try testing.expectEqual(@as(?*const Plan, null), outcome.plan());
    try testing.expectEqual(@as(usize, 2), outcome.unsupported.unmet.len);
    try testing.expectEqual(
        PreconditionKind.view_withheld,
        outcome.unsupported.unmet[0].kind,
    );
    try testing.expectEqual(
        PreconditionKind.relation_not_reconstructible,
        outcome.unsupported.unmet[1].kind,
    );

    const rendered = try outcome.explainAlloc(allocator, fixture.names());
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\guarantee: unsupported
        \\unmet preconditions:
        \\  path@0/2: the availability policy withholds this view's extension
        \\  edge/2: only views that cannot be inverted mention it
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

    var outcome = try foldQuery(allocator, &fixture.catalog, .{ .goals = &goals });
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

    // And it has no executable form. This is the whole reason the IR is not
    // `syntax`: a plan holding a value nothing can name is refused rather than
    // represented, so eliminating those values is what earns the way back.
    try testing.expectError(error.PlanNotExecutable, lowerPlan(
        allocator,
        &fixture.strings,
        &fixture.catalog.symbols,
        outcome.plan().?,
    ));

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

test "a fold that reconstructs a relation reports the plan it built to do it" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .materialized);
    defer fixture.deinit();
    const reach = try fixture.strings.intern("reach");

    // reach(X, Y) :- edge(X, Y), asked of a database that has neither `edge`
    // nor a rule for it — only the view `path` whose body reads it.
    const scope = try fixture.catalog.symbols.openScope(.query);
    const a = try fixture.catalog.symbols.userVariable(scope, fixture.x);
    const b = try fixture.catalog.symbols.userVariable(scope, fixture.y);
    const pair: [2]fold_ir.Term = .{ .{ .variable = a }, .{ .variable = b } };
    const rules = [_]fold_ir.Rule{.{
        .scope = scope,
        .head = .{
            .predicate = .{ .base = .{ .name = reach, .arity = 2 } },
            .terms = try allocator.dupe(fold_ir.Term, &pair),
        },
        .body = try allocator.dupe(fold_ir.Goal, &.{.{ .relation = .{
            .predicate = .{ .base = .{ .name = fixture.edge, .arity = 2 } },
            .terms = try allocator.dupe(fold_ir.Term, &pair),
        } }}),
    }};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try allocator.dupe(fold_ir.Goal, &.{.{ .relation = .{
        .predicate = .{ .base = .{ .name = reach, .arity = 2 } },
        .terms = try allocator.dupe(fold_ir.Term, &pair),
    } }});
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try foldQuery(allocator, &fixture.catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();

    // A view remembering every variable of its body loses nothing, so its
    // inverse has no value it cannot name and nothing needs splitting. It is
    // still only maximally contained: what the view stored may be less than
    // what the relation held.
    try testing.expectEqual(Guarantee.maximally_contained, outcome.guarantee());
    try testing.expectEqual(@as(usize, 2), outcome.plan().?.rules.len);
    const rendered = try outcome.explainAlloc(allocator, fixture.names());
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\guarantee: maximally contained
        \\goals:
        \\  reach(X#2, Y#3)
        \\rules:
        \\  edge(X#4, Y#5) :- path@0(X#4, Y#5) % generated.
        \\  reach(X#2, Y#3) :- edge(X#2, Y#3).
        \\transformations:
        \\  inverted into rules reconstructing what its body read: path@0/2
        \\  reconstructed by the plan instead of read: edge/2
        \\
    , rendered);
}

test "a reconstruction cannot stand in for a relation read under negation" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .materialized);
    defer fixture.deinit();

    // path(A, B), not edge(B, A). The view can reconstruct what `edge` held,
    // but only what it can prove it held, and asking what is *not* there of a
    // relation known incompletely answers more than the query does.
    const scope = try fixture.catalog.symbols.openScope(.query);
    const a = try fixture.catalog.symbols.userVariable(scope, fixture.x);
    const b = try fixture.catalog.symbols.userVariable(scope, fixture.y);
    const goals = try allocator.dupe(fold_ir.Goal, &.{
        .{ .relation = .{
            .predicate = fixture.catalog.view(fixture.view).predicate(),
            .terms = try allocator.dupe(
                fold_ir.Term,
                &.{ .{ .variable = a }, .{ .variable = b } },
            ),
        } },
        .{ .relation = .{
            .predicate = .{ .base = .{ .name = fixture.edge, .arity = 2 } },
            .terms = try allocator.dupe(
                fold_ir.Term,
                &.{ .{ .variable = b }, .{ .variable = a } },
            ),
            .negated = true,
        } },
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try foldQuery(allocator, &fixture.catalog, .{ .goals = goals });
    defer outcome.deinit();
    try testing.expectEqual(Guarantee.unsupported, outcome.guarantee());
    try testing.expectEqual(@as(usize, 1), outcome.unsupported.unmet.len);
    try testing.expectEqual(
        PreconditionKind.relation_read_non_positively,
        outcome.unsupported.unmet[0].kind,
    );

    // Declaring the relation available answers the objection: what is there is
    // then known exactly, and nothing is reconstructed.
    try fixture.catalog.declareBaseAvailable(.{ .name = fixture.edge, .arity = 2 });
    var allowed = try foldQuery(allocator, &fixture.catalog, .{ .goals = goals });
    defer allowed.deinit();
    try testing.expectEqual(Guarantee.equivalent, allowed.guarantee());
}
