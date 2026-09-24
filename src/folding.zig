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
const list_functions = @import("list_functions.zig");
const monotonicity = @import("monotonicity.zig");
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
    /// A relation the plan derives, and derives all of: a canonical aggregate
    /// view of that relation was available, and Lemma 6.4.2 makes the
    /// reconstruction equivalent to it rather than merely contained in it.
    relation_reconstructed_exactly,
    /// The query reads a relation it will know incompletely under negation or
    /// inside an aggregate, and that read stands because the query is
    /// monotonic: its answers can only grow with the relations it reads, so
    /// answering it over a reconstruction returns fewer answers, not other
    /// ones.
    monotonic_reads_admitted,
    /// The plan defines what it means to be in a list, because some view
    /// stored a collected one and the values inside it had to be read back.
    membership_defined,
    /// The relations a reconstruction could not name a value in were split, so
    /// that every term the plan runs on is an ordinary value.
    skolem_terms_eliminated,
    /// Some instance of a rule was refused because a goal other than a
    /// positive relation would have had to read a reconstructed value. The
    /// plan is still sound and returns less.
    instances_dropped,
    /// The query named a list function the views do not expose and defined it
    /// as a conjunction of ones they do, so the goal was replaced by that
    /// definition and the definition dropped. A plan holds no list-function
    /// definitions: what derives `sum` is the inverse of a view that stored
    /// one.
    list_function_expanded,
    /// A view that collects a set and then reads it with list functions was
    /// written as the two views it is — one collecting, one reading — so that
    /// what it collected can be spoken of apart from what it reported.
    view_split_at_its_aggregate,
    /// Two views were proved to have collected the same set, so the set one of
    /// them only named is the set the plan derives. This is Section 6.5's
    /// functional dependency, decided while the plan was built rather than
    /// carried in it.
    collected_sets_identified,
    /// Several views reconstructed one relation and one of them reconstructed
    /// it exactly, so the plan reads that one and leaves the rest out. Lemma
    /// 6.4.2 is what makes them interchangeable — an exact reconstruction is
    /// the relation, and nothing contained in it can add to it — and among
    /// interchangeable views the smallest extension is read. This is the only
    /// place cost decides anything about a fold, and it decides between plans
    /// already proved to answer the same.
    equivalent_view_preferred,

    pub fn text(self: TransformationKind) []const u8 {
        return switch (self) {
            .query_left_unchanged => "query reads only available relations",
            .view_inverted => "inverted into rules reconstructing what its body read",
            .relation_reconstructed => "reconstructed by the plan instead of read",
            .relation_reconstructed_exactly => "reconstructed exactly, from a canonical " ++
                "aggregate view of it",
            .monotonic_reads_admitted => "the query is monotonic, so reading a reconstruction " ++
                "where it negates or counts cannot answer more",
            .membership_defined => "membership in a stored list is defined by the plan",
            .skolem_terms_eliminated => "relations split so that no reconstructed value stays unnameable",
            .instances_dropped => "instances that would have read a reconstructed value were dropped",
            .list_function_expanded => "expanded into the list functions the views expose",
            .view_split_at_its_aggregate => "split into the set it collects and the list " ++
                "functions reading it",
            .collected_sets_identified => "views proved to have collected one set, so the set " ++
                "each only named is the one the plan derives",
            .equivalent_view_preferred => "read in place of views it reconstructs the same " ++
                "relation as, being the smallest of them",
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
    /// A view mentioning a relation the query needs collects a value its own
    /// outer goals bind and its head does not keep.
    view_definition_correlates_template,
    /// The query reads a relation under negation or inside an aggregate that
    /// the plan would know only as far as the views prove it — a reconstructed
    /// relation, or one the query derives from one. Such a relation holds what
    /// the views prove existed, which can be less than it held; reading what is
    /// *not* in it, or counting what is, would then answer more than the query.
    ///
    /// Two proofs discharge this and nothing else does. Either a canonical
    /// aggregate view of that relation was available and used, so the plan
    /// knows the relation exactly and there is nothing incomplete to read; or
    /// the query is monotonic, so a smaller relation can only mean fewer
    /// answers. Example 6.4.1 has neither, and is the case this refuses.
    relation_read_non_positively,
    /// Two relations a plan may read store under one name and arity, so a
    /// lowered plan could not tell them apart.
    predicate_name_ambiguous,
    /// The query defines a list function by recursion over the structure of a
    /// list. Such a definition applied to a set the plan can only *name* builds
    /// a longer list at every step, which is Example 6.5.1's non-termination,
    /// and it is outside Theorem 6.5.1's class either way: a query's list
    /// function has to be one the views expose or a conjunction of ones they
    /// do.
    query_list_function_recursive,
    /// The query reads a collected set with a list function, and no view read
    /// *that* set with it. Either no view exposes the function at all, or the
    /// one that does collected a set nothing identified with this one — so
    /// there is no rule the plan could derive the goal from.
    list_function_set_unidentified,
    /// An auxiliary view collects this relation, and the plan would know it
    /// only as far as the views prove it.
    ///
    /// This is not the ordinary doubt about reading a reconstruction, and
    /// monotonicity does not touch it. The plan says a view's stored value is
    /// the sum of *the set the auxiliary view derived*; if that set is short a
    /// value, the plan is not reading a subset of `sum` but asserting a `sum`
    /// fact that is false, and a query monotonic in every relation it reads
    /// still answers wrongly from a false fact. Only a relation the plan knows
    /// exactly will do, which is Theorem 6.5.1's canonical-aggregate-view
    /// condition read strictly.
    set_collected_from_inexact_relation,

    pub fn text(self: PreconditionKind) []const u8 {
        return switch (self) {
            .relation_unavailable => "unavailable, and no view mentions it",
            .view_withheld => "the availability policy withholds this view's extension",
            .relation_not_reconstructible => "only views that cannot be inverted mention it",
            .view_definition_recursive => "its definition reads the relation it defines",
            .view_definition_not_conjunctive => "its definition is not a conjunction of " ++
                "relations and aggregates",
            .view_definition_uses_lists => "its definition mentions a list outside its aggregate",
            .view_definition_correlates_template => "its aggregate collects a value its own " ++
                "outer goals bind",
            .relation_read_non_positively => "known only as far as the views prove it, " ++
                "and read under negation or inside an aggregate",
            .predicate_name_ambiguous => "another relation the plan may read stores under this name",
            .query_list_function_recursive => "the query defines it by structural recursion, " ++
                "which a named set would nest without end",
            .list_function_set_unidentified => "no view read the collected set with it",
            .set_collected_from_inexact_relation => "a view's list function read a set " ++
                "collected from it, and the plan would know it only as far as the views prove",
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

/// A query's identity as text: the same bytes for two questions that differ
/// only in the variable names they were written with.
///
/// A plan cache needs this and nothing else needs it. It is taken of the
/// *compiled* query rather than of the folding IR, and deliberately: lowering
/// opens a scope of its own every time, so keying on the IR would mean
/// lowering — and growing the catalog's symbol table — before a cache could
/// tell it had seen the question before. Compiled identifiers are the
/// database's and do not move, so the only thing left to normalize is variable
/// spelling, renumbered by first occurrence.
///
/// It is not the renderer. A rendering is for a person and prints spellings;
/// this prints identifiers, is never shown to anybody, and has only to be
/// equal exactly when two queries are the same question. Two questions it
/// spells differently are a cache miss, which costs a fold and no correctness.
pub fn normalizeQuery(
    allocator: std.mem.Allocator,
    goals: []const syntax.Clause,
    rules: []const syntax.Rule,
) ![]u8 {
    var text: std.Io.Writer.Allocating = .init(allocator);
    defer text.deinit();
    var normalizer: Normalizer = .{ .allocator = allocator, .writer = &text.writer };
    defer normalizer.deinit();
    normalizer.program(goals, rules) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
        else => |other| return other,
    };
    return text.toOwnedSlice();
}

const Normalizer = struct {
    allocator: std.mem.Allocator,
    writer: *std.Io.Writer,
    variables: std.array_hash_map.Auto(syntax.Id, u32) = .empty,

    fn deinit(self: *Normalizer) void {
        self.variables.deinit(self.allocator);
        self.* = undefined;
    }

    fn program(
        self: *Normalizer,
        goals: []const syntax.Clause,
        rules: []const syntax.Rule,
    ) !void {
        for (rules) |rule| {
            if (rule.seed_argument) |position| try self.writer.print("seed{d}", .{position});
            try self.expr(rule.head);
            try self.writer.writeAll(":-");
            try self.clauses(rule.body);
            try self.writer.writeByte('.');
        }
        try self.clauses(goals);
        try self.writer.writeByte('?');
    }

    fn clauses(self: *Normalizer, values: []const syntax.Clause) anyerror!void {
        for (values) |clause| {
            switch (clause) {
                .relational, .builtin => |value| try self.expr(value),
                .negated => |value| {
                    try self.writer.writeByte('!');
                    try self.expr(value);
                },
                .aggregate => |value| {
                    try self.writer.writeAll("setof(");
                    try self.term(value.template);
                    try self.writer.writeByte(';');
                    try self.clauses(value.body);
                    try self.writer.writeByte(';');
                    try self.term(value.output);
                    try self.writer.writeByte(')');
                },
            }
            try self.writer.writeByte(',');
        }
    }

    fn expr(self: *Normalizer, value: syntax.Expr) !void {
        if (value.negated) try self.writer.writeByte('!');
        try self.writer.print("{s}{d}/{d}", .{
            @tagName(value.kind),
            value.predicate,
            value.terms.len,
        });
        try self.writer.writeByte('(');
        for (value.terms) |term_value| {
            try self.term(term_value);
            try self.writer.writeByte(',');
        }
        try self.writer.writeByte(')');
    }

    fn term(self: *Normalizer, value: syntax.Term) anyerror!void {
        switch (value) {
            .scalar => |constant| try self.writer.print("c{d}", .{constant}),
            .variable => |name| {
                const entry = try self.variables.getOrPut(self.allocator, name);
                if (!entry.found_existing) entry.value_ptr.* = @intCast(self.variables.count() - 1);
                try self.writer.print("x{d}", .{entry.value_ptr.*});
            },
            .nil => try self.writer.writeAll("[]"),
            .cons => |pair| {
                try self.writer.writeByte('[');
                try self.term(pair.head);
                try self.writer.writeByte('|');
                try self.term(pair.tail);
                try self.writer.writeByte(']');
            },
        }
    }
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
    // The query first says what it wants in the vocabulary the views kept. A
    // list function it defines for itself as a conjunction of ones they expose
    // is replaced by that definition; one it defines by structural recursion
    // is outside Theorem 6.5.1's class and there is nothing further to do.
    var expansion = try list_functions.expandQuery(
        allocator,
        &catalog.symbols,
        query.goals,
        query.rules,
    );
    defer expansion.deinit();
    const expanded: Query = .{ .goals = expansion.goals, .rules = expansion.rules };

    var reads: Reads = .{ .allocator = allocator };
    defer reads.deinit();
    try reads.walkGoals(expanded.goals, true);
    for (expanded.rules) |rule| {
        try reads.defined.put(allocator, headKey(rule), {});
        try reads.walkGoals(rule.body, true);
    }

    // Which views are two views wearing one head, and which of them collected
    // the same set. Decided before the relations are examined, because an
    // auxiliary view reads the relations its own aggregate reads and a plan
    // deriving it has to get them from somewhere.
    var splitting: Splitting = .{
        .allocator = allocator,
        .chase = .{ .allocator = allocator },
        .scope = try catalog.symbols.openScope(.generated),
    };
    defer splitting.deinit();
    try splitting.plan(catalog, &reads);

    var examination: Examination = .{ .allocator = allocator };
    defer examination.deinit();
    try examine(&examination, catalog, expanded, &reads);
    // Both refusals are about what a *plan* would have to hold, so a query
    // already inside the availability boundary meets neither: it is its own
    // plan, its own rules are the ones that run, and no set was ever named.
    if (examination.wanted.items.len != 0) {
        if (expansion.recursive) |key| try note(allocator, &examination.unmet, .{
            .kind = .query_list_function_recursive,
            .subject = .{ .base = key },
        });
        try splitting.requireIdentified(&examination, catalog, expanded, &reads);
        try splitting.requireExactlyCollected(&examination, catalog, &reads);
    }
    if (examination.unmet.items.len != 0) return .{ .unsupported = .{
        .allocator = allocator,
        .unmet = try examination.unmet.toOwnedSlice(allocator),
    } };

    if (examination.wanted.items.len == 0) {
        const copied = try fold_ir.cloneGoals(allocator, expanded.goals);
        errdefer fold_ir.freeGoals(allocator, copied);
        const rules = try cloneRules(allocator, expanded.rules);
        errdefer freeRules(allocator, rules);
        var notes: std.ArrayList(Transformation) = .empty;
        errdefer notes.deinit(allocator);
        for (expansion.expanded) |key| try notes.append(allocator, .{
            .kind = .list_function_expanded,
            .subject = .{ .base = key },
        });
        try notes.append(allocator, .{ .kind = .query_left_unchanged });
        return .{ .folded = .{
            .allocator = allocator,
            .guarantee = .equivalent,
            .goals = copied,
            .rules = rules,
            .transformations = try notes.toOwnedSlice(allocator),
        } };
    }

    var combined: std.ArrayList(fold_ir.Rule) = .empty;
    defer {
        for (combined.items) |rule| fold_ir.freeRule(allocator, rule);
        combined.deinit(allocator);
    }
    var members = false;
    for (examination.wanted.items) |id| {
        if (splitting.rewrites(id)) {
            // The outer goals hold no aggregate — every one of them is in the
            // auxiliary view — so nothing this emits reads a value out of a
            // list.
            try splitting.emit(catalog, id, &combined);
            continue;
        }
        var inverted = try inversion.invert(allocator, &catalog.symbols, catalog.view(id));
        errdefer inverted.deinit();
        try combined.ensureUnusedCapacity(allocator, inverted.rules.len);
        combined.appendSliceAssumeCapacity(inverted.rules);
        allocator.free(inverted.take());
        members = members or inverted.reads_members;
    }
    try splitting.emitAuxiliaryViews(catalog, &examination, &combined);
    // Reading a value back out of a stored list needs the rules that say what
    // being in a list means. They are the plan's own, added once however many
    // views turned out to need them.
    if (members) try inversion.appendMemberRules(allocator, &catalog.symbols, &combined);
    for (expanded.rules) |rule| {
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

    const goals = try fold_ir.cloneGoals(allocator, expanded.goals);
    errdefer fold_ir.freeGoals(allocator, goals);
    const transformations = try describe(
        allocator,
        catalog,
        &reads,
        &examination,
        &expansion,
        &splitting,
        members,
        eliminated,
    );
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

    /// Records one read of a base relation. An auxiliary view's own goals
    /// arrive here as well as the query's, because a plan that derives such a
    /// view reads them exactly as the query would have.
    fn record(self: *Reads, key: relation_store.PredicateKey, positive: bool) !bool {
        const entry = try self.relations.getOrPut(self.allocator, key);
        if (!entry.found_existing) entry.value_ptr.* = false;
        const was = entry.value_ptr.*;
        if (!positive) entry.value_ptr.* = true;
        return !entry.found_existing or (was != entry.value_ptr.*);
    }

    fn walkGoals(self: *Reads, goals: []const fold_ir.Goal, positive: bool) !void {
        for (goals) |goal| try self.walkGoal(goal, positive);
    }

    fn walkGoal(self: *Reads, goal: fold_ir.Goal, positive: bool) std.mem.Allocator.Error!void {
        switch (goal) {
            .relation => |relation| switch (relation.predicate) {
                .base => |key| _ = try self.record(key, positive and !relation.negated),
                .view => |reference| try self.views.put(self.allocator, reference.id, {}),
                // Nothing lowered from a query holds either, and a plan is
                // not folded a second time.
                .generated, .auxiliary => unreachable,
            },
            // An aggregate reads its body to count what is in it, which a
            // reconstruction cannot stand in for however the body is written.
            .aggregate => |aggregate| try self.walkGoals(aggregate.body, false),
            .builtin => {},
        }
    }
};

/// The relation a query rule defines. Only the query's own rules are asked,
/// and lowering makes every one of their heads a base relation; the fold's own
/// rules are never passed through here.
fn headKey(rule: fold_ir.Rule) relation_store.PredicateKey {
    return switch (rule.head.predicate) {
        .base => |key| key,
        .view => |reference| .{ .name = reference.name, .arity = reference.arity },
        .generated, .auxiliary => unreachable,
    };
}

/// A view that collects a set its head does not keep and then reads it, and
/// what became of that set.
const Split = struct {
    id: fold_ir.ViewId,
    layers: list_functions.Layers,
    /// Which auxiliary view collects this view's set, or null when the
    /// collecting half is not a rule and there is no auxiliary view to write.
    /// Two views share a tag exactly when they collect the same set.
    tag: ?u32,
    /// The Skolem set inverting this view's layer names: the set that must
    /// have been collected for its stored tuple to be there. What the chase is
    /// about, and — for a view with no auxiliary view behind it — the only
    /// name that set will ever have.
    function: fold_ir.Function,
};

/// Section 6.5's steps 2(a) and 4, together: which views are split, which of
/// them collect one set, and what a set a Skolem term names turns out to be.
///
/// The two belong together because neither is worth anything alone. Splitting
/// a view without identifying the sets leaves two Skolem sets with no relation
/// to each other, which is exactly where the dissertation's derivation gets
/// stuck; identifying sets without splitting has nothing to identify them by,
/// because the dependency is a property of the auxiliary view.
const Splitting = struct {
    allocator: std.mem.Allocator,
    chase: list_functions.Chase,
    /// Where the Skolem set of each layer is named.
    scope: fold_ir.Scope,
    splits: std.ArrayList(Split) = .empty,
    /// The auxiliary views whose rules the plan has: one per tag some split
    /// view actually contributed.
    emitted: std.ArrayList(u32) = .empty,
    identified: bool = false,
    next_tag: u32 = 0,

    fn deinit(self: *Splitting) void {
        for (self.splits.items) |*split| split.layers.deinit();
        self.splits.deinit(self.allocator);
        self.emitted.deinit(self.allocator);
        self.chase.deinit();
        self.* = undefined;
    }

    fn find(self: *const Splitting, id: fold_ir.ViewId) ?*const Split {
        for (self.splits.items) |*split| if (split.id == id) return split;
        return null;
    }

    /// Splits every view whose list functions the query is going to need, and
    /// records what its auxiliary view will read.
    ///
    /// Run to a fixpoint, because an auxiliary view's own goals are reads like
    /// any others and can make a further view's list functions needed. It ends
    /// because each round either splits a view the catalog holds or changes
    /// nothing.
    fn plan(self: *Splitting, catalog: *view_catalog.Catalog, reads: *Reads) !void {
        var changed = true;
        while (changed) {
            changed = false;
            for (catalog.views.items) |*view| {
                if (self.find(view.id) != null) continue;
                if (!view.readable()) continue;
                if (inversion.obstacle(view) != null) continue;
                var read = (try list_functions.layers(self.allocator, view.definition)) orelse
                    continue;
                errdefer read.deinit();
                if (!wanted(&read, catalog, reads)) {
                    read.deinit();
                    continue;
                }
                try self.record(catalog, view, &read, reads);
                changed = true;
                // The list only grows, and `find` reads it, so a pointer taken
                // before this round would be stale.
                break;
            }
        }
    }

    /// Whether the query needs something only this view's layer can give it: a
    /// list function it reads, that nothing else already supplies.
    fn wanted(
        read: *const list_functions.Layers,
        catalog: *const view_catalog.Catalog,
        reads: *const Reads,
    ) bool {
        for (read.functions) |function| {
            const key = switch (function.predicate) {
                .base => |value| value,
                else => continue,
            };
            if (!reads.relations.contains(key)) continue;
            if (catalog.baseAvailable(key)) continue;
            if (reads.defined.contains(key)) continue;
            return true;
        }
        return false;
    }

    fn record(
        self: *Splitting,
        catalog: *view_catalog.Catalog,
        view: *const view_catalog.View,
        read: *list_functions.Layers,
        reads: *Reads,
    ) !void {
        // Every collected set gets a name of its own, whether or not anything
        // will be proved about it. A set with only that name is one no plan
        // can read, which is what the chase reports by leaving it alone.
        const function = try catalog.symbols.freshFunction(self.scope);
        _ = try self.chase.intern(.{ .skolem = function });

        var tag: ?u32 = null;
        if (read.auxiliary) |_| {
            // The tag is the set's identity, so a view collecting a set
            // another view already collects joins that one rather than
            // starting a class of its own. This is the whole of the functional
            // dependency: `va` is functional in its key, so two views written
            // against one `va` read one set for one group.
            tag = self.next_tag;
            for (self.splits.items) |*existing| {
                if (!try list_functions.collectTheSameSet(self.allocator, &existing.layers, read))
                    continue;
                tag = existing.tag;
                break;
            } else self.next_tag += 1;
            try self.chase.unite(.{ .skolem = function }, .{ .collected = tag.? });

            // What the auxiliary view will read. Its outer goals are read
            // positively; the relations inside its aggregate are not, because
            // it counts what they hold, and a plan that knows one of them only
            // as far as the views prove it would collect a smaller set and
            // then claim the stored sum was of *that*. Recording them before
            // the split is kept, so that a failure here leaves the caller
            // owning what it handed over.
            for (read.auxiliary.?.outer) |relation| switch (relation.predicate) {
                .base => |key| _ = try reads.record(key, true),
                else => {},
            };
            try recordAggregate(reads, read.aggregate.body);
        }
        try self.splits.append(self.allocator, .{
            .id = view.id,
            .layers = read.*,
            .tag = tag,
            .function = function,
        });
    }

    fn recordAggregate(reads: *Reads, goals: []const fold_ir.Goal) !void {
        for (goals) |goal| switch (goal) {
            .relation => |relation| switch (relation.predicate) {
                .base => |key| _ = try reads.record(key, false),
                else => {},
            },
            .aggregate => |aggregate| try recordAggregate(reads, aggregate.body),
            .builtin => {},
        };
    }

    /// Refuses a query whose list functions read a set no view read.
    ///
    /// A plan holds no list-function definitions, so a goal over a collected
    /// set is derivable only from the inverse of a view that read *that* set
    /// with *that* function. Without both there is no rule to derive it from
    /// and the plan would quietly answer nothing, which is sound and is not an
    /// answer to the question that was asked.
    fn requireIdentified(
        self: *Splitting,
        examination: *Examination,
        catalog: *const view_catalog.Catalog,
        query: Query,
        reads: *const Reads,
    ) !void {
        try self.requireIdentifiedIn(examination, catalog, query.goals, reads);
        for (query.rules) |rule|
            try self.requireIdentifiedIn(examination, catalog, rule.body, reads);
    }

    fn requireIdentifiedIn(
        self: *Splitting,
        examination: *Examination,
        catalog: *const view_catalog.Catalog,
        body: []const fold_ir.Goal,
        reads: *const Reads,
    ) !void {
        var sets: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
        defer sets.deinit(self.allocator);
        for (body) |goal| switch (goal) {
            .aggregate => |aggregate| if (aggregate.output == .variable)
                try sets.put(self.allocator, aggregate.output.variable, {}),
            else => {},
        };
        if (sets.count() == 0) return;

        for (body) |goal| {
            const relation = switch (goal) {
                .relation => |value| value,
                else => continue,
            };
            if (relation.negated) continue;
            const key = switch (relation.predicate) {
                .base => |value| value,
                else => continue,
            };
            if (catalog.baseAvailable(key) or reads.defined.contains(key)) continue;
            var reads_set = false;
            for (relation.terms) |term| switch (term) {
                .variable => |variable| if (sets.contains(variable)) {
                    reads_set = true;
                },
                else => {},
            };
            if (!reads_set) continue;
            if (try self.exposes(key)) {
                self.identified = true;
                continue;
            }
            try note(examination.allocator, &examination.unmet, .{
                .kind = .list_function_set_unidentified,
                .subject = .{ .base = key },
            });
        }
    }

    /// Refuses a plan whose auxiliary view would collect from a relation it
    /// knows incompletely.
    ///
    /// Everywhere else in this module a reconstruction being a subset costs
    /// answers and keeps containment. Here it does not, and the difference is
    /// worth being exact about. The layer rule says the value a view stored is
    /// what the list function returns *of the set the auxiliary view derived*.
    /// Derive a smaller set and the rule asserts something that never held —
    /// not less of `sum` but a different `sum` — and a query that reads it
    /// answers what it should not, however monotonic it is. So the relations
    /// inside the aggregate have to be known exactly, and Theorem 6.5.1's
    /// canonical aggregate views are what makes them so.
    fn requireExactlyCollected(
        self: *Splitting,
        examination: *Examination,
        catalog: *const view_catalog.Catalog,
        reads: *const Reads,
    ) !void {
        for (self.splits.items) |*split| {
            if (split.tag == null) continue;
            for (examination.wanted.items) |id| {
                if (id != split.id) continue;
                try requireExact(examination, catalog, reads, split.layers.aggregate.body);
            }
        }
    }

    /// Whether some split view read a set with this function and the chase
    /// knows which set that was.
    fn exposes(self: *Splitting, key: relation_store.PredicateKey) !bool {
        for (self.splits.items) |*split| {
            for (split.layers.functions) |function| {
                if (!function.predicate.equals(.{ .base = key })) continue;
                if ((try self.chase.resolve(.{ .skolem = split.function })) != null) return true;
            }
        }
        return false;
    }

    /// Whether this view's rules come from the split rather than from the
    /// ordinary Inverse Method. A view whose collecting half is not a rule has
    /// no auxiliary view to write against, so there is nothing to rewrite and
    /// it is inverted as it stands.
    fn rewrites(self: *const Splitting, id: fold_ir.ViewId) bool {
        const split = self.find(id) orelse return false;
        return split.tag != null;
    }

    /// The rules a split view contributes, in place of the ones the ordinary
    /// Inverse Method would have given it.
    ///
    /// Two halves. The outer goals are inverted exactly as any projection is,
    /// which is what still reconstructs what the view's own body read. The
    /// layer becomes one rule per list function, and this is where the chase
    /// is spent: the set that function read is a Skolem term, and a Skolem
    /// term proved to be an auxiliary view's set is replaced by the variable
    /// that view binds. The rule saying the auxiliary view holds that set is
    /// then dropped, because after the substitution it says only that the
    /// auxiliary view holds what it holds.
    fn emit(
        self: *Splitting,
        catalog: *view_catalog.Catalog,
        id: fold_ir.ViewId,
        into: *std.ArrayList(fold_ir.Rule),
    ) !void {
        const split = self.find(id).?;
        const view = catalog.view(id);
        try self.emitOuterInverse(catalog, view, split, into);
        try self.emitLayerInverse(catalog, view, split, into);
        self.identified = true;
        for (self.emitted.items) |already| {
            if (already == split.tag.?) break;
        } else try self.emitted.append(self.allocator, split.tag.?);
    }

    fn emitOuterInverse(
        self: *Splitting,
        catalog: *view_catalog.Catalog,
        view: *const view_catalog.View,
        split: *const Split,
        into: *std.ArrayList(fold_ir.Rule),
    ) !void {
        const outer = split.layers.auxiliary.?.outer;
        const goals = try self.allocator.alloc(fold_ir.Goal, outer.len);
        defer self.allocator.free(goals);
        for (outer, goals) |relation, *slot| slot.* = .{ .relation = relation };

        // A view of this catalog with the same head and only the outer goals.
        // Everything `obstacle` refuses is refused of the original too, since
        // this body is a subset of that one, so the inversion is admissible
        // exactly when the view was.
        var outer_only = view.*;
        outer_only.definition = .{
            .scope = view.definition.scope,
            .head = view.definition.head,
            .body = goals,
        };
        var inverted = try inversion.invert(self.allocator, &catalog.symbols, &outer_only);
        errdefer inverted.deinit();
        try into.ensureUnusedCapacity(self.allocator, inverted.rules.len);
        into.appendSliceAssumeCapacity(inverted.rules);
        self.allocator.free(inverted.take());
    }

    /// One rule per list function: `λ(S, T̄) :- v(X̄), va(K̄, S)`.
    ///
    /// What the Inverse Method writes here is `λ(f(X̄), T̄) :- v(X̄)`, naming
    /// the set the view read and leaving it unreadable. `f(X̄)` and the set
    /// `va(K̄, S)` derives are the same set — that is the dependency, and the
    /// chase has already decided it — so the name is replaced by the variable
    /// the auxiliary view binds, and the goal binding it is joined on. The
    /// companion rule `va(K̄, f(X̄)) :- v(X̄)` is not written at all: after the
    /// same substitution it says the auxiliary view holds what it holds.
    fn emitLayerInverse(
        self: *Splitting,
        catalog: *view_catalog.Catalog,
        view: *const view_catalog.View,
        split: *const Split,
        into: *std.ArrayList(fold_ir.Rule),
    ) !void {
        const symbols = &catalog.symbols;
        const definition = view.definition;
        const auxiliary = split.layers.auxiliary.?;
        const scope = try symbols.openScope(.generated);

        var head_variables: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
        defer head_variables.deinit(self.allocator);
        try fold_ir.collectRelationVariables(self.allocator, definition.head, &head_variables);

        var renaming: fold_ir.Substitution = .{};
        defer renaming.deinit(self.allocator);
        for (head_variables.keys()) |variable| {
            const fresh: fold_ir.Term = .{ .variable = switch (symbols.originOf(variable)) {
                .user => |name| try symbols.freshUserVariable(scope, name),
                .generated => try symbols.freshVariable(scope),
            } };
            try renaming.put(self.allocator, variable, fresh);
        }
        try renaming.put(
            self.allocator,
            split.layers.set,
            .{ .variable = try symbols.freshVariable(scope) },
        );

        const stored = try fold_ir.substituteTerms(
            self.allocator,
            definition.head.terms,
            &renaming,
        );
        defer fold_ir.freeTerms(self.allocator, stored);

        for (split.layers.functions) |function| {
            const head_terms = try fold_ir.substituteTerms(
                self.allocator,
                function.terms,
                &renaming,
            );
            errdefer fold_ir.freeTerms(self.allocator, head_terms);

            const collected = try self.allocator.alloc(fold_ir.Term, auxiliary.arity());
            errdefer self.allocator.free(collected);
            for (auxiliary.key, collected[0..auxiliary.key.len]) |variable, *slot|
                slot.* = renaming.get(variable).?;
            collected[collected.len - 1] = renaming.get(split.layers.set).?;

            const body = try self.allocator.alloc(fold_ir.Goal, 2);
            errdefer self.allocator.free(body);
            body[0] = .{ .relation = .{
                .predicate = view.predicate(),
                .terms = try fold_ir.cloneTerms(self.allocator, stored),
                .provenance = .generated,
            } };
            errdefer fold_ir.freeGoal(self.allocator, body[0]);
            body[1] = .{ .relation = .{
                .predicate = self.auxiliaryPredicate(split),
                .terms = collected,
                .provenance = .generated,
            } };
            try into.append(self.allocator, .{
                .scope = scope,
                .head = .{
                    .predicate = function.predicate,
                    .terms = head_terms,
                    .provenance = .generated,
                },
                .body = body,
            });
        }
    }

    fn auxiliaryPredicate(self: *const Splitting, split: *const Split) fold_ir.Predicate {
        _ = self;
        return .{ .auxiliary = .{ .collected = .{
            .tag = split.tag.?,
            .arity = split.layers.auxiliary.?.arity(),
        } } };
    }

    /// The auxiliary views themselves: `va(K̄, S) :- Φ, setof(Ȳ, Ψ, S)`, the
    /// half of each split view that collects.
    ///
    /// This is the relation with no stored extension that F3 declined to
    /// introduce, and the reason it earns its keep here is that the plan
    /// *derives* it rather than inverting it. Its tuples are the sets the
    /// reconstructed relations really collect, which is what a Skolem set can
    /// be replaced by; F3's objection was to reconstructing an auxiliary and
    /// then inverting it again, and nothing here inverts one.
    fn emitAuxiliaryViews(
        self: *Splitting,
        catalog: *view_catalog.Catalog,
        examination: *const Examination,
        into: *std.ArrayList(fold_ir.Rule),
    ) !void {
        var written: std.ArrayList(u32) = .empty;
        defer written.deinit(self.allocator);
        for (self.emitted.items) |tag| {
            for (written.items) |already| {
                if (already == tag) break;
            } else {
                const split = self.representative(tag, examination) orelse continue;
                try written.append(self.allocator, tag);
                try self.emitAuxiliaryView(catalog, split, into);
            }
        }
    }

    /// Which split's definition an auxiliary view is written from. Any of the
    /// views sharing the tag will do — that they say the same thing is what
    /// the tag means — so the first one the plan inverts is taken.
    fn representative(
        self: *const Splitting,
        tag: u32,
        examination: *const Examination,
    ) ?*const Split {
        for (self.splits.items) |*split| {
            if (split.tag == null or split.tag.? != tag) continue;
            for (examination.wanted.items) |id| if (id == split.id) return split;
        }
        return null;
    }

    fn emitAuxiliaryView(
        self: *Splitting,
        catalog: *view_catalog.Catalog,
        split: *const Split,
        into: *std.ArrayList(fold_ir.Rule),
    ) !void {
        const read = &split.layers;
        const auxiliary = read.auxiliary.?;
        const terms = try self.allocator.alloc(fold_ir.Term, auxiliary.arity());
        defer self.allocator.free(terms);
        for (auxiliary.key, terms[0..auxiliary.key.len]) |variable, *slot|
            slot.* = .{ .variable = variable };
        terms[terms.len - 1] = .{ .variable = read.set };

        const goals = try self.allocator.alloc(fold_ir.Goal, auxiliary.outer.len + 1);
        defer self.allocator.free(goals);
        for (auxiliary.outer, goals[0..auxiliary.outer.len]) |relation, *slot| {
            var copy = relation;
            copy.provenance = .generated;
            slot.* = .{ .relation = copy };
        }
        var collecting = read.aggregate;
        collecting.provenance = .generated;
        goals[goals.len - 1] = .{ .aggregate = collecting };

        // Borrowed throughout: renaming is what copies it, into a scope of its
        // own so that the auxiliary view's variables are nobody else's.
        const borrowed: fold_ir.Rule = .{
            .scope = catalog.view(split.id).definition.scope,
            .head = .{
                .predicate = self.auxiliaryPredicate(split),
                .terms = terms,
                .provenance = .generated,
            },
            .body = goals,
        };
        const renamed = try fold_ir.renameRule(self.allocator, &catalog.symbols, borrowed);
        errdefer fold_ir.freeRule(self.allocator, renamed);
        try into.append(self.allocator, renamed);
    }
};

/// Notes every relation these goals read that the plan would not know exactly.
fn requireExact(
    examination: *Examination,
    catalog: *const view_catalog.Catalog,
    reads: *const Reads,
    goals: []const fold_ir.Goal,
) std.mem.Allocator.Error!void {
    for (goals) |goal| switch (goal) {
        .relation => |relation| switch (relation.predicate) {
            .base => |key| {
                if (catalog.baseAvailable(key)) continue;
                if (!reads.defined.contains(key) and examination.isExact(key)) continue;
                try note(examination.allocator, &examination.unmet, .{
                    .kind = .set_collected_from_inexact_relation,
                    .subject = .{ .base = key },
                });
            },
            else => {},
        },
        .aggregate => |aggregate| try requireExact(examination, catalog, reads, aggregate.body),
        .builtin => {},
    };
}

/// What a fold worked out about the query before building anything: which
/// views it has to invert, which of the relations it reconstructs it will know
/// exactly rather than only as far as the views prove, whether the monotonic
/// class had to be appealed to, and what it could not get at all.
const Examination = struct {
    allocator: std.mem.Allocator,
    unmet: std.ArrayList(Precondition) = .empty,
    wanted: std.ArrayList(fold_ir.ViewId) = .empty,
    /// Relations a canonical aggregate view of themselves reconstructs, which
    /// Lemma 6.4.2 makes equivalent rather than merely contained.
    exact: std.ArrayList(relation_store.PredicateKey) = .empty,
    /// Whether some read stood only because the query is monotonic.
    monotonic_admitted: bool = false,
    /// Views chosen over rivals that would have reconstructed the same
    /// relation. Recorded so a plan can say that a choice was made and which
    /// way it went, since nothing else in the rendering would show it.
    preferred: std.ArrayList(fold_ir.ViewId) = .empty,

    fn deinit(self: *Examination) void {
        self.preferred.deinit(self.allocator);
        self.exact.deinit(self.allocator);
        self.wanted.deinit(self.allocator);
        self.unmet.deinit(self.allocator);
        self.* = undefined;
    }

    fn isExact(self: *const Examination, key: relation_store.PredicateKey) bool {
        for (self.exact.items) |known| {
            if (known.name == key.name and known.arity == key.arity) return true;
        }
        return false;
    }
};

/// Decides, relation by relation, whether the plan can get what the query
/// reads: it is available, the query defines it, or some invertible view reads
/// it. Records the views to invert, and the preconditions of every relation
/// none of that covers.
fn examine(
    examination: *Examination,
    catalog: *const view_catalog.Catalog,
    query: Query,
    reads: *const Reads,
) !void {
    const allocator = examination.allocator;
    const rules = query.rules;
    const unmet = &examination.unmet;
    const wanted = &examination.wanted;
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

    // The views that could reconstruct one relation, collected before any of
    // them is chosen: which ones the plan wants is a question about the whole
    // set, not about each in turn.
    var usable: std.ArrayList(fold_ir.ViewId) = .empty;
    defer usable.deinit(allocator);
    var canonical: std.ArrayList(fold_ir.ViewId) = .empty;
    defer canonical.deinit(allocator);

    for (reads.relations.keys()) |key| {
        if (reads.defined.contains(key)) continue;
        if (catalog.baseAvailable(key)) continue;
        const subject: fold_ir.Predicate = .{ .base = key };

        usable.clearRetainingCapacity();
        canonical.clearRetainingCapacity();
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
                        .aggregate_template_correlated => .view_definition_correlates_template,
                    },
                    .subject = candidate.predicate(),
                });
                continue;
            }
            try usable.append(allocator, candidate.id);
            // Lemma 6.4.2: reading the lists of a canonical aggregate view of
            // this relation back out returns the relation itself, so the plan
            // knows it exactly and there is nothing incomplete left to ask
            // about. The three conditions are one condition — it has to be
            // canonical *for this relation*, its extension has to be readable,
            // and the plan has to be inverting it — and this branch is where
            // the other two are already settled.
            if (candidate.isCanonicalFor(key)) try canonical.append(allocator, candidate.id);
        }

        if (!mentioned) {
            try note(allocator, unmet, .{ .kind = .relation_unavailable, .subject = subject });
        } else if (usable.items.len == 0) {
            try note(allocator, unmet, .{ .kind = .relation_not_reconstructible, .subject = subject });
        } else if (canonical.items.len != 0) {
            // One canonical view returns the whole relation, so the rest add
            // nothing to it and the plan is the same plan without them. Which
            // one to keep is therefore a cost question and not a semantic one,
            // which is the only shape a cost question is allowed to take here.
            const chosen = try smallestExtension(catalog, canonical.items);
            try noteView(allocator, wanted, chosen);
            if (usable.items.len > 1) try examination.preferred.append(allocator, chosen);
            try examination.exact.append(allocator, key);
        } else {
            // Nothing here reconstructs the relation whole, so every view that
            // reconstructs part of it is worth inverting: each proves tuples
            // the others do not, and leaving one out is what would cost
            // maximality.
            for (usable.items) |id| try noteView(allocator, wanted, id);
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

    // The refusal F2 recorded stands as the default, and two proofs discharge
    // it. One is per relation and has been settled above: a relation a
    // canonical aggregate view reconstructs exactly never reached `inexact` in
    // the first place. The other is a property of the whole query, and it
    // permits the read rather than removing the doubt — if the query's answers
    // can only grow with the relations it reads, then reading a reconstruction
    // returns fewer of them, never others.
    const monotonic = monotonicity.ofQuery(query.goals, query.rules);
    for (reads.relations.keys(), reads.relations.values()) |key, non_positive| {
        if (!non_positive or !inexact.contains(key)) continue;
        if (monotonic) {
            examination.monotonic_admitted = true;
            continue;
        }
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
            // A view's stored extension is exact whatever it was computed
            // from, and so is a value read back out of one.
            .view, .generated, .auxiliary => {},
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
    return goalsRead(view.definition.body, key);
}

fn goalsRead(goals: []const fold_ir.Goal, key: relation_store.PredicateKey) bool {
    for (goals) |goal| switch (goal) {
        .relation => |relation| if (relation.predicate.equals(.{ .base = key })) return true,
        // What an aggregate collected is read from the relations in its body,
        // which are as much a part of what the view remembers as its outer
        // goals are.
        .aggregate => |aggregate| if (goalsRead(aggregate.body, key)) return true,
        .builtin => {},
    };
    return false;
}

/// The smallest of several views that each reconstruct one relation exactly,
/// and the lowest identity among those that tie.
///
/// The tie-break is not decoration. A plan chosen on cost still has to be the
/// same plan whenever the same catalog is asked the same question, or a cached
/// plan and a freshly folded one would be two different programs; and a
/// catalog told nothing about where its extensions are reports every view as
/// empty, in which case this is exactly "the first one declared".
fn smallestExtension(
    catalog: *const view_catalog.Catalog,
    candidates: []const fold_ir.ViewId,
) !fold_ir.ViewId {
    var chosen = candidates[0];
    var smallest = try catalog.extent(chosen);
    for (candidates[1..]) |id| {
        const size = try catalog.extent(id);
        if (size >= smallest) continue;
        chosen = id;
        smallest = size;
    }
    return chosen;
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
    examination: *const Examination,
    expansion: *const list_functions.Expansion,
    splitting: *const Splitting,
    members: bool,
    eliminated: inversion.Elimination,
) ![]Transformation {
    var notes: std.ArrayList(Transformation) = .empty;
    errdefer notes.deinit(allocator);
    for (expansion.expanded) |key| try notes.append(allocator, .{
        .kind = .list_function_expanded,
        .subject = .{ .base = key },
    });
    for (examination.wanted.items) |id| {
        if (splitting.rewrites(id)) try notes.append(allocator, .{
            .kind = .view_split_at_its_aggregate,
            .subject = catalog.view(id).predicate(),
        });
        try notes.append(allocator, .{
            .kind = .view_inverted,
            .subject = catalog.view(id).predicate(),
        });
    }
    for (examination.preferred.items) |id| try notes.append(allocator, .{
        .kind = .equivalent_view_preferred,
        .subject = catalog.view(id).predicate(),
    });
    for (reads.relations.keys()) |key| {
        if (reads.defined.contains(key) or catalog.baseAvailable(key)) continue;
        try notes.append(allocator, .{
            .kind = if (examination.isExact(key))
                .relation_reconstructed_exactly
            else
                .relation_reconstructed,
            .subject = .{ .base = key },
        });
    }
    if (splitting.identified)
        try notes.append(allocator, .{ .kind = .collected_sets_identified });
    if (examination.monotonic_admitted)
        try notes.append(allocator, .{ .kind = .monotonic_reads_admitted });
    if (members) try notes.append(allocator, .{ .kind = .membership_defined });
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

/// The name `variable` runs under once a plan holding it is lowered, which
/// is how a caller finds a query variable of its own among a plan's answers.
pub fn executableVariableName(
    allocator: std.mem.Allocator,
    strings: *string_table.StringTable,
    symbols: *const fold_ir.Symbols,
    variable: fold_ir.Variable,
) !syntax.Id {
    var lowering: Lowering = .{ .allocator = allocator, .strings = strings, .symbols = symbols };
    return lowering.variableName(variable);
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
            .auxiliary => |relation| blk: {
                var spelling: std.Io.Writer.Allocating = .init(self.allocator);
                defer spelling.deinit();
                relation.write(&spelling.writer) catch return error.OutOfMemory;
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

/// A catalog holding one view over `edge`, and the tables its names resolve
/// against.
///
/// Which view it is decides how much of `edge` a plan gets back, which is the
/// axis F4's discharges turn on. `path(X, Y) :- edge(X, Y)` is Definition
/// 6.4.3's copy — a canonical aggregate view of `edge`, so inverting it
/// returns `edge` itself. `path(X, Z) :- edge(X, Y), edge(Y, Z)` remembers
/// only the pairs two edges apart, so inverting it returns some of `edge` and
/// says nothing about the rest.
const Fixture = struct {
    strings: string_table.StringTable,
    scalars: scalar.Store,
    catalog: view_catalog.Catalog,
    path: syntax.Id,
    edge: syntax.Id,
    x: syntax.Id,
    y: syntax.Id,
    view: fold_ir.ViewId,

    const Shape = enum { copy, hop };

    fn init(allocator: std.mem.Allocator, availability: view_catalog.Availability) !Fixture {
        return build(allocator, availability, .copy);
    }

    fn build(
        allocator: std.mem.Allocator,
        availability: view_catalog.Availability,
        shape: Shape,
    ) !Fixture {
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
        const z = try fixture.strings.intern("Z");

        var head_terms = [_]syntax.Term{
            .{ .variable = fixture.x },
            .{ .variable = switch (shape) {
                .copy => fixture.y,
                .hop => z,
            } },
        };
        var first = [_]syntax.Term{ .{ .variable = fixture.x }, .{ .variable = fixture.y } };
        var second = [_]syntax.Term{ .{ .variable = fixture.y }, .{ .variable = z } };
        var body = [_]syntax.Clause{
            .{ .relational = .{ .predicate = fixture.edge, .terms = &first } },
            .{ .relational = .{ .predicate = fixture.edge, .terms = &second } },
        };
        fixture.view = try fixture.catalog.define(.{
            .head = .{ .predicate = fixture.path, .terms = &head_terms },
            .body = body[0..switch (shape) {
                .copy => 1,
                .hop => 2,
            }],
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
    // still only maximally contained rather than equivalent: the guarantee is
    // about the plan, and the plan's other relations are not this one. What
    // this relation gets back is exact, because copying it is Definition
    // 6.4.3's first canonical view.
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
        \\  reconstructed exactly, from a canonical aggregate view of it: edge/2
        \\
    , rendered);
}

test "a reconstruction cannot stand in for a relation read under negation" {
    const allocator = testing.allocator;
    var fixture = try Fixture.build(allocator, .materialized, .hop);
    defer fixture.deinit();

    // path(A, B), not edge(B, A). The view remembers the pairs two edges
    // apart, so it reconstructs what `edge` held only as far as it can prove
    // it held it, and asking what is *not* there of a relation known
    // incompletely answers more than the query does.
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

test "a canonical view of the relation answers the objection to negating it" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator, .materialized);
    defer fixture.deinit();

    // The same query as above, against `path(X, Y) :- edge(X, Y)` instead —
    // Definition 6.4.3's copy. Lemma 6.4.2 makes inverting it equivalent to
    // reading `edge`, so the plan does not know the relation incompletely and
    // there is nothing left for the refusal to object to.
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
    try testing.expectEqual(Guarantee.maximally_contained, outcome.guarantee());

    // Withholding that view is what takes the discharge away, and the fold
    // then has nothing at all rather than a weaker plan.
    fixture.catalog.views.items[@intFromEnum(fixture.view)].availability = .withheld;
    var withheld = try foldQuery(allocator, &fixture.catalog, .{ .goals = goals });
    defer withheld.deinit();
    try testing.expectEqual(Guarantee.unsupported, withheld.guarantee());
}

test "a question keys on what it asks, not on what it spells its variables" {
    const allocator = testing.allocator;
    var strings: string_table.StringTable = .init(allocator);
    defer strings.deinit();

    const edge = try strings.intern("edge");
    const path = try strings.intern("path");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    const a = try strings.intern("A");
    const b = try strings.intern("B");

    var xy = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var ab = [_]syntax.Term{ .{ .variable = a }, .{ .variable = b } };
    var yx = [_]syntax.Term{ .{ .variable = y }, .{ .variable = x } };
    var asked = [_]syntax.Clause{
        .{ .relational = .{ .predicate = edge, .terms = &xy } },
        .{ .relational = .{ .predicate = path, .terms = &xy } },
    };
    var renamed = [_]syntax.Clause{
        .{ .relational = .{ .predicate = edge, .terms = &ab } },
        .{ .relational = .{ .predicate = path, .terms = &ab } },
    };
    var reversed = [_]syntax.Clause{
        .{ .relational = .{ .predicate = edge, .terms = &xy } },
        .{ .relational = .{ .predicate = path, .terms = &yx } },
    };
    var elsewhere = [_]syntax.Clause{
        .{ .relational = .{ .predicate = path, .terms = &xy } },
        .{ .relational = .{ .predicate = path, .terms = &xy } },
    };

    const key = try normalizeQuery(allocator, &asked, &.{});
    defer allocator.free(key);
    // The same question written with other variable names is the same
    // question, and a cache that could not see that would fold it again every
    // time — lowering opens a fresh scope, so no two askings share a variable.
    const same = try normalizeQuery(allocator, &renamed, &.{});
    defer allocator.free(same);
    try testing.expectEqualStrings(key, same);

    // Renaming is not rearranging. Reading the second relation the other way
    // round is a different join, and a key that could not tell the two apart
    // would answer one question with the other's plan.
    const swapped = try normalizeQuery(allocator, &reversed, &.{});
    defer allocator.free(swapped);
    try testing.expect(!std.mem.eql(u8, key, swapped));

    // So is the relation read.
    const other = try normalizeQuery(allocator, &elsewhere, &.{});
    defer allocator.free(other);
    try testing.expect(!std.mem.eql(u8, key, other));

    // A query's rules are part of the question, so the same goals under a
    // different program key apart.
    var edge_only = [_]syntax.Clause{.{ .relational = .{ .predicate = edge, .terms = &xy } }};
    const rules = [_]syntax.Rule{.{
        .head = .{ .predicate = path, .terms = &xy },
        .body = &edge_only,
    }};
    const with_rules = try normalizeQuery(allocator, &asked, &rules);
    defer allocator.free(with_rules);
    try testing.expect(!std.mem.eql(u8, key, with_rules));
}
