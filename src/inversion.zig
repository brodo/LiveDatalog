//! Reconstructing the relations a view's body read, and removing the terms
//! that reconstruction invents.
//!
//! A view stores what its definition kept. Inverting it runs the definition
//! backwards: from a stored tuple, each body goal must have had a fact behind
//! it, so each becomes a rule that reconstructs one. A variable the head kept
//! is still a value the plan can name, so it stays a variable. A variable the
//! head projected away is not — the tuple says such a value existed without
//! saying which — so it becomes a Skolem term applied to the values that
//! identify the witness. One function per projected variable, shared by every
//! rule the view yields: the reconstructed facts have to join back up, and in
//! Chapter 6's even-length-path example they only do because the node between
//! `X` and `Z` is the same `f(X, Z)` in both halves.
//!
//! A definition may also *collect* — `setof` gathers every value satisfying
//! its body into one list, and the head keeps that list. Inverting such a
//! definition is the same idea read the other way: the list is the evidence,
//! so each value in it is a fact the aggregate's body must have had, and the
//! inverse rules reach it with `$member`. That relation is not a builtin and
//! does not need to be — a list the database holds already holds each of its
//! own tails, so three rules over the values it has are enough. Aggregates
//! nest by chaining: collecting `Y!T` pairs means binding one of them binds
//! `T`, which is the next list to read out of.
//!
//! Two things about collecting change what a witness is, and both are easy to
//! get wrong. A value projected out of an aggregate's *own* body has one
//! witness for each value collected rather than one for the stored tuple, so
//! its Skolem term is applied to the collected value too; naming them all
//! alike would let a query join two elements through a witness the database
//! never had in common. And two aggregates side by side mean their own values
//! by the names they share, because the language says a value the surrounding
//! goals do not bind belongs to the aggregate that mentions it — so each gets
//! its own function, and inverting them as one would join what the definition
//! kept apart.
//!
//! A Skolem term cannot be evaluated, so a plan holding one is not yet a plan.
//! Eliminating them is the last part of this module, and it is not a
//! substitution: there is no value to put in a Skolem term's place. What there
//! is instead is the observation that such a term is fully described by its
//! function and its arguments, so a relation holding one can be *split* — one
//! relation per assignment of a function to each column, with the column
//! spread across the arguments the function was applied to. The split
//! relations hold ordinary values, the query's own rules are instantiated once
//! per split they can read, and the answers are the tuples of the split where
//! every column stayed ordinary, which is exactly the answers a Skolem term
//! never reached.
//!
//! The splitting is what bounds this: Skolem terms are built only in the heads
//! of inverse rules, out of values read from a view's extension, so they never
//! nest, and the number of splits is therefore finite.

const std = @import("std");
const fold_ir = @import("fold_ir.zig");
const view_catalog = @import("view_catalog.zig");

/// Why a definition is outside the class the Inverse Method inverts.
///
/// Each of these is a later phase's problem rather than a defect: a view whose
/// aggregate output the head does not keep is F4's, one carrying a list is
/// F5's, and one reading what it defines is recursion, which inversion cannot
/// bound.
/// How each of these reads is `folding.PreconditionKind`'s to say, so that one
/// place words what a fold could not do.
pub const Obstacle = enum {
    recursive,
    not_conjunctive,
    lists,
    aggregate_output_projected,
    aggregate_template_correlated,
};

/// What stops this view from being inverted, or null when nothing does.
///
/// The class is a conjunction of positive base relations and aggregates —
/// however many, however deeply nested — each of whose collected lists is
/// fixed by what already surrounds it. That last condition is the one that
/// matters: inverting an aggregate's body means reading the values back out of
/// the list it collected, so the plan has to be able to name that list. The
/// head can fix it, by keeping it or by writing it down, and so can an
/// enclosing aggregate, by collecting it. A definition that projects it away
/// leaves a set with no name, which is F4's.
///
/// A definition is one rule, so the only recursion it can express is reading
/// its own name; a recursive view would need several rules and the catalog has
/// nowhere to put them. Mutual recursion between views is therefore not
/// something this can see, and not something the catalog can hold.
pub fn obstacle(view: *const view_catalog.View) ?Obstacle {
    const definition = view.definition;
    if (definition.seed_argument != null) return .recursive;
    for (definition.head.terms) |term| if (term == .cons or term == .nil) return .lists;
    const outermost: Level = .{
        .fixed = definition.head.terms,
        .goals = definition.body,
        .enclosing = null,
    };
    return levelObstacle(view, definition.body, &outermost);
}

/// What one nesting level fixes and what it binds: the head's terms and the
/// definition's own goals at the outermost level, an aggregate's template and
/// its goals within one. Threaded rather than collected so that the check
/// allocates nothing however deeply the aggregates nest.
const Level = struct {
    fixed: []const fold_ir.Term,
    goals: []const fold_ir.Goal,
    enclosing: ?*const Level,

    /// Whether this level or one above it writes the value down, so that a
    /// plan reading the stored tuple knows what it was.
    fn fixes(self: *const Level, variable: fold_ir.Variable) bool {
        if (mentions(self.fixed, variable)) return true;
        return if (self.enclosing) |above| above.fixes(variable) else false;
    }

    /// Whether this level or one above it binds the value with a goal of its
    /// own, which is what makes a value the definition already had rather than
    /// one an aggregate collected.
    fn binds(self: *const Level, variable: fold_ir.Variable) bool {
        for (self.goals) |goal| switch (goal) {
            .relation => |relation| if (mentions(relation.terms, variable)) return true,
            else => {},
        };
        return if (self.enclosing) |above| above.binds(variable) else false;
    }
};

fn levelObstacle(
    view: *const view_catalog.View,
    goals: []const fold_ir.Goal,
    level: *const Level,
) ?Obstacle {
    for (goals) |goal| switch (goal) {
        .builtin => return .not_conjunctive,
        .relation => |relation| if (readObstacle(view, relation)) |blocker| return blocker,
        .aggregate => |aggregate| {
            if (!keptBy(level, aggregate.output)) return .aggregate_output_projected;
            if (escapes(level, view.definition.head.terms, aggregate.template))
                return .aggregate_template_correlated;
            // The collected value is what an inner aggregate's output may be
            // fixed by, which is what lets `member` chain into the nesting.
            const collected = [_]fold_ir.Term{aggregate.template};
            const inner: Level = .{
                .fixed = &collected,
                .goals = aggregate.body,
                .enclosing = level,
            };
            if (levelObstacle(view, aggregate.body, &inner)) |blocker| return blocker;
        },
    };
    return null;
}

/// What stops one of the definition's relational goals from being inverted.
fn readObstacle(view: *const view_catalog.View, relation: fold_ir.Relation) ?Obstacle {
    if (relation.negated) return .not_conjunctive;
    const key = switch (relation.predicate) {
        .base => |value| value,
        .view, .generated, .auxiliary => return .not_conjunctive,
    };
    if (key.name == view.name and key.arity == view.definition.head.terms.len) return .recursive;
    for (relation.terms) |term| if (term == .cons or term == .nil) return .lists;
    return null;
}

/// Whether every value in `term` is fixed by this level or one above it. A
/// constant and the empty list are fixed by being written down; a variable is
/// fixed by the head keeping it, or by an enclosing aggregate collecting it.
fn keptBy(level: *const Level, term: fold_ir.Term) bool {
    return switch (term) {
        .variable => |variable| level.fixes(variable),
        .cons => |pair| keptBy(level, pair.head) and keptBy(level, pair.tail),
        else => true,
    };
}

/// Whether the aggregate collects a value the definition already binds at this
/// level or above without the head keeping it.
///
/// Such a variable would have to be two things at once in the inverse rules —
/// read back out of the list, and named by a Skolem term because the head lost
/// it — and there is no reading of the definition under which those agree.
fn escapes(
    level: *const Level,
    head: []const fold_ir.Term,
    term: fold_ir.Term,
) bool {
    switch (term) {
        .variable => |variable| return !mentions(head, variable) and level.binds(variable),
        .cons => |pair| return escapes(level, head, pair.head) or escapes(level, head, pair.tail),
        else => return false,
    }
}

fn mentions(terms: []const fold_ir.Term, variable: fold_ir.Variable) bool {
    for (terms) |term| if (mentionsTerm(term, variable)) return true;
    return false;
}

fn mentionsTerm(term: fold_ir.Term, variable: fold_ir.Variable) bool {
    return switch (term) {
        .variable => |value| value == variable,
        .cons => |pair| mentionsTerm(pair.head, variable) or mentionsTerm(pair.tail, variable),
        .skolem => |call| mentions(call.arguments, variable),
        else => false,
    };
}

/// One view's inverse rules: one per body goal, each reconstructing what that
/// goal read out of what the view stored.
pub const Inversion = struct {
    allocator: std.mem.Allocator,
    rules: []fold_ir.Rule,
    /// Whether the rules read values back out of a stored list, so that the
    /// plan needs the rules that define membership.
    reads_members: bool = false,

    pub fn deinit(self: *Inversion) void {
        for (self.rules) |rule| fold_ir.freeRule(self.allocator, rule);
        self.allocator.free(self.rules);
        self.* = undefined;
    }

    /// Gives up the rules themselves, leaving only the slice holding them for
    /// the caller to release. A plan combines several views' inverses into one
    /// list, and this is how they move there without being copied.
    pub fn take(self: *Inversion) []fold_ir.Rule {
        const rules = self.rules;
        self.rules = &.{};
        return rules;
    }
};

/// Inverts `view`, whose definition must have no `obstacle`.
///
/// The rules come back in the definition's own body order and share one
/// generated scope, so the two halves of a view read as the pair they are.
/// They are standardized apart from the definition, because a plan combines
/// them with the query the definition knows nothing about.
pub fn invert(
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    view: *const view_catalog.View,
) !Inversion {
    std.debug.assert(obstacle(view) == null);
    const definition = view.definition;
    const scope = try symbols.openScope(.generated);

    // The head's variables, in the order the head writes them: what a
    // reconstructed fact may still name, and what every Skolem term of this
    // view is applied to.
    var head_variables: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
    defer head_variables.deinit(allocator);
    try fold_ir.collectRelationVariables(allocator, definition.head, &head_variables);

    // What the definition binds outside its aggregates. A value projected from
    // there has one witness per stored tuple; a value projected from inside an
    // aggregate has one per collected element, and the two are named
    // differently for exactly that reason.
    var outer: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
    defer outer.deinit(allocator);
    try fold_ir.collectRelationVariables(allocator, definition.head, &outer);
    for (definition.body) |goal| if (goal == .relation)
        try fold_ir.collectRelationVariables(allocator, goal.relation, &outer);

    var builder: Builder = .{
        .allocator = allocator,
        .symbols = symbols,
        .scope = scope,
        .view = view,
        .outer = &outer,
        .arguments = try allocator.alloc(fold_ir.Term, head_variables.count()),
    };
    defer builder.deinit();
    for (head_variables.keys(), builder.arguments) |variable, *slot| {
        slot.* = .{ .variable = switch (symbols.originOf(variable)) {
            .user => |name| try symbols.freshUserVariable(scope, name),
            .generated => try symbols.freshVariable(scope),
        } };
        try builder.renaming.put(allocator, variable, slot.*);
    }

    // The builder owns the rules until they are taken, so its own `deinit`
    // releases whatever a failure left behind.
    try builder.invertGoals(definition.body, &.{});
    return .{
        .allocator = allocator,
        .rules = try builder.rules.toOwnedSlice(allocator),
        .reads_members = builder.reads_members,
    };
}

/// Appends the rules that define membership in a list.
///
/// `member` is not a builtin of the language and does not need to be: a list
/// the database holds already holds each of its own tails, so three rules over
/// the values it has are enough — the value in a one-element list, the first
/// value of a longer one, and everything its tail already had. On failure
/// whatever was appended stays in `into` for the caller to release.
pub fn appendMemberRules(
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    into: *std.ArrayList(fold_ir.Rule),
) !void {
    const scope = try symbols.openScope(.generated);
    for ([_]Membership{ .singleton, .first, .rest }) |kind| {
        const rule = try memberRule(allocator, symbols, scope, kind);
        errdefer fold_ir.freeRule(allocator, rule);
        try into.append(allocator, rule);
    }
}

/// One aggregate's Skolem function is not another's, even for a value they
/// spell the same way, because each collects it for itself.
const FunctionKey = struct { variable: fold_ir.Variable, nesting: u32 };

/// What stepping into one aggregate changed, so that stepping back out can
/// undo it.
const Entered = struct {
    membership: fold_ir.Goal,
    previous_element: []fold_ir.Term,
    previous_nesting: u32,
    bound: []fold_ir.Variable,

    fn leave(self: *Entered, builder: *Builder) void {
        for (self.bound) |variable| builder.renaming.remove(variable);
        builder.allocator.free(self.bound);
        builder.allocator.free(builder.element);
        builder.element = self.previous_element;
        builder.nesting = self.previous_nesting;
        fold_ir.freeGoal(builder.allocator, self.membership);
        self.* = undefined;
    }
};

/// Which of the three membership rules to build: the value in a one-element
/// list, the first value of a longer one, or everything the tail already had.
const Membership = enum { singleton, first, rest };

fn memberRule(
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    scope: fold_ir.Scope,
    kind: Membership,
) !fold_ir.Rule {
    const first = try symbols.freshVariable(scope);
    const rest = try symbols.freshVariable(scope);
    const other = try symbols.freshVariable(scope);

    const list = try allocator.create(fold_ir.Term.Cons);
    errdefer allocator.destroy(list);
    list.* = .{ .head = .{ .variable = first }, .tail = .{ .variable = rest } };
    const element: fold_ir.Term = switch (kind) {
        .singleton, .first => .{ .variable = first },
        .rest => .{ .variable = other },
    };
    // The slice only, because the cons cell in it is released above.
    const head_terms = try allocator.dupe(fold_ir.Term, &.{ element, .{ .cons = list } });
    errdefer allocator.free(head_terms);

    const body = try allocator.alloc(fold_ir.Goal, 1);
    errdefer allocator.free(body);
    body[0] = switch (kind) {
        .singleton => .{ .builtin = .{
            .operator = .equality,
            .terms = try allocator.dupe(fold_ir.Term, &.{ .{ .variable = rest }, .nil }),
            .provenance = .generated,
        } },
        .first, .rest => .{ .relation = .{
            .predicate = .{ .auxiliary = .member },
            .terms = try allocator.dupe(
                fold_ir.Term,
                &.{ .{ .variable = other }, .{ .variable = rest } },
            ),
            .provenance = .generated,
        } },
    };
    return .{
        .scope = scope,
        .head = .{
            .predicate = .{ .auxiliary = .member },
            .terms = head_terms,
            .provenance = .generated,
        },
        .body = body,
    };
}

/// The state one view's inversion shares across its rules: the fresh variables
/// standing for the head's, and the function each projected variable was
/// assigned. Both must be the same in every rule, which is why they are here
/// rather than rebuilt per goal.
const Builder = struct {
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    scope: fold_ir.Scope,
    /// The view whose extension the inverse rules read.
    view: *const view_catalog.View,
    /// The variables the definition binds outside its aggregates, plus the
    /// head's.
    outer: *const std.array_hash_map.Auto(fold_ir.Variable, void),
    /// The rules built so far.
    rules: std.ArrayList(fold_ir.Rule) = .empty,
    reads_members: bool = false,
    /// Which aggregate is being inverted, counted so that two of them never
    /// share a Skolem function for a value each collects for itself.
    nesting: u32 = 0,
    next_nesting: u32 = 0,
    /// What a Skolem term of this view is applied to: the head's values.
    arguments: []fold_ir.Term,
    /// Those values followed by the element currently being reconstructed,
    /// while an aggregate's goals are being inverted.
    element: []fold_ir.Term = &.{},
    renaming: fold_ir.Substitution = .{},
    functions: std.array_hash_map.Auto(FunctionKey, fold_ir.Function) = .empty,

    fn deinit(self: *Builder) void {
        for (self.rules.items) |rule| fold_ir.freeRule(self.allocator, rule);
        self.rules.deinit(self.allocator);
        self.allocator.free(self.element);
        self.functions.deinit(self.allocator);
        self.renaming.deinit(self.allocator);
        self.allocator.free(self.arguments);
        self.* = undefined;
    }

    /// Inverts one nesting level: a relation becomes a rule reconstructing it
    /// from the stored tuple and whichever collected values were read to reach
    /// it, and an aggregate is descended into with one more such value read.
    fn invertGoals(
        self: *Builder,
        goals: []const fold_ir.Goal,
        read: []const fold_ir.Goal,
    ) std.mem.Allocator.Error!void {
        for (goals) |goal| switch (goal) {
            .relation => |relation| {
                const rule = try self.inverse(relation, read);
                errdefer fold_ir.freeRule(self.allocator, rule);
                try self.rules.append(self.allocator, rule);
            },
            .aggregate => |aggregate| {
                var entered = try self.enter(aggregate);
                defer entered.leave(self);
                const deeper = try self.allocator.alloc(fold_ir.Goal, read.len + 1);
                defer self.allocator.free(deeper);
                @memcpy(deeper[0..read.len], read);
                deeper[read.len] = entered.membership;
                self.reads_members = true;
                try self.invertGoals(aggregate.body, deeper);
            },
            .builtin => unreachable,
        };
    }

    /// Steps into one aggregate: binds what it collects to variables of its
    /// own, reads one of those values out of the stored list, and extends what
    /// a Skolem term is applied to with it.
    ///
    /// The binding is undone on the way out, because two aggregates that spell
    /// a collected value the same way do not mean the same value by it — the
    /// language says a value the surrounding goals do not bind belongs to the
    /// aggregate that mentions it — and inverting them as one would join what
    /// the definition kept apart.
    fn enter(self: *Builder, aggregate: fold_ir.Aggregate) !Entered {
        var collected: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
        defer collected.deinit(self.allocator);
        try fold_ir.collectTermVariables(self.allocator, aggregate.template, &collected);

        var bound: std.ArrayList(fold_ir.Variable) = .empty;
        errdefer {
            for (bound.items) |variable| self.renaming.remove(variable);
            bound.deinit(self.allocator);
        }
        for (collected.keys()) |variable| {
            if (self.renaming.get(variable) != null) continue;
            const fresh: fold_ir.Term = .{ .variable = switch (self.symbols.originOf(variable)) {
                .user => |name| try self.symbols.freshUserVariable(self.scope, name),
                .generated => try self.symbols.freshVariable(self.scope),
            } };
            try self.renaming.put(self.allocator, variable, fresh);
            try bound.append(self.allocator, variable);
        }

        const outer_witness = self.witness();
        const element = try self.allocator.alloc(
            fold_ir.Term,
            outer_witness.len + collected.count(),
        );
        errdefer self.allocator.free(element);
        @memcpy(element[0..outer_witness.len], outer_witness);
        for (collected.keys(), element[outer_witness.len..]) |variable, *slot|
            slot.* = self.renaming.get(variable).?;

        const read = try self.membership(aggregate);
        errdefer fold_ir.freeGoal(self.allocator, read);
        self.next_nesting += 1;
        const entered: Entered = .{
            .membership = read,
            .previous_element = self.element,
            .previous_nesting = self.nesting,
            .bound = try bound.toOwnedSlice(self.allocator),
        };
        self.element = element;
        self.nesting = self.next_nesting;
        return entered;
    }

    /// What a Skolem term is applied to in the current context: the head's
    /// values, plus every collected value read to get here.
    fn witness(self: *const Builder) []const fold_ir.Term {
        return if (self.element.len == 0) self.arguments else self.element;
    }

    /// What the witness for this variable depends on. A variable the
    /// definition binds outside its aggregates has one witness per stored
    /// tuple; one that occurs only inside has one per collected element.
    fn witnessOf(self: *const Builder, variable: fold_ir.Variable) []const fold_ir.Term {
        if (self.outer.contains(variable)) return self.arguments;
        return self.witness();
    }

    /// The identity of the function naming this variable's witness. Keyed by
    /// the aggregate as well as the variable, so that a value two aggregates
    /// each collect for themselves is named twice rather than once.
    fn functionKey(self: *const Builder, variable: fold_ir.Variable) FunctionKey {
        return .{
            .variable = variable,
            .nesting = if (self.outer.contains(variable)) 0 else self.nesting,
        };
    }

    /// The goal that reads one collected value out of the stored list. The
    /// list is whatever the head kept, which is what makes it nameable at all.
    fn membership(self: *Builder, aggregate: fold_ir.Aggregate) !fold_ir.Goal {
        const collected = try fold_ir.substituteTerm(
            self.allocator,
            aggregate.template,
            &self.renaming,
        );
        errdefer fold_ir.freeTerm(self.allocator, collected);
        const list = try fold_ir.substituteTerm(self.allocator, aggregate.output, &self.renaming);
        errdefer fold_ir.freeTerm(self.allocator, list);
        const terms = try self.allocator.alloc(fold_ir.Term, 2);
        terms[0] = collected;
        terms[1] = list;
        return .{ .relation = .{
            .predicate = .{ .auxiliary = .member },
            .terms = terms,
            .provenance = .generated,
        } };
    }

    /// The rule reconstructing one goal: the stored tuple, then every
    /// collected value that had to be read to reach the goal, then the fact
    /// those together say was there.
    fn inverse(
        self: *Builder,
        relation: fold_ir.Relation,
        read: []const fold_ir.Goal,
    ) !fold_ir.Rule {
        const terms = try self.allocator.alloc(fold_ir.Term, relation.terms.len);
        var built: usize = 0;
        errdefer {
            for (terms[0..built]) |term| fold_ir.freeTerm(self.allocator, term);
            self.allocator.free(terms);
        }
        for (relation.terms, terms) |term, *slot| {
            slot.* = try self.reconstruct(term);
            built += 1;
        }

        const stored = try fold_ir.substituteTerms(
            self.allocator,
            self.view.definition.head.terms,
            &self.renaming,
        );
        errdefer fold_ir.freeTerms(self.allocator, stored);
        const body = try self.allocator.alloc(fold_ir.Goal, read.len + 1);
        var copied: usize = 0;
        errdefer {
            for (body[1 .. 1 + copied]) |goal| fold_ir.freeGoal(self.allocator, goal);
            self.allocator.free(body);
        }
        body[0] = .{ .relation = .{
            .predicate = self.view.predicate(),
            .terms = stored,
            .provenance = .generated,
        } };
        for (read, body[1..]) |goal, *slot| {
            slot.* = try fold_ir.cloneGoal(self.allocator, goal);
            copied += 1;
        }
        return .{
            .scope = self.scope,
            .head = .{
                .predicate = relation.predicate,
                .terms = terms,
                .provenance = .generated,
            },
            .body = body,
        };
    }

    /// What a body term becomes in the reconstructed fact: itself when the
    /// head kept it, and a Skolem term when the head projected it away.
    fn reconstruct(self: *Builder, term: fold_ir.Term) !fold_ir.Term {
        const variable = switch (term) {
            .variable => |value| value,
            else => return term,
        };
        if (self.renaming.get(variable)) |replacement| return replacement;

        const key = self.functionKey(variable);
        const function = self.functions.get(key) orelse blk: {
            const fresh = try self.symbols.freshFunction(self.scope);
            try self.functions.put(self.allocator, key, fresh);
            break :blk fresh;
        };
        const call = try self.allocator.create(fold_ir.Term.Skolem);
        errdefer self.allocator.destroy(call);
        call.* = .{
            .function = function,
            .arguments = try fold_ir.cloneTerms(self.allocator, self.witnessOf(variable)),
        };
        return .{ .skolem = call };
    }
};

/// What a column of a split relation holds: an ordinary value, or the
/// arguments of one Skolem function spread across as many columns.
const Shape = union(enum) {
    plain,
    skolem: fold_ir.Function,

    fn equals(self: Shape, other: Shape) bool {
        return switch (self) {
            .plain => other == .plain,
            .skolem => |function| other == .skolem and other.skolem == function,
        };
    }
};

/// One split of one relation: which function each of its columns carries, and
/// the predicate the split goes under. A split whose columns are all ordinary
/// *is* the relation it came from, which is what makes the query's own goals
/// read the plan without being rewritten.
const Split = struct {
    origin: fold_ir.Predicate,
    shapes: []Shape,
    predicate: fold_ir.Predicate,
};

/// Rules with no Skolem term left in them, and whether anything was lost.
pub const Elimination = struct {
    allocator: std.mem.Allocator,
    rules: []fold_ir.Rule,
    /// Whether any relation had to be split. A view that projects nothing away
    /// has no Skolem term to eliminate, and its inverse rules come back as
    /// they went in.
    split: bool,
    /// Whether some instance was dropped because a goal that is not a positive
    /// relation would have had to read a Skolem value. Dropping loses answers
    /// and keeps containment, so this is what separates a plan that returns
    /// everything the views allow from one that only returns some of it.
    dropped: bool,

    pub fn deinit(self: *Elimination) void {
        for (self.rules) |rule| fold_ir.freeRule(self.allocator, rule);
        self.allocator.free(self.rules);
        self.* = undefined;
    }
};

/// Rewrites `rules` so that no Skolem term survives, by splitting every
/// relation that can hold one.
///
/// The relations a plan may actually read — a view's stored extension, a base
/// relation the policy declares — never hold a Skolem value, so `catalog` is
/// consulted for exactly one thing: which relations arrive with tuples rather
/// than being derived, since those are the ones whose ordinary split is
/// populated to begin with.
pub fn eliminateSkolems(
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    catalog: *const view_catalog.Catalog,
    rules: []const fold_ir.Rule,
) !Elimination {
    var eliminator: Eliminator = .{
        .allocator = allocator,
        .symbols = symbols,
        .catalog = catalog,
        .scope = undefined,
    };
    defer eliminator.deinit();
    try eliminator.collectFunctions(rules);
    if (eliminator.arities.count() == 0) {
        // Nothing to split: every relation has one split, itself.
        var copies: std.ArrayList(fold_ir.Rule) = .empty;
        errdefer {
            for (copies.items) |rule| fold_ir.freeRule(allocator, rule);
            copies.deinit(allocator);
        }
        for (rules) |rule| {
            const copy = try fold_ir.cloneRule(allocator, rule);
            errdefer fold_ir.freeRule(allocator, copy);
            try copies.append(allocator, copy);
        }
        return .{
            .allocator = allocator,
            .rules = try copies.toOwnedSlice(allocator),
            .split = false,
            .dropped = false,
        };
    }

    eliminator.scope = try symbols.openScope(.generated);
    try eliminator.seedStored(rules);
    while (true) {
        eliminator.changed = false;
        for (rules) |rule| try eliminator.walk(rule);
        if (!eliminator.changed) break;
    }
    eliminator.emitting = true;
    for (rules) |rule| try eliminator.walk(rule);

    return .{
        .allocator = allocator,
        .rules = try eliminator.output.toOwnedSlice(allocator),
        .split = eliminator.next_tag != 0,
        .dropped = eliminator.dropped,
    };
}

/// One rule's variables and the split column each of them stands in, plus the
/// split chosen for each of its positive goals. Enumerating the consistent
/// assignments of shapes to variables is what instantiates a rule once per
/// combination of splits it can read.
const Instance = struct {
    variables: []fold_ir.Variable,
    shapes: []?Shape,
    chosen: []usize,

    fn indexOf(self: *const Instance, variable: fold_ir.Variable) usize {
        return std.mem.indexOfScalar(fold_ir.Variable, self.variables, variable).?;
    }

    fn shapeOf(self: *const Instance, variable: fold_ir.Variable) ?Shape {
        return self.shapes[self.indexOf(variable)];
    }
};

const Eliminator = struct {
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    catalog: *const view_catalog.Catalog,
    /// The scope the columns a split spreads a Skolem term across live in.
    scope: fold_ir.Scope,
    arities: std.array_hash_map.Auto(fold_ir.Function, usize) = .empty,
    splits: std.ArrayList(Split) = .empty,
    output: std.ArrayList(fold_ir.Rule) = .empty,
    next_tag: u32 = 0,
    dropped: bool = false,
    /// Whether the last pass found a split it had not seen before.
    changed: bool = false,
    /// Whether this pass is building rules rather than discovering splits.
    emitting: bool = false,

    fn deinit(self: *Eliminator) void {
        for (self.output.items) |rule| fold_ir.freeRule(self.allocator, rule);
        self.output.deinit(self.allocator);
        for (self.splits.items) |split| self.allocator.free(split.shapes);
        self.splits.deinit(self.allocator);
        self.arities.deinit(self.allocator);
        self.* = undefined;
    }

    fn collectFunctions(self: *Eliminator, rules: []const fold_ir.Rule) !void {
        for (rules) |rule| {
            for (rule.head.terms) |term| try self.collectTermFunctions(term);
            for (rule.body) |goal| try self.collectGoalFunctions(goal);
        }
    }

    fn collectGoalFunctions(self: *Eliminator, goal: fold_ir.Goal) !void {
        switch (goal) {
            .relation => |relation| for (relation.terms) |term| try self.collectTermFunctions(term),
            .builtin => |builtin| for (builtin.terms) |term| try self.collectTermFunctions(term),
            .aggregate => |aggregate| {
                try self.collectTermFunctions(aggregate.template);
                try self.collectTermFunctions(aggregate.output);
                for (aggregate.body) |inner| try self.collectGoalFunctions(inner);
            },
        }
    }

    fn collectTermFunctions(self: *Eliminator, term: fold_ir.Term) std.mem.Allocator.Error!void {
        switch (term) {
            .skolem => |call| {
                try self.arities.put(self.allocator, call.function, call.arguments.len);
                for (call.arguments) |argument| try self.collectTermFunctions(argument);
            },
            .cons => |pair| {
                try self.collectTermFunctions(pair.head);
                try self.collectTermFunctions(pair.tail);
            },
            else => {},
        }
    }

    /// Records the ordinary split of every relation the rules read that holds
    /// tuples rather than being derived. Without this a rule reading a view
    /// would have no split to join against and would never be instantiated.
    fn seedStored(self: *Eliminator, rules: []const fold_ir.Rule) !void {
        for (rules) |rule| for (rule.body) |goal| try self.seedGoal(goal);
    }

    fn seedGoal(self: *Eliminator, goal: fold_ir.Goal) std.mem.Allocator.Error!void {
        switch (goal) {
            .relation => |relation| {
                if (!self.stored(relation.predicate)) return;
                const shapes = try self.allocator.alloc(Shape, relation.terms.len);
                @memset(shapes, .plain);
                _ = try self.register(relation.predicate, shapes);
            },
            .aggregate => |aggregate| for (aggregate.body) |inner| try self.seedGoal(inner),
            .builtin => {},
        }
    }

    fn stored(self: *const Eliminator, predicate: fold_ir.Predicate) bool {
        return switch (predicate) {
            .view => |reference| self.catalog.view(reference.id).readable(),
            .base => |key| self.catalog.baseAvailable(key),
            .generated, .auxiliary => false,
        };
    }

    fn walk(self: *Eliminator, rule: fold_ir.Rule) !void {
        var variables: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
        defer variables.deinit(self.allocator);
        try fold_ir.collectRelationVariables(self.allocator, rule.head, &variables);
        for (rule.body) |goal| try fold_ir.collectGoalVariables(self.allocator, goal, &variables);

        const named = try self.allocator.dupe(fold_ir.Variable, variables.keys());
        defer self.allocator.free(named);
        const shapes = try self.allocator.alloc(?Shape, named.len);
        defer self.allocator.free(shapes);
        const chosen = try self.allocator.alloc(usize, rule.body.len);
        defer self.allocator.free(chosen);

        var instance: Instance = .{ .variables = named, .shapes = shapes, .chosen = chosen };
        @memset(instance.shapes, null);
        try self.enumerate(rule, &instance, 0);
    }

    /// Joins the rule's positive goals against the splits discovered so far,
    /// one assignment of shapes to variables at a time.
    fn enumerate(
        self: *Eliminator,
        rule: fold_ir.Rule,
        instance: *Instance,
        index: usize,
    ) std.mem.Allocator.Error!void {
        if (index == rule.body.len) return self.complete(rule, instance);
        const relation = switch (rule.body[index]) {
            .relation => |value| if (value.negated) return self.enumerate(rule, instance, index + 1) else value,
            else => return self.enumerate(rule, instance, index + 1),
        };

        const saved = try self.allocator.alloc(?Shape, instance.shapes.len);
        defer self.allocator.free(saved);
        @memcpy(saved, instance.shapes);
        // The split list grows while this recursion runs, and a split found
        // now belongs to the next pass: the fixpoint is what makes that
        // complete, and reading a slice that is being appended to would not be.
        const known = self.splits.items.len;
        for (0..known) |candidate| {
            @memcpy(instance.shapes, saved);
            if (!match(instance, relation, self.splits.items[candidate])) continue;
            instance.chosen[index] = candidate;
            try self.enumerate(rule, instance, index + 1);
        }
        @memcpy(instance.shapes, saved);
    }

    /// One complete assignment: everything the rule can still object to is
    /// checked here, because a variable's shape is only settled now.
    fn complete(self: *Eliminator, rule: fold_ir.Rule, instance: *Instance) !void {
        const saved = try self.allocator.alloc(?Shape, instance.shapes.len);
        defer self.allocator.free(saved);
        @memcpy(saved, instance.shapes);
        defer @memcpy(instance.shapes, saved);
        for (instance.shapes) |*slot| if (slot.* == null) {
            slot.* = .plain;
        };

        for (rule.body) |goal| if (!admits(goal, instance)) {
            self.dropped = true;
            return;
        };
        if (!termsAdmit(rule.head.terms, instance)) {
            self.dropped = true;
            return;
        }

        const shapes = try self.shapesOf(rule.head.terms, instance);
        const head = try self.register(rule.head.predicate, shapes);
        if (self.emitting) try self.emit(rule, instance, head);
    }

    fn shapesOf(
        self: *Eliminator,
        terms: []const fold_ir.Term,
        instance: *const Instance,
    ) ![]Shape {
        const shapes = try self.allocator.alloc(Shape, terms.len);
        for (terms, shapes) |term, *slot| slot.* = switch (term) {
            .variable => |variable| instance.shapeOf(variable).?,
            .skolem => |call| .{ .skolem = call.function },
            else => .plain,
        };
        return shapes;
    }

    /// The index of the split with these shapes, adding it when it is new.
    /// Takes ownership of `shapes` either way.
    fn register(self: *Eliminator, origin: fold_ir.Predicate, shapes: []Shape) !usize {
        for (self.splits.items, 0..) |split, index| {
            if (!split.origin.equals(origin)) continue;
            if (split.shapes.len != shapes.len) continue;
            const same = for (split.shapes, shapes) |left, right| {
                if (!left.equals(right)) break false;
            } else true;
            if (!same) continue;
            self.allocator.free(shapes);
            return index;
        }
        errdefer self.allocator.free(shapes);

        var width: usize = 0;
        var ordinary = true;
        for (shapes) |shape| switch (shape) {
            .plain => width += 1,
            .skolem => |function| {
                width += self.arities.get(function).?;
                ordinary = false;
            },
        };
        try self.splits.append(self.allocator, .{
            .origin = origin,
            .shapes = shapes,
            .predicate = if (ordinary) origin else blk: {
                // Only a rule's head is ever split, and a head is a base
                // relation: a view is read from, never derived into, so its
                // splits are the ordinary one `seedStored` records.
                const key = switch (origin) {
                    .base => |value| value,
                    .view, .generated, .auxiliary => unreachable,
                };
                const tag = self.next_tag;
                self.next_tag += 1;
                break :blk .{ .generated = .{ .origin = key, .tag = tag, .arity = width } };
            },
        });
        self.changed = true;
        return self.splits.items.len - 1;
    }

    /// Builds the rule this assignment stands for: every goal reads the split
    /// it matched, and every column carrying a Skolem term becomes the columns
    /// that term was applied to.
    fn emit(self: *Eliminator, rule: fold_ir.Rule, instance: *const Instance, head: usize) !void {
        var columns: Columns = .{ .allocator = self.allocator };
        defer columns.deinit();
        for (instance.variables, instance.shapes) |variable, shape| switch (shape.?) {
            .plain => {},
            .skolem => |function| {
                const fresh = try self.allocator.alloc(fold_ir.Variable, self.arities.get(function).?);
                errdefer self.allocator.free(fresh);
                for (fresh) |*slot| slot.* = try self.symbols.freshVariable(self.scope);
                try columns.entries.put(self.allocator, variable, fresh);
            },
        };

        const terms = try columns.spread(rule.head.terms);
        errdefer fold_ir.freeTerms(self.allocator, terms);
        const body = try self.allocator.alloc(fold_ir.Goal, rule.body.len);
        var built: usize = 0;
        errdefer {
            for (body[0..built]) |goal| fold_ir.freeGoal(self.allocator, goal);
            self.allocator.free(body);
        }
        for (rule.body, body, 0..) |goal, *slot, index| {
            slot.* = switch (goal) {
                .relation => |relation| if (relation.negated)
                    try fold_ir.cloneGoal(self.allocator, goal)
                else
                    .{ .relation = .{
                        .predicate = self.splits.items[instance.chosen[index]].predicate,
                        .terms = try columns.spread(relation.terms),
                        .provenance = relation.provenance,
                    } },
                else => try fold_ir.cloneGoal(self.allocator, goal),
            };
            built += 1;
        }

        try self.output.append(self.allocator, .{
            .scope = self.scope,
            .head = .{
                .predicate = self.splits.items[head].predicate,
                .terms = terms,
                .provenance = rule.head.provenance,
            },
            .body = body,
            .seed_argument = self.seedArgument(rule, instance),
        });
    }

    /// Where a structurally recursive rule's seed argument ends up once the
    /// columns before it have been spread out. The seed itself is a list, so
    /// it is one column before and after.
    fn seedArgument(self: *Eliminator, rule: fold_ir.Rule, instance: *const Instance) ?usize {
        const original = rule.seed_argument orelse return null;
        var moved: usize = 0;
        for (rule.head.terms[0..original]) |term| moved += switch (term) {
            .variable => |variable| switch (instance.shapeOf(variable).?) {
                .plain => 1,
                .skolem => |function| self.arities.get(function).?,
            },
            .skolem => |call| call.arguments.len,
            else => 1,
        };
        return moved;
    }
};

/// Whether `relation` can read `split`, assigning the shapes it forces on the
/// variables it mentions. Leaves `instance` partly assigned when it returns
/// false; the caller restores.
fn match(instance: *Instance, relation: fold_ir.Relation, split: Split) bool {
    if (!split.origin.equals(relation.predicate)) return false;
    if (relation.terms.len != split.shapes.len) return false;
    for (relation.terms, split.shapes) |term, shape| switch (term) {
        .variable => |variable| {
            const slot = &instance.shapes[instance.indexOf(variable)];
            if (slot.*) |existing| {
                if (!existing.equals(shape)) return false;
            } else slot.* = shape;
        },
        .skolem => |call| {
            if (shape != .skolem or shape.skolem != call.function) return false;
        },
        else => if (shape != .plain) return false,
    };
    return true;
}

/// Whether this goal can be instantiated under the assignment.
///
/// A positive relation reads whichever split it matched, so it only objects to
/// a list holding a Skolem value. Everything else — a negated goal, a
/// comparison, an aggregate — has to see ordinary values, because what it
/// computes from a value the plan cannot name is not what the query asked.
/// Refusing the instance costs answers and keeps containment.
fn admits(goal: fold_ir.Goal, instance: *const Instance) bool {
    switch (goal) {
        .relation => |relation| return if (relation.negated)
            termsPlain(relation.terms, instance)
        else
            termsAdmit(relation.terms, instance),
        .builtin => |builtin| return termsPlain(builtin.terms, instance),
        .aggregate => |aggregate| {
            if (!termPlain(aggregate.template, instance)) return false;
            if (!termPlain(aggregate.output, instance)) return false;
            for (aggregate.body) |inner| if (!admits(inner, instance)) return false;
            return true;
        },
    }
}

/// Whether the terms of a positive goal or head can be spread out: a list
/// cannot be split, and neither can a Skolem term whose arguments are not
/// ordinary values.
fn termsAdmit(terms: []const fold_ir.Term, instance: *const Instance) bool {
    for (terms) |term| switch (term) {
        .cons => if (!termPlain(term, instance)) return false,
        .skolem => |call| if (!termsPlain(call.arguments, instance)) return false,
        else => {},
    };
    return true;
}

fn termsPlain(terms: []const fold_ir.Term, instance: *const Instance) bool {
    for (terms) |term| if (!termPlain(term, instance)) return false;
    return true;
}

fn termPlain(term: fold_ir.Term, instance: *const Instance) bool {
    return switch (term) {
        .variable => |variable| instance.shapeOf(variable).? == .plain,
        .cons => |pair| termPlain(pair.head, instance) and termPlain(pair.tail, instance),
        .skolem => false,
        else => true,
    };
}

/// The columns one instantiated rule spreads its Skolem-carrying variables
/// across. Owned for the length of that rule's construction: the variables are
/// the instance's, not the plan's.
const Columns = struct {
    allocator: std.mem.Allocator,
    entries: std.array_hash_map.Auto(fold_ir.Variable, []fold_ir.Variable) = .empty,

    fn deinit(self: *Columns) void {
        for (self.entries.values()) |fresh| self.allocator.free(fresh);
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    fn spread(self: *const Columns, terms: []const fold_ir.Term) ![]fold_ir.Term {
        var width: usize = 0;
        for (terms) |term| width += self.widthOf(term);
        const spread_terms = try self.allocator.alloc(fold_ir.Term, width);
        var built: usize = 0;
        errdefer {
            for (spread_terms[0..built]) |term| fold_ir.freeTerm(self.allocator, term);
            self.allocator.free(spread_terms);
        }
        for (terms) |term| switch (term) {
            .variable => |variable| if (self.entries.get(variable)) |fresh| {
                for (fresh) |column| {
                    spread_terms[built] = .{ .variable = column };
                    built += 1;
                }
            } else {
                spread_terms[built] = term;
                built += 1;
            },
            .skolem => |call| for (call.arguments) |argument| {
                spread_terms[built] = try fold_ir.cloneTerm(self.allocator, argument);
                built += 1;
            },
            else => {
                spread_terms[built] = try fold_ir.cloneTerm(self.allocator, term);
                built += 1;
            },
        };
        return spread_terms;
    }

    fn widthOf(self: *const Columns, term: fold_ir.Term) usize {
        return switch (term) {
            .variable => |variable| if (self.entries.get(variable)) |fresh| fresh.len else 1,
            .skolem => |call| call.arguments.len,
            else => 1,
        };
    }
};

const testing = std.testing;
const scalar = @import("scalar.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");

/// Chapter 6's even-length-path setting: a catalog holding
/// `v(X, Z) :- edge(X, Y), edge(Y, Z).`
const Fixture = struct {
    strings: string_table.StringTable,
    scalars: scalar.Store,
    catalog: view_catalog.Catalog,
    view: fold_ir.ViewId,

    fn init(allocator: std.mem.Allocator) !Fixture {
        var fixture: Fixture = .{
            .strings = .init(allocator),
            .scalars = .init(allocator),
            .catalog = .init(allocator),
            .view = undefined,
        };
        errdefer fixture.deinit();
        const v = try fixture.strings.intern("v");
        const edge = try fixture.strings.intern("edge");
        const x = try fixture.strings.intern("X");
        const y = try fixture.strings.intern("Y");
        const z = try fixture.strings.intern("Z");

        var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = z } };
        var first = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
        var second = [_]syntax.Term{ .{ .variable = y }, .{ .variable = z } };
        var body = [_]syntax.Clause{
            .{ .relational = .{ .predicate = edge, .terms = &first } },
            .{ .relational = .{ .predicate = edge, .terms = &second } },
        };
        fixture.view = try fixture.catalog.define(.{
            .head = .{ .predicate = v, .terms = &head_terms },
            .body = &body,
        }, .materialized);
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
};

fn renderRules(allocator: std.mem.Allocator, names: fold_ir.Names, rules: []const fold_ir.Rule) ![]u8 {
    var text: std.Io.Writer.Allocating = .init(allocator);
    defer text.deinit();
    for (rules) |rule| {
        fold_ir.writeRule(&text.writer, names, rule) catch return error.OutOfMemory;
        text.writer.writeByte('\n') catch return error.OutOfMemory;
    }
    return text.toOwnedSlice();
}

test "a projected variable becomes one Skolem term, the same one in every inverse rule" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator);
    defer fixture.deinit();

    const view = fixture.catalog.view(fixture.view);
    try testing.expectEqual(@as(?Obstacle, null), obstacle(view));
    var inverted = try invert(allocator, &fixture.catalog.symbols, view);
    defer inverted.deinit();

    try testing.expectEqual(@as(usize, 2), inverted.rules.len);
    // The head kept X and Z, so both stay variables wherever they occur; the
    // body's Y is gone from the extension, so both rules name it the same way
    // or the two halves of a path would not meet.
    const first = inverted.rules[0].head.terms;
    const second = inverted.rules[1].head.terms;
    try testing.expect(first[0] == .variable);
    try testing.expect(second[1] == .variable);
    try testing.expect(first[1] == .skolem);
    try testing.expect(second[0] == .skolem);
    try testing.expectEqual(first[1].skolem.function, second[0].skolem.function);
    try testing.expectEqual(first[0].variable, first[1].skolem.arguments[0].variable);
    try testing.expectEqual(second[1].variable, second[0].skolem.arguments[1].variable);
    // Standardized apart: the rules' variables are not the definition's.
    try testing.expect(first[0].variable != view.definition.head.terms[0].variable);

    const rendered = try renderRules(allocator, fixture.names(), inverted.rules);
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\edge(X#3, $f0(X#3, Z#4)) :- v@0(X#3, Z#4) % generated.
        \\edge($f0(X#3, Z#4), Z#4) :- v@0(X#3, Z#4) % generated.
        \\
    , rendered);
}

test "a definition outside the conjunctive class names what stops it" {
    const allocator = testing.allocator;
    var strings: string_table.StringTable = .init(allocator);
    defer strings.deinit();
    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();

    const path = try strings.intern("path");
    const edge = try strings.intern("edge");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    const s = try strings.intern("S");

    // path(X, Y) :- edge(X, Y), path(Y, X). Reading what it defines is
    // recursion, whatever else the body does.
    var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var edge_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var self_terms = [_]syntax.Term{ .{ .variable = y }, .{ .variable = x } };
    var recursive_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = edge, .terms = &edge_terms } },
        .{ .relational = .{ .predicate = path, .terms = &self_terms } },
    };
    const recursive = try catalog.define(.{
        .head = .{ .predicate = path, .terms = &head_terms },
        .body = &recursive_body,
    }, .materialized);
    try testing.expectEqual(Obstacle.recursive, obstacle(catalog.view(recursive)).?);

    // total(X, S) :- setof(Y, edge(X, Y), S). The head keeps the list, so a
    // plan can read the values back out of it and this is invertible.
    var aggregate_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = edge, .terms = &edge_terms } }};
    var aggregate_body = [_]syntax.Clause{.{ .aggregate = .{
        .template = .{ .variable = y },
        .body = &inner,
        .output = .{ .variable = s },
    } }};
    const aggregated = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("total"), .terms = &aggregate_terms },
        .body = &aggregate_body,
    }, .materialized);
    try testing.expectEqual(@as(?Obstacle, null), obstacle(catalog.view(aggregated)));

    // counted(X) :- edge(X, S), setof(Y, edge(X, Y), S). The same aggregate
    // with the head no longer keeping what it collected: the plan would have a
    // set it cannot name, which is F4's.
    var counted_terms = [_]syntax.Term{.{ .variable = x }};
    var outer_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    var counted_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = edge, .terms = &outer_terms } },
        .{ .aggregate = .{
            .template = .{ .variable = y },
            .body = &inner,
            .output = .{ .variable = s },
        } },
    };
    const counted = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("counted"), .terms = &counted_terms },
        .body = &counted_body,
    }, .materialized);
    try testing.expectEqual(
        Obstacle.aggregate_output_projected,
        obstacle(catalog.view(counted)).?,
    );

    // pair(X, [Y]) :- edge(X, Y). A list is F5's problem.
    var pair: syntax.Term.Cons = .{ .head = .{ .variable = y }, .tail = .nil };
    var list_head = [_]syntax.Term{ .{ .variable = x }, .{ .cons = &pair } };
    var list_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = edge, .terms = &edge_terms } },
    };
    const listed = try catalog.define(.{
        .head = .{ .predicate = try strings.intern("pair"), .terms = &list_head },
        .body = &list_body,
    }, .materialized);
    try testing.expectEqual(Obstacle.lists, obstacle(catalog.view(listed)).?);
}

test "eliminating Skolem terms splits the relations that carried them" {
    const allocator = testing.allocator;
    var fixture = try Fixture.init(allocator);
    defer fixture.deinit();

    var inverted = try invert(allocator, &fixture.catalog.symbols, fixture.catalog.view(fixture.view));
    defer inverted.deinit();
    var eliminated = try eliminateSkolems(
        allocator,
        &fixture.catalog.symbols,
        &fixture.catalog,
        inverted.rules,
    );
    defer eliminated.deinit();

    try testing.expect(!eliminated.dropped);
    try testing.expectEqual(@as(usize, 2), eliminated.rules.len);
    for (eliminated.rules) |rule| {
        for (rule.head.terms) |term| try testing.expect(!term.containsSkolem());
        // Each split spreads the one Skolem column across the two values the
        // function was applied to, so a two-column relation becomes three.
        try testing.expectEqual(@as(usize, 3), rule.head.terms.len);
        try testing.expect(rule.head.predicate == .generated);
    }
    // Two columns, two splits: the relation is not the same one twice.
    try testing.expect(!eliminated.rules[0].head.predicate.equals(eliminated.rules[1].head.predicate));

    const rendered = try renderRules(allocator, fixture.names(), eliminated.rules);
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\edge$0(X#3, X#3, Z#4) :- v@0(X#3, Z#4) % generated.
        \\edge$1(X#3, Z#4, Z#4) :- v@0(X#3, Z#4) % generated.
        \\
    , rendered);
}

test "inverting a collected list binds its values instead of naming them" {
    const allocator = testing.allocator;
    var strings: string_table.StringTable = .init(allocator);
    defer strings.deinit();
    var scalars: scalar.Store = .init(allocator);
    defer scalars.deinit();
    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();

    const v = try strings.intern("v");
    const p = try strings.intern("p");
    const r = try strings.intern("r");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    const z = try strings.intern("Z");
    const s = try strings.intern("S");

    // Chapter 6's Example 6.3.1: v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    var outer_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = z } };
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = p, .terms = &outer_terms } },
        .{ .aggregate = .{
            .template = .{ .variable = y },
            .body = &inner,
            .output = .{ .variable = s },
        } },
    };
    const id = try catalog.define(.{
        .head = .{ .predicate = v, .terms = &head_terms },
        .body = &body,
    }, .materialized);

    const view = catalog.view(id);
    try testing.expectEqual(@as(?Obstacle, null), obstacle(view));
    var inverted = try invert(allocator, &catalog.symbols, view);
    defer inverted.deinit();
    try testing.expect(inverted.reads_members);

    var rules: std.ArrayList(fold_ir.Rule) = .empty;
    defer {
        for (rules.items) |rule| fold_ir.freeRule(allocator, rule);
        rules.deinit(allocator);
    }
    try appendMemberRules(allocator, &catalog.symbols, &rules);

    const names: fold_ir.Names = .{
        .symbols = &catalog.symbols,
        .strings = &strings,
        .scalars = &scalars,
    };
    // `Z` was projected away and is named by a Skolem term; `Y` was collected
    // and is read back out of the list the head kept, so it stays a variable.
    const rendered = try renderRules(allocator, names, inverted.rules);
    defer allocator.free(rendered);
    try testing.expectEqualStrings(
        \\p(X#4, $f0(X#4, S#5)) :- v@0(X#4, S#5) % generated.
        \\r(X#4, Y#6) :- v@0(X#4, S#5) % generated, $member(Y#6, S#5) % generated.
        \\
    , rendered);

    // What being in a list means: the value in a one-element list, the first
    // value of a longer one, and everything its tail already had.
    const membership = try renderRules(allocator, names, rules.items);
    defer allocator.free(membership);
    try testing.expectEqualStrings(
        \\$member($V7, [$V7!$V8]) :- $V8 = [] % generated.
        \\$member($V10, [$V10!$V11]) :- $member($V12, $V11) % generated.
        \\$member($V15, [$V13!$V14]) :- $member($V15, $V14) % generated.
        \\
    , membership);
}

test "the list a plan reads members out of is whatever the definition fixed" {
    // What the head has to keep is the *list*, not a variable holding one. A
    // definition that wrote the collected list down fixes it just as firmly,
    // and one that wrote down part of it fixes that part.
    const allocator = testing.allocator;
    var strings: string_table.StringTable = .init(allocator);
    defer strings.deinit();
    var scalars: scalar.Store = .init(allocator);
    defer scalars.deinit();
    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();

    const p = try strings.intern("p");
    const r = try strings.intern("r");
    const x = try strings.intern("X");
    const y = try strings.intern("Y");
    const s = try strings.intern("S");
    const t = try strings.intern("T");
    const a = try scalars.internAtom("a");

    var second: syntax.Term.Cons = .{ .head = .{ .scalar = a }, .tail = .nil };
    var ground: syntax.Term.Cons = .{ .head = .{ .scalar = a }, .tail = .{ .cons = &second } };
    var partial: syntax.Term.Cons = .{ .head = .{ .scalar = a }, .tail = .{ .variable = t } };

    // One definition shape, four ways of saying what was collected.
    const outputs = [_]syntax.Term{
        .{ .variable = s },
        .{ .cons = &ground },
        .nil,
        .{ .cons = &partial },
    };
    const heads = [_][2]syntax.Term{
        .{ .{ .variable = x }, .{ .variable = s } },
        .{ .{ .variable = x }, .{ .variable = x } },
        .{ .{ .variable = x }, .{ .variable = x } },
        .{ .{ .variable = x }, .{ .variable = t } },
    };

    for (outputs, heads, 0..) |output, head_pair, index| {
        var head_terms = head_pair;
        var outer_terms = [_]syntax.Term{.{ .variable = x }};
        var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
        var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
        var body = [_]syntax.Clause{
            .{ .relational = .{ .predicate = p, .terms = &outer_terms } },
            .{ .aggregate = .{ .template = .{ .variable = y }, .body = &inner, .output = output } },
        };
        const id = try catalog.define(.{
            .head = .{ .predicate = try strings.intern("v"), .terms = &head_terms },
            .body = &body,
        }, .materialized);

        const view = catalog.view(id);
        try testing.expectEqual(@as(?Obstacle, null), obstacle(view));
        var inverted = try invert(allocator, &catalog.symbols, view);
        defer inverted.deinit();

        // The second rule reconstructs `r`, and its membership goal reads the
        // list the definition fixed.
        const list = inverted.rules[1].body[1].relation.terms[1];
        switch (index) {
            0 => try testing.expect(list == .variable),
            1 => {
                try testing.expectEqual(a, list.cons.head.constant);
                try testing.expectEqual(a, list.cons.tail.cons.head.constant);
                try testing.expect(list.cons.tail.cons.tail == .nil);
            },
            // Nothing was collected, so nothing is reconstructed — which is
            // the answer, not the absence of one.
            2 => try testing.expect(list == .nil),
            3 => {
                try testing.expectEqual(a, list.cons.head.constant);
                try testing.expect(list.cons.tail == .variable);
            },
            else => unreachable,
        }
    }
}
