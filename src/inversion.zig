//! Reconstructing the relations a view's body read, and removing the terms
//! that reconstruction invents.
//!
//! A view stores what its definition kept. Inverting it runs the definition
//! backwards: from a stored tuple, each body goal must have had a fact behind
//! it, so each becomes a rule that reconstructs one. A variable the head kept
//! is still a value the plan can name, so it stays a variable. A variable the
//! head projected away is not — the tuple says such a value existed without
//! saying which — so it becomes a Skolem term applied to the head's values.
//! One function per projected variable, shared by every rule the view yields:
//! the reconstructed facts have to join back up, and in Chapter 6's
//! even-length-path example they only do because the node between `X` and `Z`
//! is the same `f(X, Z)` in both halves.
//!
//! A Skolem term cannot be evaluated, so a plan holding one is not yet a plan.
//! Eliminating them is the second half of this module, and it is not a
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

/// Why a definition is outside the class the ordinary Inverse Method inverts.
///
/// Each of these is a later phase's problem rather than a defect: a view
/// carrying an aggregate is F3's, one carrying a list is F5's, and one reading
/// what it defines is recursion, which inversion cannot bound.
pub const Obstacle = enum {
    recursive,
    not_conjunctive,
    lists,

    pub fn text(self: Obstacle) []const u8 {
        return switch (self) {
            .recursive => "its definition reads the relation it defines",
            .not_conjunctive => "its definition is not a conjunction of positive relations",
            .lists => "its definition mentions a list",
        };
    }
};

/// What stops this view from being inverted, or null when nothing does.
///
/// A definition is one rule, so the only recursion it can express is reading
/// its own name; a recursive view would need several rules and the catalog has
/// nowhere to put them. Mutual recursion between views is therefore not
/// something this can see, and not something the catalog can hold.
pub fn obstacle(view: *const view_catalog.View) ?Obstacle {
    const definition = view.definition;
    if (definition.seed_argument != null) return .recursive;
    for (definition.head.terms) |term| if (term == .cons or term == .nil) return .lists;
    for (definition.body) |goal| {
        const relation = switch (goal) {
            .relation => |value| value,
            .builtin, .aggregate => return .not_conjunctive,
        };
        if (relation.negated) return .not_conjunctive;
        const key = switch (relation.predicate) {
            .base => |value| value,
            .view, .generated => return .not_conjunctive,
        };
        if (key.name == view.name and key.arity == definition.head.terms.len) return .recursive;
        for (relation.terms) |term| if (term == .cons or term == .nil) return .lists;
    }
    return null;
}

/// One view's inverse rules: one per body goal, each reconstructing what that
/// goal read out of what the view stored.
pub const Inversion = struct {
    allocator: std.mem.Allocator,
    rules: []fold_ir.Rule,

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

    var builder: Builder = .{
        .allocator = allocator,
        .symbols = symbols,
        .scope = scope,
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

    var rules: std.ArrayList(fold_ir.Rule) = .empty;
    errdefer {
        for (rules.items) |rule| fold_ir.freeRule(allocator, rule);
        rules.deinit(allocator);
    }
    for (definition.body) |goal| {
        const rule = try builder.inverse(view, goal.relation);
        errdefer fold_ir.freeRule(allocator, rule);
        try rules.append(allocator, rule);
    }
    return .{ .allocator = allocator, .rules = try rules.toOwnedSlice(allocator) };
}

/// The state one view's inversion shares across its rules: the fresh variables
/// standing for the head's, and the function each projected variable was
/// assigned. Both must be the same in every rule, which is why they are here
/// rather than rebuilt per goal.
const Builder = struct {
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    scope: fold_ir.Scope,
    arguments: []fold_ir.Term,
    renaming: fold_ir.Substitution = .{},
    functions: std.array_hash_map.Auto(fold_ir.Variable, fold_ir.Function) = .empty,

    fn deinit(self: *Builder) void {
        self.functions.deinit(self.allocator);
        self.renaming.deinit(self.allocator);
        self.allocator.free(self.arguments);
        self.* = undefined;
    }

    fn inverse(
        self: *Builder,
        view: *const view_catalog.View,
        relation: fold_ir.Relation,
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

        const read = try fold_ir.substituteTerms(
            self.allocator,
            view.definition.head.terms,
            &self.renaming,
        );
        errdefer fold_ir.freeTerms(self.allocator, read);
        const body = try self.allocator.alloc(fold_ir.Goal, 1);
        body[0] = .{ .relation = .{
            .predicate = view.predicate(),
            .terms = read,
            .provenance = .generated,
        } };
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

        const function = self.functions.get(variable) orelse blk: {
            const fresh = try self.symbols.freshFunction(self.scope);
            try self.functions.put(self.allocator, variable, fresh);
            break :blk fresh;
        };
        const call = try self.allocator.create(fold_ir.Term.Skolem);
        errdefer self.allocator.destroy(call);
        call.* = .{
            .function = function,
            .arguments = try fold_ir.cloneTerms(self.allocator, self.arguments),
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
            .generated => false,
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
                    .view, .generated => unreachable,
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

    // total(X, S) :- setof(Y, edge(X, Y), S). An aggregate is F3's problem.
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
    try testing.expectEqual(Obstacle.not_conjunctive, obstacle(catalog.view(aggregated)).?);

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
