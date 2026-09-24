//! What a fold does about the functions that read a collected set, and about
//! the sets two views turn out to have collected in common.
//!
//! A *list function* is an ordinary relation over a list: `sum(L, T)`,
//! `length(L, C)`. Inverting a view that uses one needs no special machinery —
//! Section 6.5's proof says as much, "the list functions that appear in the
//! views are treated no differently than base relations" — and the Inverse
//! Method already produces Definition 6.5.1's rules for
//! `v(X, T) :- p(X), setof(Y, r(X, Y), S), sum(S, T)` without knowing what
//! `sum` is. Three things it does not already do are here.
//!
//! The first is *expansion*. A query may name a list function the views do not
//! expose while defining it as a conjunction of ones they do — Example 6.5.2's
//! `avg` over `sum` and `length` — and such a goal is replaced by that
//! definition's body. A query that instead defines its list function by
//! structural recursion is refused rather than expanded: applied to a set the
//! plan can only *name*, `sum(X!Y, S) :- sum(Y, A), S = X + A` builds a longer
//! list at every step, which is Example 6.5.1's non-termination.
//!
//! The second is the *split*. A view collecting a set and then reading it with
//! list functions is two views wearing one head: an auxiliary `va(K̄, S)` that
//! collects, and a layer `v(X̄) :- va(K̄, S), λ(S, T)` that reads. Splitting is
//! not tidying. Two views collecting the same set say nothing about each other
//! while each keeps its own copy of it, and everything about each other once
//! both are written against one `va` — which is the whole content of the next
//! part.
//!
//! The third is the *chase*. Inverting a layer names the set it read with a
//! Skolem term, one per view, so `v1` reports `sum(f1(X, T), T)` and `v2`
//! reports `length(g1(X, C), C)` about sets with no evident relation. `va` is
//! functional in its key — one group collects one set — so `f1(x, t)` and
//! `g1(x, c)` are the same set whenever they belong to the same group, and
//! that is the functional dependency Section 6.5 encodes as chase rules. Here
//! it is a union-find over set terms rather than a relation the plan carries,
//! for the reason F2 gave about Skolem elimination: a plan is supposed to *be*
//! the query, and an equality the plan holds is only applied by whatever knows
//! to apply it. The union-find terminates for the reason splitting does —
//! there are finitely many set terms and they do not nest — and it gives
//! symmetry through canonical representatives, which the dissertation's rule
//! set, stating reflexivity and transitivity only, does not.
//!
//! Nothing here reads a database or a catalog. A view arrives as the rule it
//! is defined by, which is all any of these questions is about.

const std = @import("std");
const fold_ir = @import("fold_ir.zig");
const relation_store = @import("relation_store.zig");

/// Whether this rule defines a relation by recursion over the structure of a
/// list, which is what every list function in Appendix B but `first` is.
///
/// Such a definition cannot go into a plan that holds a set it can only name.
/// The recursive case builds a longer list out of the one it read, so a rule
/// deriving `sum(f(X, T), T)` from a stored tuple feeds `sum(Z!f(X, T), ...)`
/// back in, and that again, without end. Example 6.5.1 is exactly this.
///
/// The seed argument an admitted rule carries says so directly, and the shape
/// says so when a caller builds the rule without going through admission: a
/// head holding a list, and a body reading the head's own predicate.
pub fn isStructuralRecursion(rule: fold_ir.Rule) bool {
    if (rule.seed_argument != null) return true;
    var structural = false;
    for (rule.head.terms) |term| {
        if (term == .cons or term == .nil) structural = true;
    }
    if (!structural) return false;
    for (rule.body) |goal| switch (goal) {
        .relation => |relation| if (relation.predicate.equals(rule.head.predicate)) return true,
        else => {},
    };
    return false;
}

/// A view seen as the two layers it really is: what it collects, and what it
/// reads out of what it collected.
///
/// The goal slices are shallow — their terms belong to the definition this was
/// read from, which must outlive them — so `deinit` releases the slices and
/// nothing in them.
pub const Layers = struct {
    allocator: std.mem.Allocator,
    /// The one aggregate, whose output the head does not keep.
    aggregate: fold_ir.Aggregate,
    /// The collected set.
    set: fold_ir.Variable,
    /// The goals reading it. What the layer exposes.
    functions: []fold_ir.Relation,
    /// The auxiliary view the collecting half becomes, when it can become one.
    auxiliary: ?AuxiliaryView,

    pub fn deinit(self: *Layers) void {
        if (self.auxiliary) |auxiliary| {
            self.allocator.free(auxiliary.key);
            self.allocator.free(auxiliary.outer);
        }
        self.allocator.free(self.functions);
        self.* = undefined;
    }
};

/// `va(K̄, S) :- Φ(K̄), setof(Ȳ, Ψ, S)`: the half of a split view that
/// collects, with a head of its own.
pub const AuxiliaryView = struct {
    /// The `Φ`: goals that neither collect the set nor read it.
    outer: []fold_ir.Relation,
    /// The head variables that fix the set, in head order. `va` is functional
    /// in these because every variable the aggregate reads from outside itself
    /// is one of them.
    key: []fold_ir.Variable,

    /// The arity `va` stores under: the key, then the set.
    pub fn arity(self: AuxiliaryView) usize {
        return self.key.len + 1;
    }
};

/// Reads `definition` as a set it collects and the goals that read that set,
/// or null when it is neither.
///
/// The reading half is always there when there is one; the *auxiliary view* is
/// there only when the collecting half can stand as a rule of its own, which
/// is what step 2(a) of Section 6.5 assumes and does not say. Every goal
/// outside the aggregate must either read the set — and then it belongs to the
/// layer — or mention only head variables, and the head variables the
/// aggregate needs must be bound by those goals, because `va(K̄, S)` is a rule
/// and a rule whose head holds a variable nothing in its body binds is not
/// one. A definition whose only goal outside the aggregate is one *binding*
/// the collected list, which is Section 6.3.2's shape rather than 6.5's, fails
/// exactly there and is inverted the ordinary way.
///
/// Telling the two apart matters more than it looks. Without an auxiliary view
/// the set a layer read has no name but its own, so nothing can be proved
/// equal to it and the chase leaves it alone — which is the honest answer, and
/// is why the refusal falls out of the chase rather than being asserted next
/// to it.
pub fn layers(allocator: std.mem.Allocator, definition: fold_ir.Rule) !?Layers {
    if (definition.seed_argument != null) return null;

    var collecting: ?fold_ir.Aggregate = null;
    for (definition.body) |goal| switch (goal) {
        .aggregate => |value| {
            if (collecting != null) return null;
            collecting = value;
        },
        else => {},
    };
    const aggregate = collecting orelse return null;
    if (aggregate.output != .variable) return null;
    const set = aggregate.output.variable;
    if (mentions(definition.head.terms, set)) return null;

    var outer: std.ArrayList(fold_ir.Relation) = .empty;
    defer outer.deinit(allocator);
    var functions: std.ArrayList(fold_ir.Relation) = .empty;
    errdefer functions.deinit(allocator);
    var separable = true;
    for (definition.body) |goal| switch (goal) {
        .aggregate => {},
        // A comparison neither collects nor reads a list, so there is nowhere
        // for it to go; `inversion.obstacle` refuses such a definition anyway.
        .builtin => return null,
        .relation => |relation| {
            if (relation.negated) return null;
            if (readsOnly(relation.terms, set)) {
                try functions.append(allocator, relation);
            } else if (!mentions(relation.terms, set)) {
                try outer.append(allocator, relation);
            } else return null;
        },
    };
    if (functions.items.len == 0) return null;

    for (functions.items) |function| {
        for (function.terms) |term| switch (term) {
            .variable => |variable| if (variable != set and
                !mentions(definition.head.terms, variable))
            {
                separable = false;
            },
            // A list function reading a list the definition wrote down, or
            // reporting into one, is not the shape a layer exposes.
            .cons, .nil, .skolem => separable = false,
            .constant => {},
        };
    }

    var bound: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
    defer bound.deinit(allocator);
    for (outer.items) |relation|
        try fold_ir.collectRelationVariables(allocator, relation, &bound);
    var inner: std.array_hash_map.Auto(fold_ir.Variable, void) = .empty;
    defer inner.deinit(allocator);
    try fold_ir.collectTermVariables(allocator, aggregate.template, &inner);
    for (aggregate.body) |goal| try fold_ir.collectGoalVariables(allocator, goal, &inner);

    // What `va` has to be keyed by: everything the aggregate could read from
    // outside itself, plus whatever the outer goals bind. All of it has to be
    // in the head, and each of it has to be bound by an outer goal, or the
    // auxiliary view is not a rule.
    var key: std.ArrayList(fold_ir.Variable) = .empty;
    defer key.deinit(allocator);
    for (definition.head.terms) |term| switch (term) {
        .variable => |variable| {
            if (!bound.contains(variable) and !inner.contains(variable)) continue;
            for (key.items) |existing| {
                if (existing == variable) break;
            } else try key.append(allocator, variable);
        },
        else => {},
    };
    // What decides whether `va` is functional in its key: every value the
    // aggregate takes from outside itself has to be one the head kept. A
    // definition binding such a value and projecting it away leaves two stored
    // tuples with one key having collected different sets, which is the
    // dependency failing rather than a shape this cannot read.
    for (inner.keys()) |variable| {
        if (!bound.contains(variable)) continue;
        if (!mentions(definition.head.terms, variable)) separable = false;
    }
    // And `va(K̄, S) :- Φ, setof(...)` has to be a rule, so its key has to be
    // bound by the goals it kept.
    for (key.items) |variable| {
        if (!bound.contains(variable)) separable = false;
    }

    // Held as slices rather than as an optional struct, so that a failure
    // between the two copies has one owner to release rather than two: an
    // optional whose payload is half written is not something an `errdefer`
    // can read.
    var kept: []fold_ir.Relation = &.{};
    errdefer allocator.free(kept);
    var keys: []fold_ir.Variable = &.{};
    errdefer allocator.free(keys);
    if (separable) {
        kept = try allocator.dupe(fold_ir.Relation, outer.items);
        keys = try allocator.dupe(fold_ir.Variable, key.items);
    }
    return .{
        .allocator = allocator,
        .aggregate = aggregate,
        .set = set,
        .functions = try functions.toOwnedSlice(allocator),
        .auxiliary = if (separable) .{ .outer = kept, .key = keys } else null,
    };
}

/// Whether these terms mention the collected set and nothing else about it —
/// once, so that a goal relating a set to itself is not read as a function of
/// it.
fn readsOnly(terms: []const fold_ir.Term, set: fold_ir.Variable) bool {
    var seen: usize = 0;
    for (terms) |term| switch (term) {
        .variable => |variable| if (variable == set) {
            seen += 1;
        },
        else => {},
    };
    return seen == 1;
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

/// Whether two views collect the same set, so that one auxiliary view serves
/// both.
///
/// Same means same up to what the two definitions call their variables, with
/// the keys corresponding position by position: `va(X, S)` read out of `v1`
/// and out of `v2` is one relation only if `v1`'s first key column and `v2`'s
/// mean the same group. The mapping is required to be a bijection, because two
/// variables one definition keeps apart are not one variable because the other
/// spells them alike.
pub fn collectTheSameSet(
    allocator: std.mem.Allocator,
    left: *const Layers,
    right: *const Layers,
) !bool {
    const one_half = left.auxiliary orelse return false;
    const other_half = right.auxiliary orelse return false;
    if (one_half.outer.len != other_half.outer.len) return false;
    if (one_half.key.len != other_half.key.len) return false;

    var matcher: Matcher = .{ .allocator = allocator };
    defer matcher.deinit();
    for (one_half.key, other_half.key) |one, other| {
        if (!try matcher.bind(one, other)) return false;
    }
    if (!try matcher.bind(left.set, right.set)) return false;
    for (one_half.outer, other_half.outer) |one, other| {
        if (!try matcher.relation(one, other)) return false;
    }
    return matcher.aggregate(left.aggregate, right.aggregate);
}

/// A bijection between two definitions' variables, built while walking them
/// side by side.
const Matcher = struct {
    allocator: std.mem.Allocator,
    forward: std.array_hash_map.Auto(fold_ir.Variable, fold_ir.Variable) = .empty,
    backward: std.array_hash_map.Auto(fold_ir.Variable, fold_ir.Variable) = .empty,

    fn deinit(self: *Matcher) void {
        self.backward.deinit(self.allocator);
        self.forward.deinit(self.allocator);
        self.* = undefined;
    }

    fn bind(self: *Matcher, one: fold_ir.Variable, other: fold_ir.Variable) !bool {
        if (self.forward.get(one)) |existing| return existing == other;
        if (self.backward.get(other)) |existing| return existing == one;
        try self.forward.put(self.allocator, one, other);
        try self.backward.put(self.allocator, other, one);
        return true;
    }

    fn relation(
        self: *Matcher,
        one: fold_ir.Relation,
        other: fold_ir.Relation,
    ) std.mem.Allocator.Error!bool {
        if (!one.predicate.equals(other.predicate)) return false;
        if (one.negated != other.negated) return false;
        return self.terms(one.terms, other.terms);
    }

    fn aggregate(
        self: *Matcher,
        one: fold_ir.Aggregate,
        other: fold_ir.Aggregate,
    ) std.mem.Allocator.Error!bool {
        if (!try self.term(one.template, other.template)) return false;
        if (!try self.term(one.output, other.output)) return false;
        if (one.body.len != other.body.len) return false;
        for (one.body, other.body) |inner, rival| {
            if (!try self.goal(inner, rival)) return false;
        }
        return true;
    }

    fn goal(
        self: *Matcher,
        one: fold_ir.Goal,
        other: fold_ir.Goal,
    ) std.mem.Allocator.Error!bool {
        return switch (one) {
            .relation => |value| other == .relation and try self.relation(value, other.relation),
            .builtin => |value| other == .builtin and other.builtin.operator == value.operator and
                other.builtin.negated == value.negated and
                other.builtin.column_type.eql(value.column_type) and
                try self.terms(value.terms, other.builtin.terms),
            .aggregate => |value| other == .aggregate and try self.aggregate(value, other.aggregate),
        };
    }

    fn terms(
        self: *Matcher,
        one: []const fold_ir.Term,
        other: []const fold_ir.Term,
    ) std.mem.Allocator.Error!bool {
        if (one.len != other.len) return false;
        for (one, other) |value, rival| {
            if (!try self.term(value, rival)) return false;
        }
        return true;
    }

    fn term(
        self: *Matcher,
        one: fold_ir.Term,
        other: fold_ir.Term,
    ) std.mem.Allocator.Error!bool {
        return switch (one) {
            .constant => |value| other == .constant and other.constant == value,
            .variable => |value| other == .variable and try self.bind(value, other.variable),
            .nil => other == .nil,
            .cons => |pair| other == .cons and
                try self.term(pair.head, other.cons.head) and
                try self.term(pair.tail, other.cons.tail),
            .skolem => |call| other == .skolem and other.skolem.function == call.function and
                try self.terms(call.arguments, other.skolem.arguments),
        };
    }
};

/// A set the plan can name.
pub const SetTerm = union(enum) {
    /// The set an auxiliary view computes for a group. This is the one with a
    /// value: the plan derives it from the relations it reconstructed.
    collected: u32,
    /// The set inverting a layer named and cannot produce.
    skolem: fold_ir.Function,

    pub fn equals(self: SetTerm, other: SetTerm) bool {
        return switch (self) {
            .collected => |tag| other == .collected and other.collected == tag,
            .skolem => |function| other == .skolem and other.skolem == function,
        };
    }
};

/// Which set terms are known to name the same set.
///
/// Section 6.5 encodes the functional dependency on `va` as chase rules —
/// `e(S1, S2) :- va(X, S1), va(X, S2)` with reflexivity and transitivity — and
/// says so as a relation the plan carries. A relation is the wrong shape here
/// twice over. `e(X, X)` ranges over every term there is and the transitive
/// rule over an unbounded domain, so neither can be materialized; and a plan
/// that only answers correctly when something applies its equalities is not a
/// plan, which is what F2 settled about Skolem elimination. So the equalities
/// are decided here, while the plan is being built, and what the plan gets is
/// the substituted rules.
///
/// It terminates because the terms are finite and do not nest: a Skolem set is
/// built once per layer out of a view's stored values, and an auxiliary view's
/// set is named by a tag. Reflexivity holds of every term the moment it is
/// interned, transitivity is what union-find is, and symmetry — which the
/// dissertation's rule set does not state, though its dependency is symmetric
/// by construction — is having one representative per class rather than an
/// ordered pair per equality.
pub const Chase = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayList(Entry) = .empty,

    const Entry = struct {
        term: SetTerm,
        parent: u32,
        size: u32,
        /// The auxiliary view whose set this class is, once some member says
        /// so. Only a root's is meaningful.
        collected: ?u32,
    };

    pub fn deinit(self: *Chase) void {
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    /// The index of `term`, adding it on first mention. A term is equal to
    /// itself from that moment, which is reflexivity and is all of it.
    pub fn intern(self: *Chase, term: SetTerm) !u32 {
        if (self.indexOf(term)) |existing| return existing;
        const index: u32 = @intCast(self.entries.items.len);
        try self.entries.append(self.allocator, .{
            .term = term,
            .parent = index,
            .size = 1,
            .collected = switch (term) {
                .collected => |tag| tag,
                .skolem => null,
            },
        });
        return index;
    }

    fn indexOf(self: *const Chase, term: SetTerm) ?u32 {
        for (self.entries.items, 0..) |entry, index| {
            if (entry.term.equals(term)) return @intCast(index);
        }
        return null;
    }

    /// The class representative, flattening the path it walked.
    pub fn find(self: *Chase, index: u32) u32 {
        var root = index;
        while (self.entries.items[root].parent != root) root = self.entries.items[root].parent;
        var walking = index;
        while (self.entries.items[walking].parent != walking) {
            const next = self.entries.items[walking].parent;
            self.entries.items[walking].parent = root;
            walking = next;
        }
        return root;
    }

    /// Records that these two terms name the same set.
    pub fn unite(self: *Chase, left: SetTerm, right: SetTerm) !void {
        const one = self.find(try self.intern(left));
        const other = self.find(try self.intern(right));
        if (one == other) return;
        const larger, const smaller = if (self.entries.items[one].size >=
            self.entries.items[other].size) .{ one, other } else .{ other, one };
        self.entries.items[smaller].parent = larger;
        self.entries.items[larger].size += self.entries.items[smaller].size;
        if (self.entries.items[larger].collected == null)
            self.entries.items[larger].collected = self.entries.items[smaller].collected;
    }

    /// Whether these two terms are known to name the same set. Reflexive of
    /// every term, and symmetric because both sides are asked the same
    /// question about one representative.
    pub fn equal(self: *Chase, left: SetTerm, right: SetTerm) !bool {
        return self.find(try self.intern(left)) == self.find(try self.intern(right));
    }

    /// The auxiliary view whose set this one is, or null when nothing said.
    ///
    /// This is what makes a Skolem set readable: `va` derives its set from the
    /// relations the plan reconstructed, so a Skolem term proved equal to one
    /// can be replaced by a variable the plan binds, and one that was not
    /// proved equal to any stays a name for a set nothing produces.
    pub fn resolve(self: *Chase, term: SetTerm) !?u32 {
        return self.entries.items[self.find(try self.intern(term))].collected;
    }
};

/// A query's goals and rules with every list function it defines expanded into
/// the goals that define it.
pub const Expansion = struct {
    allocator: std.mem.Allocator,
    goals: []fold_ir.Goal,
    rules: []fold_ir.Rule,
    /// The list functions whose definitions were substituted in and dropped.
    expanded: []relation_store.PredicateKey,
    /// A list function the query defines by structural recursion, if it has
    /// one. Such a query is outside Theorem 6.5.1's class and the caller
    /// refuses it; the goals and rules are then the query's own, unchanged.
    recursive: ?relation_store.PredicateKey,

    pub fn deinit(self: *Expansion) void {
        self.allocator.free(self.expanded);
        for (self.rules) |rule| fold_ir.freeRule(self.allocator, rule);
        self.allocator.free(self.rules);
        fold_ir.freeGoals(self.allocator, self.goals);
        self.* = undefined;
    }
};

/// Expands the list functions a query defines for itself.
///
/// Theorem 6.5.1 holds when every list function in the query is one the views
/// expose or a conjunctive view over ones they do. The first needs nothing:
/// such a goal is reconstructed from the views like any other relation. The
/// second is this — Example 6.5.2's `avg(S, A)` becomes `sum(S, T),
/// length(S, C)` and the arithmetic between them, so that what the query asks
/// for is written in the vocabulary the views kept. The definition is then
/// dropped, because a plan holds no list-function definitions: the rules
/// deriving `sum` are the inverses of the views that stored a sum.
///
/// A goal is a list function only where it reads a set some aggregate in the
/// same body collected. A rule mentioning `avg` over an ordinary value is a
/// rule about `avg`, and nothing here touches it.
pub fn expandQuery(
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    goals: []const fold_ir.Goal,
    rules: []const fold_ir.Rule,
) !Expansion {
    var expansion: Builder = .{ .allocator = allocator, .symbols = symbols, .rules = rules };
    defer expansion.deinit();
    try expansion.walk(goals, rules);
    return expansion.finish(goals, rules);
}

const Builder = struct {
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    /// The query's own rules: where a list function's definition is looked up.
    rules: []const fold_ir.Rule,
    expanded: std.ArrayList(relation_store.PredicateKey) = .empty,
    recursive: ?relation_store.PredicateKey = null,

    fn deinit(self: *Builder) void {
        self.expanded.deinit(self.allocator);
        self.* = undefined;
    }

    /// Finds the list functions worth expanding, without changing anything
    /// yet: whether one rule's body has to be rewritten depends on what every
    /// other rule turns out to define.
    fn walk(self: *Builder, goals: []const fold_ir.Goal, rules: []const fold_ir.Rule) !void {
        // A list function the query defines by structural recursion is refused
        // wherever it is written, not only where a goal happens to reach it.
        // The plan is the query's program together with the inverse rules, so
        // such a rule would be applied to every set those rules name, and each
        // application makes a longer list to apply it to again. Theorem 6.5.1
        // asks for a list function the views expose or a conjunction of ones
        // they do, and this is neither.
        for (rules) |rule| {
            if (!isStructuralRecursion(rule)) continue;
            if (self.recursive != null) continue;
            self.recursive = switch (rule.head.predicate) {
                .base => |key| key,
                else => continue,
            };
        }
        try self.walkBody(goals);
        for (rules) |rule| try self.walkBody(rule.body);
    }

    fn walkBody(self: *Builder, body: []const fold_ir.Goal) !void {
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
            if (!readsAny(relation.terms, &sets)) continue;
            const key = switch (relation.predicate) {
                .base => |value| value,
                else => continue,
            };
            const definition = self.definitionOf(key) orelse continue;
            if (isStructuralRecursion(definition)) {
                if (self.recursive == null) self.recursive = key;
                continue;
            }
            if (!conjunctive(definition)) continue;
            for (self.expanded.items) |already| {
                if (already.name == key.name and already.arity == key.arity) break;
            } else try self.expanded.append(self.allocator, key);
        }
    }

    /// The query's definition of `key`, when it has exactly one. Several rules
    /// are a relation with cases rather than a list function written as a
    /// conjunction, and expanding one of them would answer less than the query.
    fn definitionOf(self: *const Builder, key: relation_store.PredicateKey) ?fold_ir.Rule {
        var found: ?fold_ir.Rule = null;
        for (self.rules) |rule| {
            const head = switch (rule.head.predicate) {
                .base => |value| value,
                else => continue,
            };
            if (head.name != key.name or head.arity != key.arity) continue;
            if (found != null) return null;
            found = rule;
        }
        return found;
    }

    fn isExpanded(self: *const Builder, key: relation_store.PredicateKey) bool {
        for (self.expanded.items) |already| {
            if (already.name == key.name and already.arity == key.arity) return true;
        }
        return false;
    }

    fn finish(
        self: *Builder,
        goals: []const fold_ir.Goal,
        rules: []const fold_ir.Rule,
    ) !Expansion {
        const nothing = self.expanded.items.len == 0 or self.recursive != null;
        const rewritten = if (nothing)
            try fold_ir.cloneGoals(self.allocator, goals)
        else
            try self.rewrite(goals);
        errdefer fold_ir.freeGoals(self.allocator, rewritten);

        var kept: std.ArrayList(fold_ir.Rule) = .empty;
        errdefer {
            for (kept.items) |rule| fold_ir.freeRule(self.allocator, rule);
            kept.deinit(self.allocator);
        }
        for (rules) |rule| {
            if (!nothing) {
                const head = switch (rule.head.predicate) {
                    .base => |value| value,
                    else => null,
                };
                if (head != null and self.isExpanded(head.?)) continue;
            }
            const body = if (nothing)
                try fold_ir.cloneGoals(self.allocator, rule.body)
            else
                try self.rewrite(rule.body);
            errdefer fold_ir.freeGoals(self.allocator, body);
            const terms = try fold_ir.cloneTerms(self.allocator, rule.head.terms);
            errdefer fold_ir.freeTerms(self.allocator, terms);
            try kept.append(self.allocator, .{
                .scope = rule.scope,
                .head = .{
                    .predicate = rule.head.predicate,
                    .terms = terms,
                    .negated = rule.head.negated,
                    .provenance = rule.head.provenance,
                },
                .body = body,
                .seed_argument = rule.seed_argument,
            });
        }

        // Taken before the rules are, because taking them empties the list the
        // errdefer above would have released.
        const dropped = if (nothing)
            try self.allocator.alloc(relation_store.PredicateKey, 0)
        else
            try self.allocator.dupe(relation_store.PredicateKey, self.expanded.items);
        errdefer self.allocator.free(dropped);
        return .{
            .allocator = self.allocator,
            .goals = rewritten,
            .rules = try kept.toOwnedSlice(self.allocator),
            .expanded = dropped,
            .recursive = self.recursive,
        };
    }

    /// One body with every expandable goal replaced by the goals that define
    /// it, renamed so that the definition's own variables meet nobody else's
    /// and bound to what the goal supplied.
    fn rewrite(self: *Builder, body: []const fold_ir.Goal) ![]fold_ir.Goal {
        var built: std.ArrayList(fold_ir.Goal) = .empty;
        errdefer {
            for (built.items) |goal| fold_ir.freeGoal(self.allocator, goal);
            built.deinit(self.allocator);
        }
        for (body) |goal| {
            const key = expandableKey(goal) orelse {
                const copy = try fold_ir.cloneGoal(self.allocator, goal);
                errdefer fold_ir.freeGoal(self.allocator, copy);
                try built.append(self.allocator, copy);
                continue;
            };
            if (!self.isExpanded(key)) {
                const copy = try fold_ir.cloneGoal(self.allocator, goal);
                errdefer fold_ir.freeGoal(self.allocator, copy);
                try built.append(self.allocator, copy);
                continue;
            }
            try self.substituteDefinition(goal.relation, self.definitionOf(key).?, &built);
        }
        return built.toOwnedSlice(self.allocator);
    }

    fn expandableKey(goal: fold_ir.Goal) ?relation_store.PredicateKey {
        const relation = switch (goal) {
            .relation => |value| value,
            else => return null,
        };
        if (relation.negated) return null;
        return switch (relation.predicate) {
            .base => |key| key,
            else => null,
        };
    }

    fn substituteDefinition(
        self: *Builder,
        goal: fold_ir.Relation,
        definition: fold_ir.Rule,
        into: *std.ArrayList(fold_ir.Goal),
    ) !void {
        const renamed = try fold_ir.renameRule(self.allocator, self.symbols, definition);
        defer fold_ir.freeRule(self.allocator, renamed);

        var substitution: fold_ir.Substitution = .{};
        defer substitution.deinit(self.allocator);
        for (renamed.head.terms, goal.terms) |parameter, argument| {
            if (parameter != .variable) continue;
            try substitution.put(self.allocator, parameter.variable, argument);
        }
        const expanded = try fold_ir.substituteGoals(self.allocator, renamed.body, &substitution);
        errdefer fold_ir.freeGoals(self.allocator, expanded);
        for (expanded) |*slot| markGenerated(slot);
        try into.appendSlice(self.allocator, expanded);
        self.allocator.free(expanded);
    }
};

/// A goal that came from a definition the caller wrote but did not write here.
fn markGenerated(goal: *fold_ir.Goal) void {
    switch (goal.*) {
        .relation => |*relation| relation.provenance = .generated,
        .builtin => |*builtin| builtin.provenance = .generated,
        .aggregate => |*aggregate| aggregate.provenance = .generated,
    }
}

fn readsAny(
    terms: []const fold_ir.Term,
    sets: *const std.array_hash_map.Auto(fold_ir.Variable, void),
) bool {
    for (terms) |term| switch (term) {
        .variable => |variable| if (sets.contains(variable)) return true,
        else => {},
    };
    return false;
}

/// Whether a definition is the conjunction Theorem 6.5.1 asks for: no
/// recursion, no aggregate, no negation, nothing but relations and the
/// arithmetic between them.
fn conjunctive(definition: fold_ir.Rule) bool {
    if (definition.seed_argument != null) return false;
    for (definition.head.terms) |term| if (term != .variable) return false;
    for (definition.body) |goal| switch (goal) {
        .relation => |relation| {
            if (relation.negated) return false;
            if (relation.predicate.equals(definition.head.predicate)) return false;
        },
        .builtin => |builtin| if (builtin.negated) return false,
        .aggregate => return false,
    };
    return true;
}

const testing = std.testing;
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");

/// One rule in the folding IR, lowered from the language the engine speaks so
/// that the shapes under test are shapes somebody could have written.
const Fixture = struct {
    strings: string_table.StringTable,
    symbols: fold_ir.Symbols,

    fn init(allocator: std.mem.Allocator) Fixture {
        return .{ .strings = .init(allocator), .symbols = .init(allocator) };
    }

    fn deinit(self: *Fixture) void {
        self.symbols.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    fn rule(self: *Fixture, allocator: std.mem.Allocator, value: syntax.Rule) !fold_ir.Rule {
        return fold_ir.lowerRule(
            allocator,
            &self.symbols,
            try self.symbols.openScope(.query),
            value,
        );
    }

    /// `v(X, T) :- p(X), setof(Y, r(X, Y), S), <function>(S, T).`
    fn collectingView(
        self: *Fixture,
        allocator: std.mem.Allocator,
        name: []const u8,
        function: []const u8,
    ) !fold_ir.Rule {
        const v = try self.strings.intern(name);
        const p = try self.strings.intern("p");
        const r = try self.strings.intern("r");
        const reader = try self.strings.intern(function);
        const x = try self.strings.intern("X");
        const y = try self.strings.intern("Y");
        const s = try self.strings.intern("S");
        const t = try self.strings.intern("T");

        var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = t } };
        var outer_terms = [_]syntax.Term{.{ .variable = x }};
        var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
        var reading = [_]syntax.Term{ .{ .variable = s }, .{ .variable = t } };
        var inner = [_]syntax.Clause{
            .{ .relational = .{ .predicate = r, .terms = &inner_terms } },
        };
        var body = [_]syntax.Clause{
            .{ .relational = .{ .predicate = p, .terms = &outer_terms } },
            .{ .aggregate = .{
                .template = .{ .variable = y },
                .body = &inner,
                .output = .{ .variable = s },
            } },
            .{ .relational = .{ .predicate = reader, .terms = &reading } },
        };
        return self.rule(allocator, .{
            .head = .{ .predicate = v, .terms = &head_terms },
            .body = &body,
        });
    }
};

test "a view that collects a set and then reads it is two views" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const definition = try fixture.collectingView(allocator, "v1", "sum");
    defer fold_ir.freeRule(allocator, definition);

    var split = (try layers(allocator, definition)).?;
    defer split.deinit();
    // `p(X)` collects nothing and reads nothing, so it is the auxiliary
    // view's; `sum(S, T)` reads the set, so it is the layer's; and the key is
    // the one head variable the auxiliary view needs.
    try testing.expectEqual(@as(usize, 1), split.functions.len);
    const auxiliary = split.auxiliary.?;
    try testing.expectEqual(@as(usize, 1), auxiliary.outer.len);
    try testing.expectEqual(@as(usize, 1), auxiliary.key.len);
    try testing.expectEqual(@as(usize, 2), auxiliary.arity());
}

test "a collecting half no rule could stand for leaves the set with only its own name" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    // v(X) :- p(X, S), setof(Y, r(X, Y), S). Section 6.3.2's shape: the goal
    // outside the aggregate *binds* the collected list rather than reading a
    // function of it, so the collecting half is `va(X, S) :- setof(...)`,
    // whose head holds an `X` nothing in its body binds. There is no auxiliary
    // view, and nothing can be proved equal to the set this view collected.
    const v = try fixture.strings.intern("v");
    const p = try fixture.strings.intern("p");
    const r = try fixture.strings.intern("r");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const s = try fixture.strings.intern("S");
    var head_terms = [_]syntax.Term{.{ .variable = x }};
    var outer_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
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
    const definition = try fixture.rule(allocator, .{
        .head = .{ .predicate = v, .terms = &head_terms },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, definition);

    var split = (try layers(allocator, definition)).?;
    defer split.deinit();
    try testing.expectEqual(@as(usize, 1), split.functions.len);
    try testing.expect(split.auxiliary == null);
}

test "a head that kept its collected list needs no auxiliary view" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    // v(X, S, T) :- p(X), setof(Y, r(X, Y), S), sum(S, T). The list is stored,
    // so the plan reads it rather than naming it, and there is no set whose
    // identity anything has to prove.
    const v = try fixture.strings.intern("v");
    const p = try fixture.strings.intern("p");
    const r = try fixture.strings.intern("r");
    const sum = try fixture.strings.intern("sum");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const s = try fixture.strings.intern("S");
    const t = try fixture.strings.intern("T");
    var head_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s }, .{ .variable = t } };
    var outer_terms = [_]syntax.Term{.{ .variable = x }};
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var reading = [_]syntax.Term{ .{ .variable = s }, .{ .variable = t } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = p, .terms = &outer_terms } },
        .{ .aggregate = .{
            .template = .{ .variable = y },
            .body = &inner,
            .output = .{ .variable = s },
        } },
        .{ .relational = .{ .predicate = sum, .terms = &reading } },
    };
    const definition = try fixture.rule(allocator, .{
        .head = .{ .predicate = v, .terms = &head_terms },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, definition);

    try testing.expect(try layers(allocator, definition) == null);
}

test "two views collect the same set exactly when they say the same thing about it" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const summing = try fixture.collectingView(allocator, "v1", "sum");
    defer fold_ir.freeRule(allocator, summing);
    const counting = try fixture.collectingView(allocator, "v2", "length");
    defer fold_ir.freeRule(allocator, counting);

    var one = (try layers(allocator, summing)).?;
    defer one.deinit();
    var other = (try layers(allocator, counting)).?;
    defer other.deinit();
    // The two definitions are lowered in different scopes, so no variable of
    // one is a variable of the other; what makes their sets one set is the
    // shape, not the spelling.
    try testing.expect(try collectTheSameSet(allocator, &one, &other));

    // A third view collecting over a different relation is a different set,
    // however alike the two definitions read.
    var elsewhere = try fixture.collectingView(allocator, "v3", "sum");
    defer fold_ir.freeRule(allocator, elsewhere);
    elsewhere.body[1].aggregate.body[0].relation.predicate = .{
        .base = .{ .name = try fixture.strings.intern("other"), .arity = 2 },
    };
    var third = (try layers(allocator, elsewhere)).?;
    defer third.deinit();
    try testing.expect(!try collectTheSameSet(allocator, &one, &third));
}

test "the chase is reflexive, symmetric and transitive over set terms" {
    const allocator = testing.allocator;
    var chase: Chase = .{ .allocator = allocator };
    defer chase.deinit();

    const first: SetTerm = .{ .skolem = @enumFromInt(0) };
    const second: SetTerm = .{ .skolem = @enumFromInt(1) };
    const group: SetTerm = .{ .collected = 0 };
    const apart: SetTerm = .{ .skolem = @enumFromInt(2) };

    // Reflexive of a term nothing was said about.
    try testing.expect(try chase.equal(apart, apart));
    try testing.expect(!try chase.equal(first, second));

    try chase.unite(first, group);
    try chase.unite(second, group);
    // Transitive: neither union mentioned the other Skolem set.
    try testing.expect(try chase.equal(first, second));
    // Symmetric, because both sides ask about one representative rather than
    // about an ordered pair.
    try testing.expect(try chase.equal(second, first));
    try testing.expect(!try chase.equal(first, apart));

    // And a class holding an auxiliary view's set knows which one it is, which
    // is what lets a Skolem term be replaced by a value the plan derives.
    try testing.expectEqual(@as(?u32, 0), try chase.resolve(first));
    try testing.expectEqual(@as(?u32, 0), try chase.resolve(second));
    try testing.expectEqual(@as(?u32, null), try chase.resolve(apart));
}

test "a list function defined by structural recursion is recognized as one" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    // sum(H!T, S) :- sum(T, A), S = A + H. Example 6.5.1's definition, which
    // no plan holding a named set may contain.
    const sum = try fixture.strings.intern("sum");
    const h = try fixture.strings.intern("H");
    const t = try fixture.strings.intern("T");
    const s = try fixture.strings.intern("S");
    const a = try fixture.strings.intern("A");
    const plus = try fixture.strings.intern("+");
    var pair: syntax.Term.Cons = .{ .head = .{ .variable = h }, .tail = .{ .variable = t } };
    var head_terms = [_]syntax.Term{ .{ .cons = &pair }, .{ .variable = s } };
    var recursive_terms = [_]syntax.Term{ .{ .variable = t }, .{ .variable = a } };
    var arithmetic = [_]syntax.Term{
        .{ .variable = s },
        .{ .variable = a },
        .{ .variable = h },
    };
    var body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = sum, .terms = &recursive_terms } },
        .{ .builtin = .{ .predicate = plus, .terms = &arithmetic, .kind = .add } },
    };
    const definition = try fixture.rule(allocator, .{
        .head = .{ .predicate = sum, .terms = &head_terms },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, definition);

    try testing.expect(isStructuralRecursion(definition));
    // And it is not the conjunction a query may define a list function by,
    // which is the other half of Theorem 6.5.1's condition.
    try testing.expect(!conjunctive(definition));
}

test "a query's own list function is replaced by the ones the views expose" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    // excess(L, E) :- sum(L, T), length(L, C), E = T - C.
    // q(X, E) :- p(X), setof(Y, r(X, Y), S), excess(S, E).
    const q = try fixture.strings.intern("q");
    const excess = try fixture.strings.intern("excess");
    const sum = try fixture.strings.intern("sum");
    const len = try fixture.strings.intern("length");
    const p = try fixture.strings.intern("p");
    const r = try fixture.strings.intern("r");
    const minus = try fixture.strings.intern("-");
    const l = try fixture.strings.intern("L");
    const e = try fixture.strings.intern("E");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const s = try fixture.strings.intern("S");
    const t = try fixture.strings.intern("T");
    const c = try fixture.strings.intern("C");

    var definition_head = [_]syntax.Term{ .{ .variable = l }, .{ .variable = e } };
    var summing = [_]syntax.Term{ .{ .variable = l }, .{ .variable = t } };
    var counting = [_]syntax.Term{ .{ .variable = l }, .{ .variable = c } };
    var arithmetic = [_]syntax.Term{
        .{ .variable = e },
        .{ .variable = t },
        .{ .variable = c },
    };
    var definition_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = sum, .terms = &summing } },
        .{ .relational = .{ .predicate = len, .terms = &counting } },
        .{ .builtin = .{ .predicate = minus, .terms = &arithmetic, .kind = .subtract } },
    };
    const definition = try fixture.rule(allocator, .{
        .head = .{ .predicate = excess, .terms = &definition_head },
        .body = &definition_body,
    });
    defer fold_ir.freeRule(allocator, definition);

    var query_head = [_]syntax.Term{ .{ .variable = x }, .{ .variable = e } };
    var outer_terms = [_]syntax.Term{.{ .variable = x }};
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var reading = [_]syntax.Term{ .{ .variable = s }, .{ .variable = e } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var query_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = p, .terms = &outer_terms } },
        .{ .aggregate = .{
            .template = .{ .variable = y },
            .body = &inner,
            .output = .{ .variable = s },
        } },
        .{ .relational = .{ .predicate = excess, .terms = &reading } },
    };
    const asking = try fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = &query_head },
        .body = &query_body,
    });
    defer fold_ir.freeRule(allocator, asking);

    const rules = [_]fold_ir.Rule{ definition, asking };
    var expansion = try expandQuery(allocator, &fixture.symbols, &.{}, &rules);
    defer expansion.deinit();

    try testing.expectEqual(@as(?relation_store.PredicateKey, null), expansion.recursive);
    try testing.expectEqual(@as(usize, 1), expansion.expanded.len);
    try testing.expectEqual(excess, expansion.expanded[0].name);
    // The definition is gone, because a plan holds no list-function
    // definitions: what derives `sum` is the inverse of a view that stored one.
    try testing.expectEqual(@as(usize, 1), expansion.rules.len);
    // And the goal that named it is now the three goals that defined it, bound
    // to the set the query collected.
    const body = expansion.rules[0].body;
    try testing.expectEqual(@as(usize, 5), body.len);
    try testing.expect(body[2].relation.predicate.equals(.{
        .base = .{ .name = sum, .arity = 2 },
    }));
    try testing.expect(body[3].relation.predicate.equals(.{
        .base = .{ .name = len, .arity = 2 },
    }));
    try testing.expectEqual(body[1].aggregate.output.variable, body[2].relation.terms[0].variable);
    try testing.expectEqual(body[1].aggregate.output.variable, body[3].relation.terms[0].variable);
    // The definition's own variables are not the query's, and what it reported
    // is what the goal asked for.
    try testing.expectEqual(body[4].builtin.terms[0].variable, asking.body[2].relation.terms[1].variable);
}
