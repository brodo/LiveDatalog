//! A small, embeddable Datalog engine modeled after Jatalog.
const std = @import("std");
const scalar = @import("scalar.zig");
pub const input = @import("input.zig");
const input_compiler = @import("input_compiler.zig");
const relation_store = @import("relation_store.zig");

const Id = u64;
const ValueId = u64;
const Fact = relation_store.Fact;
const PredicateKey = relation_store.PredicateKey;
const RelationStore = relation_store.RelationStore;
pub const Error = error{
    InvalidFact,
    InvalidRule,
    InvalidQuery,
    InvalidTerm,
    InvalidSyntax,
    NotStratified,
    UnboundVariable,
    UnknownOperator,
    NumericType,
    NumericOverflow,
    NotAdmissible,
    UnknownVariable,
    TypeMismatch,
    /// Shadow verification found the maintained closure disagreeing with a
    /// fresh rebuild. Only reachable with `setShadowVerification(true)`.
    MaintenanceMismatch,
};

/// Interns predicate and variable symbols used by a database. IDs are
/// insertion indexes, which makes `resolve` a reverse lookup into the ordered
/// keys of the same StringArrayHashMapUnmanaged.
const StringTable = struct {
    allocator: std.mem.Allocator,
    strings: std.StringArrayHashMapUnmanaged(Id) = .empty,

    fn init(allocator: std.mem.Allocator) StringTable {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *StringTable) void {
        for (self.strings.keys()) |string| self.allocator.free(string);
        self.strings.deinit(self.allocator);
        self.* = undefined;
    }

    fn clone(self: *const StringTable) !StringTable {
        var result: StringTable = .init(self.allocator);
        errdefer result.deinit();
        for (self.strings.keys()) |string| _ = try result.intern(string);
        return result;
    }

    fn intern(self: *StringTable, string: []const u8) !Id {
        if (self.strings.get(string)) |id| return id;
        const owned = try self.allocator.dupe(u8, string);
        errdefer self.allocator.free(owned);
        const id: Id = @intCast(self.strings.count());
        try self.strings.putNoClobber(self.allocator, owned, id);
        return id;
    }

    fn get(self: *const StringTable, string: []const u8) ?Id {
        return self.strings.get(string);
    }

    fn resolve(self: *const StringTable, id: Id) []const u8 {
        return self.strings.keys()[@intCast(id)];
    }
};

const Value = union(enum) {
    scalar: scalar.Id,
    nil,
    cons: struct { head: ValueId, tail: ValueId },
};

const ValueTable = struct {
    allocator: std.mem.Allocator,
    values: std.ArrayList(Value) = .empty,

    fn init(allocator: std.mem.Allocator) ValueTable {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *ValueTable) void {
        self.values.deinit(self.allocator);
        self.* = undefined;
    }

    fn clone(self: *const ValueTable) !ValueTable {
        return .{
            .allocator = self.allocator,
            .values = try self.values.clone(self.allocator),
        };
    }

    fn intern(self: *ValueTable, value: Value) !ValueId {
        for (self.values.items, 0..) |existing, index| {
            if (std.meta.eql(existing, value)) return @intCast(index);
        }
        try self.values.append(self.allocator, value);
        return @intCast(self.values.items.len - 1);
    }

    fn get(self: *const ValueTable, id: ValueId) Value {
        return self.values.items[@intCast(id)];
    }

    fn internFrom(self: *ValueTable, source: *const ValueTable, id: ValueId) !ValueId {
        return switch (source.get(id)) {
            .scalar => |value| try self.intern(.{ .scalar = value }),
            .nil => try self.intern(.nil),
            .cons => |pair| try self.intern(.{ .cons = .{
                .head = try self.internFrom(source, pair.head),
                .tail = try self.internFrom(source, pair.tail),
            } }),
        };
    }
};

const InputBuilder = struct {
    database: *Jatalog,

    pub fn allocator(self: *InputBuilder) std.mem.Allocator {
        return self.database.allocator;
    }

    pub fn nilTerm(_: *InputBuilder) Term { // ziglint-ignore: Z012
        return .nil;
    }

    pub fn atomTerm(self: *InputBuilder, atom: []const u8) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.scalars.internAtom(atom) };
    }

    pub fn integerTerm(self: *InputBuilder, integer: i64) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.scalars.internInteger(integer) };
    }

    pub fn floatTerm(self: *InputBuilder, float: f64) !Term { // ziglint-ignore: Z012
        return .{ .scalar = try self.database.scalars.internFloat(float) };
    }

    pub fn variableTerm(self: *InputBuilder, name: []const u8) !Term { // ziglint-ignore: Z012
        return .{ .variable = try self.database.strings.intern(name) };
    }

    pub fn consTerm(self: *InputBuilder, head: Term, tail: Term) !Term { // ziglint-ignore: Z012
        const pair = try self.database.allocator.create(Term.Cons);
        pair.* = .{ .head = head, .tail = tail };
        return .{ .cons = pair };
    }

    pub fn releaseTerm(self: *InputBuilder, term: Term) void { // ziglint-ignore: Z012
        freeTerm(self.database.allocator, term);
    }
};

const Term = union(enum) {
    scalar: scalar.Id,
    variable: Id,
    nil,
    cons: *Cons,

    pub const Cons = struct {
        head: Term,
        tail: Term,
    };

    fn isGround(self: Term) bool {
        return switch (self) {
            .variable => false,
            .cons => |pair| pair.head.isGround() and pair.tail.isGround(),
            else => true,
        };
    }
};

const GoalKind = enum {
    relation,
    equality,
    inequality,
    less_than,
    less_or_equal,
    greater_than,
    greater_or_equal,
    add,
    subtract,
};

const Expr = struct {
    predicate: Id,
    terms: []Term,
    negated: bool = false,
    kind: GoalKind = .relation,

    fn arity(self: Expr) usize {
        return self.terms.len;
    }

    fn isGround(self: Expr) bool {
        for (self.terms) |term| if (!term.isGround()) return false;
        return true;
    }
};

const Rule = struct {
    /// Stable database-local identifier; body occurrences are identified by
    /// `(id, clause index)`. Ids survive cloning and are never reused.
    id: u32 = 0,
    head: Expr,
    body: []Clause,
    seed_argument: ?usize = null,
};

/// Restricts one relational body occurrence to facts appended during the
/// previous semi-naive round.
const DeltaConstraint = struct {
    clause_index: usize,
    delta_start: usize,
    delta_end: usize,
};

/// How a batch's changed predicates affect one stratum's maintenance.
const StratumImpact = enum { none, aggregate, rebuild };

/// CReaM-style auxiliary view for a maintained aggregate rule whose head
/// projects out some of its outer-goal variables. Each tuple retains those
/// projected values followed by the head values they derive, so the number
/// of auxiliary tuples carrying a head tuple is that tuple's derivation
/// count. A projected head tuple becomes visible on a zero-to-one count
/// transition and is deleted on a one-to-zero transition.
const AuxiliaryView = struct {
    rule_id: u32,
    /// Outer-goal variables omitted from the head, in ascending id order.
    projected: []Id,
    head_arity: usize,
    tuples: RelationStore,

    fn deinit(self: *AuxiliaryView, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
        allocator.free(self.projected);
        self.tuples.deinit();
        self.* = undefined;
    }

    fn clone(self: *const AuxiliaryView, allocator: std.mem.Allocator) !AuxiliaryView { // ziglint-ignore: Z023
        const projected = try allocator.dupe(Id, self.projected);
        errdefer allocator.free(projected);
        return .{
            .rule_id = self.rule_id,
            .projected = projected,
            .head_arity = self.head_arity,
            .tuples = try self.tuples.clone(),
        };
    }

    fn arity(self: *const AuxiliaryView) usize {
        return self.projected.len + self.head_arity;
    }

    fn key(self: *const AuxiliaryView) PredicateKey {
        return .{ .name = self.rule_id, .arity = self.arity() };
    }

    fn headTerms(self: *const AuxiliaryView, tuple: Fact) []const ValueId {
        return tuple.terms[self.projected.len..];
    }
};

fn fillOuterClauses(rule: Rule, clause_index: usize, buffer: []Clause) usize {
    var count: usize = 0;
    for (rule.body, 0..) |clause, index| {
        if (index == clause_index) continue;
        buffer[count] = clause;
        count += 1;
    }
    return count;
}

/// Returns the body index of the single unnested `setof` occurrence a rule
/// can have maintained incrementally, or null when the rule falls outside
/// the maintainable class and needs the rebuild fallback: no aggregate,
/// several aggregates, a nested aggregate, or seeded structural recursion.
fn maintainableAggregateIndex(rule: Rule) ?usize {
    if (rule.seed_argument != null) return null;
    var found: ?usize = null;
    for (rule.body, 0..) |clause, index| {
        const aggregate = switch (clause) {
            .aggregate => |value| value,
            else => continue,
        };
        if (found != null) return null;
        for (aggregate.body) |inner| if (inner == .aggregate) return null;
        found = index;
    }
    return found;
}

fn copyFactInto(allocator: std.mem.Allocator, store: *RelationStore, fact: Fact) !void {
    const terms = try allocator.dupe(ValueId, fact.terms);
    _ = store.insert(.{ .predicate = fact.predicate, .terms = terms }, false) catch |err| {
        allocator.free(terms);
        return err;
    };
}

fn bindingsEqual(left: *const Binding, right: *const Binding) bool {
    if (left.values.count() != right.values.count()) return false;
    for (left.values.keys(), left.values.values()) |variable, value| {
        const other = right.values.get(variable) orelse return false;
        if (other != value) return false;
    }
    return true;
}

const Materialization = union(enum) {
    uninitialized,
    clean,
    dirty_from_stratum: usize,
};

/// Rule analysis cached after validation: the stratum mapping plus, for each
/// predicate read anywhere in a rule body, the lowest head stratum that
/// depends on it. Invalidated whenever the rule set changes.
const Analysis = struct {
    strata: std.array_hash_map.Auto(PredicateKey, usize),
    first_dependent: std.array_hash_map.Auto(PredicateKey, usize),
    max_level: usize,
    has_seed_rules: bool,

    fn deinit(self: *Analysis, allocator: std.mem.Allocator) void { // ziglint-ignore: Z023
        self.strata.deinit(allocator);
        self.first_dependent.deinit(allocator);
        self.* = undefined;
    }
};

const Aggregate = struct {
    template: Term,
    body: []Clause,
    output: Term,
};

const Clause = union(enum) {
    relational: Expr,
    builtin: Expr,
    negated: Expr,
    aggregate: Aggregate,
};

fn noteBodyDependencies(
    allocator: std.mem.Allocator,
    body: []const Clause,
    head_level: usize,
    first_dependent: *std.array_hash_map.Auto(PredicateKey, usize),
) !void {
    for (body) |clause| switch (clause) {
        .relational, .negated => |expression| {
            const entry = try first_dependent.getOrPut(allocator, predicateKey(expression));
            if (!entry.found_existing or entry.value_ptr.* > head_level)
                entry.value_ptr.* = head_level;
        },
        .builtin => {},
        .aggregate => |aggregate| try noteBodyDependencies(
            allocator,
            aggregate.body,
            head_level,
            first_dependent,
        ),
    };
}

fn clausesReadGrownNonPositively(
    body: []const Clause,
    grown: *const std.AutoHashMapUnmanaged(PredicateKey, void),
) bool {
    for (body) |clause| switch (clause) {
        .negated => |expression| if (grown.contains(predicateKey(expression))) return true,
        .aggregate => |aggregate| if (clausesReadGrownAnywhere(aggregate.body, grown)) return true,
        .relational, .builtin => {},
    };
    return false;
}

fn clausesReadGrownAnywhere(
    body: []const Clause,
    grown: *const std.AutoHashMapUnmanaged(PredicateKey, void),
) bool {
    for (body) |clause| switch (clause) {
        .relational, .negated => |expression| if (grown.contains(predicateKey(expression))) return true,
        .aggregate => |aggregate| if (clausesReadGrownAnywhere(aggregate.body, grown)) return true,
        .builtin => {},
    };
    return false;
}

fn predicateKey(expression: Expr) PredicateKey {
    return .{ .name = expression.predicate, .arity = expression.terms.len };
}

const Binding = struct {
    values: std.array_hash_map.Auto(Id, ValueId) = .empty,

    pub fn deinit(self: *Binding, allocator: std.mem.Allocator) void {
        self.values.deinit(allocator);
        self.* = undefined;
    }

    fn clone(self: *const Binding, allocator: std.mem.Allocator) !Binding {
        return .{ .values = try self.values.clone(allocator) };
    }
};

const ResultNode = union(enum) {
    atom: []u8,
    integer: i64,
    float: f64,
    nil,
    cons: *ResultCons,
};

const ResultCons = struct {
    head: *ResultNode,
    tail: *ResultNode,
};

pub const ResultValue = struct {
    node: *const ResultNode,

    pub const Kind = enum { atom, integer, float, nil, cons };

    pub fn kind(self: ResultValue) Kind {
        return switch (self.node.*) {
            .atom => .atom,
            .integer => .integer,
            .float => .float,
            .nil => .nil,
            .cons => .cons,
        };
    }

    pub fn getAtom(self: ResultValue) Error![]const u8 {
        return switch (self.node.*) {
            .atom => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn getInteger(self: ResultValue) Error!i64 {
        return switch (self.node.*) {
            .integer => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn getFloat(self: ResultValue) Error!f64 {
        return switch (self.node.*) {
            .float => |value| value,
            else => Error.TypeMismatch,
        };
    }

    pub fn head(self: ResultValue) Error!ResultValue {
        return switch (self.node.*) {
            .cons => |pair| .{ .node = pair.head },
            else => Error.TypeMismatch,
        };
    }

    pub fn tail(self: ResultValue) Error!ResultValue {
        return switch (self.node.*) {
            .cons => |pair| .{ .node = pair.tail },
            else => Error.TypeMismatch,
        };
    }

    pub fn formatAlloc(self: ResultValue, allocator: std.mem.Allocator) ![]u8 {
        var output: std.Io.Writer.Allocating = .init(allocator);
        defer output.deinit();
        self.write(&output.writer) catch return error.OutOfMemory;
        return output.toOwnedSlice();
    }

    pub fn write(self: ResultValue, writer: *std.Io.Writer) !void {
        switch (self.node.*) {
            .atom => |value| {
                try scalar.writeAtom(writer, value);
            },
            .integer => |value| try writer.print("{d}", .{value}),
            .float => |value| try scalar.writeFloat(writer, value),
            .nil => try writer.writeAll("[]"),
            .cons => |pair| if (isProperResultList(self.node)) {
                try writer.writeByte('[');
                var current = self.node;
                var first = true;
                while (current.* == .cons) {
                    if (!first) try writer.writeAll(", ");
                    try (ResultValue{ .node = current.cons.head }).write(writer);
                    current = current.cons.tail;
                    first = false;
                }
                try writer.writeByte(']');
            } else {
                try writer.writeAll("cons(");
                try (ResultValue{ .node = pair.head }).write(writer);
                try writer.writeAll(", ");
                try (ResultValue{ .node = pair.tail }).write(writer);
                try writer.writeByte(')');
            },
        }
    }
};

fn isProperResultList(root: *const ResultNode) bool {
    var current = root;
    while (true) switch (current.*) {
        .nil => return true,
        .cons => |pair| current = pair.tail,
        else => return false,
    };
}

fn freeResultNode(allocator: std.mem.Allocator, node: *ResultNode) void {
    switch (node.*) {
        .atom => |atom| allocator.free(atom),
        .integer, .float, .nil => {},
        .cons => |pair| {
            freeResultNode(allocator, pair.head);
            freeResultNode(allocator, pair.tail);
            allocator.destroy(pair);
        },
    }
    allocator.destroy(node);
}

pub const Answer = struct {
    allocator: std.mem.Allocator,
    bindings: std.ArrayList(ResultBinding) = .empty,

    pub const ResultBinding = struct {
        name: []u8,
        value: ResultValue,
    };

    fn deinit(self: *Answer) void {
        for (self.bindings.items) |binding| {
            self.allocator.free(binding.name);
            freeResultNode(self.allocator, @constCast(binding.value.node));
        }
        self.bindings.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn getValue(self: *const Answer, variable: []const u8) Error!ResultValue {
        for (self.bindings.items) |binding|
            if (std.mem.eql(u8, binding.name, variable)) return binding.value;
        return Error.UnknownVariable;
    }

    pub fn getAtom(self: *const Answer, variable: []const u8) Error![]const u8 {
        return (try self.getValue(variable)).getAtom();
    }

    pub fn getInteger(self: *const Answer, variable: []const u8) Error!i64 {
        return (try self.getValue(variable)).getInteger();
    }

    pub fn getFloat(self: *const Answer, variable: []const u8) Error!f64 {
        return (try self.getValue(variable)).getFloat();
    }
};

pub const QueryResult = struct {
    allocator: std.mem.Allocator,
    answers: std.ArrayList(Answer) = .empty,

    pub fn deinit(self: *QueryResult) void {
        for (self.answers.items) |*answer| answer.deinit();
        self.answers.deinit(self.allocator);
        self.* = undefined;
    }
};

pub const MaintenanceStats = struct {
    closure_facts: usize,
    /// Facts added to the closure by incremental insertion propagation.
    propagated_facts: usize,
    /// Facts removed from the closure by delete-and-rederive.
    removed_facts: usize,
    stratum_expansions: usize,
    /// Updates that abandoned incremental maintenance for a stratum rebuild.
    rebuild_fallbacks: usize,
    /// Aggregate groups recomputed by incremental maintenance.
    maintained_groups: usize,
    /// Maintained aggregate views whose head retains every outer variable.
    self_maintainable_views: usize,
    /// Maintained aggregate views whose head projects outer variables away
    /// and therefore need auxiliary derivation counts.
    projected_views: usize,
    auxiliary_tuples: usize,
};

pub const ExecutionResult = union(enum) {
    none,
    changed: bool,
    query: QueryResult,

    pub fn deinit(self: *ExecutionResult) void {
        switch (self.*) {
            .query => |*result| result.deinit(),
            else => {},
        }
        self.* = undefined;
    }
};

pub const Jatalog = struct {
    allocator: std.mem.Allocator,
    strings: StringTable,
    scalars: scalar.Store,
    values: ValueTable,
    facts: RelationStore,
    rules: std.ArrayList(Rule) = .empty,
    next_rule_id: u32 = 0,
    /// Persistent derived closure: the base facts plus every derived fact,
    /// exposed to evaluation as one unified read view. Null until the first
    /// evaluation on a database with rules.
    closure: ?RelationStore = null,
    materialization: Materialization = .uninitialized,
    analysis: ?Analysis = null,
    /// Auxiliary views for maintained aggregate rules with projected heads.
    auxiliary: std.ArrayList(AuxiliaryView) = .empty,
    /// Counts stratum expansions; tests use it to prove that repeated
    /// queries perform no rule expansion after the first materialization.
    expansions: usize = 0,
    /// Counts facts added to the closure by incremental batch propagation,
    /// distinguishing incrementally added facts from rebuilt facts.
    propagated_facts: usize = 0,
    /// Counts facts removed from the closure by incremental
    /// delete-and-rederive, net of rederived facts.
    removed_facts: usize = 0,
    /// Counts updates that abandoned incremental maintenance for a
    /// stratum rebuild.
    rebuild_fallbacks: usize = 0,
    /// Counts aggregate groups recomputed by incremental maintenance.
    maintained_groups: usize = 0,
    /// Debug mode: verify every maintained closure against a fresh rebuild.
    shadow_verification: bool = false,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{
            .allocator = allocator,
            .strings = .init(allocator),
            .scalars = .init(allocator),
            .values = .init(allocator),
            .facts = .init(allocator),
        };
    }

    pub fn deinit(self: *Jatalog) void {
        for (self.auxiliary.items) |*view| view.deinit(self.allocator);
        self.auxiliary.deinit(self.allocator);
        if (self.closure) |*closure| closure.deinit();
        if (self.analysis) |*analysis| analysis.deinit(self.allocator);
        self.facts.deinit();
        for (self.rules.items) |rule| {
            freeExpr(self.allocator, rule.head);
            for (rule.body) |clause| freeClauseTree(self.allocator, clause);
            self.allocator.free(rule.body);
        }
        self.rules.deinit(self.allocator);
        self.values.deinit();
        self.scalars.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    fn clone(self: *const Jatalog) !Jatalog {
        var result: Jatalog = .{
            .allocator = self.allocator,
            .strings = try self.strings.clone(),
            .scalars = undefined,
            .values = undefined,
            .facts = undefined,
            .next_rule_id = self.next_rule_id,
        };
        errdefer result.strings.deinit();
        result.scalars = try self.scalars.clone();
        errdefer result.scalars.deinit();
        result.values = try self.values.clone();
        errdefer result.values.deinit();
        result.facts = try self.facts.clone();
        errdefer result.facts.deinit();
        if (self.closure) |*closure| result.closure = try closure.clone();
        errdefer if (result.closure) |*closure| closure.deinit();
        result.materialization = self.materialization;
        result.expansions = self.expansions;
        result.propagated_facts = self.propagated_facts;
        result.removed_facts = self.removed_facts;
        result.rebuild_fallbacks = self.rebuild_fallbacks;
        result.maintained_groups = self.maintained_groups;
        result.shadow_verification = self.shadow_verification;
        errdefer {
            for (result.auxiliary.items) |*view| view.deinit(self.allocator);
            result.auxiliary.deinit(self.allocator);
        }
        for (self.auxiliary.items) |*view| {
            var copy = try view.clone(self.allocator);
            result.auxiliary.append(self.allocator, copy) catch |err| {
                copy.deinit(self.allocator);
                return err;
            };
        }
        errdefer {
            for (result.rules.items) |rule| freeRule(self.allocator, rule);
            result.rules.deinit(self.allocator);
        }
        for (self.rules.items) |rule| {
            const copy = try cloneRule(self.allocator, rule);
            result.rules.append(self.allocator, copy) catch |err| {
                freeRule(self.allocator, copy);
                return err;
            };
        }
        return result;
    }

    fn commit(self: *Jatalog, staging: *Jatalog) void {
        const previous = self.*;
        self.* = staging.*;
        staging.* = previous;
    }

    /// Applies the base facts a retraction removed. `staging` holds the
    /// post-retraction base facts computed by goal evaluation; the removals
    /// are replayed onto a fresh clone so query-local values interned while
    /// evaluating the goals never reach the committed database. The removals
    /// then take the same incremental deletion path as a batch: exact facts
    /// through delete-and-rederive and aggregate maintenance when the
    /// closure is clean, and dirty-stratum rebuild otherwise.
    fn commitRetraction(self: *Jatalog, staging: *Jatalog) !void {
        var committed = try self.clone();
        defer committed.deinit();
        const maintain = committed.closure != null and committed.materialization == .clean;
        var removed: RelationStore = .init(committed.allocator);
        defer removed.deinit();
        var index = committed.facts.len();
        while (index > 0) {
            index -= 1;
            const fact = committed.facts.factAt(index);
            if (try staging.facts.contains(fact)) continue;
            if (maintain) {
                try copyFactInto(committed.allocator, &removed, fact);
            } else {
                try committed.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
            }
            committed.facts.removeAt(index);
        }
        if (maintain and removed.len() > 0) {
            try committed.propagateDeletions(&removed);
            var touched: RelationStore = .init(committed.allocator);
            defer touched.deinit();
            for (0..removed.len()) |position|
                try copyFactInto(committed.allocator, &touched, removed.factAt(position));
            if (touched.len() > 0) try committed.maintainAggregates(&touched);
        }
        try committed.verifyShadow();
        self.commit(&committed);
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const input.Term) !void {
        var staging = try self.clone();
        defer staging.deinit();
        const expression = try staging.compileRelation(predicate, terms, false);
        defer freeExpr(staging.allocator, expression);
        try staging.addFactExpr(expression);
        self.commit(&staging);
    }

    pub fn addRule(self: *Jatalog, head: input.Goal, body: []const input.Goal) !void {
        var staging = try self.clone();
        defer staging.deinit();
        const compiled_head = switch (head) {
            .relation => |relation| try staging.compileRelation(relation.predicate, relation.terms, false),
            else => return Error.InvalidRule,
        };
        var head_owned = true;
        defer if (head_owned) freeExpr(staging.allocator, compiled_head);
        const compiled_body = try staging.compileGoals(body);
        var body_owned = true;
        defer {
            if (body_owned) for (compiled_body) |clause| freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled_body);
        }
        try staging.addRuleClauses(compiled_head, compiled_body);
        head_owned = false;
        body_owned = false;
        self.commit(&staging);
    }

    pub fn query(self: *Jatalog, goals: []const input.Goal) !QueryResult {
        try self.ensureMaterialized();
        var staging = try self.clone();
        defer staging.deinit();
        const compiled = try staging.compileGoals(goals);
        defer {
            for (compiled) |clause| freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        return staging.queryClauses(compiled);
    }

    pub fn retract(self: *Jatalog, goals: []const input.Goal) !bool {
        try self.ensureMaterialized();
        var staging = try self.clone();
        defer staging.deinit();
        const compiled = try staging.compileGoals(goals);
        defer {
            for (compiled) |clause| freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        const changed = try staging.deleteClauses(compiled);
        if (changed) try self.commitRetraction(&staging);
        return changed;
    }

    /// Applies one batch of exact ground base-fact insertions and deletions
    /// with set semantics: re-inserting an existing fact and deleting an
    /// absent fact are no-ops. Insertions into a clean materialized closure
    /// propagate incrementally through positive strata with the semi-naive
    /// delta engine; when the update reaches negation or `setof`, that
    /// stratum is marked dirty and rebuilt through the M1 path. Deletions
    /// always take the dirty-stratum rebuild path. The batch commits
    /// atomically: any failure leaves the database unchanged. Returns
    /// whether the base fact set changed.
    pub fn applyChanges(
        self: *Jatalog,
        insertions: []const input.Relation,
        deletions: []const input.Relation,
    ) !bool {
        var staging = try self.clone();
        defer staging.deinit();
        const changed = try staging.applyChangesCompiled(insertions, deletions);
        try staging.verifyShadow();
        if (changed) self.commit(&staging);
        return changed;
    }

    /// Brings the derived closure up to date now instead of at the next
    /// query. Maintenance is otherwise lazy: an update marks the affected
    /// strata and the next evaluation repairs them. Calling this on a
    /// database without rules is a no-op and allocates nothing.
    pub fn materialize(self: *Jatalog) !void {
        var staging = try self.clone();
        defer staging.deinit();
        try staging.ensureMaterialized();
        try staging.verifyShadow();
        self.commit(&staging);
    }

    /// Discards the derived closure and every auxiliary view and recomputes
    /// them from the current base facts and rules. This is the reference
    /// path incremental maintenance is checked against; it is always
    /// available and always correct, at the cost of full recomputation.
    pub fn rebuild(self: *Jatalog) !void {
        var staging = try self.clone();
        defer staging.deinit();
        if (staging.closure) |*closure| {
            closure.deinit();
            staging.closure = null;
        }
        staging.dropAuxiliaryViews();
        staging.materialization = .uninitialized;
        try staging.ensureMaterialized();
        self.commit(&staging);
    }

    /// Enables or disables shadow verification. When enabled, every
    /// maintained closure is compared against a fresh rebuild from the same
    /// base facts before the change is committed, and a disagreement is
    /// reported as `MaintenanceMismatch` with the database unchanged. This
    /// roughly doubles update cost and is intended for tests and debugging.
    pub fn setShadowVerification(self: *Jatalog, enabled: bool) void {
        self.shadow_verification = enabled;
    }

    /// Compares the maintained closure against a rebuild performed on a
    /// throwaway copy, so verification never disturbs this database.
    fn verifyShadow(self: *Jatalog) !void {
        if (!self.shadow_verification) return;
        const closure = if (self.closure) |*value| value else return;
        var staging = try self.clone();
        defer staging.deinit();
        var reference = try staging.facts.clone();
        defer reference.deinit();
        try staging.expandNaive(&reference);
        if (reference.len() != closure.len()) return Error.MaintenanceMismatch;
        for (0..reference.len()) |index|
            if (!try closure.contains(reference.factAt(index))) return Error.MaintenanceMismatch;
    }

    fn applyChangesCompiled(
        self: *Jatalog,
        insertions: []const input.Relation,
        deletions: []const input.Relation,
    ) !bool {
        var changed = false;
        const maintain = self.closure != null and self.materialization == .clean;
        var removed: RelationStore = .init(self.allocator);
        defer removed.deinit();
        for (deletions) |relation| {
            const expression = try self.compileRelation(relation.predicate, relation.terms, false);
            defer freeExpr(self.allocator, expression);
            if (!expression.isGround()) return Error.InvalidFact;
            const terms = try self.allocator.alloc(ValueId, expression.terms.len);
            defer self.allocator.free(terms);
            for (expression.terms, terms) |term, *id| id.* = try self.termToValue(term, null);
            const fact: Fact = .{ .predicate = expression.predicate, .terms = terms };
            if (try self.facts.removeFact(fact)) {
                changed = true;
                if (maintain) {
                    const copy = try self.allocator.dupe(ValueId, terms);
                    _ = removed.insert(.{ .predicate = fact.predicate, .terms = copy }, false) catch |err| {
                        self.allocator.free(copy);
                        return err;
                    };
                } else {
                    try self.markBaseChanged(.{ .name = fact.predicate, .arity = terms.len });
                }
            }
        }
        var touched: RelationStore = .init(self.allocator);
        defer touched.deinit();
        if (maintain and removed.len() > 0) {
            try self.propagateDeletions(&removed);
            for (0..removed.len()) |index| try copyFactInto(self.allocator, &touched, removed.factAt(index));
        }

        const propagate = self.closure != null and self.materialization == .clean;
        const batch_start = if (propagate) self.closure.?.len() else 0;
        for (insertions) |relation| {
            const expression = try self.compileRelation(relation.predicate, relation.terms, false);
            defer freeExpr(self.allocator, expression);
            if (try self.applyInsertion(expression, propagate)) changed = true;
        }
        if (propagate and self.closure.?.len() > batch_start) {
            try self.propagateInsertions(batch_start);
            if (self.materialization == .clean) {
                for (batch_start..self.closure.?.len()) |index|
                    try copyFactInto(self.allocator, &touched, self.closure.?.factAt(index));
            }
        }
        if (touched.len() > 0) try self.maintainAggregates(&touched);
        return changed;
    }

    /// Propagates a batch of base insertions already appended to the clean
    /// closure at `batch_start`, one stratum at a time. A stratum whose
    /// negated or aggregated dependencies gained facts falls back to the
    /// dirty-stratum rebuild; strata below it keep their incremental state.
    fn propagateInsertions(self: *Jatalog, batch_start: usize) !void {
        const start_len = self.closure.?.len();
        const analysis = try self.ensureAnalysis();
        const max_level = analysis.max_level;
        var level: usize = 0;
        while (level <= max_level) : (level += 1) {
            if (try self.propagationBlocked(level, batch_start)) {
                self.rebuild_fallbacks += 1;
                self.markDirty(level);
                try self.ensureMaterialized();
                return;
            }
            try self.propagateLevel(&self.closure.?, &analysis.strata, level, batch_start);
        }
        self.propagated_facts += self.closure.?.len() - start_len;
    }

    /// A stratum blocks incremental propagation when one of its rules reads
    /// a predicate that gained facts during this batch through negation or
    /// through an aggregate this phase cannot maintain.
    fn propagationBlocked(self: *Jatalog, level: usize, batch_start: usize) !bool {
        const closure = &self.closure.?;
        var grown: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
        defer grown.deinit(self.allocator);
        for (batch_start..closure.len()) |index| {
            const fact = closure.factAt(index);
            try grown.put(self.allocator, .{
                .name = fact.predicate,
                .arity = fact.terms.len,
            }, {});
        }
        return self.strataBlockedBy(level, &grown);
    }

    fn strataBlockedBy(
        self: *Jatalog,
        level: usize,
        changed: *const std.AutoHashMapUnmanaged(PredicateKey, void),
    ) !bool {
        return try self.stratumImpact(level, changed) == .rebuild;
    }

    /// Classifies how a batch's changed predicates affect one stratum:
    /// negation over a changed predicate always needs the rebuild path, an
    /// aggregate over a changed predicate needs it only when the rule is
    /// outside the maintainable class, and everything else is handled by
    /// the ordinary delta and delete-and-rederive engines.
    fn stratumImpact(
        self: *Jatalog,
        level: usize,
        changed: *const std.AutoHashMapUnmanaged(PredicateKey, void),
    ) !StratumImpact {
        if (changed.count() == 0) return .none;
        const analysis = try self.ensureAnalysis();
        var impact: StratumImpact = .none;
        for (self.rules.items) |rule| {
            const rule_level = analysis.strata.get(predicateKey(rule.head)) orelse 0;
            if (rule_level != level and (rule.seed_argument == null or rule_level > level)) continue;
            for (rule.body) |clause| switch (clause) {
                .negated => |expression| if (changed.contains(predicateKey(expression))) return .rebuild,
                .aggregate => |aggregate| if (clausesReadGrownAnywhere(aggregate.body, changed)) {
                    if (maintainableAggregateIndex(rule) == null) return .rebuild;
                    impact = .aggregate;
                },
                .relational, .builtin => {},
            };
        }
        return impact;
    }

    /// Maintains rules containing one unnested `setof` after a batch changed
    /// the aggregate's inner relations. Only groups reachable from a changed
    /// inner fact are recomputed. A group whose canonical list changed emits
    /// its stale head tuples as deletions and its recomputed tuple as an
    /// insertion, which then cascade through the ordinary deletion and
    /// insertion maintenance. Rounds repeat while aggregate results keep
    /// changing, with a bounded fallback to a full rebuild.
    fn maintainAggregates(self: *Jatalog, touched: *RelationStore) !void {
        if (self.closure == null or self.materialization != .clean) return;
        const round_cap = (try self.ensureAnalysis()).max_level + 4;
        var round: usize = 0;
        while (true) {
            round += 1;
            if (round > round_cap) {
                self.rebuild_fallbacks += 1;
                self.markDirty(0);
                return self.ensureMaterialized();
            }
            var removals: RelationStore = .init(self.allocator);
            defer removals.deinit();
            var additions: std.ArrayList(Fact) = .empty;
            defer {
                for (additions.items) |fact| self.allocator.free(fact.terms);
                additions.deinit(self.allocator);
            }
            var changed: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
            defer changed.deinit(self.allocator);
            for (0..touched.len()) |index| {
                const fact = touched.factAt(index);
                try changed.put(self.allocator, .{
                    .name = fact.predicate,
                    .arity = fact.terms.len,
                }, {});
            }
            for (self.rules.items) |rule| {
                const clause_index = maintainableAggregateIndex(rule) orelse continue;
                // A projected view also reacts to outer-goal changes, which
                // create and destroy whole groups.
                const trigger = if (self.auxiliaryFor(rule.id) == null)
                    rule.body[clause_index].aggregate.body
                else
                    rule.body;
                if (!clausesReadGrownAnywhere(trigger, &changed)) continue;
                try self.maintainAggregateRule(rule, clause_index, touched, &removals, &additions);
            }
            if (removals.len() == 0 and additions.items.len == 0) return;

            touched.clear();
            if (removals.len() > 0) {
                try self.propagateDeletions(&removals);
                for (0..removals.len()) |index| {
                    const fact = removals.factAt(index);
                    const terms = try self.allocator.dupe(ValueId, fact.terms);
                    _ = touched.insert(.{ .predicate = fact.predicate, .terms = terms }, false) catch |err| {
                        self.allocator.free(terms);
                        return err;
                    };
                }
            }
            if (self.materialization != .clean) return;
            const batch_start = self.closure.?.len();
            for (additions.items) |fact| {
                if (try self.closure.?.contains(fact)) continue;
                const terms = try self.allocator.dupe(ValueId, fact.terms);
                _ = self.closure.?.insert(.{ .predicate = fact.predicate, .terms = terms }, true) catch |err| {
                    self.allocator.free(terms);
                    return err;
                };
            }
            if (self.closure.?.len() > batch_start) {
                try self.propagateInsertions(batch_start);
                if (self.materialization != .clean) return;
                for (batch_start..self.closure.?.len()) |index| {
                    const fact = self.closure.?.factAt(index);
                    const terms = try self.allocator.dupe(ValueId, fact.terms);
                    _ = touched.insert(.{ .predicate = fact.predicate, .terms = terms }, false) catch |err| {
                        self.allocator.free(terms);
                        return err;
                    };
                }
            }
        }
    }

    fn maintainAggregateRule(
        self: *Jatalog,
        rule: Rule,
        clause_index: usize,
        touched: *RelationStore,
        removals: *RelationStore,
        additions: *std.ArrayList(Fact),
    ) !void {
        const aggregate = rule.body[clause_index].aggregate;
        const outer = try self.allocator.alloc(Clause, rule.body.len - 1);
        defer self.allocator.free(outer);
        const outer_count = fillOuterClauses(rule, clause_index, outer);

        // Only variables the outer goals or the head can constrain identify a
        // group; variables local to the aggregate body must stay free.
        var scope: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer scope.deinit(self.allocator);
        for (outer[0..outer_count]) |clause|
            try collectClauseSurfaceVariables(self.allocator, clause, &scope);
        for (rule.head.terms) |term| try collectTermVariables(self.allocator, term, &scope);

        var groups: std.ArrayList(Binding) = .empty;
        defer {
            for (groups.items) |*group| group.deinit(self.allocator);
            groups.deinit(self.allocator);
        }
        // A changed fact reaches a group either through the aggregate's
        // inner goals (its member set changed) or through the outer goals
        // (the group itself appeared or disappeared).
        const view = self.auxiliaryFor(rule.id);
        for (0..touched.len()) |index| {
            const fact = touched.factAt(index);
            for ([_][]const Clause{ aggregate.body, outer[0..outer_count] }) |clauses| {
                for (clauses) |candidate| {
                    const expression = switch (candidate) {
                        .relational => |value| value,
                        else => continue,
                    };
                    if (expression.predicate != fact.predicate or
                        expression.terms.len != fact.terms.len) continue;
                    var seed: Binding = .{};
                    defer seed.deinit(self.allocator);
                    if (!try self.unify(fact, expression, &seed)) continue;
                    var restricted: Binding = .{};
                    defer restricted.deinit(self.allocator);
                    for (seed.values.keys(), seed.values.values()) |variable, value| {
                        if (scope.contains(variable))
                            try restricted.values.put(self.allocator, variable, value);
                    }
                    try self.collectAggregateGroups(outer[0..outer_count], &restricted, &groups);
                }
            }
        }

        self.maintained_groups += groups.items.len;
        for (groups.items) |*group| {
            if (view) |projected| {
                try self.maintainProjectedGroup(rule, projected, group, removals, additions);
            } else {
                try self.maintainAggregateGroup(rule, group, removals, additions);
            }
        }
        if (view) |projected|
            try self.sweepVanishedGroups(rule, clause_index, projected, touched, removals);
    }

    /// Maintains one group of a projected view through its derivation
    /// counts: an auxiliary tuple that no longer holds is retracted, and its
    /// head tuple is deleted only on the resulting one-to-zero transition;
    /// a newly derived auxiliary tuple makes its head tuple visible only on
    /// the zero-to-one transition. A group whose aggregate list changed
    /// therefore transfers support from the old head tuple to the new one
    /// within a single batch.
    fn maintainProjectedGroup(
        self: *Jatalog,
        rule: Rule,
        view: *AuxiliaryView,
        group: *const Binding,
        removals: *RelationStore,
        additions: *std.ArrayList(Fact),
    ) !void {
        var derived: RelationStore = .init(self.allocator);
        defer derived.deinit();
        try self.deriveGroupHeads(rule, group, &derived);

        // Auxiliary tuples this group currently contributes.
        var mask: u64 = 0;
        var bound: [64]ValueId = undefined;
        for (view.projected, 0..) |variable, index| {
            bound[index] = group.values.get(variable) orelse return;
            mask |= @as(u64, 1) << @intCast(index);
        }
        var stale: std.ArrayList(Fact) = .empty;
        defer {
            for (stale.items) |fact| self.allocator.free(fact.terms);
            stale.deinit(self.allocator);
        }
        {
            const candidates = try view.tuples.lookup(view.key(), mask, bound[0..view.projected.len]);
            for (candidates) |candidate| {
                const tuple = view.tuples.factAt(candidate);
                if (!std.mem.eql(ValueId, tuple.terms[0..view.projected.len], bound[0..view.projected.len]))
                    continue;
                const head: Fact = .{
                    .predicate = rule.head.predicate,
                    .terms = @constCast(view.headTerms(tuple)),
                };
                // Projected values alone do not identify a group: head
                // variables the group binds must agree as well, or the
                // tuple belongs to a different group sharing these values.
                var owner = try group.clone(self.allocator);
                defer owner.deinit(self.allocator);
                if (!try self.unify(head, rule.head, &owner)) continue;
                if (try derived.contains(head)) continue;
                const terms = try self.allocator.dupe(ValueId, tuple.terms);
                stale.append(self.allocator, .{
                    .predicate = view.rule_id,
                    .terms = terms,
                }) catch |err| {
                    self.allocator.free(terms);
                    return err;
                };
            }
        }
        for (stale.items) |tuple| {
            const head = view.headTerms(tuple);
            const before = try self.derivationCount(view, head);
            if (!try view.tuples.removeFact(tuple)) continue;
            if (before == 1) try self.recordHeadRemoval(rule, head, removals);
        }

        for (0..derived.len()) |index| {
            const head = derived.factAt(index);
            const terms = (try self.auxiliaryTerms(view, group, head)) orelse continue;
            var owned = true;
            defer if (owned) self.allocator.free(terms);
            const tuple: Fact = .{ .predicate = view.rule_id, .terms = terms };
            if (try view.tuples.contains(tuple)) continue;
            const before = try self.derivationCount(view, view.headTerms(tuple));
            owned = false;
            _ = view.tuples.insert(tuple, false) catch |err| {
                self.allocator.free(terms);
                return err;
            };
            if (before == 0 and !try self.closure.?.contains(head)) {
                const copy = try self.allocator.dupe(ValueId, head.terms);
                additions.append(self.allocator, .{
                    .predicate = head.predicate,
                    .terms = copy,
                }) catch |err| {
                    self.allocator.free(copy);
                    return err;
                };
            }
        }
    }

    /// Retracts auxiliary tuples whose group no longer has any solution of
    /// the rule's outer goals, deleting the head tuple on a one-to-zero
    /// derivation-count transition. Only groups a changed outer-goal fact
    /// can reach are examined: a group can vanish only when an outer fact
    /// disappears, so batches that touch just the aggregate's members do no
    /// sweeping at all.
    fn sweepVanishedGroups(
        self: *Jatalog,
        rule: Rule,
        clause_index: usize,
        view: *AuxiliaryView,
        touched: *RelationStore,
        removals: *RelationStore,
    ) !void {
        const outer = try self.allocator.alloc(Clause, rule.body.len - 1);
        defer self.allocator.free(outer);
        const outer_count = fillOuterClauses(rule, clause_index, outer);

        var candidates: RelationStore = .init(self.allocator);
        defer candidates.deinit();
        try self.collectSweepCandidates(rule, view, outer[0..outer_count], touched, &candidates);

        for (0..candidates.len()) |index| {
            const tuple = candidates.factAt(index);
            var seed: Binding = .{};
            defer seed.deinit(self.allocator);
            // The group is identified by its projected values together with
            // the head variables the outer goals bind.
            const stored: Fact = .{
                .predicate = rule.head.predicate,
                .terms = @constCast(view.headTerms(tuple)),
            };
            if (!try self.unify(stored, rule.head, &seed)) continue;
            for (view.projected, 0..) |variable, position|
                try seed.values.put(self.allocator, variable, tuple.terms[position]);
            var solutions: std.ArrayList(Binding) = .empty;
            defer {
                for (solutions.items) |*solution| solution.deinit(self.allocator);
                solutions.deinit(self.allocator);
            }
            self.matchClauses(
                outer[0..outer_count],
                &self.closure.?,
                0,
                &seed,
                &solutions,
                null,
            ) catch |err| switch (err) {
                Error.NumericType, Error.NumericOverflow => continue,
                else => return err,
            };
            if (solutions.items.len > 0) continue;
            const head = view.headTerms(tuple);
            const before = try self.derivationCount(view, head);
            if (!try view.tuples.removeFact(tuple)) continue;
            if (before == 1) try self.recordHeadRemoval(rule, head, removals);
        }
    }

    /// Auxiliary tuples a changed outer-goal fact could have invalidated,
    /// found by binding the fact against each outer goal and looking up the
    /// auxiliary columns that binding determines.
    fn collectSweepCandidates(
        self: *Jatalog,
        rule: Rule,
        view: *AuxiliaryView,
        outer: []const Clause,
        touched: *RelationStore,
        candidates: *RelationStore,
    ) !void {
        for (0..touched.len()) |index| {
            const fact = touched.factAt(index);
            for (outer) |clause| {
                const expression = switch (clause) {
                    .relational => |value| value,
                    else => continue,
                };
                if (expression.predicate != fact.predicate or
                    expression.terms.len != fact.terms.len) continue;
                var binding: Binding = .{};
                defer binding.deinit(self.allocator);
                if (!try self.unify(fact, expression, &binding)) continue;

                var mask: u64 = 0;
                var bound: [64]ValueId = undefined;
                var count: usize = 0;
                for (view.projected, 0..) |variable, position| {
                    const value = binding.values.get(variable) orelse continue;
                    mask |= @as(u64, 1) << @intCast(position);
                    bound[count] = value;
                    count += 1;
                }
                for (rule.head.terms, 0..) |term, position| {
                    const variable = switch (term) {
                        .variable => |name| name,
                        else => continue,
                    };
                    const value = binding.values.get(variable) orelse continue;
                    mask |= @as(u64, 1) << @intCast(view.projected.len + position);
                    bound[count] = value;
                    count += 1;
                }
                for (try view.tuples.lookup(view.key(), mask, bound[0..count])) |candidate| {
                    const tuple = view.tuples.factAt(candidate);
                    if (try candidates.contains(tuple)) continue;
                    try copyFactInto(self.allocator, candidates, tuple);
                }
            }
        }
    }

    fn recordHeadRemoval(
        self: *Jatalog,
        rule: Rule,
        head: []const ValueId,
        removals: *RelationStore,
    ) !void {
        const fact: Fact = .{ .predicate = rule.head.predicate, .terms = @constCast(head) };
        if (!try self.closure.?.contains(fact)) return;
        if (try removals.contains(fact)) return;
        const terms = try self.allocator.dupe(ValueId, head);
        _ = removals.insert(.{ .predicate = rule.head.predicate, .terms = terms }, true) catch |err| {
            self.allocator.free(terms);
            return err;
        };
    }

    fn deriveGroupHeads(
        self: *Jatalog,
        rule: Rule,
        group: *const Binding,
        derived: *RelationStore,
    ) !void {
        var answers: std.ArrayList(Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        self.matchClauses(
            rule.body,
            &self.closure.?,
            0,
            group,
            &answers,
            null,
        ) catch |err| switch (err) {
            Error.NumericType, Error.NumericOverflow => return,
            else => return err,
        };
        for (answers.items) |*answer| {
            const fact = try self.deriveFact(rule.head, answer);
            _ = derived.insert(fact, true) catch |err| {
                self.allocator.free(fact.terms);
                return err;
            };
        }
    }

    fn collectAggregateGroups(
        self: *Jatalog,
        outer: []const Clause,
        seed: *const Binding,
        groups: *std.ArrayList(Binding),
    ) !void {
        var solutions: std.ArrayList(Binding) = .empty;
        defer {
            for (solutions.items) |*solution| solution.deinit(self.allocator);
            solutions.deinit(self.allocator);
        }
        self.matchClauses(
            outer,
            &self.closure.?,
            0,
            seed,
            &solutions,
            null,
        ) catch |err| switch (err) {
            Error.NumericType, Error.NumericOverflow => return,
            else => return err,
        };
        for (solutions.items) |*solution| {
            var duplicate = false;
            for (groups.items) |*existing| {
                if (bindingsEqual(existing, solution)) {
                    duplicate = true;
                    break;
                }
            }
            if (duplicate) continue;
            var copy = try solution.clone(self.allocator);
            groups.append(self.allocator, copy) catch |err| {
                copy.deinit(self.allocator);
                return err;
            };
        }
    }

    /// Recomputes one group: the head tuples currently stored for it become
    /// deletions unless the recomputation still derives them, and newly
    /// derived tuples become insertions.
    fn maintainAggregateGroup(
        self: *Jatalog,
        rule: Rule,
        group: *const Binding,
        removals: *RelationStore,
        additions: *std.ArrayList(Fact),
    ) !void {
        var derived: RelationStore = .init(self.allocator);
        defer derived.deinit();
        try self.deriveGroupHeads(rule, group, &derived);

        // Stale stored tuples for this group: head matches under the group
        // binding but the recomputation no longer derives them.
        for (try self.lookupCandidates(&self.closure.?, rule.head, group)) |candidate| {
            const stored = self.closure.?.factAt(candidate);
            var matched = try group.clone(self.allocator);
            defer matched.deinit(self.allocator);
            if (!try self.unify(stored, rule.head, &matched)) continue;
            if (try derived.contains(stored)) continue;
            if (try removals.contains(stored)) continue;
            const terms = try self.allocator.dupe(ValueId, stored.terms);
            _ = removals.insert(.{ .predicate = stored.predicate, .terms = terms }, true) catch |err| {
                self.allocator.free(terms);
                return err;
            };
        }

        for (0..derived.len()) |index| {
            const fact = derived.factAt(index);
            if (try self.closure.?.contains(fact)) continue;
            const terms = try self.allocator.dupe(ValueId, fact.terms);
            additions.append(self.allocator, .{
                .predicate = fact.predicate,
                .terms = terms,
            }) catch |err| {
                self.allocator.free(terms);
                return err;
            };
        }
    }

    /// Applies a batch of base deletions to the clean closure with
    /// delete-and-rederive, one stratum at a time: over-delete every fact
    /// whose derivation used a deleted fact, joining against a snapshot of
    /// the pre-deletion closure, then reinsert facts that retain an
    /// alternative proof in the reduced closure. Plain reference counts
    /// would be unsound here because cyclic derivations support one another
    /// after their base support disappears. A stratum whose negated or
    /// aggregated dependencies lost facts is invalidated and recomputed
    /// through the dirty-stratum rebuild instead.
    fn propagateDeletions(self: *Jatalog, deleted: *RelationStore) !void {
        var old_closure = try self.closure.?.clone();
        defer old_closure.deinit();
        for (0..deleted.len()) |index| {
            _ = try self.closure.?.removeFact(deleted.factAt(index));
        }
        const analysis = try self.ensureAnalysis();
        var level: usize = 0;
        while (level <= analysis.max_level) : (level += 1) {
            if (try self.deletionBlocked(level, deleted)) {
                self.rebuild_fallbacks += 1;
                self.markDirty(level);
                try self.ensureMaterialized();
                return;
            }
            try self.overdeleteLevel(&old_closure, deleted, &analysis.strata, level);
            try self.rederiveLevel(deleted, &analysis.strata, level);
        }
        self.removed_facts += deleted.len();
    }

    fn deletionBlocked(self: *Jatalog, level: usize, deleted: *const RelationStore) !bool {
        var shrunk: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
        defer shrunk.deinit(self.allocator);
        for (0..deleted.len()) |index| {
            const fact = deleted.factAt(index);
            try shrunk.put(self.allocator, .{
                .name = fact.predicate,
                .arity = fact.terms.len,
            }, {});
        }
        return self.strataBlockedBy(level, &shrunk);
    }

    /// Over-deletes stratum `level`: every fact derivable by one of the
    /// stratum's rules from at least one already-deleted fact is removed
    /// from the closure and queued for rederivation. The remaining body
    /// occurrences join against the pre-deletion snapshot so derivations
    /// that used several deleted facts are still found.
    fn overdeleteLevel(
        self: *Jatalog,
        old_closure: *RelationStore,
        deleted: *RelationStore,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        level: usize,
    ) !void {
        var cursor: usize = 0;
        while (cursor < deleted.len()) : (cursor += 1) {
            const victim = deleted.factAt(cursor);
            for (self.rules.items) |rule| {
                if ((levels.get(predicateKey(rule.head)) orelse 0) != level) continue;
                for (rule.body, 0..) |clause, clause_index| {
                    const expression = switch (clause) {
                        .relational => |value| value,
                        else => continue,
                    };
                    if (expression.predicate != victim.predicate or
                        expression.terms.len != victim.terms.len) continue;
                    try self.overdeleteOccurrence(
                        old_closure,
                        deleted,
                        rule,
                        clause_index,
                        victim,
                    );
                }
            }
        }
    }

    fn overdeleteOccurrence(
        self: *Jatalog,
        old_closure: *RelationStore,
        deleted: *RelationStore,
        rule: Rule,
        clause_index: usize,
        victim: Fact,
    ) !void {
        const expression = rule.body[clause_index].relational;
        var initial: Binding = .{};
        defer initial.deinit(self.allocator);
        if (!try self.unify(victim, expression, &initial)) return;
        const rest = try self.allocator.alloc(Clause, rule.body.len - 1);
        defer self.allocator.free(rest);
        var count: usize = 0;
        for (rule.body, 0..) |clause, index| {
            if (index == clause_index) continue;
            rest[count] = clause;
            count += 1;
        }
        var answers: std.ArrayList(Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        self.matchClauses(rest, old_closure, 0, &initial, &answers, null) catch |err| switch (err) {
            Error.NumericType, Error.NumericOverflow => return,
            else => return err,
        };
        for (answers.items) |*answer| {
            const head_fact = try self.deriveFact(rule.head, answer);
            var keep = false;
            defer if (!keep) self.allocator.free(head_fact.terms);
            if (try self.facts.contains(head_fact)) continue;
            if (try deleted.contains(head_fact)) continue;
            if (!try self.closure.?.contains(head_fact)) continue;
            _ = try self.closure.?.removeFact(head_fact);
            _ = try deleted.insert(head_fact, true);
            keep = true;
        }
    }

    /// Reinserts over-deleted facts of this stratum that retain an
    /// alternative proof in the reduced closure, repeating until no further
    /// fact can be rederived so that chains of rederivations settle.
    fn rederiveLevel(
        self: *Jatalog,
        deleted: *RelationStore,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        level: usize,
    ) !void {
        var progress = true;
        while (progress) {
            progress = false;
            var index: usize = 0;
            while (index < deleted.len()) {
                const candidate = deleted.factAt(index);
                const key: PredicateKey = .{
                    .name = candidate.predicate,
                    .arity = candidate.terms.len,
                };
                if ((levels.get(key) orelse 0) != level or
                    !try self.hasAlternativeDerivation(candidate))
                {
                    index += 1;
                    continue;
                }
                const terms = try self.allocator.dupe(ValueId, candidate.terms);
                _ = self.closure.?.insert(.{
                    .predicate = candidate.predicate,
                    .terms = terms,
                }, true) catch |err| {
                    self.allocator.free(terms);
                    return err;
                };
                deleted.removeAt(index);
                progress = true;
            }
        }
    }

    fn hasAlternativeDerivation(self: *Jatalog, fact: Fact) !bool {
        for (self.rules.items) |rule| {
            if (rule.head.predicate != fact.predicate or
                rule.head.terms.len != fact.terms.len) continue;
            var bindings: Binding = .{};
            defer bindings.deinit(self.allocator);
            if (!try self.unify(fact, rule.head, &bindings)) continue;
            var answers: std.ArrayList(Binding) = .empty;
            defer {
                for (answers.items) |*answer| answer.deinit(self.allocator);
                answers.deinit(self.allocator);
            }
            self.matchClauses(
                rule.body,
                &self.closure.?,
                0,
                &bindings,
                &answers,
                null,
            ) catch |err| switch (err) {
                Error.NumericType, Error.NumericOverflow => continue,
                else => return err,
            };
            if (answers.items.len > 0) return true;
        }
        return false;
    }

    /// Runs semi-naive delta rounds for one stratum during batch
    /// propagation. Unlike `expandLevel` there is no naive round zero: the
    /// initial delta is everything appended since the batch began, and every
    /// relational body occurrence is delta-joined because the batch may have
    /// grown predicates at any lower stratum.
    fn propagateLevel(
        self: *Jatalog,
        facts: *RelationStore,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        level: usize,
        batch_start: usize,
    ) !void {
        const ActiveRule = struct {
            rule: Rule,
            occurrences: []usize,
        };
        var active: std.ArrayList(ActiveRule) = .empty;
        defer {
            for (active.items) |entry| self.allocator.free(entry.occurrences);
            active.deinit(self.allocator);
        }
        for (self.rules.items) |rule| {
            const rule_level = levels.get(predicateKey(rule.head)) orelse 0;
            if (rule_level != level and (rule.seed_argument == null or rule_level > level)) continue;
            var occurrences: std.ArrayList(usize) = .empty;
            errdefer occurrences.deinit(self.allocator);
            if (rule.seed_argument == null) {
                for (rule.body, 0..) |clause, clause_index| {
                    if (clause == .relational)
                        try occurrences.append(self.allocator, clause_index);
                }
            }
            const owned = try occurrences.toOwnedSlice(self.allocator);
            active.append(self.allocator, .{
                .rule = rule,
                .occurrences = owned,
            }) catch |err| {
                self.allocator.free(owned);
                return err;
            };
        }

        var delta_start = batch_start;
        var value_mark = self.values.values.items.len;
        while (true) {
            const delta_end = facts.len();
            const values_grew = self.values.values.items.len != value_mark;
            if (delta_end == delta_start and !values_grew) break;
            value_mark = self.values.values.items.len;
            for (active.items) |entry| {
                if (entry.rule.seed_argument != null) {
                    try self.applyRule(facts, entry.rule, null);
                } else for (entry.occurrences) |occurrence| {
                    try self.applyRule(facts, entry.rule, .{
                        .clause_index = occurrence,
                        .delta_start = delta_start,
                        .delta_end = delta_end,
                    });
                }
            }
            delta_start = delta_end;
        }
    }

    fn compileRelation(
        self: *Jatalog,
        predicate: []const u8,
        descriptors: []const input.Term,
        negated: bool,
    ) !Expr {
        if (predicate.len == 0) return Error.InvalidTerm;
        var builder: InputBuilder = .{ .database = self };
        return .{
            .predicate = try self.strings.intern(predicate),
            .terms = try input_compiler.compileTerms(&builder, descriptors),
            .negated = negated,
        };
    }

    fn compileGoals(self: *Jatalog, descriptors: []const input.Goal) anyerror![]Clause {
        try input_compiler.validateGoals(self.allocator, descriptors);
        return self.compileGoalsValidated(descriptors);
    }

    fn compileGoalsValidated(self: *Jatalog, descriptors: []const input.Goal) anyerror![]Clause {
        const clauses = try self.allocator.alloc(Clause, descriptors.len);
        var initialized: usize = 0;
        errdefer {
            for (clauses[0..initialized]) |clause| freeClauseTree(self.allocator, clause);
            self.allocator.free(clauses);
        }
        for (descriptors, clauses) |descriptor, *clause| {
            clause.* = try self.compileGoalValidated(descriptor);
            initialized += 1;
        }
        return clauses;
    }

    fn compileGoalValidated(self: *Jatalog, descriptor: input.Goal) anyerror!Clause {
        return switch (descriptor) {
            .relation => |relation| .{
                .relational = try self.compileRelation(relation.predicate, relation.terms, false),
            },
            .negation => |relation| .{ .negated = try self.compileRelation(relation.predicate, relation.terms, true) },
            .equality => |binary| .{ .builtin = try self.compileBuiltin(.equality, &.{ binary.left, binary.right }) },
            .inequality => |binary| .{
                .builtin = try self.compileBuiltin(.inequality, &.{ binary.left, binary.right }),
            },
            .comparison => |comparison| .{ .builtin = try self.compileBuiltin(switch (comparison.kind) {
                .less_than => .less_than,
                .less_or_equal => .less_or_equal,
                .greater_than => .greater_than,
                .greater_or_equal => .greater_or_equal,
            }, &.{ comparison.operands.left, comparison.operands.right }) },
            .arithmetic => |arithmetic| .{ .builtin = try self.compileBuiltin(switch (arithmetic.kind) {
                .add => .add,
                .subtract => .subtract,
            }, &.{ arithmetic.output, arithmetic.left, arithmetic.right }) },
            .aggregate => |aggregate| blk: {
                var builder: InputBuilder = .{ .database = self };
                const template = try input_compiler.compileTerm(&builder, aggregate.template);
                errdefer freeTerm(self.allocator, template);
                const output = try input_compiler.compileTerm(&builder, aggregate.output);
                errdefer freeTerm(self.allocator, output);
                const body = try self.compileGoalsValidated(aggregate.body);
                break :blk .{ .aggregate = .{ .template = template, .body = body, .output = output } };
            },
        };
    }

    fn compileBuiltin(self: *Jatalog, kind: GoalKind, terms: []const input.Term) !Expr {
        var result = try self.compileRelation(goalOperator(kind), terms, false);
        result.kind = kind;
        return result;
    }

    fn addFactExpr(self: *Jatalog, value: Expr) !void {
        _ = try self.applyInsertion(value, false);
    }

    /// Inserts one ground base fact. When `propagate` is set the fact also
    /// joins the clean closure for incremental propagation; otherwise the
    /// first dependent stratum is marked dirty for the lazy rebuild path.
    fn applyInsertion(self: *Jatalog, value: Expr, propagate: bool) !bool {
        if (!value.isGround() or value.negated) return Error.InvalidFact;
        const terms = try self.allocator.alloc(ValueId, value.terms.len);
        var terms_owned = true;
        errdefer if (terms_owned) self.allocator.free(terms);
        for (value.terms, terms) |term, *id| id.* = try self.termToValue(term, null);
        const fact: Fact = .{ .predicate = value.predicate, .terms = terms };
        const key: PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
        const added = try self.facts.insert(fact, false);
        terms_owned = false;
        if (!added) return false;
        if (propagate) {
            const copy = try self.allocator.dupe(ValueId, terms);
            _ = self.closure.?.insert(.{ .predicate = fact.predicate, .terms = copy }, false) catch |err| {
                self.allocator.free(copy);
                return err;
            };
        } else {
            try self.markBaseChanged(key);
        }
        return true;
    }

    /// Adds a rule whose body may contain aggregate clauses. On success the
    /// database owns `head` and every clause in `body`; on failure the caller
    /// retains ownership. The body slice itself is only borrowed.
    fn addRuleClauses(self: *Jatalog, head: Expr, body: []const Clause) !void {
        const seed_argument = try self.validateRule(head, body);
        const owned_body = try self.orderClauses(body);
        errdefer self.allocator.free(owned_body);
        const id = self.next_rule_id;
        self.next_rule_id += 1;
        try self.rules.append(self.allocator, .{
            .id = id,
            .head = head,
            .body = owned_body,
            .seed_argument = seed_argument,
        });
        self.validateRecursiveArithmetic() catch |err| {
            _ = self.rules.pop();
            return err;
        };
        self.validateStratification() catch |err| {
            _ = self.rules.pop();
            return err;
        };
        self.invalidateAnalysis();
        if (self.closure != null) {
            // Lazy rebuild policy for rule additions: invalidate from the new
            // head's stratum now, rebuild at the next evaluation.
            const analysis = try self.ensureAnalysis();
            self.markDirty(analysis.strata.get(predicateKey(head)) orelse 0);
        }
    }

    fn classifyExpr(self: *const Jatalog, expression: Expr) Clause {
        if (expression.negated) return .{ .negated = expression };
        if (isBuiltin(self, expression)) return .{ .builtin = expression };
        return .{ .relational = expression };
    }

    /// Evaluates relational, built-in, negated, or aggregate goals. Goals and
    /// their structural terms remain caller-owned and may be freed immediately
    /// after this function returns.
    fn queryClauses(self: *Jatalog, goals: []const Clause) !QueryResult {
        var internal_answers = try self.evaluateClauses(goals);
        defer {
            for (internal_answers.items) |*answer| answer.deinit(self.allocator);
            internal_answers.deinit(self.allocator);
        }
        return self.copyQueryResult(internal_answers.items);
    }

    fn evaluateClauses(self: *Jatalog, goals: []const Clause) !std.ArrayList(Binding) {
        if (goals.len == 0) return Error.InvalidQuery;
        var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (goals) |clause| try collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try self.orderClauses(goals);
        defer self.allocator.free(ordered);
        for (ordered) |clause|
            try self.validateClause(clause, &bound, &outer_variables, Error.InvalidQuery);

        try self.ensureMaterialized();
        const values_before = self.values.values.items.len;
        for (goals) |clause| try self.internGroundStructuresInClause(clause);
        if (self.values.values.items.len != values_before) {
            // Novel ground query structures must join the seed set of
            // admissible structural recursion, so derive their consequences
            // on this database's own (discardable) closure.
            if (self.closure) |*closure| {
                if ((try self.ensureAnalysis()).has_seed_rules)
                    try self.expandFrom(closure, 0);
            }
        }

        var internal_answers: std.ArrayList(Binding) = .empty;
        errdefer {
            for (internal_answers.items) |*answer| answer.deinit(self.allocator);
            internal_answers.deinit(self.allocator);
        }
        var initial: Binding = .{};
        defer initial.deinit(self.allocator);
        try self.matchClauses(ordered, self.closureStore(), 0, &initial, &internal_answers, null);
        return internal_answers;
    }

    fn copyQueryResult(self: *const Jatalog, bindings: []const Binding) !QueryResult {
        var result: QueryResult = .{ .allocator = self.allocator };
        errdefer result.deinit();
        for (bindings) |binding| {
            var answer: Answer = .{ .allocator = self.allocator };
            errdefer answer.deinit();
            for (binding.values.keys(), binding.values.values()) |variable, value| {
                const name = try self.allocator.dupe(u8, self.strings.resolve(variable));
                errdefer self.allocator.free(name);
                const owned_value = try self.copyResultNode(value);
                answer.bindings.append(self.allocator, .{
                    .name = name,
                    .value = .{ .node = owned_value },
                }) catch |err| {
                    freeResultNode(self.allocator, owned_value);
                    return err;
                };
            }
            try result.answers.append(self.allocator, answer);
        }
        return result;
    }

    fn copyResultNode(self: *const Jatalog, value: ValueId) !*ResultNode {
        const node = try self.allocator.create(ResultNode);
        errdefer self.allocator.destroy(node);
        node.* = switch (self.values.get(value)) {
            .scalar => |scalar_id| switch (self.scalars.get(scalar_id)) {
                .atom => |atom| .{ .atom = try self.allocator.dupe(u8, atom) },
                .integer => |integer| .{ .integer = integer },
                .float => |float| .{ .float = float },
            },
            .nil => .nil,
            .cons => |value_pair| blk: {
                const pair = try self.allocator.create(ResultCons);
                errdefer self.allocator.destroy(pair);
                pair.head = try self.copyResultNode(value_pair.head);
                errdefer freeResultNode(self.allocator, pair.head);
                pair.tail = try self.copyResultNode(value_pair.tail);
                break :blk .{ .cons = pair };
            },
        };
        return node;
    }

    /// Records how the maintained views are classified and how much work
    /// incremental maintenance has done. A view whose head retains every
    /// outer variable is self-maintainable in the sense of Chapter 5: its
    /// tuple belongs to exactly one group, so an update decides the tuple
    /// without consulting other derivations. A projected view needs the
    /// auxiliary view's derivation counts, and recomputing an aggregate
    /// member set always consults the closure.
    pub fn maintenanceStats(self: *const Jatalog) MaintenanceStats {
        var self_maintainable: usize = 0;
        var projected: usize = 0;
        var auxiliary_tuples: usize = 0;
        for (self.rules.items) |rule| {
            if (maintainableAggregateIndex(rule) == null) continue;
            var found = false;
            for (self.auxiliary.items) |*view| {
                if (view.rule_id != rule.id) continue;
                found = true;
                auxiliary_tuples += view.tuples.len();
                break;
            }
            if (found) projected += 1 else self_maintainable += 1;
        }
        return .{
            .closure_facts = if (self.closure) |*closure| closure.len() else 0,
            .propagated_facts = self.propagated_facts,
            .removed_facts = self.removed_facts,
            .stratum_expansions = self.expansions,
            .rebuild_fallbacks = self.rebuild_fallbacks,
            .maintained_groups = self.maintained_groups,
            .self_maintainable_views = self_maintainable,
            .projected_views = projected,
            .auxiliary_tuples = auxiliary_tuples,
        };
    }

    pub fn execute(self: *Jatalog, source: []const u8) !ExecutionResult {
        var parser: Parser = .{ .jatalog = self, .source = source };
        return parser.executeAll();
    }

    fn closureStore(self: *Jatalog) *RelationStore {
        if (self.closure) |*closure| return closure;
        return &self.facts;
    }

    fn invalidateAnalysis(self: *Jatalog) void {
        if (self.analysis) |*analysis| analysis.deinit(self.allocator);
        self.analysis = null;
        self.dropAuxiliaryViews();
    }

    fn dropAuxiliaryViews(self: *Jatalog) void {
        for (self.auxiliary.items) |*view| view.deinit(self.allocator);
        self.auxiliary.clearRetainingCapacity();
    }

    fn auxiliaryFor(self: *Jatalog, rule_id: u32) ?*AuxiliaryView {
        for (self.auxiliary.items) |*view| if (view.rule_id == rule_id) return view;
        return null;
    }

    /// Rebuilds every projected aggregate view from the materialized
    /// closure. Views are built into a temporary list and installed only on
    /// success, so a failure leaves the previous views in place.
    fn rebuildAuxiliaryViews(self: *Jatalog) !void {
        var built: std.ArrayList(AuxiliaryView) = .empty;
        errdefer {
            for (built.items) |*view| view.deinit(self.allocator);
            built.deinit(self.allocator);
        }
        for (self.rules.items) |rule| {
            const clause_index = maintainableAggregateIndex(rule) orelse continue;
            var view = (try self.buildAuxiliaryView(rule, clause_index)) orelse continue;
            built.append(self.allocator, view) catch |err| {
                view.deinit(self.allocator);
                return err;
            };
        }
        for (self.auxiliary.items) |*view| view.deinit(self.allocator);
        self.auxiliary.deinit(self.allocator);
        self.auxiliary = built;
    }

    /// Returns the projected variables of a maintained aggregate rule: the
    /// outer-goal variables its head omits. An empty result means the head
    /// retains every outer variable, so each head tuple already belongs to
    /// exactly one group and no auxiliary view is needed.
    fn projectedVariables(self: *Jatalog, rule: Rule, clause_index: usize) ![]Id {
        const outer = try self.allocator.alloc(Clause, rule.body.len - 1);
        defer self.allocator.free(outer);
        const outer_count = fillOuterClauses(rule, clause_index, outer);
        var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (outer[0..outer_count]) |clause|
            try collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);
        var head_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer head_variables.deinit(self.allocator);
        for (rule.head.terms) |term| try collectTermVariables(self.allocator, term, &head_variables);

        var projected: std.ArrayList(Id) = .empty;
        errdefer projected.deinit(self.allocator);
        var iterator = outer_variables.keyIterator();
        while (iterator.next()) |variable| {
            if (!head_variables.contains(variable.*))
                try projected.append(self.allocator, variable.*);
        }
        std.mem.sort(Id, projected.items, {}, std.sort.asc(Id));
        return projected.toOwnedSlice(self.allocator);
    }

    fn buildAuxiliaryView(self: *Jatalog, rule: Rule, clause_index: usize) !?AuxiliaryView {
        const projected = try self.projectedVariables(rule, clause_index);
        var projected_owned = true;
        defer if (projected_owned) self.allocator.free(projected);
        if (projected.len == 0) return null;
        // The lookup mask addresses one bit per auxiliary column.
        if (projected.len + rule.head.terms.len > 64) return null;

        var view: AuxiliaryView = .{
            .rule_id = rule.id,
            .projected = projected,
            .head_arity = rule.head.terms.len,
            .tuples = .init(self.allocator),
        };
        projected_owned = false;
        errdefer view.deinit(self.allocator);

        const outer = try self.allocator.alloc(Clause, rule.body.len - 1);
        defer self.allocator.free(outer);
        const outer_count = fillOuterClauses(rule, clause_index, outer);
        var groups: std.ArrayList(Binding) = .empty;
        defer {
            for (groups.items) |*group| group.deinit(self.allocator);
            groups.deinit(self.allocator);
        }
        var initial: Binding = .{};
        defer initial.deinit(self.allocator);
        self.matchClauses(
            outer[0..outer_count],
            &self.closure.?,
            0,
            &initial,
            &groups,
            null,
        ) catch |err| switch (err) {
            Error.NumericType, Error.NumericOverflow => return view,
            else => return err,
        };
        for (groups.items) |*group| try self.recordGroupTuples(rule, &view, group);
        return view;
    }

    /// Records the auxiliary tuples one group contributes: its projected
    /// values followed by each head tuple the rule derives for it.
    fn recordGroupTuples(
        self: *Jatalog,
        rule: Rule,
        view: *AuxiliaryView,
        group: *const Binding,
    ) !void {
        var answers: std.ArrayList(Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        self.matchClauses(
            rule.body,
            &self.closure.?,
            0,
            group,
            &answers,
            null,
        ) catch |err| switch (err) {
            Error.NumericType, Error.NumericOverflow => return,
            else => return err,
        };
        for (answers.items) |*answer| {
            const head_fact = try self.deriveFact(rule.head, answer);
            defer self.allocator.free(head_fact.terms);
            const terms = (try self.auxiliaryTerms(view, group, head_fact)) orelse continue;
            _ = view.tuples.insert(.{ .predicate = view.rule_id, .terms = terms }, false) catch |err| {
                self.allocator.free(terms);
                return err;
            };
        }
    }

    fn auxiliaryTerms(
        self: *Jatalog,
        view: *const AuxiliaryView,
        group: *const Binding,
        head: Fact,
    ) !?[]ValueId {
        const terms = try self.allocator.alloc(ValueId, view.arity());
        var owned = true;
        defer if (owned) self.allocator.free(terms);
        for (view.projected, 0..) |variable, index| {
            terms[index] = group.values.get(variable) orelse return null;
        }
        @memcpy(terms[view.projected.len..], head.terms);
        owned = false;
        return terms;
    }

    /// Number of auxiliary tuples deriving one projected head tuple. The
    /// count is derived from the auxiliary view itself rather than stored
    /// separately, so it cannot drift, and it is reported as an overflow
    /// rather than wrapped when it exceeds the counter width.
    fn derivationCount(self: *Jatalog, view: *AuxiliaryView, head: []const ValueId) !u32 {
        _ = self;
        var mask: u64 = 0;
        var bound: [64]ValueId = undefined;
        for (head, 0..) |term, index| {
            mask |= @as(u64, 1) << @intCast(view.projected.len + index);
            bound[index] = term;
        }
        const candidates = try view.tuples.lookup(view.key(), mask, bound[0..head.len]);
        var count: usize = 0;
        for (candidates) |candidate| {
            const tuple = view.tuples.factAt(candidate);
            if (std.mem.eql(ValueId, view.headTerms(tuple), head)) count += 1;
        }
        return std.math.cast(u32, count) orelse Error.NumericOverflow;
    }

    fn ensureAnalysis(self: *Jatalog) !*const Analysis {
        if (self.analysis == null) {
            var strata = try self.computeStrata();
            errdefer strata.deinit(self.allocator);
            var max_level: usize = 0;
            for (strata.values()) |level| max_level = @max(max_level, level);
            var first_dependent: std.array_hash_map.Auto(PredicateKey, usize) = .empty;
            errdefer first_dependent.deinit(self.allocator);
            var has_seed_rules = false;
            for (self.rules.items) |rule| {
                if (rule.seed_argument != null) has_seed_rules = true;
                const head_level = strata.get(predicateKey(rule.head)) orelse 0;
                try noteBodyDependencies(self.allocator, rule.body, head_level, &first_dependent);
            }
            self.analysis = .{
                .strata = strata,
                .first_dependent = first_dependent,
                .max_level = max_level,
                .has_seed_rules = has_seed_rules,
            };
        }
        return &self.analysis.?;
    }

    fn markDirty(self: *Jatalog, level: usize) void {
        switch (self.materialization) {
            .uninitialized => {},
            .clean => self.materialization = .{ .dirty_from_stratum = level },
            .dirty_from_stratum => |existing| self.materialization = .{
                .dirty_from_stratum = @min(existing, level),
            },
        }
    }

    /// Marks the first stratum that depends on a changed base predicate as
    /// dirty. A predicate no rule reads dirties the level past the last
    /// stratum, so the rebuild refreshes only the closure's base partition.
    fn markBaseChanged(self: *Jatalog, key: PredicateKey) !void {
        if (self.closure == null) return;
        const analysis = try self.ensureAnalysis();
        self.markDirty(analysis.first_dependent.get(key) orelse analysis.max_level + 1);
    }

    /// Builds or refreshes the persistent closure. Materialization is lazy:
    /// a database whose rule set is empty never allocates derived-state
    /// machinery, and a dirty closure is rebuilt from its first dirty
    /// stratum, reusing the derived facts of every stratum below it. On
    /// failure the previous closure and state remain installed; values
    /// interned by the aborted expansion stay in the value table and are
    /// reclaimed at deinit.
    fn ensureMaterialized(self: *Jatalog) !void {
        if (self.rules.items.len == 0) return;
        const from_level: usize = switch (self.materialization) {
            .clean => return,
            .uninitialized => 0,
            .dirty_from_stratum => |level| level,
        };
        const closure = try self.buildClosure(from_level);
        if (self.closure) |*old| old.deinit();
        self.closure = closure;
        self.materialization = .clean;
        try self.rebuildAuxiliaryViews();
    }

    fn buildClosure(self: *Jatalog, from_level: usize) !RelationStore {
        var closure = try self.facts.clone();
        errdefer closure.deinit();
        if (from_level > 0) {
            const analysis = try self.ensureAnalysis();
            if (self.closure) |*old| {
                for (0..old.len()) |index| {
                    if (!old.isDerived(index)) continue;
                    const fact = old.factAt(index);
                    const key: PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
                    if ((analysis.strata.get(key) orelse 0) >= from_level) continue;
                    const terms = try self.allocator.dupe(ValueId, fact.terms);
                    _ = closure.insert(.{ .predicate = fact.predicate, .terms = terms }, true) catch |err| {
                        self.allocator.free(terms);
                        return err;
                    };
                }
            }
        }
        try self.expandFrom(&closure, from_level);
        return closure;
    }

    fn expand(self: *Jatalog, facts: *RelationStore) !void {
        try self.expandFrom(facts, 0);
    }

    fn expandFrom(self: *Jatalog, facts: *RelationStore, first_level: usize) !void {
        const analysis = try self.ensureAnalysis();
        if (first_level > analysis.max_level) return;
        for (first_level..analysis.max_level + 1) |level|
            try self.expandLevel(facts, &analysis.strata, level);
    }

    /// Reference naive fixpoint kept as the semantic oracle for the
    /// semi-naive engine; differential tests compare both closures.
    fn expandNaive(self: *Jatalog, facts: *RelationStore) !void {
        var levels = try self.computeStrata();
        defer levels.deinit(self.allocator);
        var max_level: usize = 0;
        for (levels.values()) |level| max_level = @max(max_level, level);

        for (0..max_level + 1) |level| {
            while (true) {
                const fact_count_before = facts.len();
                const value_count_before = self.values.values.items.len;
                for (self.rules.items) |rule| {
                    const rule_level = levels.get(predicateKey(rule.head)) orelse 0;
                    if (rule_level != level and (rule.seed_argument == null or rule_level > level)) continue;
                    try self.applyRule(facts, rule, null);
                }
                if (facts.len() == fact_count_before and
                    self.values.values.items.len == value_count_before) break;
            }
        }
    }

    /// Runs one stratum to its fixpoint with semi-naive delta rounds. Round
    /// zero evaluates every active rule against the complete store. Later
    /// rounds re-evaluate a rule once per growing body occurrence with that
    /// occurrence restricted to the previous round's delta, while seeded
    /// structural recursion keeps its naive evaluation because its seed set
    /// is the growing value table rather than a fact relation. A predicate
    /// counts as growing when it belongs to this stratum or is the head of an
    /// active seed rule, since only those relations gain facts mid-stratum.
    fn expandLevel(
        self: *Jatalog,
        facts: *RelationStore,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        level: usize,
    ) !void {
        self.expansions += 1;
        const ActiveRule = struct {
            rule: Rule,
            growing_occurrences: []usize,
        };
        var active: std.ArrayList(ActiveRule) = .empty;
        defer {
            for (active.items) |entry| self.allocator.free(entry.growing_occurrences);
            active.deinit(self.allocator);
        }
        var growing: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
        defer growing.deinit(self.allocator);
        for (self.rules.items) |rule| {
            const rule_level = levels.get(predicateKey(rule.head)) orelse 0;
            if (rule_level != level and (rule.seed_argument == null or rule_level > level)) continue;
            if (rule.seed_argument != null)
                try growing.put(self.allocator, predicateKey(rule.head), {});
        }
        for (self.rules.items) |rule| {
            const rule_level = levels.get(predicateKey(rule.head)) orelse 0;
            if (rule_level != level and (rule.seed_argument == null or rule_level > level)) continue;
            var occurrences: std.ArrayList(usize) = .empty;
            errdefer occurrences.deinit(self.allocator);
            if (rule.seed_argument == null) {
                for (rule.body, 0..) |clause, clause_index| {
                    const expression = switch (clause) {
                        .relational => |value| value,
                        else => continue,
                    };
                    const body_level = levels.get(predicateKey(expression)) orelse 0;
                    if (body_level == level or growing.contains(predicateKey(expression)))
                        try occurrences.append(self.allocator, clause_index);
                }
            }
            const owned = try occurrences.toOwnedSlice(self.allocator);
            active.append(self.allocator, .{
                .rule = rule,
                .growing_occurrences = owned,
            }) catch |err| {
                self.allocator.free(owned);
                return err;
            };
        }

        var delta_start = facts.len();
        var value_mark = self.values.values.items.len;
        for (active.items) |entry| try self.applyRule(facts, entry.rule, null);

        while (true) {
            const delta_end = facts.len();
            const values_grew = self.values.values.items.len != value_mark;
            if (delta_end == delta_start and !values_grew) break;
            value_mark = self.values.values.items.len;
            for (active.items) |entry| {
                if (entry.rule.seed_argument != null) {
                    try self.applyRule(facts, entry.rule, null);
                } else for (entry.growing_occurrences) |occurrence| {
                    try self.applyRule(facts, entry.rule, .{
                        .clause_index = occurrence,
                        .delta_start = delta_start,
                        .delta_end = delta_end,
                    });
                }
            }
            delta_start = delta_end;
        }
    }

    fn applyRule(
        self: *Jatalog,
        facts: *RelationStore,
        rule: Rule,
        constraint: ?DeltaConstraint,
    ) !void {
        var answers: std.ArrayList(Binding) = .empty;
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        if (rule.seed_argument) |argument| {
            const value_count = self.values.values.items.len;
            for (0..value_count) |value| {
                var initial: Binding = .{};
                defer initial.deinit(self.allocator);
                const seeded = try self.unifyValueTerm(
                    @intCast(value),
                    rule.head.terms[argument],
                    &initial,
                );
                if (seeded) {
                    self.matchClauses(
                        rule.body,
                        facts,
                        0,
                        &initial,
                        &answers,
                        null,
                    ) catch |err| switch (err) {
                        Error.NumericType, Error.NumericOverflow => continue,
                        else => return err,
                    };
                }
            }
        } else {
            var initial: Binding = .{};
            defer initial.deinit(self.allocator);
            try self.matchClauses(rule.body, facts, 0, &initial, &answers, constraint);
        }
        for (answers.items) |*answer| {
            const derived = try self.deriveFact(rule.head, answer);
            _ = facts.insert(derived, true) catch |err| {
                self.allocator.free(derived.terms);
                return err;
            };
        }
    }

    fn deriveFact(self: *Jatalog, head: Expr, bindings: *const Binding) !Fact {
        const terms = try self.allocator.alloc(ValueId, head.terms.len);
        errdefer self.allocator.free(terms);
        for (head.terms, terms) |term, *id| id.* = try self.termToValue(term, bindings);
        return .{ .predicate = head.predicate, .terms = terms };
    }

    fn termToValue(self: *Jatalog, term: Term, bindings: ?*const Binding) !ValueId {
        return switch (term) {
            .scalar => |value| try self.values.intern(.{ .scalar = value }),
            .nil => try self.values.intern(.nil),
            .variable => |variable| if (bindings) |bound|
                bound.values.get(variable) orelse Error.UnboundVariable
            else
                Error.UnboundVariable,
            .cons => |pair| try self.values.intern(.{ .cons = .{
                .head = try self.termToValue(pair.head, bindings),
                .tail = try self.termToValue(pair.tail, bindings),
            } }),
        };
    }

    // Structural recursion is seeded from interned values during expansion, so
    // ground structures supplied by a query must join that seed set first.
    fn internGroundStructuresInExpr(self: *Jatalog, expression: Expr) !void {
        for (expression.terms) |term| try self.internGroundStructuresInTerm(term);
    }

    fn internGroundStructuresInClause(self: *Jatalog, clause: Clause) !void {
        switch (clause) {
            .relational, .builtin, .negated => |expression| try self.internGroundStructuresInExpr(expression),
            .aggregate => |aggregate| {
                try self.internGroundStructuresInTerm(aggregate.template);
                for (aggregate.body) |body_clause|
                    try self.internGroundStructuresInClause(body_clause);
                try self.internGroundStructuresInTerm(aggregate.output);
            },
        }
    }

    fn internGroundStructuresInTerm(self: *Jatalog, term: Term) !void {
        switch (term) {
            .nil => _ = try self.termToValue(term, null),
            .cons => |pair| {
                if (term.isGround()) {
                    _ = try self.termToValue(term, null);
                    return;
                }
                try self.internGroundStructuresInTerm(pair.head);
                try self.internGroundStructuresInTerm(pair.tail);
            },
            .scalar, .variable => {},
        }
    }

    fn matchClauses(
        self: *Jatalog,
        clauses: []const Clause,
        facts: *RelationStore,
        index: usize,
        bindings: *const Binding,
        answers: *std.ArrayList(Binding),
        constraint: ?DeltaConstraint,
    ) !void {
        if (index == clauses.len) {
            var answer = try bindings.clone(self.allocator);
            answers.append(self.allocator, answer) catch |err| {
                answer.deinit(self.allocator);
                return err;
            };
            return;
        }
        if (clauses[index] == .aggregate) {
            const aggregate = clauses[index].aggregate;
            var inner_answers: std.ArrayList(Binding) = .empty;
            defer {
                for (inner_answers.items) |*answer| answer.deinit(self.allocator);
                inner_answers.deinit(self.allocator);
            }
            try self.matchClauses(aggregate.body, facts, 0, bindings, &inner_answers, null);

            var values: std.ArrayList(ValueId) = .empty;
            defer values.deinit(self.allocator);
            for (inner_answers.items) |*answer| {
                const value = try self.termToValue(aggregate.template, answer);
                var duplicate = false;
                for (values.items) |existing| {
                    if (existing == value) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) try values.append(self.allocator, value);
            }
            self.sortValues(values.items);

            var list = try self.values.intern(.nil);
            var value_index = values.items.len;
            while (value_index > 0) {
                value_index -= 1;
                list = try self.values.intern(.{ .cons = .{
                    .head = values.items[value_index],
                    .tail = list,
                } });
            }

            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unifyValueTerm(list, aggregate.output, &next))
                try self.matchClauses(clauses, facts, index + 1, &next, answers, constraint);
            return;
        }
        const expression = switch (clauses[index]) {
            .aggregate => unreachable,
            .relational => |value| value,
            .builtin => |value| value,
            .negated => |value| value,
        };
        if (isBuiltin(self, expression)) {
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            const matched = try self.evalBuiltin(expression, &next);
            if (matched != expression.negated)
                try self.matchClauses(clauses, facts, index + 1, &next, answers, constraint);
            return;
        }
        if (expression.negated) {
            for (try self.lookupCandidates(facts, expression, bindings)) |candidate| {
                var next = try bindings.clone(self.allocator);
                defer next.deinit(self.allocator);
                if (try self.unify(facts.factAt(candidate), expression, &next)) return;
            }
            try self.matchClauses(clauses, facts, index + 1, bindings, answers, constraint);
            return;
        }
        for (try self.lookupCandidates(facts, expression, bindings)) |candidate| {
            if (constraint) |delta| {
                if (index == delta.clause_index and
                    (candidate < delta.delta_start or candidate >= delta.delta_end)) continue;
            }
            var next = try bindings.clone(self.allocator);
            defer next.deinit(self.allocator);
            if (try self.unify(facts.factAt(candidate), expression, &next))
                try self.matchClauses(clauses, facts, index + 1, &next, answers, constraint);
        }
    }

    /// Resolves the goal's ground positions under the current bindings and
    /// asks the store for candidate facts, in insertion order, through its
    /// single lookup interface. Candidates are a superset of the matches;
    /// callers unify each candidate exactly.
    fn lookupCandidates(
        self: *Jatalog,
        facts: *RelationStore,
        goal: Expr,
        bindings: *const Binding,
    ) ![]const u32 {
        const key: PredicateKey = .{ .name = goal.predicate, .arity = goal.terms.len };
        var mask: u64 = 0;
        var bound: [64]ValueId = undefined;
        var count: usize = 0;
        for (goal.terms, 0..) |term, position| {
            if (position >= 64) break;
            const resolved = self.termToValue(term, bindings) catch |err| switch (err) {
                Error.UnboundVariable => continue,
                else => return err,
            };
            mask |= @as(u64, 1) << @intCast(position);
            bound[count] = resolved;
            count += 1;
        }
        return facts.lookup(key, mask, bound[0..count]);
    }

    fn unify(self: *Jatalog, fact: Fact, goal: Expr, bindings: *Binding) !bool {
        for (fact.terms, goal.terms) |value, term| {
            if (!try self.unifyValueTerm(value, term, bindings)) return false;
        }
        return true;
    }

    fn unifyValueTerm(self: *Jatalog, value: ValueId, term: Term, bindings: *Binding) !bool {
        return switch (term) {
            .variable => |variable| if (bindings.values.get(variable)) |bound|
                bound == value
            else blk: {
                try bindings.values.put(self.allocator, variable, value);
                break :blk true;
            },
            .scalar => |expected| switch (self.values.get(value)) {
                .scalar => |actual| actual == expected,
                else => false,
            },
            .nil => self.values.get(value) == .nil,
            .cons => |pair| switch (self.values.get(value)) {
                .cons => |actual| try self.unifyValueTerm(actual.head, pair.head, bindings) and
                    try self.unifyValueTerm(actual.tail, pair.tail, bindings),
                else => false,
            },
        };
    }

    fn evalBuiltin(self: *Jatalog, expr_value: Expr, bindings: *Binding) !bool {
        if (expr_value.kind == .add or expr_value.kind == .subtract) {
            if (expr_value.terms.len != 3) return Error.InvalidQuery;
            const left_id = try self.termToValue(expr_value.terms[1], bindings);
            const right_id = try self.termToValue(expr_value.terms[2], bindings);
            const result_scalar = if (expr_value.kind == .add)
                try self.scalars.add(try self.valueScalar(left_id), try self.valueScalar(right_id))
            else
                try self.scalars.subtract(try self.valueScalar(left_id), try self.valueScalar(right_id));
            const value = try self.values.intern(.{ .scalar = result_scalar });
            return self.unifyValueTerm(value, expr_value.terms[0], bindings);
        }
        if (expr_value.terms.len != 2) return Error.InvalidQuery;
        const left = expr_value.terms[0];
        const right = expr_value.terms[1];
        const left_id = self.termToValue(left, bindings) catch |err| switch (err) {
            Error.UnboundVariable => null,
            else => return err,
        };
        const right_id = self.termToValue(right, bindings) catch |err| switch (err) {
            Error.UnboundVariable => null,
            else => return err,
        };

        if (expr_value.kind == .equality) {
            if (left_id == null and right_id == null) return Error.UnboundVariable;
            if (left_id == null) return self.unifyValueTerm(right_id.?, left, bindings);
            if (right_id == null) return self.unifyValueTerm(left_id.?, right, bindings);
            return self.valuesEqual(left_id.?, right_id.?);
        }
        if (left_id == null or right_id == null) return Error.UnboundVariable;
        if (expr_value.kind == .inequality) return !self.valuesEqual(left_id.?, right_id.?);

        const order = try self.scalars.compareNumeric(
            try self.valueScalar(left_id.?),
            try self.valueScalar(right_id.?),
        );
        return switch (expr_value.kind) {
            .less_than => order == .lt,
            .less_or_equal => order != .gt,
            .greater_than => order == .gt,
            .greater_or_equal => order != .lt,
            else => Error.UnknownOperator,
        };
    }

    fn valueScalar(self: *const Jatalog, value: ValueId) !scalar.Id {
        return switch (self.values.get(value)) {
            .scalar => |scalar_id| scalar_id,
            else => Error.NumericType,
        };
    }

    fn valuesEqual(self: *const Jatalog, left: ValueId, right: ValueId) bool {
        const left_value = self.values.get(left);
        const right_value = self.values.get(right);
        return switch (left_value) {
            .scalar => |left_scalar| switch (right_value) {
                .scalar => |right_scalar| left_scalar == right_scalar,
                else => false,
            },
            .nil => right_value == .nil,
            .cons => |left_cons| switch (right_value) {
                .cons => |right_cons| self.valuesEqual(left_cons.head, right_cons.head) and
                    self.valuesEqual(left_cons.tail, right_cons.tail),
                else => false,
            },
        };
    }

    fn validateRule(self: *Jatalog, head: Expr, body: []const Clause) !?usize {
        if (body.len == 0 or head.negated or isBuiltin(self, head)) return Error.InvalidRule;
        const recursive_seed = try admissibleSeedArgument(head, body);
        var outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (head.terms) |term| try collectTermVariables(self.allocator, term, &outer_variables);
        for (body) |clause| try collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);

        const ordered = try self.orderClauses(body);
        defer self.allocator.free(ordered);
        if (recursive_seed) |seed_argument| {
            try self.validateRuleSafety(head, ordered, &outer_variables, seed_argument);
            return seed_argument;
        }
        self.validateRuleSafety(head, ordered, &outer_variables, null) catch |err| switch (err) {
            Error.InvalidRule => {
                const seed_argument = firstStructuralArgument(head) orelse
                    return Error.InvalidRule;
                try self.validateRuleSafety(head, ordered, &outer_variables, seed_argument);
                return seed_argument;
            },
            else => return err,
        };
        return null;
    }

    fn validateRuleSafety(
        self: *Jatalog,
        head: Expr,
        ordered: []const Clause,
        outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
        seed_argument: ?usize,
    ) !void {
        var bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer bound.deinit(self.allocator);
        if (seed_argument) |argument|
            try bindTermVariables(self.allocator, head.terms[argument], &bound);
        for (ordered) |clause| try self.validateClause(clause, &bound, outer_variables, Error.InvalidRule);
        for (head.terms) |term| if (!termVariablesBound(term, &bound)) return Error.InvalidRule;
    }

    fn admissibleSeedArgument(head: Expr, body: []const Clause) !?usize {
        var seed: ?usize = null;
        for (body) |clause| {
            const call = switch (clause) {
                .relational => |expression| expression,
                else => continue,
            };
            if (call.predicate != head.predicate or call.terms.len != head.terms.len) continue;

            var involves_cons = false;
            var call_seed: ?usize = null;
            for (head.terms, call.terms, 0..) |head_term, call_term, index| {
                if (!termContainsCons(head_term) and !termContainsCons(call_term)) continue;
                involves_cons = true;
                if (!termEqual(head_term, call_term) and !isTailDescendant(head_term, call_term))
                    return Error.NotAdmissible;
                if (isTailDescendant(head_term, call_term) and call_seed == null) call_seed = index;
            }
            if (!involves_cons) continue;
            const candidate = call_seed orelse return Error.NotAdmissible;
            if (seed) |existing| {
                if (existing != candidate) return Error.NotAdmissible;
            } else seed = candidate;
        }
        return seed;
    }

    fn firstStructuralArgument(head: Expr) ?usize {
        for (head.terms, 0..) |term, index|
            if (termContainsCons(term)) return index;
        return null;
    }

    fn validateRecursiveArithmetic(self: *Jatalog) !void {
        for (self.rules.items) |rule| {
            if (!self.ruleContainsArithmetic(rule)) continue;
            const head = predicateKey(rule.head);
            for (rule.body) |clause| {
                const expression = switch (clause) {
                    .relational => |value| value,
                    else => continue,
                };
                var visited: std.AutoHashMapUnmanaged(PredicateKey, void) = .empty;
                defer visited.deinit(self.allocator);
                const dependency = predicateKey(expression);
                const structurally_proven = rule.seed_argument != null and std.meta.eql(dependency, head);
                if (!structurally_proven and try self.predicateReaches(dependency, head, &visited))
                    return Error.NotAdmissible;
            }
        }
    }

    fn ruleContainsArithmetic(self: *const Jatalog, rule: Rule) bool {
        for (rule.body) |clause| switch (clause) {
            .builtin => |expression| if (isArithmetic(self, expression)) return true,
            else => {},
        };
        return false;
    }

    fn predicateReaches(
        self: *Jatalog,
        current: PredicateKey,
        target: PredicateKey,
        visited: *std.AutoHashMapUnmanaged(PredicateKey, void),
    ) !bool {
        if (std.meta.eql(current, target)) return true;
        if (visited.contains(current)) return false;
        try visited.put(self.allocator, current, {});
        for (self.rules.items) |rule| {
            if (!std.meta.eql(predicateKey(rule.head), current)) continue;
            for (rule.body) |clause| {
                const expression = switch (clause) {
                    .relational => |value| value,
                    else => continue,
                };
                if (try self.predicateReaches(predicateKey(expression), target, visited)) return true;
            }
        }
        return false;
    }

    fn validateClause(
        self: *Jatalog,
        clause: Clause,
        bound: *std.AutoHashMapUnmanaged(Id, void),
        outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
        safety_error: anyerror,
    ) anyerror!void {
        switch (clause) {
            .relational => |expression| for (expression.terms) |term|
                try bindTermVariables(self.allocator, term, bound),
            .negated => |expression| for (expression.terms) |term|
                if (!termVariablesBound(term, bound)) return safety_error,
            .builtin => |expression| {
                if (isArithmetic(self, expression)) {
                    if (expression.terms.len != 3 or
                        !termVariablesBound(expression.terms[1], bound) or
                        !termVariablesBound(expression.terms[2], bound)) return safety_error;
                    try bindTermVariables(self.allocator, expression.terms[0], bound);
                    return;
                }
                if (expression.terms.len != 2) return safety_error;
                const a_bound = termVariablesBound(expression.terms[0], bound);
                const b_bound = termVariablesBound(expression.terms[1], bound);
                if (expression.kind == .equality and !expression.negated) {
                    if (!a_bound and !b_bound) return safety_error;
                    try bindTermVariables(self.allocator, expression.terms[0], bound);
                    try bindTermVariables(self.allocator, expression.terms[1], bound);
                } else if (!a_bound or !b_bound) return safety_error;
            },
            .aggregate => |aggregate| {
                try self.validateAggregate(aggregate, bound, outer_variables, safety_error);
                try bindTermVariables(self.allocator, aggregate.output, bound);
            },
        }
    }

    fn validateAggregate(
        self: *Jatalog,
        aggregate: Aggregate,
        outer_bound: *const std.AutoHashMapUnmanaged(Id, void),
        outer_variables: *const std.AutoHashMapUnmanaged(Id, void),
        safety_error: anyerror,
    ) anyerror!void {
        if (aggregate.body.len == 0) return safety_error;
        var inner_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer inner_variables.deinit(self.allocator);
        try collectTermVariables(self.allocator, aggregate.template, &inner_variables);
        for (aggregate.body) |clause| try collectClauseAllVariables(self.allocator, clause, &inner_variables);

        var inner_bound: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer inner_bound.deinit(self.allocator);
        var iterator = inner_variables.keyIterator();
        while (iterator.next()) |variable| {
            if (!outer_variables.contains(variable.*)) continue;
            if (!outer_bound.contains(variable.*)) return safety_error;
            try inner_bound.put(self.allocator, variable.*, {});
        }

        var inner_outer_variables: std.AutoHashMapUnmanaged(Id, void) = .empty;
        defer inner_outer_variables.deinit(self.allocator);
        try collectTermVariables(self.allocator, aggregate.template, &inner_outer_variables);
        for (aggregate.body) |clause|
            try collectClauseSurfaceVariables(self.allocator, clause, &inner_outer_variables);

        const ordered = try self.orderClauses(aggregate.body);
        defer self.allocator.free(ordered);
        for (ordered) |clause|
            try self.validateClause(clause, &inner_bound, &inner_outer_variables, safety_error);
        if (!termVariablesBound(aggregate.template, &inner_bound)) return safety_error;
    }

    fn orderClauses(self: *Jatalog, clauses: []const Clause) ![]Clause {
        const result = try self.allocator.alloc(Clause, clauses.len);
        var index: usize = 0;
        for (clauses) |clause| switch (clause) {
            .relational => {
                result[index] = clause;
                index += 1;
            },
            .builtin => |expression| if (!expression.negated and expression.kind == .equality) {
                result[index] = clause;
                index += 1;
            },
            else => {},
        };
        for (clauses) |clause| switch (clause) {
            .builtin => |expression| {
                if (isArithmetic(self, expression)) {
                    result[index] = clause;
                    index += 1;
                }
            },
            else => {},
        };
        for (clauses) |clause| if (clause == .aggregate) {
            result[index] = clause;
            index += 1;
        };
        for (clauses) |clause| switch (clause) {
            .negated => {
                result[index] = clause;
                index += 1;
            },
            .builtin => |expression| if (expression.negated or
                (expression.kind != .equality and !isArithmetic(self, expression)))
            {
                result[index] = clause;
                index += 1;
            },
            else => {},
        };
        return result;
    }

    fn validateStratification(self: *Jatalog) !void {
        var levels = try self.computeStrata();
        levels.deinit(self.allocator);
    }

    fn computeStrata(self: *Jatalog) !std.array_hash_map.Auto(PredicateKey, usize) {
        var levels: std.array_hash_map.Auto(PredicateKey, usize) = .empty;
        errdefer levels.deinit(self.allocator);
        for (self.rules.items) |rule| {
            try levels.put(self.allocator, predicateKey(rule.head), 0);
            for (rule.body) |clause| try self.collectDependencyPredicates(clause, &levels);
        }
        const predicate_count = levels.count();
        for (0..predicate_count + 1) |iteration| {
            var changed = false;
            for (self.rules.items) |rule| {
                var required: usize = 0;
                for (rule.body) |clause|
                    required = @max(required, self.clauseRequiredStratum(clause, &levels, false));
                const head = predicateKey(rule.head);
                const current = levels.get(head) orelse 0;
                if (required > current) {
                    try levels.put(self.allocator, head, required);
                    changed = true;
                }
            }
            if (!changed) return levels;
            if (iteration == predicate_count) return Error.NotStratified;
        }
        return levels;
    }

    fn collectDependencyPredicates(
        self: *Jatalog,
        clause: Clause,
        levels: *std.array_hash_map.Auto(PredicateKey, usize),
    ) !void {
        switch (clause) {
            .relational => |expression| try levels.put(self.allocator, predicateKey(expression), 0),
            .negated => |expression| if (!isBuiltin(self, expression))
                try levels.put(self.allocator, predicateKey(expression), 0),
            .builtin => {},
            .aggregate => |aggregate| for (aggregate.body) |body_clause|
                try self.collectDependencyPredicates(body_clause, levels),
        }
    }

    fn clauseRequiredStratum(
        self: *const Jatalog,
        clause: Clause,
        levels: *const std.array_hash_map.Auto(PredicateKey, usize),
        aggregate_context: bool,
    ) usize {
        return switch (clause) {
            .relational => |expression| (levels.get(predicateKey(expression)) orelse 0) +
                @intFromBool(aggregate_context),
            .negated => |expression| if (isBuiltin(self, expression))
                0
            else
                (levels.get(predicateKey(expression)) orelse 0) + 1,
            .builtin => 0,
            .aggregate => |aggregate| blk: {
                var required: usize = 0;
                for (aggregate.body) |body_clause|
                    required = @max(required, self.clauseRequiredStratum(body_clause, levels, true));
                break :blk required;
            },
        };
    }

    fn deleteClauses(self: *Jatalog, goals: []const Clause) !bool {
        var answers = try self.evaluateClauses(goals);
        defer {
            for (answers.items) |*answer| answer.deinit(self.allocator);
            answers.deinit(self.allocator);
        }
        var to_remove: std.ArrayList(usize) = .empty;
        defer to_remove.deinit(self.allocator);
        var seen: std.AutoHashMapUnmanaged(usize, void) = .empty;
        defer seen.deinit(self.allocator);
        for (answers.items) |*answer| {
            for (goals) |clause| {
                const goal = switch (clause) {
                    .relational => |expression| expression,
                    else => continue,
                };
                for (try self.lookupCandidates(&self.facts, goal, answer)) |candidate| {
                    if (seen.contains(candidate)) continue;
                    var matched = try answer.clone(self.allocator);
                    defer matched.deinit(self.allocator);
                    if (try self.unify(self.facts.factAt(candidate), goal, &matched)) {
                        try seen.put(self.allocator, candidate, {});
                        try to_remove.append(self.allocator, candidate);
                    }
                }
            }
        }
        std.mem.sort(usize, to_remove.items, {}, std.sort.desc(usize));
        for (to_remove.items) |index| {
            const fact = self.facts.factAt(index);
            try self.markBaseChanged(.{ .name = fact.predicate, .arity = fact.terms.len });
            self.facts.removeAt(index);
        }
        return to_remove.items.len > 0;
    }

    fn writeValue(self: *const Jatalog, writer: *std.Io.Writer, value: ValueId) !void {
        switch (self.values.get(value)) {
            .scalar => |scalar_id| try self.scalars.write(writer, scalar_id),
            .nil => try writer.writeAll("[]"),
            .cons => |pair| if (self.isProperList(value)) {
                try writer.writeByte('[');
                var current = value;
                var first = true;
                while (true) {
                    switch (self.values.get(current)) {
                        .cons => |cell| {
                            if (!first) try writer.writeAll(", ");
                            try self.writeValue(writer, cell.head);
                            current = cell.tail;
                            first = false;
                        },
                        .nil => break,
                        else => unreachable,
                    }
                }
                try writer.writeByte(']');
            } else {
                try writer.writeAll("cons(");
                try self.writeValue(writer, pair.head);
                try writer.writeAll(", ");
                try self.writeValue(writer, pair.tail);
                try writer.writeByte(')');
            },
        }
    }

    fn isProperList(self: *const Jatalog, value: ValueId) bool {
        var current = value;
        while (true) switch (self.values.get(current)) {
            .nil => return true,
            .cons => |pair| current = pair.tail,
            else => return false,
        };
    }

    /// Numbers by value, atoms by spelling, nil, then cons cells recursively.
    fn compareValues(self: *const Jatalog, left: ValueId, right: ValueId) std.math.Order {
        const a = self.values.get(left);
        const b = self.values.get(right);
        const a_rank: u2 = switch (a) {
            .scalar => 0,
            .nil => 1,
            .cons => 2,
        };
        const b_rank: u2 = switch (b) {
            .scalar => 0,
            .nil => 1,
            .cons => 2,
        };
        if (a_rank != b_rank) return std.math.order(a_rank, b_rank);
        return switch (a) {
            .scalar => |a_scalar| switch (b) {
                .scalar => |b_scalar| self.scalars.compare(a_scalar, b_scalar),
                else => unreachable,
            },
            .nil => .eq,
            .cons => |a_pair| switch (b) {
                .cons => |b_pair| blk: {
                    const head_order = self.compareValues(a_pair.head, b_pair.head);
                    break :blk if (head_order != .eq) head_order else self.compareValues(a_pair.tail, b_pair.tail);
                },
                else => unreachable,
            },
        };
    }

    fn sortValues(self: *const Jatalog, values: []ValueId) void {
        if (values.len < 2) return;
        for (values[1..], 1..) |value, index| {
            var insertion = index;
            while (insertion > 0 and self.compareValues(value, values[insertion - 1]) == .lt) {
                values[insertion] = values[insertion - 1];
                insertion -= 1;
            }
            values[insertion] = value;
        }
    }
};

fn freeExpr(allocator: std.mem.Allocator, value: Expr) void {
    for (value.terms) |term| freeTerm(allocator, term);
    allocator.free(value.terms);
}

fn freeRule(allocator: std.mem.Allocator, rule: Rule) void {
    freeExpr(allocator, rule.head);
    for (rule.body) |clause| freeClauseTree(allocator, clause);
    allocator.free(rule.body);
}

fn cloneTerm(allocator: std.mem.Allocator, term: Term) !Term {
    return switch (term) {
        .cons => |pair| blk: {
            const copy = try allocator.create(Term.Cons);
            errdefer allocator.destroy(copy);
            copy.head = try cloneTerm(allocator, pair.head);
            errdefer freeTerm(allocator, copy.head);
            copy.tail = try cloneTerm(allocator, pair.tail);
            break :blk .{ .cons = copy };
        },
        else => term,
    };
}

fn cloneExpr(allocator: std.mem.Allocator, expression: Expr) !Expr {
    const terms = try allocator.alloc(Term, expression.terms.len);
    var initialized: usize = 0;
    errdefer {
        for (terms[0..initialized]) |term| freeTerm(allocator, term);
        allocator.free(terms);
    }
    for (expression.terms, terms) |term, *copy| {
        copy.* = try cloneTerm(allocator, term);
        initialized += 1;
    }
    return .{
        .predicate = expression.predicate,
        .terms = terms,
        .negated = expression.negated,
        .kind = expression.kind,
    };
}

fn cloneClause(allocator: std.mem.Allocator, clause: Clause) !Clause {
    return switch (clause) {
        .relational => |expression| .{ .relational = try cloneExpr(allocator, expression) },
        .builtin => |expression| .{ .builtin = try cloneExpr(allocator, expression) },
        .negated => |expression| .{ .negated = try cloneExpr(allocator, expression) },
        .aggregate => |aggregate| blk: {
            const template = try cloneTerm(allocator, aggregate.template);
            errdefer freeTerm(allocator, template);
            const output = try cloneTerm(allocator, aggregate.output);
            errdefer freeTerm(allocator, output);
            const body = try allocator.alloc(Clause, aggregate.body.len);
            var initialized: usize = 0;
            errdefer {
                for (body[0..initialized]) |body_clause| freeClauseTree(allocator, body_clause);
                allocator.free(body);
            }
            for (aggregate.body, body) |body_clause, *copy| {
                copy.* = try cloneClause(allocator, body_clause);
                initialized += 1;
            }
            break :blk .{ .aggregate = .{ .template = template, .body = body, .output = output } };
        },
    };
}

fn cloneRule(allocator: std.mem.Allocator, rule: Rule) !Rule {
    const head = try cloneExpr(allocator, rule.head);
    errdefer freeExpr(allocator, head);
    const body = try allocator.alloc(Clause, rule.body.len);
    var initialized: usize = 0;
    errdefer {
        for (body[0..initialized]) |clause| freeClauseTree(allocator, clause);
        allocator.free(body);
    }
    for (rule.body, body) |clause, *copy| {
        copy.* = try cloneClause(allocator, clause);
        initialized += 1;
    }
    return .{ .id = rule.id, .head = head, .body = body, .seed_argument = rule.seed_argument };
}

fn freeClauseTree(allocator: std.mem.Allocator, clause: Clause) void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| freeExpr(allocator, expression),
        .aggregate => |aggregate| {
            freeTerm(allocator, aggregate.template);
            for (aggregate.body) |body_clause| freeClauseTree(allocator, body_clause);
            allocator.free(aggregate.body);
            freeTerm(allocator, aggregate.output);
        },
    }
}

fn freeTerm(allocator: std.mem.Allocator, term: Term) void {
    switch (term) {
        .cons => |pair| {
            freeTerm(allocator, pair.head);
            freeTerm(allocator, pair.tail);
            allocator.destroy(pair);
        },
        else => {},
    }
}

fn termVariablesBound(term: Term, bound: *const std.AutoHashMapUnmanaged(Id, void)) bool {
    return switch (term) {
        .variable => |variable| bound.contains(variable),
        .cons => |pair| termVariablesBound(pair.head, bound) and termVariablesBound(pair.tail, bound),
        else => true,
    };
}

fn bindTermVariables(
    allocator: std.mem.Allocator,
    term: Term,
    bound: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (term) {
        .variable => |variable| try bound.put(allocator, variable, {}),
        .cons => |pair| {
            try bindTermVariables(allocator, pair.head, bound);
            try bindTermVariables(allocator, pair.tail, bound);
        },
        else => {},
    }
}

fn collectTermVariables(
    allocator: std.mem.Allocator,
    term: Term,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    try bindTermVariables(allocator, term, variables);
}

fn collectExprVariables(
    allocator: std.mem.Allocator,
    expression: Expr,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    for (expression.terms) |term| try collectTermVariables(allocator, term, variables);
}

fn collectClauseSurfaceVariables(
    allocator: std.mem.Allocator,
    clause: Clause,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| try collectExprVariables(allocator, expression, variables),
        .aggregate => |aggregate| try collectTermVariables(allocator, aggregate.output, variables),
    }
}

fn collectClauseAllVariables(
    allocator: std.mem.Allocator,
    clause: Clause,
    variables: *std.AutoHashMapUnmanaged(Id, void),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| try collectExprVariables(allocator, expression, variables),
        .aggregate => |aggregate| {
            try collectTermVariables(allocator, aggregate.template, variables);
            try collectTermVariables(allocator, aggregate.output, variables);
            for (aggregate.body) |body_clause|
                try collectClauseAllVariables(allocator, body_clause, variables);
        },
    }
}

fn isVariable(string: []const u8) bool {
    return string.len != 0 and std.ascii.isUpper(string[0]);
}

fn goalKind(operator: []const u8) ?GoalKind {
    if (std.mem.eql(u8, operator, "=")) return .equality;
    if (std.mem.eql(u8, operator, "!=") or std.mem.eql(u8, operator, "<>")) return .inequality;
    if (std.mem.eql(u8, operator, "<")) return .less_than;
    if (std.mem.eql(u8, operator, "<=")) return .less_or_equal;
    if (std.mem.eql(u8, operator, ">")) return .greater_than;
    if (std.mem.eql(u8, operator, ">=")) return .greater_or_equal;
    if (std.mem.eql(u8, operator, "+")) return .add;
    if (std.mem.eql(u8, operator, "-")) return .subtract;
    return null;
}

fn goalOperator(kind: GoalKind) []const u8 {
    return switch (kind) {
        .relation => unreachable,
        .equality => "=",
        .inequality => "<>",
        .less_than => "<",
        .less_or_equal => "<=",
        .greater_than => ">",
        .greater_or_equal => ">=",
        .add => "+",
        .subtract => "-",
    };
}

fn isBuiltin(_: *const Jatalog, value: Expr) bool {
    return value.kind != .relation;
}

fn isArithmetic(_: *const Jatalog, value: Expr) bool {
    return value.kind == .add or value.kind == .subtract;
}

fn termContainsCons(term: Term) bool {
    return switch (term) {
        .cons => true,
        else => false,
    };
}

fn termEqual(left: Term, right: Term) bool {
    return switch (left) {
        .scalar => |value| switch (right) {
            .scalar => |other| value == other,
            else => false,
        },
        .variable => |value| switch (right) {
            .variable => |other| value == other,
            else => false,
        },
        .nil => right == .nil,
        .cons => |pair| switch (right) {
            .cons => |other| termEqual(pair.head, other.head) and termEqual(pair.tail, other.tail),
            else => false,
        },
    };
}

fn isTailDescendant(ancestor: Term, candidate: Term) bool {
    var current = ancestor;
    while (current == .cons) {
        current = current.cons.tail;
        if (termEqual(current, candidate)) return true;
    }
    return false;
}

const Parser = struct {
    jatalog: *Jatalog,
    source: []const u8,
    index: usize = 0,

    fn executeAll(self: *Parser) !ExecutionResult {
        var last: ?ExecutionResult = null;
        errdefer if (last) |*result| result.deinit();
        while (true) {
            self.skipSpace();
            if (self.index == self.source.len) return last orelse .none;
            if (last) |*result| result.deinit();
            last = null;
            // Materialize the committed database before cloning statement
            // staging for evaluations, so the staged copy shares the
            // closure's value identifiers and evaluation never expands.
            switch (self.peekStatementKind()) {
                .query, .retraction => try self.jatalog.ensureMaterialized(),
                .assertion, .end => {},
            }
            var staging = try self.jatalog.clone();
            defer staging.deinit();
            var statement_parser = self.*;
            statement_parser.jatalog = &staging;
            const statement_result = try statement_parser.executeStatement();
            self.index = statement_parser.index;
            switch (statement_result) {
                .query => {},
                .none => self.jatalog.commit(&staging),
                .changed => |changed| if (changed) try self.jatalog.commitRetraction(&staging),
            }
            last = statement_result;
        }
    }

    const StatementKind = enum { assertion, query, retraction, end };

    /// Classifies the next statement by scanning for its terminator without
    /// interning anything, mirroring the tokenizer's comment, quote, and
    /// digit-dot-digit rules.
    fn peekStatementKind(self: *const Parser) StatementKind {
        var index = self.index;
        while (index < self.source.len) : (index += 1) {
            const byte = self.source[index];
            if (byte == '%' or (byte == '/' and index + 1 < self.source.len and
                self.source[index + 1] == '/'))
            {
                while (index < self.source.len and self.source[index] != '\n') index += 1;
                continue;
            }
            if (byte == '/' and index + 1 < self.source.len and self.source[index + 1] == '*') {
                const end = std.mem.indexOfPos(u8, self.source, index + 2, "*/") orelse
                    return .end;
                index = end + 1;
                continue;
            }
            if (byte == '\'' or byte == '"') {
                index += 1;
                while (index < self.source.len and self.source[index] != byte) {
                    if (self.source[index] == '\\') index += 1;
                    index += 1;
                }
                if (index == self.source.len) return .end;
                continue;
            }
            if (byte == '?') return .query;
            if (byte == '~') return .retraction;
            if (byte == '.') {
                const digit_before = index > self.index and
                    std.ascii.isDigit(self.source[index - 1]);
                const digit_after = index + 1 < self.source.len and
                    std.ascii.isDigit(self.source[index + 1]);
                if (!(digit_before and digit_after)) return .assertion;
            }
        }
        return .end;
    }

    fn executeStatement(self: *Parser) !ExecutionResult {
        const first = try self.parseClause();
        var first_owned = true;
        errdefer if (first_owned) freeClauseTree(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.consume(":-")) {
            const head = switch (first) {
                .relational => |expression| expression,
                else => return Error.InvalidRule,
            };
            var body: std.ArrayList(Clause) = .empty;
            defer body.deinit(self.jatalog.allocator);
            errdefer for (body.items) |clause| freeClauseTree(self.jatalog.allocator, clause);
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    freeClauseTree(self.jatalog.allocator, clause);
                    return err;
                };
                self.skipSpace();
                if (!self.consume(",")) break;
            }
            try self.expect(".");
            try self.jatalog.addRuleClauses(head, body.items);
            first_owned = false;
            return .none;
        }
        self.skipSpace();
        if (self.consume(".")) {
            const fact = switch (first) {
                .relational => |expression| expression,
                else => return Error.InvalidFact,
            };
            try self.jatalog.addFactExpr(fact);
            freeClauseTree(self.jatalog.allocator, first);
            first_owned = false;
            return .none;
        }

        var goals: std.ArrayList(Clause) = .empty;
        defer {
            for (goals.items) |clause| freeClauseTree(self.jatalog.allocator, clause);
            goals.deinit(self.jatalog.allocator);
        }
        try goals.append(self.jatalog.allocator, first);
        first_owned = false;
        while (self.consume(",")) {
            const goal = try self.parseClause();
            goals.append(self.jatalog.allocator, goal) catch |err| {
                freeClauseTree(self.jatalog.allocator, goal);
                return err;
            };
        }
        if (self.consume("?")) return .{ .query = try self.jatalog.queryClauses(goals.items) };
        if (self.consume("~")) return .{ .changed = try self.jatalog.deleteClauses(goals.items) };
        return Error.InvalidSyntax;
    }

    fn parseClause(self: *Parser) anyerror!Clause {
        self.skipSpace();
        if (self.peekKeyword("setof")) return .{ .aggregate = try self.parseAggregate() };
        const expression = try self.parseExpr();
        return self.jatalog.classifyExpr(expression);
    }

    fn parseAggregate(self: *Parser) anyerror!Aggregate {
        const keyword = try self.parseBare();
        if (!std.mem.eql(u8, keyword, "setof")) return Error.InvalidSyntax;
        try self.expect("(");
        const template = try self.parseTerm();
        var template_owned = true;
        errdefer if (template_owned) freeTerm(self.jatalog.allocator, template);
        try self.expect(",");

        var body: std.ArrayList(Clause) = .empty;
        errdefer {
            for (body.items) |clause| freeClauseTree(self.jatalog.allocator, clause);
            body.deinit(self.jatalog.allocator);
        }
        if (self.consume("(")) {
            while (true) {
                const clause = try self.parseClause();
                body.append(self.jatalog.allocator, clause) catch |err| {
                    freeClauseTree(self.jatalog.allocator, clause);
                    return err;
                };
                if (self.consume(")")) break;
                try self.expect(",");
            }
        } else {
            const clause = try self.parseClause();
            body.append(self.jatalog.allocator, clause) catch |err| {
                freeClauseTree(self.jatalog.allocator, clause);
                return err;
            };
        }
        try self.expect(",");
        const output = try self.parseTerm();
        errdefer freeTerm(self.jatalog.allocator, output);
        try self.expect(")");
        const owned_body = try body.toOwnedSlice(self.jatalog.allocator);
        template_owned = false;
        return .{
            .template = template,
            .body = owned_body,
            .output = output,
        };
    }

    fn parseExpr(self: *Parser) !Expr {
        self.skipSpace();
        var negated = false;
        if (self.peekKeyword("not")) {
            _ = try self.parseBare();
            negated = true;
        }
        const first = try self.parseTerm();
        var first_owned = true;
        errdefer if (first_owned) freeTerm(self.jatalog.allocator, first);
        self.skipSpace();
        if (self.parseOperator()) |operator| {
            const second = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, second);
            if (std.mem.eql(u8, operator, "=")) {
                const arithmetic: ?GoalKind = if (self.consume("+"))
                    .add
                else if (self.consume("-"))
                    .subtract
                else
                    null;
                if (arithmetic) |arithmetic_kind| {
                    if (negated) return Error.InvalidSyntax;
                    const third = try self.parseTerm();
                    errdefer freeTerm(self.jatalog.allocator, third);
                    const predicate = try self.jatalog.strings.intern(goalOperator(arithmetic_kind));
                    const terms = try self.jatalog.allocator.alloc(Term, 3);
                    terms[0] = first;
                    terms[1] = second;
                    terms[2] = third;
                    first_owned = false;
                    return .{ .predicate = predicate, .terms = terms, .kind = arithmetic_kind };
                }
            }
            const kind = goalKind(operator) orelse return Error.UnknownOperator;
            const predicate = try self.jatalog.strings.intern(goalOperator(kind));
            const terms = try self.jatalog.allocator.alloc(Term, 2);
            terms[0] = first;
            terms[1] = second;
            first_owned = false;
            return .{
                .predicate = predicate,
                .terms = terms,
                .negated = negated,
                .kind = kind,
            };
        }
        if (!self.consume("(")) return Error.InvalidSyntax;
        const predicate = switch (first) {
            .scalar => |scalar_id| switch (self.jatalog.scalars.get(scalar_id)) {
                .atom => |atom| try self.jatalog.strings.intern(atom),
                .integer, .float => return Error.InvalidSyntax,
            },
            else => return Error.InvalidSyntax,
        };
        first_owned = false;
        var terms: std.ArrayList(Term) = .empty;
        errdefer {
            for (terms.items) |term| freeTerm(self.jatalog.allocator, term);
            terms.deinit(self.jatalog.allocator);
        }
        self.skipSpace();
        if (!self.consume(")")) {
            while (true) {
                const term = try self.parseTerm();
                terms.append(self.jatalog.allocator, term) catch |err| {
                    freeTerm(self.jatalog.allocator, term);
                    return err;
                };
                self.skipSpace();
                if (self.consume(")")) break;
                try self.expect(",");
            }
        }
        return .{ .predicate = predicate, .terms = try terms.toOwnedSlice(self.jatalog.allocator), .negated = negated };
    }

    fn parseTerm(self: *Parser) anyerror!Term {
        var head = try self.parseTermPrimary();
        errdefer freeTerm(self.jatalog.allocator, head);
        if (self.consumeConsBang()) {
            const tail = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, tail);
            head = try self.makeCons(head, tail);
        }
        return head;
    }

    fn parseTermPrimary(self: *Parser) anyerror!Term {
        self.skipSpace();
        if (self.index == self.source.len) return Error.InvalidSyntax;
        if (self.consume("[")) return self.parseListTail();
        if (self.source[self.index] == '"' or self.source[self.index] == '\'') {
            const quote = self.source[self.index];
            self.index += 1;
            var string: std.ArrayList(u8) = .empty;
            defer string.deinit(self.jatalog.allocator);
            while (self.index < self.source.len and self.source[self.index] != quote) {
                if (self.source[self.index] == '\\' and self.index + 1 < self.source.len) self.index += 1;
                try string.append(self.jatalog.allocator, self.source[self.index]);
                self.index += 1;
            }
            if (self.index == self.source.len) return Error.InvalidSyntax;
            self.index += 1;
            return .{ .scalar = try self.jatalog.scalars.internAtom(string.items) };
        }
        const value = try self.parseBare();
        if (std.mem.eql(u8, value, "cons") and self.consume("(")) {
            const head = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, head);
            try self.expect(",");
            const tail = try self.parseTerm();
            errdefer freeTerm(self.jatalog.allocator, tail);
            try self.expect(")");
            return self.makeCons(head, tail);
        }
        if (isVariable(value)) return .{ .variable = try self.jatalog.strings.intern(value) };
        return .{ .scalar = try self.jatalog.scalars.parseBare(value) };
    }

    fn parseListTail(self: *Parser) anyerror!Term {
        if (self.consume("]")) return .nil;
        const head = try self.parseTerm();
        errdefer freeTerm(self.jatalog.allocator, head);
        var tail: Term = undefined;
        if (self.consume("]")) {
            tail = .nil;
        } else if (self.consume(",")) {
            tail = try self.parseListTail();
        } else if (self.consumeConsBang()) {
            tail = try self.parseImproperListTail();
        } else return Error.InvalidSyntax;
        errdefer freeTerm(self.jatalog.allocator, tail);
        return self.makeCons(head, tail);
    }

    fn parseImproperListTail(self: *Parser) anyerror!Term {
        const tail = try self.parseTerm();
        errdefer freeTerm(self.jatalog.allocator, tail);
        try self.expect("]");
        return tail;
    }

    fn makeCons(self: *Parser, head: Term, tail: Term) !Term {
        const pair = try self.jatalog.allocator.create(Term.Cons);
        pair.* = .{ .head = head, .tail = tail };
        return .{ .cons = pair };
    }

    fn parseBare(self: *Parser) ![]const u8 {
        self.skipSpace();
        const start = self.index;
        while (self.index < self.source.len) : (self.index += 1) {
            const c = self.source[self.index];
            if (std.ascii.isAlphanumeric(c) or c == '_') continue;
            if (c == '.' and self.index > start and self.index + 1 < self.source.len and
                std.ascii.isDigit(self.source[self.index - 1]) and
                std.ascii.isDigit(self.source[self.index + 1])) continue;
            if ((c == '+' or c == '-') and (self.index == start or
                (self.index > start and (self.source[self.index - 1] == 'e' or
                    self.source[self.index - 1] == 'E')))) continue;
            break;
        }
        if (self.index == start) return Error.InvalidSyntax;
        return self.source[start..self.index];
    }

    fn parseOperator(self: *Parser) ?[]const u8 {
        self.skipSpace();
        const operators = [_][]const u8{ "!=", "<>", "<=", ">=", "=", "<", ">" };
        for (operators) |operator| if (self.consume(operator)) return operator;
        return null;
    }

    fn skipSpace(self: *Parser) void {
        while (self.index < self.source.len) {
            if (std.ascii.isWhitespace(self.source[self.index])) {
                self.index += 1;
            } else if (self.source[self.index] == '%') {
                while (self.index < self.source.len and self.source[self.index] != '\n') self.index += 1;
            } else if (std.mem.startsWith(u8, self.source[self.index..], "//")) {
                while (self.index < self.source.len and self.source[self.index] != '\n') self.index += 1;
            } else if (std.mem.startsWith(u8, self.source[self.index..], "/*")) {
                const end = std.mem.indexOfPos(u8, self.source, self.index + 2, "*/") orelse {
                    self.index = self.source.len;
                    return;
                };
                self.index = end + 2;
            } else return;
        }
    }

    fn consume(self: *Parser, token: []const u8) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], token)) return false;
        self.index += token.len;
        return true;
    }

    fn consumeConsBang(self: *Parser) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], "!") or
            std.mem.startsWith(u8, self.source[self.index..], "!=")) return false;
        self.index += 1;
        return true;
    }

    fn expect(self: *Parser, token: []const u8) !void {
        if (!self.consume(token)) return Error.InvalidSyntax;
    }

    fn peekKeyword(self: *Parser, keyword: []const u8) bool {
        self.skipSpace();
        if (!std.mem.startsWith(u8, self.source[self.index..], keyword)) return false;
        const end = self.index + keyword.len;
        return end == self.source.len or !(std.ascii.isAlphanumeric(self.source[end]) or self.source[end] == '_');
    }
};

test "string table maps strings to stable ids and back" {
    var table: StringTable = .init(std.testing.allocator);
    defer table.deinit();
    const alice = try table.intern("alice");
    try std.testing.expectEqual(alice, try table.intern("alice"));
    try std.testing.expectEqualStrings("alice", table.resolve(alice));
}

test "recursive query and numeric builtins" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\parent(alice, bob). parent(bob, carol).
        \\ancestor(X, Y) :- parent(X, Y).
        \\ancestor(X, Y) :- ancestor(X, Z), parent(Z, Y).
        \\ancestor(X, carol), X != carol?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
}

test "stratified negation and retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). employed(alice).
        \\idle(X) :- person(X), not employed(X).
        \\idle(X)?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();
    result = try db.execute("person(bob)~");
    defer result.deinit();
    try std.testing.expect(result.changed);
}

test "negative recursion is rejected" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NotStratified, db.execute(
        \\p(X) :- q(X).
        \\q(X) :- not p(X), seed(X).
    ));
}

test "a parse error after a query releases the previous result" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidSyntax, db.execute(
        \\p(a). p(X)?
        \\bad(X) :- q(X), X <>.
    ));
}

test {
    _ = relation_store;
}

/// Compares the semi-naive closure against the naive reference closure on a
/// staging clone, so the database under test is left untouched.
fn expectSemiNaiveMatchesNaive(db: *Jatalog) !void {
    var staging = try db.clone();
    defer staging.deinit();
    var semi = try staging.facts.clone();
    defer semi.deinit();
    try staging.expand(&semi);
    var naive = try staging.facts.clone();
    defer naive.deinit();
    try staging.expandNaive(&naive);
    try std.testing.expectEqual(naive.len(), semi.len());
    for (0..naive.len()) |index|
        try std.testing.expect(try semi.contains(naive.factAt(index)));
}

test "semi-naive and naive closures agree across rule classes" {
    // Non-recursive joins.
    var joins: Jatalog = .init(std.testing.allocator);
    defer joins.deinit();
    var joins_setup = try joins.execute(
        \\parent(a, b). parent(b, c). parent(c, d).
        \\grand(X, Z) :- parent(X, Y), parent(Y, Z).
    );
    joins_setup.deinit();
    try expectSemiNaiveMatchesNaive(&joins);

    // Direct recursion.
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    var direct_setup = try direct.execute(
        \\edge(a, b). edge(b, c). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    direct_setup.deinit();
    try expectSemiNaiveMatchesNaive(&direct);

    // Mutual recursion across two predicates in one stratum.
    var mutual: Jatalog = .init(std.testing.allocator);
    defer mutual.deinit();
    var mutual_setup = try mutual.execute(
        \\start(n0). step(n0, n1). step(n1, n2). step(n2, n3). step(n3, n4).
        \\even(X) :- start(X).
        \\even(X) :- odd(Y), step(Y, X).
        \\odd(X) :- even(Y), step(Y, X).
    );
    mutual_setup.deinit();
    try expectSemiNaiveMatchesNaive(&mutual);

    // Seeded structural recursion feeding a same-stratum consumer.
    var structural: Jatalog = .init(std.testing.allocator);
    defer structural.deinit();
    var structural_setup = try structural.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    structural_setup.deinit();
    try expectSemiNaiveMatchesNaive(&structural);

    // Stratified negation above a recursive stratum.
    var negated: Jatalog = .init(std.testing.allocator);
    defer negated.deinit();
    var negated_setup = try negated.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\reachable(X) :- edge(a, X).
        \\reachable(X) :- reachable(Y), edge(Y, X).
        \\isolated(X) :- node(X), not reachable(X).
    );
    negated_setup.deinit();
    try expectSemiNaiveMatchesNaive(&negated);

    // Aggregation over a recursive relation.
    var aggregated: Jatalog = .init(std.testing.allocator);
    defer aggregated.deinit();
    var aggregated_setup = try aggregated.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    );
    aggregated_setup.deinit();
    try expectSemiNaiveMatchesNaive(&aggregated);
}

test "multiple recursive body occurrences miss no derivations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(n1, n2). edge(n2, n3). edge(n3, n4). edge(n4, n5).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- path(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectSemiNaiveMatchesNaive(&db);

    // The doubling rule needs delta joins on both occurrences: n1 to n5
    // only exists by combining two derived paths.
    try expectAnswerCount(&db, "path(n1, n5)?", 1);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
}

test "repeated queries reuse the persistent closure without expansion" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try std.testing.expectEqual(@as(usize, 0), db.expansions);

    try expectAnswerCount(&db, "path(a, X)?", 3);
    const after_first = db.expansions;
    try std.testing.expect(after_first > 0);
    try std.testing.expect(db.materialization == .clean);

    for (0..3) |_| try expectAnswerCount(&db, "path(a, X)?", 3);
    var typed = try db.query(&.{input.relation("path", &.{
        input.atom("a"),
        input.variable("target"),
    })});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 3), typed.answers.items.len);
    try std.testing.expectEqual(after_first, db.expansions);
}

test "persistent closure equals a fresh naive rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\blocked(c).
        \\open(X) :- path(a, X), not blocked(X).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    setup.deinit();
    try expectAnswerCount(&db, "numchildren(alice, 1)?", 1);
    try std.testing.expect(db.materialization == .clean);

    var staging = try db.clone();
    defer staging.deinit();
    var reference = try staging.facts.clone();
    defer reference.deinit();
    try staging.expandNaive(&reference);
    try std.testing.expectEqual(reference.len(), db.closure.?.len());
    for (0..reference.len()) |index|
        try std.testing.expect(try db.closure.?.contains(reference.factAt(index)));
}

test "base updates and rule additions rebuild the closure correctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // A base insertion marks the closure dirty and the next query repairs it.
    var inserted = try db.execute("edge(c, d).");
    inserted.deinit();
    try std.testing.expect(db.materialization == .dirty_from_stratum);
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try std.testing.expect(db.materialization == .clean);

    // Retraction removes derived consequences through the dirty rebuild.
    var retracted = try db.execute("edge(a, b)~");
    retracted.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try expectAnswerCount(&db, "path(b, d)?", 1);

    // Typed updates take the same paths.
    try db.addFact("edge", &.{ input.atom("d"), input.atom("e") });
    try expectAnswerCount(&db, "path(b, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try expectAnswerCount(&db, "path(b, e)?", 0);

    // Rule addition invalidates from the new head's stratum.
    var extended = try db.execute("reach(X) :- path(b, X).");
    extended.deinit();
    try std.testing.expect(db.materialization == .dirty_from_stratum);
    try expectAnswerCount(&db, "reach(d)?", 1);
}

test "dirty stratum rebuild skips clean lower strata" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). flag(a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\note(X) :- flag(X), not path(a, X).
    );
    setup.deinit();
    // First materialization runs both strata.
    try expectAnswerCount(&db, "note(a)?", 1);
    const full_build = db.expansions;
    try std.testing.expectEqual(@as(usize, 2), full_build);

    // Only the negation stratum reads flag, so its update rebuilds one level.
    var flagged = try db.execute("flag(c).");
    flagged.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 1, db.expansions);

    // An edge update dirties the recursive stratum and rebuilds both levels.
    var edged = try db.execute("edge(c, d).");
    edged.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 3, db.expansions);
}

test "a database without rules allocates no derived machinery" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    try expectAnswerCount(&db, "kept(1)?", 1);
    var typed = try db.query(&.{input.relation("kept", &.{input.variable("n")})});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 1), typed.answers.items.len);
    try std.testing.expect(db.closure == null);
    try std.testing.expect(db.materialization == .uninitialized);
    try std.testing.expect(db.analysis == null);
    try std.testing.expectEqual(@as(usize, 0), db.expansions);
}

fn materializationAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    );
    setup.deinit();
    var first = try db.execute("summary(S)?");
    first.deinit();
    var inserted = try db.execute("edge(c, d).");
    inserted.deinit();
    var second = try db.execute("path(a, d)?");
    second.deinit();
    var retracted = try db.execute("edge(c, d)~");
    retracted.deinit();
    var third = try db.execute("path(a, d)?");
    defer third.deinit();
    if (third.query.answers.items.len != 0) return error.UnexpectedAnswer;
}

test "materialization lifecycle releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        materializationAllocationScenario,
        .{},
    );
}

/// Compares the database's materialized closure against a fresh naive
/// rebuild from its current base facts and rules.
fn expectClosureMatchesRebuild(db: *Jatalog) !void {
    var staging = try db.clone();
    defer staging.deinit();
    var rebuilt = try staging.facts.clone();
    defer rebuilt.deinit();
    try staging.expandNaive(&rebuilt);
    const closure = &db.closure.?;
    try std.testing.expectEqual(rebuilt.len(), closure.len());
    for (0..rebuilt.len()) |index|
        try std.testing.expect(try closure.contains(rebuilt.factAt(index)));
}

test "insert-only batches propagate incrementally and match full rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(n0, n1). edge(n1, n2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(n0, n2)?", 1);
    const expansions_after_build = db.expansions;

    // Each batch extends the chain; the closure stays clean and matches a
    // full rebuild after every batch without any stratum expansion.
    var name_buffer: [16]u8 = undefined;
    var next_buffer: [16]u8 = undefined;
    for (2..6) |index| {
        const from = try std.fmt.bufPrint(&name_buffer, "n{d}", .{index});
        const to = try std.fmt.bufPrint(&next_buffer, "n{d}", .{index + 1});
        try std.testing.expect(try db.applyChanges(&.{
            input.fact("edge", &.{ input.atom(from), input.atom(to) }),
        }, &.{}));
        try std.testing.expect(db.materialization == .clean);
        try expectClosureMatchesRebuild(&db);
    }
    try std.testing.expectEqual(expansions_after_build, db.expansions);
    try std.testing.expect(db.propagated_facts > 0);
    try expectAnswerCount(&db, "path(n0, n6)?", 1);
    try expectAnswerCount(&db, "path(X, Y)?", 21);
}

test "one inserted edge propagates each recursive consequence exactly once" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(X, Y)?", 6);

    // Inserting edge(d, e) derives exactly the four new paths a-e, b-e,
    // c-e, and d-e; each is propagated and counted exactly once.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
    try std.testing.expectEqual(@as(usize, 4), db.propagated_facts);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
    try expectClosureMatchesRebuild(&db);
}

test "duplicate base insertions produce no derived delta" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, b)?", 1);
    const closure_len = db.closure.?.len();
    const propagated = db.propagated_facts;

    try std.testing.expect(!try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }, &.{}));
    try std.testing.expectEqual(closure_len, db.closure.?.len());
    try std.testing.expectEqual(propagated, db.propagated_facts);
    try std.testing.expect(db.materialization == .clean);
}

test "propagation reaching negation or setof falls back to dirty rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). flag(a). flag(b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\note(X) :- flag(X), not path(a, X).
    );
    setup.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    const expansions_after_build = db.expansions;

    // flag is only read positively, so its insertion propagates through the
    // negation stratum without any rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("flag", &.{input.atom("c")}),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build, db.expansions);
    try std.testing.expect(db.materialization == .clean);
    try expectAnswerCount(&db, "note(c)?", 1);
    try expectClosureMatchesRebuild(&db);

    // An edge insertion grows path, which the negation reads, so the
    // negation stratum rebuilds while the positive stratum stays
    // incremental.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build + 1, db.expansions);
    try std.testing.expect(db.materialization == .clean);
    try expectAnswerCount(&db, "note(c)?", 0);
    try expectClosureMatchesRebuild(&db);
}

test "batch deletions and mixed batches maintain the closure correctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // Deleting an absent fact alone is a no-op that commits nothing.
    try std.testing.expect(!try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("x"), input.atom("y") }),
    }));
    try std.testing.expect(db.materialization == .clean);

    // A mixed batch deletes one edge and inserts another as one transition.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
    }, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try expectAnswerCount(&db, "path(b, d)?", 1);
    try expectClosureMatchesRebuild(&db);

    try std.testing.expectError(Error.InvalidFact, db.applyChanges(&.{
        input.fact("edge", &.{ input.variable("x"), input.atom("y") }),
    }, &.{}));
    try std.testing.expectError(Error.InvalidFact, db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.variable("x"), input.atom("y") }),
    }));
}

test "deleting the only base support removes the entire unsupported cycle" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    // The full cycle reaches every node from every node.
    try expectAnswerCount(&db, "path(X, Y)?", 9);
    const expansions_after_build = db.expansions;

    // After deleting edge(a, b) the cyclically self-supporting facts such
    // as path(a, a) must all disappear; reference counts alone would keep
    // them alive. The deletion is incremental: no stratum expansion runs.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.expansions);
    try std.testing.expect(db.removed_facts > 0);
    try expectAnswerCount(&db, "path(a, a)?", 0);
    try expectAnswerCount(&db, "path(X, Y)?", 3);
    try expectClosureMatchesRebuild(&db);
}

test "alternative recursive and non-recursive derivations preserve facts" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\marked(a).
        \\special(X) :- marked(X).
        \\special(X) :- path(X, d).
    );
    setup.deinit();
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try expectAnswerCount(&db, "special(b)?", 1);

    // path(a, d) survives the deletion through the c branch of the diamond,
    // while path(b, d) and with it special(b) lose their only support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("d") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try expectAnswerCount(&db, "special(b)?", 0);
    try expectClosureMatchesRebuild(&db);

    // special(a) loses its non-recursive derivation but survives through
    // the recursive path(a, d) alternative.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("marked", &.{input.atom("a")}),
    }));
    try expectAnswerCount(&db, "special(a)?", 1);
    try expectClosureMatchesRebuild(&db);
}

test "adding and removing a fact toggles negation-dependent conclusions" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\item(a). item(b).
        \\blocked(b).
        \\allowed(X) :- item(X), not blocked(X).
    );
    setup.deinit();
    try expectAnswerCount(&db, "allowed(a)?", 1);
    try expectAnswerCount(&db, "allowed(b)?", 0);

    try std.testing.expect(try db.applyChanges(&.{
        input.fact("blocked", &.{input.atom("a")}),
    }, &.{}));
    try expectAnswerCount(&db, "allowed(a)?", 0);
    try expectClosureMatchesRebuild(&db);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("blocked", &.{input.atom("a")}),
    }));
    try expectAnswerCount(&db, "allowed(a)?", 1);
    try expectAnswerCount(&db, "allowed(b)?", 0);
    try expectClosureMatchesRebuild(&db);
}

test "projection counts change without prematurely deleting supported tuples" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\holds(a, b1). holds(a, b2).
        \\present(X) :- holds(X, Y).
    );
    setup.deinit();
    try expectAnswerCount(&db, "present(a)?", 1);
    const present_id = db.strings.get("present").?;
    const support_before = blk: {
        for (0..db.closure.?.len()) |index| {
            const fact = db.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_before >= 2);

    // Removing one of two supports keeps the tuple with changed support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("holds", &.{ input.atom("a"), input.atom("b1") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try expectAnswerCount(&db, "present(a)?", 1);
    const support_after = blk: {
        for (0..db.closure.?.len()) |index| {
            const fact = db.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_after != support_before);
    try expectClosureMatchesRebuild(&db);

    // Removing the last support deletes the tuple.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("holds", &.{ input.atom("a"), input.atom("b2") }),
    }));
    try expectAnswerCount(&db, "present(a)?", 0);
    try expectClosureMatchesRebuild(&db);
}

test "random mixed update traces match a clean rebuild after every batch" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e).
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
        \\summary(S) :- node(a), setof([X, Y], path(X, Y), S).
    );
    setup.deinit();
    try expectAnswerCount(&db, "summary(S)?", 1);

    const names = [_][]const u8{ "a", "b", "c", "d", "e" };
    var prng = std.Random.DefaultPrng.init(0x5eed5eed5eed5eed);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [3][2]input.Term = undefined;
        var inserts: [3]input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            insert_buffer[slot] = .{
                input.atom(names[random.uintLessThan(usize, names.len)]),
                input.atom(names[random.uintLessThan(usize, names.len)]),
            };
            inserts[slot] = input.fact("edge", &insert_buffer[slot]);
        }
        var delete_buffer: [3][2]input.Term = undefined;
        var deletes: [3]input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            delete_buffer[slot] = .{
                input.atom(names[random.uintLessThan(usize, names.len)]),
                input.atom(names[random.uintLessThan(usize, names.len)]),
            };
            deletes[slot] = input.fact("edge", &delete_buffer[slot]);
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.materialization == .clean);
        try expectClosureMatchesRebuild(&db);
    }
}

test "aggregate groups are maintained incrementally across member changes" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2).
        \\member(g1, b). member(g1, a). member(g2, z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var initial = try db.execute("collected(g1, S)?");
    try expectBindingValue(&db, &initial.query.answers.items[0], "S", "[a, b]");
    initial.deinit();
    const expansions_after_build = db.expansions;

    // Member insertion updates only the affected group, with no rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g1"), input.atom("c") }),
    }, &.{}));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.expansions);
    var inserted = try db.execute("collected(g1, S)?");
    try expectBindingValue(&db, &inserted.query.answers.items[0], "S", "[a, b, c]");
    inserted.deinit();
    try expectClosureMatchesRebuild(&db);

    // The untouched group keeps its list and there is exactly one tuple
    // per group after the change.
    var untouched = try db.execute("collected(g2, S)?");
    try expectBindingValue(&db, &untouched.query.answers.items[0], "S", "[z]");
    untouched.deinit();
    try expectAnswerCount(&db, "collected(G, S)?", 2);

    // Member deletion shrinks the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("a") }),
    }));
    var deleted = try db.execute("collected(g1, S)?");
    try expectBindingValue(&db, &deleted.query.answers.items[0], "S", "[b, c]");
    deleted.deinit();
    try expectClosureMatchesRebuild(&db);

    // Deleting the last member leaves the enumerated group with an empty
    // list, because its outer goal still derives the group.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g2"), input.atom("z") }),
    }));
    var emptied = try db.execute("collected(g2, S)?");
    try expectBindingValue(&db, &emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try expectClosureMatchesRebuild(&db);

    // Deleting the group key removes the tuple entirely.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("group", &.{input.atom("g2")}),
    }));
    try expectAnswerCount(&db, "collected(g2, S)?", 0);
    try expectAnswerCount(&db, "collected(G, S)?", 1);
    try expectClosureMatchesRebuild(&db);

    // Restoring the group key brings back an empty group.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("group", &.{input.atom("g2")}),
    }, &.{}));
    var restored = try db.execute("collected(g2, S)?");
    try expectBindingValue(&db, &restored.query.answers.items[0], "S", "[]");
    restored.deinit();
    try expectClosureMatchesRebuild(&db);
}

test "duplicate member derivations do not disturb a maintained group" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g). direct(g, a). mirrored(g, a). direct(g, b).
        \\member(G, X) :- direct(G, X).
        \\member(G, X) :- mirrored(G, X).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var initial = try db.execute("collected(g, S)?");
    try expectBindingValue(&db, &initial.query.answers.items[0], "S", "[a, b]");
    initial.deinit();

    // Removing one of two derivations of member(g, a) keeps the member.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("mirrored", &.{ input.atom("g"), input.atom("a") }),
    }));
    var kept = try db.execute("collected(g, S)?");
    try expectBindingValue(&db, &kept.query.answers.items[0], "S", "[a, b]");
    kept.deinit();
    try expectClosureMatchesRebuild(&db);

    // Removing the last derivation drops it from the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("direct", &.{ input.atom("g"), input.atom("a") }),
    }));
    var dropped = try db.execute("collected(g, S)?");
    try expectBindingValue(&db, &dropped.query.answers.items[0], "S", "[b]");
    dropped.deinit();
    try expectClosureMatchesRebuild(&db);
}

test "canonical aggregate lists are independent of update order" {
    const orders = [_][3][]const u8{
        .{ "c", "a", "b" },
        .{ "b", "c", "a" },
        .{ "a", "b", "c" },
    };
    for (orders) |order| {
        var db: Jatalog = .init(std.testing.allocator);
        defer db.deinit();
        var setup = try db.execute(
            \\group(g).
            \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        );
        setup.deinit();
        var empty = try db.execute("collected(g, S)?");
        try expectBindingValue(&db, &empty.query.answers.items[0], "S", "[]");
        empty.deinit();

        for (order) |name| {
            _ = try db.applyChanges(&.{
                input.fact("member", &.{ input.atom("g"), input.atom(name) }),
            }, &.{});
        }
        var result = try db.execute("collected(g, S)?");
        try expectBindingValue(&db, &result.query.answers.items[0], "S", "[a, b, c]");
        result.deinit();
        try expectClosureMatchesRebuild(&db);
    }
}

test "bag emulation retains equal values with distinct discriminators" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g). reading(g, r1, 5). reading(g, r2, 5). reading(g, r3, 7).
        \\bag(G, S) :- group(G), setof([V, D], reading(G, D, V), S).
    );
    setup.deinit();
    var initial = try db.execute("bag(g, S)?");
    try expectBindingValue(
        &db,
        &initial.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [7, r3]]",
    );
    initial.deinit();

    try std.testing.expect(try db.applyChanges(&.{
        input.fact("reading", &.{ input.atom("g"), input.atom("r4"), input.integer(5) }),
    }, &.{}));
    var added = try db.execute("bag(g, S)?");
    try expectBindingValue(
        &db,
        &added.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [5, r4], [7, r3]]",
    );
    added.deinit();
    try expectClosureMatchesRebuild(&db);

    // Removing one duplicate value keeps the others.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("reading", &.{ input.atom("g"), input.atom("r2"), input.integer(5) }),
    }));
    var removed = try db.execute("bag(g, S)?");
    try expectBindingValue(
        &db,
        &removed.query.answers.items[0],
        "S",
        "[[5, r1], [5, r4], [7, r3]]",
    );
    removed.deinit();
    try expectClosureMatchesRebuild(&db);
}

test "maintained aggregates feed downstream strata and recursive consumers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\person(alice). person(bob).
        \\parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    );
    setup.deinit();
    var initial = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 1), try initial.query.answers.items[0].getInteger("N"));
    initial.deinit();

    // A new child changes the aggregate list, which must flow through the
    // downstream structural list function.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("person", &.{input.atom("carol")}),
        input.fact("parent", &.{ input.atom("alice"), input.atom("carol") }),
    }, &.{}));
    var grown = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    try expectAnswerCount(&db, "numchildren(X, N)?", 3);
    try expectClosureMatchesRebuild(&db);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("parent", &.{ input.atom("alice"), input.atom("bob") }),
    }));
    var shrunk = try db.execute("numchildren(alice, N)?");
    try std.testing.expectEqual(@as(i64, 1), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try expectClosureMatchesRebuild(&db);
}

test "multiple and nested aggregates stay correct through the rebuild path" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). item(g1, a). item(g2, b). tag(g1, t1). tag(g2, t2).
        \\both(G, S, T) :- group(G), setof(X, item(G, X), S), setof(Y, tag(G, Y), T).
        \\nested(S) :- group(g1), setof([G, T], (group(G), setof(X, item(G, X), T)), S).
    );
    setup.deinit();
    var initial = try db.execute("both(g1, S, T)?");
    try expectBindingValue(&db, &initial.query.answers.items[0], "S", "[a]");
    try expectBindingValue(&db, &initial.query.answers.items[0], "T", "[t1]");
    initial.deinit();

    // Rules outside the maintainable class fall back to the stratum
    // rebuild, which must still produce rebuild-equivalent results.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("item", &.{ input.atom("g1"), input.atom("c") }),
        input.fact("tag", &.{ input.atom("g1"), input.atom("t3") }),
    }, &.{}));
    var updated = try db.execute("both(g1, S, T)?");
    try expectBindingValue(&db, &updated.query.answers.items[0], "S", "[a, c]");
    try expectBindingValue(&db, &updated.query.answers.items[0], "T", "[t1, t3]");
    updated.deinit();
    var nested = try db.execute("nested(S)?");
    try expectBindingValue(
        &db,
        &nested.query.answers.items[0],
        "S",
        "[[g1, [a, c]], [g2, [b]]]",
    );
    nested.deinit();
    try expectClosureMatchesRebuild(&db);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("item", &.{ input.atom("g1"), input.atom("a") }),
    }));
    var reduced = try db.execute("both(g1, S, T)?");
    try expectBindingValue(&db, &reduced.query.answers.items[0], "S", "[c]");
    reduced.deinit();
    try expectClosureMatchesRebuild(&db);
}

test "random aggregate update traces match a clean rebuild after every batch" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). group(g3).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\empty(G) :- group(G), not member(G, m1), not member(G, m2), not member(G, m3).
    );
    setup.deinit();
    try expectAnswerCount(&db, "size(G, N)?", 3);

    const groups = [_][]const u8{ "g1", "g2", "g3" };
    const members = [_][]const u8{ "m1", "m2", "m3" };
    var prng = std.Random.DefaultPrng.init(0xa99a6a7e5eed);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [2][2]input.Term = undefined;
        var inserts: [2]input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            insert_buffer[slot] = .{
                input.atom(groups[random.uintLessThan(usize, groups.len)]),
                input.atom(members[random.uintLessThan(usize, members.len)]),
            };
            inserts[slot] = input.fact("member", &insert_buffer[slot]);
        }
        var delete_buffer: [2][2]input.Term = undefined;
        var deletes: [2]input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            delete_buffer[slot] = .{
                input.atom(groups[random.uintLessThan(usize, groups.len)]),
                input.atom(members[random.uintLessThan(usize, members.len)]),
            };
            deletes[slot] = input.fact("member", &delete_buffer[slot]);
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.materialization == .clean);
        try expectClosureMatchesRebuild(&db);
    }
}

/// Derivation count the auxiliary view records for the single tuple of
/// `predicate` whose first argument is the atom `first_atom`.
fn derivationCountOf(
    db: *Jatalog,
    predicate: []const u8,
    first_atom: []const u8,
) !u32 {
    const predicate_id = db.strings.get(predicate) orelse return error.MissingPredicate;
    const scalar_id = try db.scalars.internAtom(first_atom);
    const first_value = try db.values.intern(.{ .scalar = scalar_id });
    for (db.rules.items) |rule| {
        if (rule.head.predicate != predicate_id) continue;
        const view = db.auxiliaryFor(rule.id) orelse return error.NotProjected;
        const closure = &db.closure.?;
        for (0..closure.len()) |index| {
            const fact = closure.factAt(index);
            if (fact.predicate != predicate_id or fact.terms[0] != first_value) continue;
            return db.derivationCount(view, fact.terms);
        }
        return 0;
    }
    return error.MissingPredicate;
}

test "Chapter 5 Example 5.2.1 maintains a view without projections" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a). p(b). r(a, 1). r(c, 3).
        \\v(X, S) :- p(X), setof(Y, r(X, Y), S).
    );
    setup.deinit();

    // The materialization contains v(a, [1]) and v(b, []).
    var initial = try db.execute("v(a, S)?");
    try expectBindingValue(&db, &initial.query.answers.items[0], "S", "[1]");
    initial.deinit();
    var empty = try db.execute("v(b, S)?");
    try expectBindingValue(&db, &empty.query.answers.items[0], "S", "[]");
    empty.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 2);

    // Deleting p(a) and inserting r(b, 2) deletes v(a, [1]) and updates
    // v(b, []) to v(b, [2]).
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("r", &.{ input.atom("b"), input.integer(2) }),
    }, &.{
        input.fact("p", &.{input.atom("a")}),
    }));
    try std.testing.expect(db.materialization == .clean);
    try expectAnswerCount(&db, "v(a, S)?", 0);
    var updated = try db.execute("v(b, S)?");
    try expectBindingValue(&db, &updated.query.answers.items[0], "S", "[2]");
    updated.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 1);
    try expectClosureMatchesRebuild(&db);

    // This view retains every outer variable, so it is self-maintainable and
    // needs no auxiliary derivation counts.
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.self_maintainable_views);
    try std.testing.expectEqual(@as(usize, 0), stats.projected_views);
    try std.testing.expectEqual(@as(usize, 0), stats.auxiliary_tuples);
}

test "Chapter 5 Example 5.3.1 counts derivations of a projected view" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a, 1). p(a, 2). p(b, 1). r(a, 1). r(a, 2). r(b, 2).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();

    var initial = try db.execute("v(a, S)?");
    try expectBindingValue(&db, &initial.query.answers.items[0], "S", "[1, 2]");
    initial.deinit();
    var other = try db.execute("v(b, S)?");
    try expectBindingValue(&db, &other.query.answers.items[0], "S", "[2]");
    other.deinit();

    // The auxiliary counting view holds v(a, [1, 2]) with two derivations
    // and v(b, [2]) with one, matching the chapter's v_c extension.
    const stats = db.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 1), stats.projected_views);
    try std.testing.expectEqual(@as(usize, 0), stats.self_maintainable_views);
    try std.testing.expectEqual(@as(usize, 3), stats.auxiliary_tuples);
    try std.testing.expectEqual(@as(u32, 2), try derivationCountOf(&db, "v", "a"));
    try std.testing.expectEqual(@as(u32, 1), try derivationCountOf(&db, "v", "b"));

    // Deleting p(a, 2) removes one of two derivations, so the tuple stays.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("p", &.{ input.atom("a"), input.integer(2) }),
    }));
    try std.testing.expect(db.materialization == .clean);
    var retained = try db.execute("v(a, S)?");
    try expectBindingValue(&db, &retained.query.answers.items[0], "S", "[1, 2]");
    retained.deinit();
    try std.testing.expectEqual(@as(u32, 1), try derivationCountOf(&db, "v", "a"));
    try expectClosureMatchesRebuild(&db);

    // Deleting p(a, 1) removes the last derivation, so the tuple goes.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("p", &.{ input.atom("a"), input.integer(1) }),
    }));
    try expectAnswerCount(&db, "v(a, S)?", 0);
    try std.testing.expectEqual(@as(u32, 0), try derivationCountOf(&db, "v", "a"));
    try expectAnswerCount(&db, "v(X, S)?", 1);
    try expectClosureMatchesRebuild(&db);
}

test "a changed aggregate list transfers support to the new tuple" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a, 1). p(a, 2). p(a, 3). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();
    var initial = try db.execute("v(a, S)?");
    try expectBindingValue(&db, &initial.query.answers.items[0], "S", "[1]");
    initial.deinit();
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));

    // Growing the member set replaces the old tuple with the new one and
    // carries all three derivations across in the same batch.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("r", &.{ input.atom("a"), input.integer(2) }),
    }, &.{}));
    try std.testing.expect(db.materialization == .clean);
    var moved = try db.execute("v(a, S)?");
    try expectBindingValue(&db, &moved.query.answers.items[0], "S", "[1, 2]");
    moved.deinit();
    try expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try std.testing.expectEqual(@as(usize, 3), db.maintenanceStats().auxiliary_tuples);
    try expectClosureMatchesRebuild(&db);

    // Shrinking it back transfers the support again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("r", &.{ input.atom("a"), input.integer(1) }),
    }));
    var shrunk = try db.execute("v(a, S)?");
    try expectBindingValue(&db, &shrunk.query.answers.items[0], "S", "[2]");
    shrunk.deinit();
    try expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try expectClosureMatchesRebuild(&db);
}

test "projected view counts agree with explicit proof enumeration" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a, 1). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    );
    setup.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 1);

    const keys = [_][]const u8{ "a", "b", "c" };
    var prng = std.Random.DefaultPrng.init(0xc0107501c0107);
    const random = prng.random();
    for (0..40) |_| {
        var insert_buffer: [2][2]input.Term = undefined;
        var inserts: [2]input.Relation = undefined;
        const insert_count = random.uintLessThan(usize, 3);
        for (0..insert_count) |slot| {
            const key = keys[random.uintLessThan(usize, keys.len)];
            const number: i64 = @intCast(random.uintLessThan(usize, 3) + 1);
            insert_buffer[slot] = .{ input.atom(key), input.integer(number) };
            inserts[slot] = input.fact(
                if (random.boolean()) "p" else "r",
                &insert_buffer[slot],
            );
        }
        var delete_buffer: [2][2]input.Term = undefined;
        var deletes: [2]input.Relation = undefined;
        const delete_count = random.uintLessThan(usize, 3);
        for (0..delete_count) |slot| {
            const key = keys[random.uintLessThan(usize, keys.len)];
            const number: i64 = @intCast(random.uintLessThan(usize, 3) + 1);
            delete_buffer[slot] = .{ input.atom(key), input.integer(number) };
            deletes[slot] = input.fact(
                if (random.boolean()) "p" else "r",
                &delete_buffer[slot],
            );
        }
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try std.testing.expect(db.materialization == .clean);
        try expectClosureMatchesRebuild(&db);

        // Every proof of v(k, S) comes from one p(k, Z) fact, so the stored
        // derivation count must equal the number of such base facts.
        for (keys) |key| {
            var proofs = try db.execute("p(K, Z)?");
            defer proofs.deinit();
            var expected: u32 = 0;
            for (proofs.query.answers.items) |*answer| {
                const bound = try answer.getAtom("K");
                if (std.mem.eql(u8, bound, key)) expected += 1;
            }
            try std.testing.expectEqual(expected, try derivationCountOf(&db, "v", key));
        }
    }
}

test "retraction maintains the closure incrementally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a). edge(x, y).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "path(X, Y)?", 10);
    const after_build = db.maintenanceStats();

    // A typed retraction runs delete-and-rederive rather than dirtying the
    // stratum, so no rule expansion happens and the closure stays clean.
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("x"), input.atom("y") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().removed_facts > after_build.removed_facts);
    try expectAnswerCount(&db, "path(x, y)?", 0);
    try expectClosureMatchesRebuild(&db);

    // Retracting the only base support of a cycle removes the whole
    // unsupported cycle, still without a rebuild.
    const before_cycle = db.maintenanceStats();
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("c"), input.atom("a") }),
    }));
    try std.testing.expectEqual(before_cycle.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "path(a, a)?", 0);
    try expectAnswerCount(&db, "path(a, c)?", 1);
    try expectClosureMatchesRebuild(&db);
}

test "pattern retraction removes every matching fact incrementally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(a, d). edge(b, e).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // One goal with a variable retracts all three outgoing edges of a.
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("a"), input.variable("target") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "edge(a, X)?", 0);
    try expectAnswerCount(&db, "path(a, X)?", 0);
    try expectAnswerCount(&db, "path(b, e)?", 1);
    try expectClosureMatchesRebuild(&db);

    // Source-level retraction takes the same path.
    const before_source = db.maintenanceStats();
    var retracted = try db.execute("edge(b, e)~");
    retracted.deinit();
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(before_source.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "path(X, Y)?", 0);
    try expectClosureMatchesRebuild(&db);
}

test "retraction maintains aggregate groups and negation strata" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a). member(g1, b). member(g2, z).
        \\banned(g2).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\allowed(G) :- group(G), not banned(G).
    );
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // Retracting a member updates only the affected group's list.
    try std.testing.expect(try db.retract(&.{
        input.relation("member", &.{ input.atom("g1"), input.atom("a") }),
    }));
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().maintained_groups > after_build.maintained_groups);
    var collected = try db.execute("collected(g1, S)?");
    try expectBindingValue(&db, &collected.query.answers.items[0], "S", "[b]");
    collected.deinit();
    try expectClosureMatchesRebuild(&db);

    // Retracting the last member leaves the enumerated group empty.
    try std.testing.expect(try db.retract(&.{
        input.relation("member", &.{ input.atom("g1"), input.atom("b") }),
    }));
    var emptied = try db.execute("collected(g1, S)?");
    try expectBindingValue(&db, &emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try expectClosureMatchesRebuild(&db);

    // Retracting a negated predicate is the documented rebuild category.
    const before_negation = db.maintenanceStats();
    try expectAnswerCount(&db, "allowed(g2)?", 0);
    try std.testing.expect(try db.retract(&.{
        input.relation("banned", &.{input.atom("g2")}),
    }));
    try expectAnswerCount(&db, "allowed(g2)?", 1);
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before_negation.rebuild_fallbacks);
    try expectClosureMatchesRebuild(&db);
}

fn retractionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, c). group(g). member(g, m1). member(g, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    try db.materialize();
    _ = try db.retract(&.{
        input.relation("edge", &.{ input.atom("a"), input.variable("target") }),
    });
    _ = try db.retract(&.{
        input.relation("member", &.{ input.atom("g"), input.atom("m1") }),
    });
    var result = try db.execute("collected(g, S)?");
    defer result.deinit();
    const formatted = try (try result.query.answers.items[0].getValue("S")).formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[m2]")) return error.UnexpectedAggregate;
}

test "incremental retraction releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        retractionAllocationScenario,
        .{},
    );
}

test "aggregate changes propagate through downstream list functions and arithmetic" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\team(red). team(blue).
        \\roster(T, S) :- team(T), setof(P, plays(T, P), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(T, N) :- roster(T, S), length(S, N).
        \\headcount(T, N) :- size(T, M), N = M + 1.
        \\staffed(T) :- size(T, N), N > 1.
    );
    setup.deinit();
    try db.materialize();

    // Empty rosters flow through length, arithmetic, and the comparison.
    var initial = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 1), try initial.query.answers.items[0].getInteger("N"));
    initial.deinit();
    try expectAnswerCount(&db, "staffed(T)?", 0);

    // Growing one group must reach every downstream stratum.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("plays", &.{ input.atom("red"), input.atom("ann") }),
        input.fact("plays", &.{ input.atom("red"), input.atom("bo") }),
    }, &.{}));
    var grown = try db.execute("size(red, N)?");
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    var counted = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 3), try counted.query.answers.items[0].getInteger("N"));
    counted.deinit();
    try expectAnswerCount(&db, "staffed(red)?", 1);
    try expectAnswerCount(&db, "staffed(blue)?", 0);
    try expectClosureMatchesRebuild(&db);

    // Shrinking it retracts the downstream conclusions again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("plays", &.{ input.atom("red"), input.atom("bo") }),
    }));
    var shrunk = try db.execute("headcount(red, N)?");
    try std.testing.expectEqual(@as(i64, 2), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try expectAnswerCount(&db, "staffed(T)?", 0);
    try expectClosureMatchesRebuild(&db);

    // A downstream structural-recursive component recomputes within its own
    // stratum rather than forcing a whole-closure rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.maintained_groups > 0);
}

test "materialize rebuild and stats form the explicit maintenance API" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\group(g). member(g, m1).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();

    // Maintenance is lazy until asked: nothing is materialized yet.
    try std.testing.expect(db.closure == null);
    try std.testing.expectEqual(@as(usize, 0), db.maintenanceStats().closure_facts);

    try db.materialize();
    try std.testing.expect(db.materialization == .clean);
    const after_materialize = db.maintenanceStats();
    try std.testing.expect(after_materialize.closure_facts > 0);
    try std.testing.expectEqual(@as(usize, 0), after_materialize.rebuild_fallbacks);

    // materialize is idempotent and performs no further expansion.
    try db.materialize();
    try std.testing.expectEqual(
        after_materialize.stratum_expansions,
        db.maintenanceStats().stratum_expansions,
    );

    // rebuild recomputes from base facts and reproduces the same closure.
    try db.rebuild();
    try std.testing.expect(db.materialization == .clean);
    try std.testing.expectEqual(after_materialize.closure_facts, db.maintenanceStats().closure_facts);
    try expectClosureMatchesRebuild(&db);
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // The single-statement entry points keep working alongside the batch
    // API. Pattern retraction is not a subset of it: it deletes every base
    // fact matching a goal, which exact-fact batch deletion cannot express.
    try db.addFact("edge", &.{ input.atom("c"), input.atom("d") });
    try expectAnswerCount(&db, "path(a, d)?", 1);
    var executed = try db.execute("edge(d, e).");
    executed.deinit();
    try expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try expectAnswerCount(&db, "path(a, e)?", 0);

    // Retraction takes the same incremental deletion path as a batch, so
    // the closure stays clean and this materialize is a no-op.
    try std.testing.expect(db.materialization == .clean);
    const before_materialize = db.maintenanceStats();
    try db.materialize();
    try std.testing.expectEqual(
        before_materialize.stratum_expansions,
        db.maintenanceStats().stratum_expansions,
    );

    // An inserted edge derives new path facts through the delta engine.
    const before_edge = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
    try expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(db.maintenanceStats().propagated_facts > before_edge.propagated_facts);

    // An inserted member recomputes exactly the affected aggregate group.
    const before_member = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g"), input.atom("m2") }),
    }, &.{}));
    var collected = try db.execute("collected(g, S)?");
    try expectBindingValue(&db, &collected.query.answers.items[0], "S", "[m1, m2]");
    collected.deinit();
    try std.testing.expect(db.maintenanceStats().maintained_groups > before_member.maintained_groups);
    try expectClosureMatchesRebuild(&db);

    const before_delete = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }));
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try std.testing.expect(db.maintenanceStats().removed_facts > before_delete.removed_facts);
    try expectClosureMatchesRebuild(&db);

    // Every update category is accounted for by one of the documented
    // paths: incremental propagation, delete-and-rederive, or rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.propagated_facts > 0);
    try std.testing.expect(stats.removed_facts > 0);
    try std.testing.expectEqual(@as(usize, 1), stats.self_maintainable_views);
}

test "shadow verification accepts maintained closures and reports corruption" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). group(g). member(g, m1).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\reachable(X) :- path(a, X).
        \\unreachable(X) :- edge(X, Y), not reachable(X).
    );
    setup.deinit();
    try db.materialize();

    // Insertions, deletions, and aggregate changes all pass verification.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
        input.fact("member", &.{ input.atom("g"), input.atom("m2") }),
    }, &.{}));
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }, &.{
        input.fact("member", &.{ input.atom("g"), input.atom("m1") }),
    }));
    try expectClosureMatchesRebuild(&db);

    // A closure corrupted behind the maintenance engine's back is caught:
    // this path tuple has no derivation from any base fact.
    const terms = try std.testing.allocator.alloc(ValueId, 2);
    var terms_owned = true;
    defer if (terms_owned) std.testing.allocator.free(terms);
    terms[0] = try db.values.intern(.{ .scalar = try db.scalars.internAtom("phantom1") });
    terms[1] = try db.values.intern(.{ .scalar = try db.scalars.internAtom("phantom2") });
    const added = try db.closure.?.insert(.{
        .predicate = db.strings.get("path").?,
        .terms = terms,
    }, true);
    terms_owned = false;
    try std.testing.expect(added);
    try std.testing.expectError(Error.MaintenanceMismatch, db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
}

test "randomized mixed traces hold under shadow verification" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\node(a). node(b). node(c). group(g1). group(g2).
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\quiet(G) :- group(G), not member(G, m1).
    );
    setup.deinit();
    try db.materialize();

    const nodes = [_][]const u8{ "a", "b", "c" };
    const groups = [_][]const u8{ "g1", "g2" };
    const members = [_][]const u8{ "m1", "m2" };
    var prng = std.Random.DefaultPrng.init(0x5ade0e5ade0e);
    const random = prng.random();
    for (0..30) |_| {
        var edge_terms: [2]input.Term = .{
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
        };
        var member_terms: [2]input.Term = .{
            input.atom(groups[random.uintLessThan(usize, groups.len)]),
            input.atom(members[random.uintLessThan(usize, members.len)]),
        };
        const insert_edge = random.boolean();
        var inserts: [2]input.Relation = undefined;
        var deletes: [2]input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (insert_edge) {
            inserts[insert_count] = input.fact("edge", &edge_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("edge", &edge_terms);
            delete_count += 1;
        }
        if (random.boolean()) {
            inserts[insert_count] = input.fact("member", &member_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("member", &member_terms);
            delete_count += 1;
        }
        // Shadow verification asserts rebuild equality inside the call.
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try expectClosureMatchesRebuild(&db);
    }
}

fn aggregateMaintenanceAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    );
    setup.deinit();
    var first = try db.execute("collected(G, S)?");
    first.deinit();
    _ = try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g1"), input.atom("b") }),
        input.fact("member", &.{ input.atom("g2"), input.atom("c") }),
    }, &.{});
    _ = try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("a") }),
    });
    var second = try db.execute("collected(g1, S)?");
    defer second.deinit();
    const formatted = try (try second.query.answers.items[0].getValue("S"))
        .formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[b]")) return error.UnexpectedAggregate;
}

test "aggregate maintenance releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        aggregateMaintenanceAllocationScenario,
        .{},
    );
}

fn batchUpdateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    var first = try db.execute("path(a, c)?");
    first.deinit();
    _ = try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
    }, &.{});
    _ = try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    });
    var second = try db.execute("path(b, e)?");
    defer second.deinit();
    if (second.query.answers.items.len != 1) return error.UnexpectedAnswer;
}

test "batch updates roll back completely on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        batchUpdateAllocationScenario,
        .{},
    );
}

test "duplicate derivations create no duplicate facts or endless rounds" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // A diamond plus a cycle derives many facts through multiple proofs.
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    );
    setup.deinit();
    try expectSemiNaiveMatchesNaive(&db);
    // Every node reaches every node exactly once in the answer set.
    try expectAnswerCount(&db, "path(X, Y)?", 16);
    try expectAnswerCount(&db, "path(a, d)?", 1);
}

test "indexed lookups match every structural binding pattern deterministically" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(a, c).
        \\holds([1, 2], a). holds([1, [2, 3]], b). holds(cons(1, 2), c). holds([], d).
        \\p(a). p(a, b).
    );
    setup.deinit();

    // Bound-position patterns over atoms.
    try expectAnswerCount(&db, "edge(a, X)?", 2);
    try expectAnswerCount(&db, "edge(X, Y)?", 3);
    try expectAnswerCount(&db, "edge(a, b)?", 1);
    try expectAnswerCount(&db, "edge(c, X)?", 0);

    // Answers arrive in fact insertion order.
    var ordered = try db.execute("edge(X, c)?");
    defer ordered.deinit();
    try std.testing.expectEqual(@as(usize, 2), ordered.query.answers.items.len);
    try std.testing.expectEqualStrings("b", try ordered.query.answers.items[0].getAtom("X"));
    try std.testing.expectEqualStrings("a", try ordered.query.answers.items[1].getAtom("X"));

    // Bound structural values: proper, nested, improper, and empty lists.
    var proper = try db.execute("holds([1, 2], X)?");
    defer proper.deinit();
    try std.testing.expectEqualStrings("a", try proper.query.answers.items[0].getAtom("X"));
    var nested = try db.execute("holds([1, [2, 3]], X)?");
    defer nested.deinit();
    try std.testing.expectEqualStrings("b", try nested.query.answers.items[0].getAtom("X"));
    var improper = try db.execute("holds(cons(1, 2), X)?");
    defer improper.deinit();
    try std.testing.expectEqualStrings("c", try improper.query.answers.items[0].getAtom("X"));
    var empty = try db.execute("holds([], X)?");
    defer empty.deinit();
    try std.testing.expectEqualStrings("d", try empty.query.answers.items[0].getAtom("X"));

    // A structural value bound through the second position.
    var reverse = try db.execute("holds(X, c)?");
    defer reverse.deinit();
    try expectBindingValue(&db, &reverse.query.answers.items[0], "X", "cons(1, 2)");

    // A partially ground structure is unbound for indexing and still unifies.
    try expectAnswerCount(&db, "holds([1, T], X)?", 2);

    // One predicate name at two arities never shares matches.
    try expectAnswerCount(&db, "p(X)?", 1);
    try expectAnswerCount(&db, "p(X, Y)?", 1);

    // Retraction through the same lookup interface removes exactly one fact.
    var retract = try db.execute("edge(a, X)~");
    defer retract.deinit();
    try expectAnswerCount(&db, "edge(X, Y)?", 1);
    try expectAnswerCount(&db, "edge(b, c)?", 1);
}

fn expectBindingValue(
    _: *const Jatalog,
    binding: *const Answer,
    variable: []const u8,
    expected: []const u8,
) !void {
    const value = try binding.getValue(variable);
    const formatted = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(formatted);
    try std.testing.expectEqualStrings(expected, formatted);
}

test "lists round trip through queries and nested terms unify structurally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\nested([a, [b, []]]).
        \\nested(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "X", "[a, [b, []]]");
}

test "head tail patterns work in rules and cons syntax is equivalent" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items(cons(a, cons(b, []))).
        \\tail(T) :- items(H!T).
        \\tail(X)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "X", "[b]");
}

test "repeated variables inside structures enforce equality" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\pair([a, [a]]). pair([a, [b]]).
        \\pair([X, [X]])?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));
}

test "facts reject variables at every structural depth" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidFact, db.execute("bad([a, X])."));
    try std.testing.expectError(Error.InvalidFact, db.execute("bad(a!T)."));

    var result = try db.execute("improper(a!b). improper(X)?");
    defer result.deinit();
    try expectBindingValue(&db, &result.query.answers.items[0], "X", "cons(a, b)");
}

test "structural equality binds variables recursively and parse errors clean up" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("seed(a). seed(X), [X] = [a]?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));

    try std.testing.expectError(Error.InvalidSyntax, db.execute("broken([a, [b])."));
}

test "ground values have a deterministic structural total order" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\value(z). value(a). value('1'). value(-2). value(10). value(2). value([]).
        \\value([-1]). value(cons(a, z)). value([a]). value([a, b]).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[-2, 2, 10, '1', a, z, [], [-1], cons(a, z), [a], [a, b]]",
    );
}

fn structuralAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items([a, [b], c]).
        \\tail(T) :- items(H!T).
        \\tail([X, c])?
    );
    defer result.deinit();
    const value = try result.query.answers.items[0].getValue("X");
    const formatted = try value.formatAlloc(allocator);
    defer allocator.free(formatted);
    try std.testing.expectEqualStrings("[b]", formatted);
}

test "structural parsing and evaluation release every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        structuralAllocationScenario,
        .{},
    );
}

test "correlated aggregate clauses parse and validate without evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). parent(alice, bob). passed(bob).
        \\children(X, S) :- person(X), setof([Y, X], (parent(X, Y), passed(Y)), S).
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.rules.items.len);
    try std.testing.expect(db.rules.items[0].body[0] == .relational);
    const aggregate = db.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), aggregate.body.len);
    try std.testing.expect(aggregate.body[0] == .relational);
    try std.testing.expect(aggregate.body[1] == .relational);
}

test "rule bodies classify every clause kind distinctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(a).
        \\classified(X, S) :- seed(X), X = X, not blocked(X), setof(Y, item(X, Y), S).
    );
    defer result.deinit();
    const body = db.rules.items[0].body;
    try std.testing.expect(body[0] == .relational);
    try std.testing.expect(body[1] == .builtin);
    try std.testing.expect(body[2] == .aggregate);
    try std.testing.expect(body[3] == .negated);
}

test "aggregate safety rejects unbound correlations and escaping locals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidRule, db.execute(
        "bad(X, S) :- setof(Y, parent(X, Y), S).",
    ));
    try std.testing.expectError(Error.InvalidRule, db.execute(
        "bad(Y, S) :- seed(k), setof(Y, parent(X, Y), S).",
    ));
}

test "aggregate output binds head variables and aggregate locals stay local" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\all_parents(S) :- seed(k), setof([X, Y], parent(X, Y), S).
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.rules.items.len);
}

test "nested aggregates are represented directly and validate recursively" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\grouped(S) :- seed(k), setof(T, (group(G), setof(Y, parent(G, Y), T)), S).
    );
    defer result.deinit();
    const outer = db.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), outer.body.len);
    try std.testing.expect(outer.body[1] == .aggregate);
}

test "direct and indirect recursion through aggregation are rejected" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(Error.NotStratified, direct.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, p(X), S).
    ));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(Error.NotStratified, indirect.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, q(X), S).
        \\q(X) :- p(X).
    ));
}

test "positive recursion may complete below an aggregate stratum" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all_reachable(S) :- seed(k), setof([X, Y], reachable(X, Y), S).
    );
    defer result.deinit();
    var levels = try db.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const reachable: PredicateKey = .{ .name = db.strings.get("reachable").?, .arity = 2 };
    const all_reachable: PredicateKey = .{ .name = db.strings.get("all_reachable").?, .arity = 1 };
    try std.testing.expectEqual(@as(usize, 0), levels.get(reachable).?);
    try std.testing.expectEqual(@as(usize, 1), levels.get(all_reachable).?);
}

test "negation and aggregate strict edges share one dependency graph" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(a). excluded(b).
        \\allowed(X) :- seed(X), not excluded(X).
        \\summary(S) :- seed(a), setof(X, allowed(X), S).
    );
    defer result.deinit();
    var levels = try db.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const allowed: PredicateKey = .{ .name = db.strings.get("allowed").?, .arity = 1 };
    const summary: PredicateKey = .{ .name = db.strings.get("summary").?, .arity = 1 };
    try std.testing.expectEqual(@as(usize, 1), levels.get(allowed).?);
    try std.testing.expectEqual(@as(usize, 2), levels.get(summary).?);
}

test "grouped setof is sorted, deduplicated, and includes empty groups" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(bob). person(alice). parent(alice, carol). parent(alice, bob).
        \\from_left(X, Y) :- parent(X, Y).
        \\from_right(X, Y) :- parent(X, Y).
        \\child(X, Y) :- from_left(X, Y).
        \\child(X, Y) :- from_right(X, Y).
        \\children(X, S) :- person(X), setof(Y, child(X, Y), S).
        \\children(X, S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    for (result.query.answers.items) |*answer| {
        const person = try answer.getAtom("X");
        if (std.mem.eql(u8, person, "alice")) {
            try expectBindingValue(&db, answer, "S", "[bob, carol]");
        } else if (std.mem.eql(u8, person, "bob")) {
            try expectBindingValue(&db, answer, "S", "[]");
        } else return error.UnexpectedPerson;
    }
}

test "setof evaluates directly in queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("item(c). item(a). setof(X, item(X), S)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[a, c]");
}

test "setof sees completed recursive strata and preserves structural templates" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all(S) :- seed(k), setof([Y, X], reachable(X, Y), S).
        \\all(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[[b, a], [c, a], [c, b], [d, a], [d, b], [d, c]]",
    );
}

test "nested and multiple setof goals evaluate from correlated bindings" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). group(g2). group(g1). item(g1, b). item(g1, a).
        \\summary(All, Groups) :- seed(k), setof(X, item(g1, X), All),
        \\  setof([G, S], (group(G), setof(X, item(G, X), S)), Groups).
        \\summary(All, Groups)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "All", "[a, b]");
    try expectBindingValue(&db, &result.query.answers.items[0], "Groups", "[[g1, [a, b]], [g2, []]]");
}

test "setof recomputes after retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). item(b). item(a).
        \\items(S) :- seed(k), setof(X, item(X), S).
        \\item(b)~
    );
    result.deinit();
    result = try db.execute("items(S)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[a]");
}

test "setof ordering is independent of insertion and rule order" {
    var first: Jatalog = .init(std.testing.allocator);
    defer first.deinit();
    var first_result = try first.execute(
        \\seed(k). base(c). base(a). base(b).
        \\value(X) :- base(X).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\values(S)?
    );
    defer first_result.deinit();

    var second: Jatalog = .init(std.testing.allocator);
    defer second.deinit();
    var second_result = try second.execute(
        \\base(b). base(c). base(a). seed(k).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\value(X) :- base(X).
        \\values(S)?
    );
    defer second_result.deinit();

    const first_value = try first_result.query.answers.items[0].getValue("S");
    const first_text = try first_value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(first_text);
    const second_value = try second_result.query.answers.items[0].getValue("S");
    const second_text = try second_value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(second_text);
    try std.testing.expectEqualStrings(first_text, second_text);
}

fn aggregateEvaluationAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\group(g1). group(g2). item(g1, b). item(g1, a).
        \\grouped(Groups) :- group(g1), setof([G, S], (group(G), setof(X, item(G, X), S)), Groups).
        \\grouped(Groups)?
    );
    defer result.deinit();
}

test "aggregate evaluation releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        aggregateEvaluationAllocationScenario,
        .{},
    );
}

fn aggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\nested(S) :- seed(k), setof(T, (group(G), setof([Y, G], parent(G, Y), T)), S).
    );
    result.deinit();
    var malformed = db.execute("broken(S) :- seed(k), setof(X, (parent(X, Y), bad([Y])), S.") catch |err| switch (err) {
        Error.InvalidSyntax => return,
        else => return err,
    };
    malformed.deinit();
    return error.ExpectedInvalidSyntax;
}

test "aggregate parser errors release all partial clause trees" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        aggregateAllocationScenario,
        .{},
    );
}

fn floatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 1e-3). measure(c, 4.0).
        \\small(X) :- measure(X, V), V < 3.
        \\setof([X, V], measure(X, V), S)?
    );
    result.deinit();
    var overflow = db.execute("measure(d, 1e400).") catch |err| switch (err) {
        Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "float parsing evaluation and overflow release every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        floatAllocationScenario,
        .{},
    );
}

fn mixedArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 0.5).
        \\shifted(X, S) :- measure(X, V), S = V + 0.5.
        \\setof([X, S], shifted(X, S), Out)?
    );
    result.deinit();
    var overflow = db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
    ) catch |err| switch (err) {
        Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "mixed arithmetic releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        mixedArithmeticAllocationScenario,
        .{},
    );
}

test "recursive list length and sum use checked integer arithmetic" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
        \\numbers([1, 2, 3]).
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\total(N) :- numbers(S), sum(S, N).
        \\numchildren(X, N)?
    );
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("total(N)?");
    try std.testing.expectEqual(@as(i64, 6), try result.query.answers.items[0].getInteger("N"));
    result.deinit();

    result = try db.execute("person(alice), 3 = 1 + 2, -2 = 1 - 3?");
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("person(alice), 4 = 1 + 2?");
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
    result.deinit();

    try std.testing.expectError(Error.NumericType, db.execute("person(alice), N = nope + 1?"));
    try std.testing.expectError(
        Error.NumericOverflow,
        db.execute("person(alice), N = 9223372036854775807 + 1?"),
    );
}

test "ground list query inputs seed recursive evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var result = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([3, 3, 3], Total)?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try result.query.answers.items[0].getInteger("Total"));
    result.deinit();

    result = try db.execute(
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\length([a, b, c], Count)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 3), try result.query.answers.items[0].getInteger("Count"));

    const value_count_before_typed_query = db.values.values.items.len;
    var query_result = try db.query(&.{input.relation("sum", &.{
        input.list(&.{ input.integer(4), input.integer(5) }),
        input.variable("total"),
    })});
    defer query_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), query_result.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try query_result.answers.items[0].getInteger("total"));
    try std.testing.expectEqual(value_count_before_typed_query, db.values.values.items.len);

    var open_result = try db.execute("sum(Input, Total)?");
    defer open_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), open_result.query.answers.items.len);
    try expectBindingValue(&db, &open_result.query.answers.items[0], "Input", "[]");
    try std.testing.expectEqual(@as(i64, 0), try open_result.query.answers.items[0].getInteger("Total"));

    var structural_result = try db.execute("Value = [a, b]?");
    defer structural_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), structural_result.query.answers.items.len);
    try expectBindingValue(&db, &structural_result.query.answers.items[0], "Value", "[a, b]");
}

test "member and collectfirst are ordinary admissible list relations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\items([a, b, c]).
        \\member(X, H!T) :- X = H.
        \\member(X, H!T) :- member(X, T).
        \\collectfirst([], []).
        \\collectfirst([H, K]!T, H!R) :- collectfirst(T, R).
        \\score(s1, 10). score(s2, 10). score(s3, 20). seed(k).
        \\bag(S) :- seed(k), setof([Score, Student], score(Student, Score), Pairs), collectfirst(Pairs, S).
        \\items(S), member(X, S)?
    );
    try std.testing.expectEqual(@as(usize, 3), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("bag(S)?");
    const value = try result.query.answers.items[0].getValue("S");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[10, 10, 20]", text);
    result.deinit();
}

test "structurally growing recursion is not admissible" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NotAdmissible, db.execute(
        \\q([X]) :- q(X).
    ));
}

test "non-recursive rules may construct structural head values" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\item(a).
        \\wrapped([X]) :- item(X).
        \\wrapped(Value)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "Value", "[a]");
}

test "structurally recursive rules retain their proven input seed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\base(a).
        \\p([a]).
        \\p(H!T) :- base(H), p(T).
        \\p(Value)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "Value", "[a]");
}

test "recursive arithmetic generators are not admissible" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(Error.NotAdmissible, direct.execute(
        \\number(0).
        \\number(N) :- number(M), N = M + 1.
    ));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(Error.NotAdmissible, indirect.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    ));
}

fn recursiveArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = db.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    ) catch |err| switch (err) {
        Error.NotAdmissible => return,
        else => return err,
    };
    result.deinit();
    return error.ExpectedNotAdmissible;
}

test "recursive arithmetic rejection is allocation safe" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        recursiveArithmeticAllocationScenario,
        .{},
    );
}

test "stratification distinguishes predicate arities" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\p(a, b). seed(k).
        \\p(S) :- seed(k), setof([X, Y], p(X, Y), S).
        \\p(S)?
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[[a, b]]");
}

test "embedding API constructs structural aggregate rules and queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("person", &.{input.atom("alice")});
    try db.addFact("person", &.{input.atom("bob")});
    try db.addFact("parent", &.{ input.atom("alice"), input.atom("bob") });

    const x = input.variable("x");
    const y = input.variable("y");
    const children = input.variable("children");
    const aggregate_body = [_]input.Goal{input.relation("parent", &.{ x, y })};
    try db.addRule(
        input.relation("children", &.{ x, children }),
        &.{
            input.relation("person", &.{x}),
            input.setof(y, &aggregate_body, children),
        },
    );

    var result = try db.query(&.{input.relation("children", &.{ x, children })});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.answers.items.len);
    for (result.answers.items) |*answer| {
        const person_name = try answer.getAtom("x");
        if (std.mem.eql(u8, person_name, "alice")) {
            try expectBindingValue(&db, answer, "children", "[bob]");
        } else {
            try std.testing.expectEqualStrings("bob", person_name);
            try expectBindingValue(&db, answer, "children", "[]");
        }
    }
}

test "typed nested setof matches source aggregate semantics" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("group", &.{input.atom("g1")});
    try db.addFact("group", &.{input.atom("g2")});
    try db.addFact("item", &.{ input.atom("g1"), input.atom("a") });

    const group = input.variable("group");
    const item = input.variable("item");
    const values = input.variable("values");
    const groups = input.variable("groups");
    const inner_body = [_]input.Goal{input.relation("item", &.{ group, item })};
    const outer_body = [_]input.Goal{
        input.relation("group", &.{group}),
        input.setof(item, &inner_body, values),
    };
    var result = try db.query(&.{input.setof(
        input.list(&.{ group, values }),
        &outer_body,
        groups,
    )});
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.answers.items[0],
        "groups",
        "[[g1, [a]], [g2, []]]",
    );
}

fn embeddedAggregateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("item", &.{input.atom("b")});
    try db.addFact("item", &.{input.atom("a")});

    const x = input.variable("x");
    const output = input.variable("output");
    const body = [_]input.Goal{input.relation("item", &.{x})};
    var result = try db.query(&.{input.setof(input.list(&.{x}), &body, output)});
    defer result.deinit();
    try expectBindingValue(&db, &result.answers.items[0], "output", "[[a], [b]]");
}

test "embedding aggregate ownership is allocation safe" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        embeddedAggregateAllocationScenario,
        .{},
    );
}

test "aggregate retraction is correct across the complete language tour" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
        \\numchildren(X, N)?
    );
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("parent(alice, bob)~");
    try std.testing.expect(result.changed);
    result.deinit();

    result = try db.execute("children(alice, S), numchildren(alice, N)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[]");
    try std.testing.expectEqual(@as(i64, 0), try result.query.answers.items[0].getInteger("N"));
}

test "public errors distinguish each aggregation failure boundary" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.InvalidSyntax, db.execute("broken([a)."));
    try std.testing.expectError(
        Error.InvalidRule,
        db.execute("bad(X, S) :- setof(Y, parent(X, Y), S)."),
    );
    try std.testing.expectError(
        Error.NotStratified,
        db.execute("seed(k). cycle(S) :- seed(k), setof(X, cycle(X), S)."),
    );
    try std.testing.expectError(
        Error.InvalidQuery,
        db.query(&.{input.add(input.variable("x"), input.variable("y"), input.integer(1))}),
    );
    try std.testing.expectError(Error.NotAdmissible, db.execute("grow([X]) :- grow(X)."));
}

test "public source interface canonicalizes the complete i64 domain" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(0). number(-0). number(+0). number(00).
        \\number(1). number(01). number(+1).
        \\number(-9223372036854775808). number(9223372036854775807).
        \\setof(X, number(X), Values)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "Values",
        "[-9223372036854775808, 0, 1, 9223372036854775807]",
    );

    try std.testing.expectError(Error.NumericOverflow, db.execute("number(9223372036854775808)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("number(-9223372036854775809)."));
}

test "quoted numeric atoms remain distinct from numeric scalars" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("value(1). value('1'). value('1.0'). setof(X, value(X), S)?");
    defer result.deinit();
    try expectBindingValue(&db, &result.query.answers.items[0], "S", "[1, '1', '1.0']");

    var inequality = try db.execute("1 = '1'?");
    defer inequality.deinit();
    try std.testing.expectEqual(@as(usize, 0), inequality.query.answers.items.len);

    var quoted_float = try db.execute("1000 = '1e3'?");
    defer quoted_float.deinit();
    try std.testing.expectEqual(@as(usize, 0), quoted_float.query.answers.items.len);

    var nested = try db.execute("nested([1]). nested(['1']). nested([1.0]). nested([1])?");
    defer nested.deinit();
    try std.testing.expectEqual(@as(usize, 1), nested.query.answers.items.len);

    var quoted_setof = try db.execute("text('2.5'). text(2.5). setof(X, text(X), S)?");
    defer quoted_setof.deinit();
    try expectBindingValue(&db, &quoted_setof.query.answers.items[0], "S", "[2.5, '2.5']");

    var arithmetic = try db.execute("01 = +0 + 1?");
    defer arithmetic.deinit();
    try std.testing.expectEqual(@as(usize, 1), arithmetic.query.answers.items.len);

    try std.testing.expectError(Error.NumericType, db.execute("value(X), X < 2?"));
}

test "float literals parse and integral values canonicalize to integers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\value(2.5). value(0.5). value(-0.025). value(1.0).
        \\value(1). value(1e0). value(1e3). value(-0.0).
        \\value(0). value(1e-999).
        \\setof(X, value(X), S)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[-0.025, 0, 0.5, 1, 2.5, 1000]",
    );

    var canonical = try db.execute("nested([1.0]). nested([1])?");
    defer canonical.deinit();
    try std.testing.expectEqual(@as(usize, 1), canonical.query.answers.items.len);

    var integral = try db.execute("value(X), X = 1e0?");
    defer integral.deinit();
    try std.testing.expectEqual(@as(usize, 1), integral.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 1),
        try integral.query.answers.items[0].getInteger("X"),
    );
}

test "float extremes format deterministically and round-trip" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\extreme(5e-324). extreme(2.2250738585072014e-308).
        \\extreme(1.7976931348623157e308). extreme(-1.7976931348623157e308).
        \\extreme(1e300).
        \\setof(X, extreme(X), S)?
    );
    defer result.deinit();
    try expectBindingValue(
        &db,
        &result.query.answers.items[0],
        "S",
        "[-1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, 1e300, " ++
            "1.7976931348623157e308]",
    );

    for ([_][]const u8{
        "extreme(5e-324)?",
        "extreme(2.2250738585072014e-308)?",
        "extreme(1.7976931348623157e308)?",
        "extreme(-1.7976931348623157e308)?",
        "extreme(1e300)?",
    }) |query| {
        var ground = try db.execute(query);
        defer ground.deinit();
        try std.testing.expectEqual(@as(usize, 1), ground.query.answers.items.len);
    }

    var formatted = try db.execute("half(0.5). half(X)?");
    defer formatted.deinit();
    const value = try formatted.query.answers.items[0].getValue("X");
    const spelled = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("0.5", spelled);
    try std.testing.expectEqual(ResultValue.Kind.float, value.kind());
    try std.testing.expectError(Error.TypeMismatch, value.getInteger());
}

test "non-finite and malformed numeric source reports stable errors" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NumericOverflow, db.execute("value(1e400)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("value(-1e400)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("value(2e308)."));

    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1e)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1e+)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1.2.3)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(12abc)."));
    try std.testing.expectError(Error.InvalidSyntax, db.execute("value(1.)."));

    var absent = try db.execute("value(X)?");
    defer absent.deinit();
    try std.testing.expectEqual(@as(usize, 0), absent.query.answers.items.len);
}

test "mixed numeric comparison and query-local float literals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var less = try db.execute("1.5 < 2?");
    defer less.deinit();
    try std.testing.expectEqual(@as(usize, 1), less.query.answers.items.len);

    var greater = try db.execute("2 < 1.5?");
    defer greater.deinit();
    try std.testing.expectEqual(@as(usize, 0), greater.query.answers.items.len);

    const scalar_count = db.scalars.values.items.len;
    var bound = try db.execute("X = 2.5?");
    const spelled = try (try bound.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    bound.deinit();
    try std.testing.expectEqual(scalar_count, db.scalars.values.items.len);
}

fn expectAnswerCount(db: *Jatalog, source: []const u8, expected: usize) !void {
    var result = try db.execute(source);
    defer result.deinit();
    try std.testing.expectEqual(expected, result.query.answers.items.len);
}

test "mixed arithmetic promotes to f64 and canonicalizes integral results" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var promoted = try db.execute("X = 1.5 + 1?");
    const spelled = try (try promoted.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    promoted.deinit();

    var integral = try db.execute("X = 1.5 + 2.5?");
    defer integral.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try integral.query.answers.items[0].getInteger("X"),
    );

    var negative = try db.execute("X = -0.5 - 0.5?");
    defer negative.deinit();
    try std.testing.expectEqual(
        @as(i64, -1),
        try negative.query.answers.items[0].getInteger("X"),
    );

    // Bound-output success, mismatch, and subtraction with both signs.
    try expectAnswerCount(&db, "4 = 1.5 + 2.5?", 1);
    try expectAnswerCount(&db, "5 = 1.5 + 2?", 0);
    try expectAnswerCount(&db, "-2.5 = -1.5 - 1?", 1);
    try expectAnswerCount(&db, "2.5 = 1 - -1.5?", 1);

    // Gradual underflow keeps exact subnormal results.
    try expectAnswerCount(
        &db,
        "1.1125369292536007e-308 = 2.2250738585072014e-308 - 1.1125369292536007e-308?",
        1,
    );
    try expectAnswerCount(&db, "0 = 5e-324 - 5e-324?", 1);

    // A mixed operation on an i64 extreme produces the rounded f64, which
    // stays a float because its integral value is outside the i64 range.
    var extreme = try db.execute("X = 9223372036854775807 + 0.5?");
    const extreme_spelled = try (try extreme.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(extreme_spelled);
    try std.testing.expectEqualStrings("9.223372036854776e18", extreme_spelled);
    extreme.deinit();

    try std.testing.expectError(Error.NumericOverflow, db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
    ));
    try std.testing.expectError(Error.NumericOverflow, db.execute(
        "N = -1.7976931348623157e308 - 1.7976931348623157e308?",
    ));
    try std.testing.expectError(Error.NumericType, db.execute("N = nope + 0.5?"));

    // Integer-only overflow behavior is unchanged by promotion.
    try std.testing.expectError(Error.NumericOverflow, db.execute(
        "N = 9223372036854775807 + 1?",
    ));
}

test "mixed equality and ordering are exact at numeric boundaries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    // Around 2^53: float literals canonicalize to their exact integer, so
    // nearby odd integers stay distinct.
    try expectAnswerCount(&db, "9007199254740993 > 9.007199254740992e15?", 1);
    try expectAnswerCount(&db, "9007199254740993 = 9.007199254740993e15?", 0);
    try expectAnswerCount(&db, "9007199254740992 = 9.007199254740992e15?", 1);

    // Both i64 limits against the adjacent representable floats.
    try expectAnswerCount(&db, "9223372036854775807 < 9.223372036854776e18?", 1);
    try expectAnswerCount(&db, "-9223372036854775808 = -9.223372036854775808e18?", 1);
    try expectAnswerCount(&db, "-9223372036854775807 > -9.223372036854776e18?", 1);

    // Adjacent representable floats around 1.
    try expectAnswerCount(&db, "1.0000000000000002 > 1?", 1);
    try expectAnswerCount(&db, "0.9999999999999999 < 1?", 1);
    try expectAnswerCount(&db, "1.0000000000000002 = 1?", 0);

    var ordered = try db.execute(
        \\near(0.9999999999999999). near(1). near(1.0000000000000002).
        \\setof(X, near(X), S)?
    );
    defer ordered.deinit();
    try expectBindingValue(
        &db,
        &ordered.query.answers.items[0],
        "S",
        "[0.9999999999999999, 1, 1.0000000000000002]",
    );
}

test "canonical numeric identity holds inside lists and nested aggregates" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var dedup = try db.execute(
        \\one(1). one(1.0). one(01). one(1e0). one('1'). one('1.0').
        \\setof(X, one(X), S)?
    );
    defer dedup.deinit();
    try expectBindingValue(&db, &dedup.query.answers.items[0], "S", "[1, '1', '1.0']");

    try expectAnswerCount(&db, "nested([1.0, 2.5]). nested([1, 2.5])?", 1);
    try expectAnswerCount(&db, "pair(cons(0.5, 1.0)). pair(cons(0.5, 1))?", 1);

    var grouped = try db.execute(
        \\kind(g). kind(h). item(g, 0.5). item(g, 1.0). item(g, 1). item(h, 2.5).
        \\grouped(Out) :- kind(g), setof([G, S], (kind(G), setof(V, item(G, V), S)), Out).
        \\grouped(Out)?
    );
    defer grouped.deinit();
    try expectBindingValue(
        &db,
        &grouped.query.answers.items[0],
        "Out",
        "[[g, [0.5, 1]], [h, [2.5]]]",
    );

    var summed = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([1, 0.5, 2.5], Total)?
    );
    defer summed.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try summed.query.answers.items[0].getInteger("Total"),
    );
}

test "source and typed mixed numeric operations produce identical answers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute("measure(a, 2.5). measure(b, 3). measure(c, 0.5).");
    setup.deinit();

    const x = input.variable("x");
    const v = input.variable("v");
    const s = input.variable("s");
    const d = input.variable("d");
    var typed = try db.query(&.{
        input.relation("measure", &.{ x, v }),
        input.compare(.less_than, v, input.integer(3)),
        input.add(s, v, input.integer(1)),
        input.subtract(d, v, input.integer(2)),
    });
    defer typed.deinit();

    var source = try db.execute("measure(X, V), V < 3, S = V + 1, D = V - 2?");
    defer source.deinit();

    try std.testing.expectEqual(@as(usize, 2), typed.answers.items.len);
    try std.testing.expectEqual(
        typed.answers.items.len,
        source.query.answers.items.len,
    );
    for (typed.answers.items, source.query.answers.items) |*typed_answer, *source_answer| {
        for ([_][2][]const u8{
            .{ "v", "V" },
            .{ "s", "S" },
            .{ "d", "D" },
        }) |names| {
            const typed_value = try (try typed_answer.getValue(names[0]))
                .formatAlloc(std.testing.allocator);
            defer std.testing.allocator.free(typed_value);
            const source_value = try (try source_answer.getValue(names[1]))
                .formatAlloc(std.testing.allocator);
            defer std.testing.allocator.free(source_value);
            try std.testing.expectEqualStrings(source_value, typed_value);
        }
    }

    const typed_shifted = try (try typed.answers.items[0].getValue("s"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(typed_shifted);
    try std.testing.expectEqualStrings("3.5", typed_shifted);
}

test "typed float descriptors canonicalize and getters never coerce" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("measure", &.{ input.atom("a"), input.float(2.5) });
    try db.addFact("measure", &.{ input.atom("b"), input.float(1.0) });
    try db.addFact("measure", &.{ input.atom("c"), input.float(-0.0) });
    try db.addFact("items", &.{input.list(&.{ input.float(0.5), input.integer(2) })});

    var fractional = try db.query(&.{
        input.relation("measure", &.{ input.atom("a"), input.variable("v") }),
    });
    defer fractional.deinit();
    const value = try fractional.answers.items[0].getValue("v");
    try std.testing.expectEqual(ResultValue.Kind.float, value.kind());
    try std.testing.expectEqual(@as(f64, 2.5), try fractional.answers.items[0].getFloat("v"));
    try std.testing.expectError(Error.TypeMismatch, fractional.answers.items[0].getInteger("v"));
    try std.testing.expectError(Error.TypeMismatch, fractional.answers.items[0].getAtom("v"));
    try std.testing.expectError(Error.UnknownVariable, fractional.answers.items[0].getFloat("missing"));

    // Integral typed floats canonicalize to integers, so the float getter
    // reports TypeMismatch and the integer getter succeeds.
    var canonical = try db.query(&.{
        input.relation("measure", &.{ input.atom("b"), input.variable("v") }),
    });
    defer canonical.deinit();
    try std.testing.expectEqual(@as(i64, 1), try canonical.answers.items[0].getInteger("v"));
    try std.testing.expectError(Error.TypeMismatch, canonical.answers.items[0].getFloat("v"));

    // Identity across construction paths: source literals match typed facts.
    try expectAnswerCount(&db, "measure(a, 2.5)?", 1);
    try expectAnswerCount(&db, "measure(b, 1)?", 1);
    try expectAnswerCount(&db, "measure(c, 0)?", 1);
    try expectAnswerCount(&db, "items([0.5, 2])?", 1);

    // Typed retraction matches a fact added from source, and vice versa.
    var added = try db.execute("measure(d, 3.5).");
    added.deinit();
    try std.testing.expect(try db.retract(&.{
        input.relation("measure", &.{ input.atom("d"), input.float(3.5) }),
    }));
    try expectAnswerCount(&db, "measure(d, X)?", 0);
}

test "non-finite typed floats fail compilation transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const scalar_count = db.scalars.values.items.len;
    const fact_count = db.facts.len();

    try std.testing.expectError(
        Error.NumericType,
        db.addFact("bad", &.{input.float(std.math.nan(f64))}),
    );
    try std.testing.expectError(
        Error.NumericOverflow,
        db.addFact("bad", &.{input.float(std.math.inf(f64))}),
    );
    try std.testing.expectError(
        Error.NumericOverflow,
        db.addFact("bad", &.{input.float(-std.math.inf(f64))}),
    );
    try std.testing.expectError(
        Error.NumericOverflow,
        db.query(&.{input.relation("kept", &.{input.float(std.math.inf(f64))})}),
    );
    const v = input.variable("v");
    try std.testing.expectError(
        Error.NumericType,
        db.addRule(
            input.relation("derived", &.{v}),
            &.{input.equal(v, input.float(std.math.nan(f64)))},
        ),
    );

    try std.testing.expectEqual(scalar_count, db.scalars.values.items.len);
    try std.testing.expectEqual(fact_count, db.facts.len());
    try std.testing.expectEqual(@as(usize, 0), db.rules.items.len);
    try expectAnswerCount(&db, "kept(1)?", 1);
    try expectAnswerCount(&db, "bad(X)?", 0);
}

fn typedFloatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("measure", &.{ input.atom("a"), input.float(2.5) });
    try db.addFact("measure", &.{ input.atom("b"), input.float(1.0) });
    var result = try db.query(&.{
        input.relation("measure", &.{ input.variable("x"), input.variable("v") }),
        input.compare(.less_than, input.variable("v"), input.integer(3)),
        input.add(input.variable("s"), input.variable("v"), input.float(0.25)),
    });
    result.deinit();
    db.addFact("bad", &.{input.float(std.math.inf(f64))}) catch |err| switch (err) {
        error.NumericOverflow => return,
        else => return err,
    };
    return error.ExpectedNumericOverflow;
}

test "typed float input releases every allocation on failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        typedFloatAllocationScenario,
        .{},
    );
}

test "integer identity is exact above 2^53 and recursive inside lists" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(9007199254740992). number(9007199254740993).
        \\nested([9007199254740992]). nested([9007199254740993]).
        \\number(X), X = 9007199254740993?
    );
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740993),
        try result.query.answers.items[0].getInteger("X"),
    );
    result.deinit();

    result = try db.execute("nested([X]), X = 9007199254740992?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740992),
        try result.query.answers.items[0].getInteger("X"),
    );
}

test "numeric comparisons reject every nonnumeric ground value kind" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). seed(X), X < 1?"));
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). [] < 1?"));
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). [1] < 2?"));
    try std.testing.expectError(Error.NumericType, db.execute("seed(ok). cons(1, 2) < 3?"));
}

test "typed descriptors cover scalars lists rules builtins negation and retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("age", &.{ input.atom("alice"), input.integer(20) });
    try db.addFact("age", &.{ input.atom("bob"), input.integer(17) });
    try db.addFact("banned", &.{input.atom("bob")});
    try db.addFact("payload", &.{input.atom("123")});

    const person = input.variable("person");
    const age = input.variable("age");
    try db.addRule(
        input.relation("adult", &.{person}),
        &.{
            input.relation("age", &.{ person, age }),
            input.compare(.greater_or_equal, age, input.integer(18)),
            input.not("banned", &.{person}),
        },
    );

    var result = try db.query(&.{input.relation("adult", &.{person})});
    try std.testing.expectEqual(@as(usize, 1), result.answers.items.len);
    try std.testing.expectEqualStrings("alice", try result.answers.items[0].getAtom("person"));
    result.deinit();

    const head = input.atom("head");
    const tail = input.atom("tail");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    try db.addFact("improper", &.{input.cons(&pair)});
    result = try db.query(&.{input.relation("improper", &.{input.variable("value")})});
    try expectBindingValue(&db, &result.answers.items[0], "value", "cons(head, tail)");
    result.deinit();

    try db.addFact("items", &.{input.list(&.{ input.integer(1), input.integer(2) })});
    const list_head = input.variable("list_head");
    const list_tail = input.variable("list_tail");
    const list_pair: input.Term.Cons = .{ .head = &list_head, .tail = &list_tail };
    try db.addRule(
        input.relation("tail", &.{list_tail}),
        &.{input.relation("items", &.{input.cons(&list_pair)})},
    );
    result = try db.query(&.{input.relation("tail", &.{input.variable("result")})});
    try expectBindingValue(&db, &result.answers.items[0], "result", "[2]");
    result.deinit();

    try std.testing.expect(try db.retract(&.{input.relation("age", &.{
        input.atom("bob"),
        input.integer(17),
    })}));
    result = try db.query(&.{input.relation("age", &.{ input.atom("bob"), input.variable("n") })});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
}

test "typed equality inequality and arithmetic use canonical integer identity" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const value = input.variable("value");
    const sum = input.variable("sum");
    var result = try db.query(&.{
        input.equal(value, input.integer(1)),
        input.notEqual(value, input.integer(2)),
        input.add(sum, value, input.integer(2)),
        input.equal(sum, input.integer(3)),
    });
    defer result.deinit();
    try std.testing.expectEqual(@as(i64, 1), try result.answers.items[0].getInteger("value"));
    try std.testing.expectEqual(@as(i64, 3), try result.answers.items[0].getInteger("sum"));

    try std.testing.expectError(
        Error.NumericOverflow,
        db.query(&.{input.add(
            sum,
            input.integer(std.math.maxInt(i64)),
            input.integer(1),
        )}),
    );
    try std.testing.expectError(
        Error.NumericType,
        db.query(&.{input.subtract(sum, input.atom("one"), input.integer(1))}),
    );

    var difference = try db.query(&.{input.subtract(
        input.variable("difference"),
        input.integer(-2),
        input.integer(3),
    )});
    try std.testing.expectEqual(
        @as(i64, -5),
        try difference.answers.items[0].getInteger("difference"),
    );
    difference.deinit();

    var mismatch = try db.query(&.{input.add(input.integer(0), input.integer(1), input.integer(2))});
    try std.testing.expectEqual(@as(usize, 0), mismatch.answers.items.len);
    mismatch.deinit();
    try std.testing.expectError(
        Error.NumericOverflow,
        db.query(&.{input.subtract(
            sum,
            input.integer(std.math.minInt(i64)),
            input.integer(1),
        )}),
    );
}

test "malformed and cyclic typed descriptors are rejected transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.atom("yes")});

    var cyclic: input.Term = undefined;
    var pair: input.Term.Cons = .{ .head = &cyclic, .tail = &cyclic };
    cyclic = input.cons(&pair);
    try std.testing.expectError(Error.InvalidTerm, db.addFact("broken", &.{cyclic}));

    var cyclic_items: [1]input.Term = undefined;
    cyclic_items[0] = input.list(&cyclic_items);
    try std.testing.expectError(Error.InvalidTerm, db.addFact("broken", &cyclic_items));

    var cyclic_goals: [1]input.Goal = undefined;
    cyclic_goals[0] = input.setof(input.integer(1), &cyclic_goals, input.variable("values"));
    try std.testing.expectError(Error.InvalidTerm, db.query(&cyclic_goals));

    try std.testing.expectError(Error.InvalidTerm, db.addFact("", &.{input.atom("value")}));
    try std.testing.expectError(
        Error.InvalidTerm,
        db.query(&.{input.relation("kept", &.{input.variable("")})}),
    );

    const shared_items = [_]input.Term{input.atom("shared")};
    const shared_list = input.list(&shared_items);
    try db.addFact("shared", &.{ shared_list, shared_list });

    var result = try db.query(&.{input.relation("kept", &.{input.variable("value")})});
    defer result.deinit();
    try std.testing.expectEqualStrings("yes", try result.answers.items[0].getAtom("value"));
}

test "query results own names scalars and structures after database destruction" {
    var db: Jatalog = .init(std.testing.allocator);
    var result = blk: {
        try db.addFact("answer", &.{input.list(&.{ input.atom("x"), input.integer(42) })});
        try db.addFact("scalars", &.{ input.atom("atom"), input.integer(7), input.float(2.5) });
        const query_result = try db.query(&.{
            input.relation("answer", &.{input.variable("value")}),
            input.relation("scalars", &.{
                input.variable("atom"),
                input.variable("integer"),
                input.variable("float"),
            }),
        });
        db.deinit();
        break :blk query_result;
    };
    defer result.deinit();

    const value = try result.answers.items[0].getValue("value");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[x, 42]", text);
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getAtom("value"));
    try std.testing.expectError(Error.UnknownVariable, result.answers.items[0].getInteger("missing"));
    try std.testing.expectEqualStrings("atom", try result.answers.items[0].getAtom("atom"));
    try std.testing.expectEqual(@as(i64, 7), try result.answers.items[0].getInteger("integer"));
    try std.testing.expectEqual(@as(f64, 2.5), try result.answers.items[0].getFloat("float"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getInteger("atom"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getAtom("integer"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getFloat("integer"));
    try std.testing.expectError(Error.TypeMismatch, result.answers.items[0].getInteger("float"));
    try std.testing.expectEqualStrings("x", try (try value.head()).getAtom());
    try std.testing.expectEqual(@as(i64, 42), try (try (try value.tail()).head()).getInteger());
}

test "novel typed queries release all query-local storage" {
    var tracking = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    var db: Jatalog = .init(tracking.allocator());
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const persistent_bytes = tracking.allocated_bytes - tracking.freed_bytes;

    for (0..100) |index| {
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "novel_{d}", .{index});
        var result = try db.query(&.{input.relation("missing", &.{input.atom(novel)})});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        const novel = @as(f64, @floatFromInt(index)) + 0.5;
        var result = try db.query(&.{input.relation("missing", &.{input.float(novel)})});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "retract_{d}", .{index});
        try std.testing.expect(!try db.retract(&.{input.relation("missing", &.{
            input.variable(novel),
        })}));
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    try db.addFact("temporary", &.{input.integer(1)});
    try std.testing.expect(try db.retract(&.{input.relation("temporary", &.{
        input.variable("warmup"),
    })}));
    const retracted_bytes = tracking.allocated_bytes - tracking.freed_bytes;
    for (0..100) |index| {
        try db.addFact("temporary", &.{input.integer(1)});
        var name_buffer: [32]u8 = undefined;
        const novel = try std.fmt.bufPrint(&name_buffer, "changed_{d}", .{index});
        try std.testing.expect(try db.retract(&.{input.relation("temporary", &.{
            input.variable(novel),
        })}));
        try std.testing.expectEqual(
            retracted_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }
}

test "source statements are atomic while prior statements remain committed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(
        Error.NumericOverflow,
        db.execute("kept(ok). rejected(9223372036854775808)."),
    );
    var result = try db.execute("kept(X)?");
    try std.testing.expectEqualStrings("ok", try result.query.answers.items[0].getAtom("X"));
    result.deinit();
    result = try db.execute("rejected(X)?");
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
}

test "typed persistent operations roll back every allocation failure point" {
    var fact_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.addFact("added", &.{input.atom("fresh")});
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |_| {
            fact_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(fact_succeeded);

    var rule_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.addRule(
            input.relation("derived", &.{input.variable("x")}),
            &.{input.relation("kept", &.{input.variable("x")})},
        );
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |_| {
            rule_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var kept = try db.query(&.{input.relation("kept", &.{input.variable("x")})});
                defer kept.deinit();
                try std.testing.expectEqual(@as(i64, 1), try kept.answers.items[0].getInteger("x"));
                var absent = try db.query(&.{input.relation("derived", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(rule_succeeded);

    var retraction_succeeded = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        try db.addFact("removed", &.{input.atom("value")});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.retract(&.{input.relation("removed", &.{input.variable("novel")})});
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |changed| {
            try std.testing.expect(changed);
            retraction_succeeded = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var present = try db.query(&.{input.relation("removed", &.{input.variable("x")})});
                defer present.deinit();
                try std.testing.expectEqualStrings("value", try present.answers.items[0].getAtom("x"));
            },
            else => return err,
        }
    }
    try std.testing.expect(retraction_succeeded);
}

test "source persistent statements roll back every allocation failure point" {
    var observed_success = false;
    for (0..512) |offset| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        try db.addFact("kept", &.{input.integer(1)});
        const persistent_bytes = failing.allocated_bytes - failing.freed_bytes;

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.execute("added(fresh).");
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |result_value| {
            var result = result_value;
            result.deinit();
            observed_success = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                try std.testing.expectEqual(
                    persistent_bytes,
                    failing.allocated_bytes - failing.freed_bytes,
                );
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(observed_success);
}
