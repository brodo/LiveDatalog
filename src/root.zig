//! A small, embeddable Datalog engine modeled after Jatalog.
//!
//! This is the public interface: the database an embedder holds, and the names
//! it needs to use one. `Jatalog` owns the engine's state and exposes the
//! operations that change it; everything those operations are built from lives
//! below and is not re-exported. Nothing inside the engine imports this file,
//! which is what keeps the dependency graph pointing one way.

const std = @import("std");
const aggregate_view = @import("aggregate_view.zig");
const auxiliary_view = @import("auxiliary_view.zig");
const compile = @import("compile.zig");
const contribution = @import("contribution.zig");
const cost_model = @import("cost_model.zig");
const database = @import("database.zig");
const errors = @import("errors.zig");
const evaluator = @import("evaluator.zig");
const fold_ir = @import("fold_ir.zig");
const folding = @import("folding.zig");
const input_compiler = @import("input_compiler.zig");
const intern_index = @import("intern_index.zig");
const inversion = @import("inversion.zig");
const list_functions = @import("list_functions.zig");
const maintenance = @import("maintenance.zig");
const materialization = @import("materialization.zig");
const monotonicity = @import("monotonicity.zig");
const parser = @import("parser.zig");
const planner = @import("planner.zig");
const program_runner = @import("program.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const scalar = @import("scalar.zig");
const schema = @import("schema.zig");
const update = @import("update.zig");
const string_table = @import("string_table.zig");
const transaction = @import("transaction.zig");
const syntax = @import("syntax.zig");
const test_support = @import("test_support.zig");
const typing = @import("typing.zig");
const validation = @import("validation.zig");
const view_catalog = @import("view_catalog.zig");
const view_selection = @import("view_selection.zig");

/// Descriptors a caller builds facts, rules, and goals out of.
pub const input = @import("input.zig");

/// Re-exported so embedders name one error set, whichever layer produced it.
pub const Error = errors.Error;
pub const ResultValue = results.ResultValue;
pub const Answer = results.Answer;
pub const QueryResult = results.QueryResult;
pub const ExecutionResult = results.ExecutionResult;
/// Re-exported so callers select a policy without importing the model.
pub const MaintenancePolicy = cost_model.MaintenancePolicy;
/// Re-exported so callers select a policy without importing the planner.
pub const PlanPolicy = planner.PlanPolicy;
pub const MaintenanceStats = database.MaintenanceStats;
pub const InternStats = database.InternStats;
/// What `Jatalog.countFacts` reports for one predicate.
pub const FactCount = struct {
    base: usize = 0,
    derived: usize = 0,
};
/// Writes an atom in canonical syntax: bare when it can be, otherwise quoted,
/// with quotes, backslashes, line breaks and tabs escaped.
pub const writeAtom = scalar.writeAtom;
/// A column type a schema declares. See "Schema" in CONTEXT.md.
pub const ColumnType = schema.ColumnType;
/// One predicate `Jatalog.predicates` lists: a name and arity the database
/// holds facts of, has rules for, or declares a schema for.
pub const PredicateInfo = struct {
    /// Borrowed from the database, and valid while it lives.
    name: []const u8,
    arity: usize,
    facts: FactCount,
    /// Whether some rule has this predicate as its head.
    has_rules: bool,
    /// Whether its name has a schema.
    typed: bool,
};
/// One column of a schema, as `Jatalog.schemaColumns` lists it.
pub const SchemaColumn = struct {
    /// Borrowed from the database; null where the schema names no column.
    name: ?[]const u8,
    type: ColumnType,
};
/// The transaction a front end stages a run of assertions in.
pub const Transaction = transaction.Transaction;

/// Where a parse or a program run failed. See `parseProgram` and `execute`.
pub const Diagnostic = parser.Diagnostic;
/// A byte range of source text.
pub const Span = parser.Span;
/// A parse result together with the arena its descriptors borrow from.
pub const Parsed = parser.Parsed;
/// A parsed program: its statements, and the span of source each came from.
pub const Program = parser.Program;
/// Parses a whole program into `input.Statement`s without a database. Run the
/// result with `Jatalog.executeStatements`.
pub const parseProgram = parser.parseProgram;
/// Parses one rule, for `addRule`, `defineView` or a fold's query program.
pub const parseRule = parser.parseRule;
/// Parses a list of goals, for `query`, `retract`, `explainQuery` or `foldQuery`.
pub const parseGoals = parser.parseGoals;

/// A view this database's catalog holds, as `defineView` handed it back.
pub const ViewId = fold_ir.ViewId;
/// Whether a folded plan may read a view's stored extension. A withheld view
/// still says what it would have contained, which is what lets a fold report
/// what it was missing.
pub const Availability = view_catalog.Availability;
/// What a folded plan's answers are worth, relative to the query's. Read the
/// documentation on `foldQuery` before deciding that one of them is enough.
pub const Guarantee = folding.Guarantee;
/// A plan a fold produced: a guarantee, and a handle on a plan the database
/// holds. See `foldQuery`.
pub const Fold = view_selection.Fold;
/// A relation a plan derives instead of reading, and whether it gets all of
/// it. See `foldReconstructions`.
pub const Reconstruction = view_selection.Reconstruction;
/// The relations one plan reconstructs. Owned by the caller.
pub const Reconstructions = view_selection.Reconstructions;
/// How many views are declared and how the plan cache has been doing.
pub const FoldStats = view_selection.FoldStats;

/// An embeddable Datalog database.
///
/// The engine's state is `state`, and every operation here is expressed in
/// terms of the layers that act on it. Those layers are not part of this
/// interface: an embedder drives the database through these methods, and a
/// statement front end additionally through `Transaction`.
pub const Jatalog = struct {
    state: database.Database,
    /// What a fold of a query against this database is allowed to read, and
    /// the plans already folded against it.
    ///
    /// The views are owned here rather than held beside a database because
    /// they cannot outlive one: their predicate names and their constants are
    /// this database's identifiers, so a catalog paired with the wrong
    /// database resolves to nothing and a catalog paired with none resolves to
    /// nothing at all. Owning them, and passing `state` on every call, is what
    /// makes that pairing impossible to get wrong, and it is also the only way
    /// a view can be declared from the borrowed descriptors this interface
    /// speaks, since compiling them needs the database that will hold them.
    views: view_selection.ViewSelection,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{
            .state = .init(allocator),
            .views = .init(allocator),
        };
    }

    pub fn deinit(self: *Jatalog) void {
        self.views.deinit();
        self.state.deinit();
        self.* = undefined;
    }

    /// A copy sharing nothing with this one, so the two can be updated
    /// independently.
    ///
    /// The views come with it, because a catalog belongs to a database and the
    /// copy is a database. The folded plans do not: a cache is not state, and
    /// the copy folds what it is asked for.
    pub fn clone(self: *const Jatalog) !Jatalog {
        var copied_state = try self.state.clone();
        errdefer copied_state.deinit();
        return .{
            .state = copied_state,
            .views = try self.views.clone(),
        };
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const input.Term) !void {
        var staging = try self.state.clone();
        defer self.state.release(&staging);
        try program_runner.addFact(&staging, input.fact(predicate, terms), null);
        self.state.commit(&staging);
    }

    pub fn addRule(self: *Jatalog, head: input.Goal, body: []const input.Goal) !void {
        const relation = switch (head) {
            .relation => |relation| relation,
            else => return errors.Error.InvalidRule,
        };
        var staging = try self.state.clone();
        defer self.state.release(&staging);
        try program_runner.addRule(&staging, input.rule(relation, body));
        self.state.commit(&staging);
    }

    /// Declares a predicate's schema: its arity and column types. See
    /// "Schema" in CONTEXT.md. Declaring the schema a predicate already has
    /// changes nothing, and any other schema for it is `SchemaConflict`. The
    /// facts and rules the database already holds must fit it —
    /// `SchemaViolation` for a fact, `IllTyped` for a rule — or nothing
    /// changes.
    pub fn declareSchema(self: *Jatalog, declared: input.Schema) !void {
        var staging = try self.state.clone();
        defer self.state.release(&staging);
        try program_runner.declareSchema(&staging, declared);
        self.state.commit(&staging);
    }

    /// Answers `goals`, listed in the order `order` asks for; an empty `order`
    /// lists them in the default answer order. See "Answer order" in
    /// CONTEXT.md.
    pub fn query(
        self: *Jatalog,
        goals: []const input.Goal,
        order: []const input.SortKey,
    ) !results.QueryResult {
        return transaction.query(&self.state, goals, order);
    }

    /// Removes the base facts `goals` resolve to, and whatever was derived
    /// from them alone. Returns whether the goals named any.
    pub fn retract(self: *Jatalog, goals: []const input.Goal) !bool {
        return transaction.retract(&self.state, goals);
    }

    /// Applies one batch of exact ground base-fact insertions and deletions
    /// with set semantics: re-inserting an existing fact and deleting an
    /// absent fact are no-ops.
    ///
    /// Against a clean materialized closure the batch may be maintained
    /// incrementally — insertions through the semi-naive delta engine,
    /// deletions through delete-and-rederive, followed by aggregate group
    /// maintenance — or the affected strata may be marked dirty and
    /// recomputed. Both produce the same database, so the choice is the cost
    /// model's unless `setMaintenancePolicy` pins it. Maintenance that
    /// reaches negation or an aggregate outside the maintainable class
    /// abandons the incremental path for a dirty-stratum rebuild.
    ///
    /// The batch commits atomically: any failure leaves the database
    /// unchanged. Returns whether the base fact set changed.
    pub fn applyChanges(
        self: *Jatalog,
        insertions: []const input.Relation,
        deletions: []const input.Relation,
    ) !bool {
        var staging = try self.state.clone();
        defer self.state.release(&staging);
        const compiled_deletions = try compileRelations(&staging, deletions);
        defer freeRelations(staging.allocator, compiled_deletions);
        const compiled_insertions = try compileRelations(&staging, insertions);
        defer freeRelations(staging.allocator, compiled_insertions);
        const changed = try update.apply(
            &staging,
            .{ .named = compiled_deletions },
            compiled_insertions,
        ) > 0;
        try materialization.verifyShadow(&staging);
        if (changed) self.state.commit(&staging);
        return changed;
    }

    /// Brings the derived closure up to date now instead of at the next
    /// query. Maintenance is otherwise lazy: an update marks the affected
    /// strata and the next evaluation repairs them. Calling this on a
    /// database without rules is a no-op and allocates nothing.
    pub fn materialize(self: *Jatalog) !void {
        var staging = try self.state.clone();
        defer self.state.release(&staging);
        try materialization.ensureMaterialized(&staging);
        try materialization.verifyShadow(&staging);
        self.state.commit(&staging);
    }

    /// Discards the derived closure and every auxiliary view and recomputes
    /// them from the current base facts and rules. This is the reference
    /// path incremental maintenance is checked against; it is always
    /// available and always correct, at the cost of full recomputation.
    pub fn rebuild(self: *Jatalog) !void {
        var staging = try self.state.clone();
        defer self.state.release(&staging);
        if (staging.closure) |*closure| {
            closure.deinit();
            staging.closure = null;
        }
        materialization.dropAuxiliaryViews(&staging);
        staging.materialization = .uninitialized;
        try materialization.ensureMaterialized(&staging);
        self.state.commit(&staging);
    }

    /// Enables or disables shadow verification. When enabled, every
    /// maintained closure is compared against a fresh rebuild from the same
    /// base facts before the change is committed, and a disagreement is
    /// reported as `MaintenanceMismatch` with the database unchanged. This
    /// roughly doubles update cost and is intended for tests and debugging.
    pub fn setShadowVerification(self: *Jatalog, enabled: bool) void {
        self.state.shadow_verification = enabled;
    }

    /// Selects how updates bring the closure up to date. The default is
    /// `.automatic`; pin `.incremental` or `.recompute` when a caller needs
    /// one specific path regardless of cost.
    pub fn setMaintenancePolicy(self: *Jatalog, policy: cost_model.MaintenancePolicy) void {
        self.state.eval.cost.policy = policy;
    }

    /// Selects the order a rule body or query is solved in. The default is
    /// `.cost_based`, which reorders goals whose bindings allow it by how many
    /// candidate facts each is expected to examine. `.source_order` keeps the
    /// order admission stored, which is what the engine did before it planned;
    /// both produce the same answers, so this is a cost choice only.
    pub fn setPlanPolicy(self: *Jatalog, policy: planner.PlanPolicy) void {
        self.state.eval.plan_policy = policy;
    }

    /// Renders the plan these goals would be solved under: the clause order,
    /// the index each goal is looked up through, and the candidates the
    /// planner expected it to examine. The caller owns the returned text.
    ///
    /// Planning reads the closure's statistics, so this materializes the
    /// database exactly as running the query would, and answers nothing.
    pub fn explainQuery(self: *Jatalog, goals: []const input.Goal) ![]u8 {
        return transaction.explain(&self.state, goals);
    }

    /// Declares a view a fold may reason about: what it is defined by, and
    /// whether its stored extension may be read.
    ///
    /// A view is *not* a rule. Nothing here is added to the program, nothing
    /// is derived, and no fact changes. What is recorded is a definition — the
    /// relations the view's tuples were computed from — so that a fold can run
    /// it backwards when those relations are no longer there. The extension
    /// itself is whatever this database happens to hold under the view's name
    /// and arity; declaring a view says the definition is true of it.
    ///
    /// The definition is checked for safety exactly as a rule would be, and
    /// rejected with `InvalidRule` if it fails. Descriptors are borrowed for
    /// the call.
    pub fn defineView(
        self: *Jatalog,
        head: input.Relation,
        body: []const input.Goal,
        availability: Availability,
    ) !ViewId {
        return self.views.define(&self.state, head, body, availability);
    }

    /// Declares a predicate this database maintains as a view, taking the
    /// definition from the rule that derives it.
    ///
    /// This is the bridge from the maintenance project to the folding one: a
    /// materialized predicate already has a stored extension and the engine
    /// already keeps it up to date, so the only thing missing was a statement
    /// of what it remembers. A predicate no single rule defines is refused
    /// with `UndefinedView` — a view has one definition, and a predicate with
    /// several has no one rule to invert.
    ///
    /// A published definition is the rule's, so it stops being true if the
    /// rules change. The rule generation is recorded and a later fold reports
    /// `StaleViewDefinition` rather than reasoning from a definition the
    /// database has moved on from.
    pub fn publishView(
        self: *Jatalog,
        predicate: []const u8,
        arity: usize,
        availability: Availability,
    ) !ViewId {
        return self.views.publish(&self.state, predicate, arity, availability);
    }

    /// Withdraws or restores a view's stored extension. The definition stays
    /// known either way, which is what lets a fold say that the view it needed
    /// was withheld rather than that the relation was unreachable.
    pub fn setViewAvailability(self: *Jatalog, id: ViewId, availability: Availability) void {
        self.views.setAvailability(id, availability);
    }

    /// Declares that a folded plan may read this base relation directly.
    ///
    /// The honest default is that it may not: a fold exists because the
    /// original relations are gone, and a plan that helped itself to them
    /// would prove nothing. Declaring one is how a caller that still has some
    /// of its data asks for a hybrid plan — folding where it must, reading
    /// where it can. It never costs answers, because a relation read directly
    /// is the relation, and a reconstruction is at best that.
    pub fn declareBaseAvailable(self: *Jatalog, predicate: []const u8, arity: usize) !void {
        return self.views.declareBaseAvailable(&self.state, predicate, arity);
    }

    /// Rewrites a query to run against the declared views, and says what the
    /// rewrite is worth. **This answers nothing.**
    ///
    /// That is the distinction this whole interface turns on. `query` returns
    /// the answers to what was asked. A fold returns a *plan* — a different
    /// program, over different relations — together with a statement of how
    /// its answers relate to the query's, and it is the caller who decides
    /// whether that statement is good enough to act on. Chapter 6 of the
    /// dissertation this follows shows the unrestricted case producing plans
    /// whose answers are not the query's, which is why a fold cannot be
    /// applied silently the way join planning is.
    ///
    /// The guarantee is one of four:
    ///
    /// - `equivalent`: the same answers as the query over any database. Only
    ///   returned when nothing had to be reconstructed, because everything the
    ///   query reads was available already.
    /// - `maximally_contained`: every answer it returns is one the query
    ///   returns, and no plan over these views returns more. A view remembers
    ///   less than the relations behind it, so this is the best a fold that
    ///   reconstructed anything can promise — unless a canonical aggregate
    ///   view made the reconstruction exact, which `foldReconstructions`
    ///   reports per relation.
    /// - `contained`: every answer it returns is one the query returns, with
    ///   nothing claimed about how many. Eliminating the terms a
    ///   reconstruction could not name dropped rule instances.
    /// - `unsupported`: there is no plan. Not an empty one — none. Ask
    ///   `explainFold` for the preconditions that were not met.
    ///
    /// `rules` are the rules the query defines its own predicates by, and are
    /// part of the question rather than of the program: a folded plan is the
    /// query's rules together with the inverse rules of the views, and a
    /// recursive query over a relation only a non-recursive view remembers is
    /// the case the method exists for.
    ///
    /// Folding twice with the same views and the same question returns the
    /// same plan without folding again.
    pub fn foldQuery(
        self: *Jatalog,
        goals: []const input.Goal,
        rules: []const input.Rule,
    ) !Fold {
        return self.views.fold(&self.state, goals, rules);
    }

    /// Runs a folded plan and returns its answers.
    ///
    /// The plan runs against a copy of this database holding exactly what the
    /// catalog said was available — every readable view's stored extension,
    /// plus the base relations the policy declared — with everything else
    /// removed: the other facts, the database's own rules, and the derived
    /// closure. That is not a precaution, it is the contract. A plan is built
    /// to answer from what remains once the original relations are gone, and
    /// running it somewhere that still holds them would let it read exactly
    /// what it was built to do without.
    ///
    /// The copy never joins this database, so a plan's reconstructed relations
    /// are not here afterwards. It is kept beside the plan, so asking the same
    /// question again only solves the goals, until a base fact changes what
    /// the plan reads; a fact changes no plan, so a `Fold` handle stays live
    /// across one. See `ViewSelection.answer`.
    ///
    /// Answers list the caller's own variables under the caller's own names,
    /// even when another caller's question folded the plan first, and nothing
    /// the plan introduced for itself. `order` lists them as `query` would: the order
    /// is presentation, so it is not part of the fold and the same plan
    /// serves every order.
    pub fn answerFolded(self: *Jatalog, fold: Fold, order: []const input.SortKey) !results.QueryResult {
        return self.views.answer(&self.state, fold, order);
    }

    /// Renders a fold: its guarantee, then either the plan and every
    /// transformation that produced it, or the preconditions it could not
    /// meet. The caller owns the returned text.
    ///
    /// A plan's goals are not the caller's goals, so this is the only way to
    /// read one. Generated names are spelled so that they cannot be mistaken
    /// for a program somebody wrote, and a variable prints its identity as
    /// well as its spelling, because a plan combining a query with the inverse
    /// of a view has two variables of one name by construction.
    pub fn explainFold(self: *Jatalog, fold: Fold) ![]u8 {
        return self.views.explain(&self.state, fold);
    }

    /// Which relations the plan derives instead of reading, and how much of
    /// each it gets.
    ///
    /// This is what makes `maximally_contained` mean something. On its own the
    /// guarantee says the plan answers no more than the query and no less than
    /// any other plan over these views; it does not say *where* the loss is.
    /// Each relation here is a place a query's answers could have gone
    /// missing — unless it is `exact`, in which case a canonical aggregate
    /// view of it was read and Lemma 6.4.2 makes the reconstruction the
    /// relation itself. A plan whose reconstructions are all exact is
    /// maximally contained and loses nothing.
    pub fn foldReconstructions(self: *Jatalog, fold: Fold) !Reconstructions {
        return self.views.reconstructions(&self.state, fold);
    }

    /// How many views are declared and how the plan cache has been doing.
    pub fn foldStats(self: *const Jatalog) FoldStats {
        return self.views.stats();
    }

    /// Discards every folded plan, and every reconstruction one of them was
    /// keeping. Folding and running again reproduces both; this is for a
    /// caller that would rather have the memory.
    ///
    /// It is now the memory control of this interface rather than a
    /// convenience. A cache entry used to be a plan; it can now be a plan plus
    /// a copy of every readable extension and its closure, and while the
    /// number of those is bounded, their size is whatever the database is.
    pub fn clearPlanCache(self: *Jatalog) void {
        self.views.clear();
    }

    /// Candidate facts this database's evaluator has examined — the cost
    /// model's unit, and the same number on every machine, which is what
    /// makes it worth reporting beside a time.
    ///
    /// Counted for work done on this database's behalf, including on the
    /// staging copies it evaluates on and then discards. A counter that went
    /// with the copy would report nothing for a query, since a query is
    /// exactly that: evaluation on a copy nobody keeps.
    pub fn evaluationWork(self: *const Jatalog) u64 {
        return self.state.eval.cost.work;
    }

    /// Records how the maintained views are classified and how much work
    /// incremental maintenance has done. A view whose head retains every
    /// outer variable is self-maintainable in the sense of Chapter 5: its
    /// tuple belongs to exactly one group, so an update decides the tuple
    /// without consulting other derivations. A projected view needs the
    /// auxiliary view's derivation counts, and recomputing an aggregate
    /// member set always consults the closure.
    pub fn maintenanceStats(self: *const Jatalog) MaintenanceStats {
        return self.state.maintenanceStats();
    }

    /// What interning has cost this database, in comparisons rather than in
    /// time. Every fact loaded and every value derived goes through the value
    /// tables, and a comparison count is the same number on every machine,
    /// which is what makes a change to how they are searched reportable.
    pub fn internStats(self: *const Jatalog) InternStats {
        return self.state.internStats();
    }

    /// How many facts `predicate` of `arity` holds: its base facts, and the
    /// facts only its rules derive. A base fact a rule also derives counts
    /// once, as base. Brings the closure up to date first, as a query would.
    pub fn countFacts(self: *Jatalog, predicate: []const u8, arity: usize) !FactCount {
        if (self.state.materialization != .clean) try self.materialize();
        const name = self.state.strings.get(predicate) orelse return .{};
        const key: relation_store.PredicateKey = .{ .name = name, .arity = arity };
        const base = (try self.state.facts.predicateEntries(key)).len;
        const all = (try self.state.closureStore().predicateEntries(key)).len;
        return .{ .base = base, .derived = all - base };
    }

    /// Every predicate the database knows of, ordered by name and then arity:
    /// those with facts, base or derived, those some rule has as its head, and
    /// those a schema declares, even with no facts. Brings the closure up to
    /// date first, as a query would. The caller frees the slice; the names
    /// are the database's.
    pub fn predicates(self: *Jatalog, allocator: std.mem.Allocator) ![]PredicateInfo {
        if (self.state.materialization != .clean) try self.materialize();
        var keys: std.array_hash_map.Auto(relation_store.PredicateKey, bool) = .empty;
        defer keys.deinit(allocator);
        const closure = self.state.closureStore();
        for (0..closure.len()) |index| {
            const fact = closure.factAt(index);
            const slot = try keys.getOrPut(allocator, .{ .name = fact.predicate, .arity = fact.terms.len });
            if (!slot.found_existing) slot.value_ptr.* = false;
        }
        for (self.state.eval.rules.items) |rule|
            try keys.put(allocator, .{ .name = rule.head.predicate, .arity = rule.head.terms.len }, true);
        for (self.state.schemas.schemas.keys(), self.state.schemas.schemas.values()) |name, declared| {
            const slot = try keys.getOrPut(allocator, .{ .name = name, .arity = declared.columns.len });
            if (!slot.found_existing) slot.value_ptr.* = false;
        }

        const listed = try allocator.alloc(PredicateInfo, keys.count());
        errdefer allocator.free(listed);
        for (keys.keys(), keys.values(), listed) |key, has_rules, *info| {
            const base = (try self.state.facts.predicateEntries(key)).len;
            const all = (try closure.predicateEntries(key)).len;
            info.* = .{
                .name = self.state.strings.resolve(key.name),
                .arity = key.arity,
                .facts = .{ .base = base, .derived = all - base },
                .has_rules = has_rules,
                .typed = self.state.schemas.get(key.name) != null,
            };
        }
        std.mem.sort(PredicateInfo, listed, {}, struct {
            fn lessThan(_: void, a: PredicateInfo, b: PredicateInfo) bool {
                return switch (std.mem.order(u8, a.name, b.name)) {
                    .lt => true,
                    .gt => false,
                    .eq => a.arity < b.arity,
                };
            }
        }.lessThan);
        return listed;
    }

    /// The facts of `predicate` of `arity` asserted rather than only derived,
    /// in the order they were asserted, each listing its arguments under its
    /// 1-based position: `1`, `2`, ... A fact a rule also derives is listed,
    /// since it is asserted all the same.
    pub fn baseFacts(self: *Jatalog, predicate: []const u8, arity: usize) !results.QueryResult {
        var names_arena: std.heap.ArenaAllocator = .init(self.state.allocator);
        defer names_arena.deinit();
        const names = try names_arena.allocator().alloc([]const u8, arity);
        for (names, 1..) |*name, position|
            name.* = try std.fmt.allocPrint(names_arena.allocator(), "{d}", .{position});
        const name = self.state.strings.get(predicate) orelse {
            var empty: results.QueryResult = .{ .allocator = self.state.allocator };
            errdefer empty.deinit();
            for (names) |position| try empty.appendVariable(position);
            return empty;
        };
        return self.state.copyFactsResult(&self.state.facts, .{ .name = name, .arity = arity }, names);
    }

    /// The columns of `predicate`'s schema, or null when it has none. The
    /// caller frees the slice; the names are the database's.
    pub fn schemaColumns(
        self: *const Jatalog,
        allocator: std.mem.Allocator,
        predicate: []const u8,
    ) !?[]SchemaColumn {
        const name = self.state.strings.get(predicate) orelse return null;
        const declared = self.state.schemas.get(name) orelse return null;
        const columns = try allocator.alloc(SchemaColumn, declared.columns.len);
        for (declared.columns, declared.names, columns) |column_type, column_name, *column| column.* = .{
            .name = if (column_name) |id| self.state.strings.resolve(id) else null,
            .type = column_type,
        };
        return columns;
    }

    /// Parses `source` and runs it, returning the last statement's result.
    ///
    /// The whole program is parsed before any of it runs, so a syntax error
    /// anywhere leaves the database untouched. A statement that fails when it
    /// runs keeps every statement before it and none of itself. On failure,
    /// `diagnostic` says where: the offending token for a syntax error, the
    /// failing statement for any other.
    pub fn execute(
        self: *Jatalog,
        source: []const u8,
        diagnostic: ?*Diagnostic,
    ) !results.ExecutionResult {
        const parsed = try parser.parseProgram(self.state.allocator, source, diagnostic);
        defer parsed.deinit();
        return program_runner.execute(
            &self.state,
            parsed.value.statements,
            .{ .text = source, .spans = parsed.value.spans },
            diagnostic,
            null,
        );
    }

    /// Runs statements — parsed by `parseProgram` or built by hand — in
    /// order, returning the last one's result. Consecutive facts and rules
    /// share one transaction, which is what makes loading many facts cheap; a
    /// statement that fails keeps every statement before it and none of
    /// itself, and `diagnostic` names it by index.
    ///
    /// The facts the statements assert are `contributor`'s, as though each
    /// were added to its contribution in turn; null asserts them for the
    /// direct contributor, as `execute` does. See "Contributor" in
    /// CONTEXT.md. Everything else runs as it would without one: rules and
    /// schemas belong to the program, and a retraction takes its facts from
    /// every contributor at its place in the order, so `p(a)~. p(a).` leaves
    /// `p(a)` asserted by `contributor` alone.
    pub fn executeStatements(
        self: *Jatalog,
        statements: []const input.Statement,
        diagnostic: ?*Diagnostic,
        contributor: ?[]const u8,
    ) !results.ExecutionResult {
        return program_runner.execute(&self.state, statements, null, diagnostic, contributor);
    }

    /// Replaces everything `contributor` asserts with `facts`, and returns
    /// whether the set of base facts changed.
    ///
    /// A base fact is present while at least one contributor asserts it —
    /// a named one like `contributor`, or the direct contributor that
    /// `addFact`, `applyChanges` and statements run without a contributor
    /// assert for — so only the facts this makes present or absent change
    /// anything, and only they take the update path `applyChanges` takes,
    /// maintained or recomputed as the cost model decides. Sameness is the
    /// engine's scalar identity: `1` and `1.0` are one fact, and so are a
    /// cons chain and the list it spells, whoever asserts each. An empty
    /// `facts` withdraws the contributor. See "Contributor" in CONTEXT.md.
    ///
    /// Only base facts are contributed; rules and schemas belong to the
    /// program. Deleting a fact — by `applyChanges` or a retraction — takes
    /// it from every contributor, and it comes back only when one asserts it
    /// again.
    ///
    /// Commits atomically: a contribution holding a fact that is not ground
    /// (`InvalidFact`), or one its schema rejects (`SchemaViolation`), fails
    /// whole and leaves both the facts and every contribution as they were.
    pub fn setContribution(
        self: *Jatalog,
        contributor: []const u8,
        facts: []const input.Relation,
    ) !bool {
        return transaction.contribute(&self.state, contributor, facts);
    }
};

/// Compiles a batch's relation descriptors into expressions the update path
/// applies. Compilation belongs here rather than below because it is what
/// turns *descriptors* — this front end's input — into the engine's syntax;
/// the source front end arrives with expressions already.
fn compileRelations(db: *database.Database, relations: []const input.Relation) ![]syntax.Expr {
    const compiled = try db.allocator.alloc(syntax.Expr, relations.len);
    var built: usize = 0;
    errdefer {
        for (compiled[0..built]) |expression| syntax.freeExpr(db.allocator, expression);
        db.allocator.free(compiled);
    }
    for (relations, compiled) |relation, *slot| {
        slot.* = try compile.compileRelation(db, relation.predicate, relation.terms, false);
        built += 1;
    }
    return compiled;
}

fn freeRelations(allocator: std.mem.Allocator, compiled: []syntax.Expr) void {
    for (compiled) |expression| syntax.freeExpr(allocator, expression);
    allocator.free(compiled);
}

test {
    // Zig contributes a file's tests only once something has referenced the
    // file, and the interface above does not reference every module it is
    // built from. Naming them here is what puts their tests in this build; a
    // module left out still compiles and still passes, it just stops being
    // tested.
    _ = aggregate_view;
    _ = auxiliary_view;
    _ = compile;
    _ = contribution;
    _ = cost_model;
    _ = database;
    _ = evaluator;
    _ = fold_ir;
    _ = folding;
    _ = input_compiler;
    _ = intern_index;
    _ = inversion;
    _ = list_functions;
    _ = maintenance;
    _ = monotonicity;
    _ = parser;
    _ = program_runner;
    _ = relation_store;
    _ = scalar;
    _ = schema;
    _ = string_table;
    _ = syntax;
    _ = test_support;
    _ = transaction;
    _ = typing;
    _ = validation;
    _ = view_catalog;
    _ = view_selection;
}

/// Runs one source query and asserts how many answers it produces. This one
/// assertion needs `execute`, so unlike the rest of `test_support` it cannot
/// live below the interface.
fn expectAnswerCount(db: *Jatalog, source: []const u8, expected: usize) !void {
    var result = try db.execute(source, null);
    defer result.deinit();
    try std.testing.expectEqual(expected, result.query.answers.items.len);
}

test "string table maps strings to stable ids and back" {
    var table: string_table.StringTable = .init(std.testing.allocator);
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
    , null);
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
    , null);
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();
    result = try db.execute("person(bob)~", null);
    defer result.deinit();
    try std.testing.expect(result.changed);
}

test "negative recursion is rejected" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NotStratified, db.execute(
        \\p(X) :- q(X).
        \\q(X) :- not p(X), seed(X).
    , null));
}

test "repeated queries reuse the persistent closure without expansion" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try std.testing.expectEqual(@as(usize, 0), db.state.eval.expansions);

    try expectAnswerCount(&db, "path(a, X)?", 3);
    const after_first = db.state.eval.expansions;
    try std.testing.expect(after_first > 0);
    try std.testing.expect(db.state.materialization == .clean);

    for (0..3) |_| try expectAnswerCount(&db, "path(a, X)?", 3);
    var typed = try db.query(&.{input.relation("path", &.{
        input.atom("a"),
        input.variable("target"),
    })}, &.{});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 3), typed.answers.items.len);
    try std.testing.expectEqual(after_first, db.state.eval.expansions);
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
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "numchildren(alice, 1)?", 1);
    try std.testing.expect(db.state.materialization == .clean);

    var staging = try db.clone();
    defer staging.deinit();
    var reference = try staging.state.facts.clone();
    defer reference.deinit();
    try staging.state.eval.expandNaive(&reference);
    try std.testing.expectEqual(reference.len(), db.state.closure.?.len());
    for (0..reference.len()) |index|
        try std.testing.expect(try db.state.closure.?.contains(reference.factAt(index)));
}

test "base updates and rule additions rebuild the closure correctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // A base insertion marks the closure dirty and the next query repairs it.
    var inserted = try db.execute("edge(c, d).", null);
    inserted.deinit();
    try std.testing.expect(db.state.materialization == .dirty_from_stratum);
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try std.testing.expect(db.state.materialization == .clean);

    // Retraction removes derived consequences through the dirty rebuild.
    var retracted = try db.execute("edge(a, b)~", null);
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
    var extended = try db.execute("reach(X) :- path(b, X).", null);
    extended.deinit();
    try std.testing.expect(db.state.materialization == .dirty_from_stratum);
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
    , null);
    setup.deinit();
    // First materialization runs both strata.
    try expectAnswerCount(&db, "note(a)?", 1);
    const full_build = db.state.eval.expansions;
    try std.testing.expectEqual(@as(usize, 2), full_build);

    // Only the negation stratum reads flag, so its update rebuilds one level.
    var flagged = try db.execute("flag(c).", null);
    flagged.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 1, db.state.eval.expansions);

    // An edge update dirties the recursive stratum and rebuilds both levels.
    var edged = try db.execute("edge(c, d).", null);
    edged.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 3, db.state.eval.expansions);
}

test "a database without rules allocates no derived machinery" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    try expectAnswerCount(&db, "kept(1)?", 1);
    var typed = try db.query(&.{input.relation("kept", &.{input.variable("n")})}, &.{});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 1), typed.answers.items.len);
    try std.testing.expect(db.state.closure == null);
    try std.testing.expect(db.state.materialization == .uninitialized);
    try std.testing.expect(db.state.eval.analysis == null);
    try std.testing.expectEqual(@as(usize, 0), db.state.eval.expansions);
}

fn materializationAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    , null);
    setup.deinit();
    var first = try db.execute("summary(S)?", null);
    first.deinit();
    var inserted = try db.execute("edge(c, d).", null);
    inserted.deinit();
    var second = try db.execute("path(a, d)?", null);
    second.deinit();
    var retracted = try db.execute("edge(c, d)~", null);
    retracted.deinit();
    var third = try db.execute("path(a, d)?", null);
    defer third.deinit();
    if (third.query.answers.items.len != 0) return error.UnexpectedAnswer;
}

test "materialization lifecycle releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(materializationAllocationScenario);
}

test "materialize rebuild and stats form the explicit maintenance API" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\group(g). member(g, m1).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    , null);
    setup.deinit();

    // Maintenance is lazy until asked: nothing is materialized yet.
    try std.testing.expect(db.state.closure == null);
    try std.testing.expectEqual(@as(usize, 0), db.maintenanceStats().closure_facts);

    try db.materialize();
    try std.testing.expect(db.state.materialization == .clean);
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
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_materialize.closure_facts, db.maintenanceStats().closure_facts);
    try test_support.expectClosureMatchesRebuild(&db.state);
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // The single-statement entry points keep working alongside the batch
    // API. Pattern retraction is not a subset of it: it deletes every base
    // fact matching a goal, which exact-fact batch deletion cannot express.
    try db.addFact("edge", &.{ input.atom("c"), input.atom("d") });
    try expectAnswerCount(&db, "path(a, d)?", 1);
    var executed = try db.execute("edge(d, e).", null);
    executed.deinit();
    try expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try expectAnswerCount(&db, "path(a, e)?", 0);

    // Retraction takes the same incremental deletion path as a batch, so
    // the closure stays clean and this materialize is a no-op.
    try std.testing.expect(db.state.materialization == .clean);
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
    var collected = try db.execute("collected(g, S)?", null);
    try test_support.expectBindingValue(&collected.query.answers.items[0], "S", "[m1, m2]");
    collected.deinit();
    try std.testing.expect(db.maintenanceStats().maintained_groups > before_member.maintained_groups);
    try test_support.expectClosureMatchesRebuild(&db.state);

    const before_delete = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }));
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try std.testing.expect(db.maintenanceStats().removed_facts > before_delete.removed_facts);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Every update category is accounted for by one of the documented
    // paths: incremental propagation, delete-and-rederive, or rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.propagated_facts > 0);
    try std.testing.expect(stats.removed_facts > 0);
    try std.testing.expectEqual(@as(usize, 1), stats.self_maintainable_views);
}

test "lists round trip through queries and nested terms unify structurally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\nested([a, [b, []]]).
        \\nested(X)?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "[a, [b, []]]");
}

test "repeated variables inside structures enforce equality" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\pair([a, [a]]). pair([a, [b]]).
        \\pair([X, [X]])?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try result.query.answers.items[0].getAtom("X"));
}

test "facts reject variables at every structural depth" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidFact, db.execute("bad([a, X]).", null));
    try std.testing.expectError(errors.Error.InvalidFact, db.execute("bad(a!T).", null));

    var result = try db.execute("improper(a!b). improper(X)?", null);
    defer result.deinit();
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "cons(a, b)");
}

test "ground values have a deterministic structural total order" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\value(z). value(a). value('1'). value(-2). value(10). value(2). value([]).
        \\value([-1]). value(cons(a, z)). value([a]). value([a, b]).
        \\setof(X, value(X), S)?
    , null);
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "S",
        "[-2, 2, 10, '1', a, z, [], [-1], cons(a, z), [a], [a, b]]",
    );
}

test "correlated aggregate clauses parse and validate without evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\person(alice). parent(alice, bob). passed(bob).
        \\children(X, S) :- person(X), setof([Y, X], (parent(X, Y), passed(Y)), S).
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.state.eval.rules.items.len);
    try std.testing.expect(db.state.eval.rules.items[0].body[0] == .relational);
    const aggregate = db.state.eval.rules.items[0].body[1].aggregate;
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
    , null);
    defer result.deinit();
    const body = db.state.eval.rules.items[0].body;
    try std.testing.expect(body[0] == .relational);
    try std.testing.expect(body[1] == .builtin);
    try std.testing.expect(body[2] == .aggregate);
    try std.testing.expect(body[3] == .negated);
}

test "aggregate safety rejects unbound correlations and escaping locals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidRule, db.execute(
        "bad(X, S) :- setof(Y, parent(X, Y), S).",
        null,
    ));
    try std.testing.expectError(errors.Error.InvalidRule, db.execute(
        "bad(Y, S) :- seed(k), setof(Y, parent(X, Y), S).",
        null,
    ));
}

test "aggregate output binds head variables and aggregate locals stay local" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\all_parents(S) :- seed(k), setof([X, Y], parent(X, Y), S).
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.state.eval.rules.items.len);
}

test "nested aggregates are represented directly and validate recursively" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\grouped(S) :- seed(k), setof(T, (group(G), setof(Y, parent(G, Y), T)), S).
    , null);
    defer result.deinit();
    const outer = db.state.eval.rules.items[0].body[1].aggregate;
    try std.testing.expectEqual(@as(usize, 2), outer.body.len);
    try std.testing.expect(outer.body[1] == .aggregate);
}

test "direct and indirect recursion through aggregation are rejected" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(errors.Error.NotStratified, direct.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, p(X), S).
    , null));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(errors.Error.NotStratified, indirect.execute(
        \\seed(k).
        \\p(S) :- seed(k), setof(X, q(X), S).
        \\q(X) :- p(X).
    , null));
}

test "positive recursion may complete below an aggregate stratum" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). seed(k).
        \\reachable(X, Y) :- edge(X, Y).
        \\reachable(X, Y) :- reachable(X, Z), edge(Z, Y).
        \\all_reachable(S) :- seed(k), setof([X, Y], reachable(X, Y), S).
    , null);
    defer result.deinit();
    var levels = try db.state.eval.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const reachable: relation_store.PredicateKey = .{ .name = db.state.strings.get("reachable").?, .arity = 2 };
    const all_reachable: relation_store.PredicateKey = .{ .name = db.state.strings.get("all_reachable").?, .arity = 1 };
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
    , null);
    defer result.deinit();
    var levels = try db.state.eval.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const allowed: relation_store.PredicateKey = .{ .name = db.state.strings.get("allowed").?, .arity = 1 };
    const summary: relation_store.PredicateKey = .{ .name = db.state.strings.get("summary").?, .arity = 1 };
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
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    for (result.query.answers.items) |*answer| {
        const person = try answer.getAtom("X");
        if (std.mem.eql(u8, person, "alice")) {
            try test_support.expectBindingValue(answer, "S", "[bob, carol]");
        } else if (std.mem.eql(u8, person, "bob")) {
            try test_support.expectBindingValue(answer, "S", "[]");
        } else return error.UnexpectedPerson;
    }
}

test "setof evaluates directly in queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("item(c). item(a). setof(X, item(X), S)?", null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a, c]");
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
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(
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
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "All", "[a, b]");
    try test_support.expectBindingValue(&result.query.answers.items[0], "Groups", "[[g1, [a, b]], [g2, []]]");
}

test "setof recomputes after retraction" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k). item(b). item(a).
        \\items(S) :- seed(k), setof(X, item(X), S).
        \\item(b)~
    , null);
    result.deinit();
    result = try db.execute("items(S)?", null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a]");
}

test "setof ordering is independent of insertion and rule order" {
    var first: Jatalog = .init(std.testing.allocator);
    defer first.deinit();
    var first_result = try first.execute(
        \\seed(k). base(c). base(a). base(b).
        \\value(X) :- base(X).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\values(S)?
    , null);
    defer first_result.deinit();

    var second: Jatalog = .init(std.testing.allocator);
    defer second.deinit();
    var second_result = try second.execute(
        \\base(b). base(c). base(a). seed(k).
        \\values(S) :- seed(k), setof(X, value(X), S).
        \\value(X) :- base(X).
        \\values(S)?
    , null);
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
    , null);
    defer result.deinit();
}

test "aggregate evaluation releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(aggregateEvaluationAllocationScenario);
}

fn floatAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 1e-3). measure(c, 4.0).
        \\small(X) :- measure(X, V), V < 3.
        \\setof([X, V], measure(X, V), S)?
    , null);
    result.deinit();
    var overflow = db.execute("measure(d, 1e400).", null) catch |err| switch (err) {
        errors.Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "float parsing evaluation and overflow release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(floatAllocationScenario);
}

fn mixedArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = try db.execute(
        \\measure(a, 2.5). measure(b, 0.5).
        \\shifted(X, S) :- measure(X, V), S = V + 0.5.
        \\setof([X, S], shifted(X, S), Out)?
    , null);
    result.deinit();
    var overflow = db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
        null,
    ) catch |err| switch (err) {
        errors.Error.NumericOverflow => return,
        else => return err,
    };
    overflow.deinit();
    return error.ExpectedNumericOverflow;
}

test "mixed arithmetic releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(mixedArithmeticAllocationScenario);
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
    , null);
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("total(N)?", null);
    try std.testing.expectEqual(@as(i64, 6), try result.query.answers.items[0].getInteger("N"));
    result.deinit();

    result = try db.execute("person(alice), 3 = 1 + 2, -2 = 1 - 3?", null);
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("person(alice), 4 = 1 + 2?", null);
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
    result.deinit();

    try std.testing.expectError(errors.Error.NumericType, db.execute("person(alice), N = nope + 1?", null));
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.execute("person(alice), N = 9223372036854775807 + 1?", null),
    );
}

test "ground list query inputs seed recursive evaluation" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var result = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([3, 3, 3], Total)?
    , null);
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try result.query.answers.items[0].getInteger("Total"));
    result.deinit();

    result = try db.execute(
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\length([a, b, c], Count)?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(@as(i64, 3), try result.query.answers.items[0].getInteger("Count"));

    const value_count_before_typed_query = db.state.eval.values.values.items.len;
    var query_result = try db.query(&.{input.relation("sum", &.{
        input.list(&.{ input.integer(4), input.integer(5) }),
        input.variable("total"),
    })}, &.{});
    defer query_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), query_result.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try query_result.answers.items[0].getInteger("total"));
    try std.testing.expectEqual(value_count_before_typed_query, db.state.eval.values.values.items.len);

    var open_result = try db.execute("sum(Input, Total)?", null);
    defer open_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), open_result.query.answers.items.len);
    try test_support.expectBindingValue(&open_result.query.answers.items[0], "Input", "[]");
    try std.testing.expectEqual(@as(i64, 0), try open_result.query.answers.items[0].getInteger("Total"));

    var structural_result = try db.execute("Value = [a, b]?", null);
    defer structural_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), structural_result.query.answers.items.len);
    try test_support.expectBindingValue(&structural_result.query.answers.items[0], "Value", "[a, b]");
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
    , null);
    try std.testing.expectEqual(@as(usize, 3), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("bag(S)?", null);
    const value = try result.query.answers.items[0].getValue("S");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[10, 10, 20]", text);
    result.deinit();
}

test "structurally growing recursion is not admissible" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.NotAdmissible, db.execute(
        \\q([X]) :- q(X).
    , null));
}

test "non-recursive rules may construct structural head values" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\item(a).
        \\wrapped([X]) :- item(X).
        \\wrapped(Value)?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "Value", "[a]");
}

test "structurally recursive rules retain their proven input seed" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\base(a).
        \\p([a]).
        \\p(H!T) :- base(H), p(T).
        \\p(Value)?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "Value", "[a]");
}

test "recursive arithmetic generators are not admissible" {
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    try std.testing.expectError(errors.Error.NotAdmissible, direct.execute(
        \\number(0).
        \\number(N) :- number(M), N = M + 1.
    , null));

    var indirect: Jatalog = .init(std.testing.allocator);
    defer indirect.deinit();
    try std.testing.expectError(errors.Error.NotAdmissible, indirect.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    , null));
}

fn recursiveArithmeticAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var result = db.execute(
        \\left(0).
        \\left(N) :- right(N).
        \\right(N) :- left(M), N = M + 1.
    , null) catch |err| switch (err) {
        errors.Error.NotAdmissible => return,
        else => return err,
    };
    result.deinit();
    return error.ExpectedNotAdmissible;
}

test "recursive arithmetic rejection is allocation safe" {
    try test_support.expectEveryAllocationFailureReleased(recursiveArithmeticAllocationScenario);
}

test "recursive list construction outside a proven self-call is not admissible" {
    // Each program here used to be admitted; the first three then never
    // finished a query, because the cycle builds a longer list every round.
    const rejected = [_][]const u8{
        // A head that builds a list, reached back through another predicate.
        \\q([]).
        \\p(a!L) :- q(L).
        \\q(L) :- p(L).
        ,
        // The same growth, built by an equality instead of the head.
        \\q([]).
        \\p(X) :- q(L), X = a!L.
        \\q(L) :- p(L).
        ,
        // A direct self-call the decrease proof does not cover.
        \\p([]).
        \\p(X) :- p(L), X = a!L.
        ,
        // Mutual recursion that consumes tails would terminate, but nothing
        // proves a decrease across two predicates, so it is refused too.
        \\even([]).
        \\even(H!T) :- odd(T).
        \\odd(H!T) :- even(T).
    };
    for (rejected) |program| {
        var db: Jatalog = .init(std.testing.allocator);
        defer db.deinit();
        try std.testing.expectError(errors.Error.NotAdmissible, db.execute(program, null));
    }

    // Mutual recursion that builds nothing is ordinary Datalog and stays.
    var plain: Jatalog = .init(std.testing.allocator);
    defer plain.deinit();
    var result = try plain.execute(
        \\start(n0). step(n0, n1). step(n1, n2).
        \\even(X) :- start(X).
        \\even(X) :- odd(Y), step(Y, X).
        \\odd(X) :- even(Y), step(Y, X).
        \\even(X)?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
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

    var result = try db.query(&.{input.relation("children", &.{ x, children })}, &.{});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 2), result.answers.items.len);
    for (result.answers.items) |*answer| {
        const person_name = try answer.getAtom("x");
        if (std.mem.eql(u8, person_name, "alice")) {
            try test_support.expectBindingValue(answer, "children", "[bob]");
        } else {
            try std.testing.expectEqualStrings("bob", person_name);
            try test_support.expectBindingValue(answer, "children", "[]");
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
    )}, &.{});
    defer result.deinit();
    try test_support.expectBindingValue(
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
    var result = try db.query(&.{input.setof(input.list(&.{x}), &body, output)}, &.{});
    defer result.deinit();
    try test_support.expectBindingValue(&result.answers.items[0], "output", "[[a], [b]]");
}

test "embedding aggregate ownership is allocation safe" {
    try test_support.expectEveryAllocationFailureReleased(embeddedAggregateAllocationScenario);
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
    , null);
    try std.testing.expectEqual(@as(usize, 2), result.query.answers.items.len);
    result.deinit();

    result = try db.execute("parent(alice, bob)~", null);
    try std.testing.expect(result.changed);
    result.deinit();

    result = try db.execute("children(alice, S), numchildren(alice, N)?", null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[]");
    try std.testing.expectEqual(@as(i64, 0), try result.query.answers.items[0].getInteger("N"));
}

test "public errors distinguish each aggregation failure boundary" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expectError(errors.Error.InvalidSyntax, db.execute("broken([a).", null));
    try std.testing.expectError(
        errors.Error.InvalidRule,
        db.execute("bad(X, S) :- setof(Y, parent(X, Y), S).", null),
    );
    try std.testing.expectError(
        errors.Error.NotStratified,
        db.execute("seed(k). cycle(S) :- seed(k), setof(X, cycle(X), S).", null),
    );
    try std.testing.expectError(
        errors.Error.InvalidQuery,
        db.query(&.{input.add(input.variable("x"), input.variable("y"), input.integer(1))}, &.{}),
    );
    try std.testing.expectError(errors.Error.NotAdmissible, db.execute("grow([X]) :- grow(X).", null));
}

test "public source interface canonicalizes the complete i64 domain" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(0). number(-0). number(+0). number(00).
        \\number(1). number(01). number(+1).
        \\number(-9223372036854775808). number(9223372036854775807).
        \\setof(X, number(X), Values)?
    , null);
    defer result.deinit();
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "Values",
        "[-9223372036854775808, 0, 1, 9223372036854775807]",
    );

    try std.testing.expectError(errors.Error.NumericOverflow, db.execute("number(9223372036854775808).", null));
    try std.testing.expectError(errors.Error.NumericOverflow, db.execute("number(-9223372036854775809).", null));
}

test "mixed numeric comparison and query-local float literals" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var less = try db.execute("1.5 < 2?", null);
    defer less.deinit();
    try std.testing.expectEqual(@as(usize, 1), less.query.answers.items.len);

    var greater = try db.execute("2 < 1.5?", null);
    defer greater.deinit();
    try std.testing.expectEqual(@as(usize, 0), greater.query.answers.items.len);

    const scalar_count = db.state.eval.scalars.values.items.len;
    var bound = try db.execute("X = 2.5?", null);
    const spelled = try (try bound.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    bound.deinit();
    try std.testing.expectEqual(scalar_count, db.state.eval.scalars.values.items.len);
}

test "mixed arithmetic promotes to f64 and canonicalizes integral results" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();

    var promoted = try db.execute("X = 1.5 + 1?", null);
    const spelled = try (try promoted.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    promoted.deinit();

    var integral = try db.execute("X = 1.5 + 2.5?", null);
    defer integral.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try integral.query.answers.items[0].getInteger("X"),
    );

    var negative = try db.execute("X = -0.5 - 0.5?", null);
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
    var extreme = try db.execute("X = 9223372036854775807 + 0.5?", null);
    const extreme_spelled = try (try extreme.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(extreme_spelled);
    try std.testing.expectEqualStrings("9.223372036854776e18", extreme_spelled);
    extreme.deinit();

    try std.testing.expectError(errors.Error.NumericOverflow, db.execute(
        "N = 1.7976931348623157e308 + 1.7976931348623157e308?",
        null,
    ));
    try std.testing.expectError(errors.Error.NumericOverflow, db.execute(
        "N = -1.7976931348623157e308 - 1.7976931348623157e308?",
        null,
    ));
    try std.testing.expectError(errors.Error.NumericType, db.execute("N = nope + 0.5?", null));

    // Integer-only overflow behavior is unchanged by promotion.
    try std.testing.expectError(errors.Error.NumericOverflow, db.execute(
        "N = 9223372036854775807 + 1?",
        null,
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
    , null);
    defer ordered.deinit();
    try test_support.expectBindingValue(
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
    , null);
    defer dedup.deinit();
    try test_support.expectBindingValue(&dedup.query.answers.items[0], "S", "[1, '1', '1.0']");

    try expectAnswerCount(&db, "nested([1.0, 2.5]). nested([1, 2.5])?", 1);
    try expectAnswerCount(&db, "pair(cons(0.5, 1.0)). pair(cons(0.5, 1))?", 1);

    var grouped = try db.execute(
        \\kind(g). kind(h). item(g, 0.5). item(g, 1.0). item(g, 1). item(h, 2.5).
        \\grouped(Out) :- kind(g), setof([G, S], (kind(G), setof(V, item(G, V), S)), Out).
        \\grouped(Out)?
    , null);
    defer grouped.deinit();
    try test_support.expectBindingValue(
        &grouped.query.answers.items[0],
        "Out",
        "[[g, [0.5, 1]], [h, [2.5]]]",
    );

    var summed = try db.execute(
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\sum([1, 0.5, 2.5], Total)?
    , null);
    defer summed.deinit();
    try std.testing.expectEqual(
        @as(i64, 4),
        try summed.query.answers.items[0].getInteger("Total"),
    );
}

test "source and typed mixed numeric operations produce identical answers" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute("measure(a, 2.5). measure(b, 3). measure(c, 0.5).", null);
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
    }, &.{});
    defer typed.deinit();

    var source = try db.execute("measure(X, V), V < 3, S = V + 1, D = V - 2?", null);
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
    }, &.{});
    defer fractional.deinit();
    const value = try fractional.answers.items[0].getValue("v");
    try std.testing.expectEqual(results.ResultValue.Kind.float, value.kind());
    try std.testing.expectEqual(@as(f64, 2.5), try fractional.answers.items[0].getFloat("v"));
    try std.testing.expectError(errors.Error.TypeMismatch, fractional.answers.items[0].getInteger("v"));
    try std.testing.expectError(errors.Error.TypeMismatch, fractional.answers.items[0].getAtom("v"));
    try std.testing.expectError(errors.Error.UnknownVariable, fractional.answers.items[0].getFloat("missing"));

    // Integral typed floats canonicalize to integers, so the float getter
    // reports TypeMismatch and the integer getter succeeds.
    var canonical = try db.query(&.{
        input.relation("measure", &.{ input.atom("b"), input.variable("v") }),
    }, &.{});
    defer canonical.deinit();
    try std.testing.expectEqual(@as(i64, 1), try canonical.answers.items[0].getInteger("v"));
    try std.testing.expectError(errors.Error.TypeMismatch, canonical.answers.items[0].getFloat("v"));

    // Identity across construction paths: source literals match typed facts.
    try expectAnswerCount(&db, "measure(a, 2.5)?", 1);
    try expectAnswerCount(&db, "measure(b, 1)?", 1);
    try expectAnswerCount(&db, "measure(c, 0)?", 1);
    try expectAnswerCount(&db, "items([0.5, 2])?", 1);

    // Typed retraction matches a fact added from source, and vice versa.
    var added = try db.execute("measure(d, 3.5).", null);
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
    const scalar_count = db.state.eval.scalars.values.items.len;
    const fact_count = db.state.facts.len();

    try std.testing.expectError(
        errors.Error.NumericType,
        db.addFact("bad", &.{input.float(std.math.nan(f64))}),
    );
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.addFact("bad", &.{input.float(std.math.inf(f64))}),
    );
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.addFact("bad", &.{input.float(-std.math.inf(f64))}),
    );
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.query(&.{input.relation("kept", &.{input.float(std.math.inf(f64))})}, &.{}),
    );
    const v = input.variable("v");
    try std.testing.expectError(
        errors.Error.NumericType,
        db.addRule(
            input.relation("derived", &.{v}),
            &.{input.equal(v, input.float(std.math.nan(f64)))},
        ),
    );

    try std.testing.expectEqual(scalar_count, db.state.eval.scalars.values.items.len);
    try std.testing.expectEqual(fact_count, db.state.facts.len());
    try std.testing.expectEqual(@as(usize, 0), db.state.eval.rules.items.len);
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
    }, &.{});
    result.deinit();
    db.addFact("bad", &.{input.float(std.math.inf(f64))}) catch |err| switch (err) {
        error.NumericOverflow => return,
        else => return err,
    };
    return error.ExpectedNumericOverflow;
}

test "typed float input releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(typedFloatAllocationScenario);
}

test "integer identity is exact above 2^53 and recursive inside lists" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\number(9007199254740992). number(9007199254740993).
        \\nested([9007199254740992]). nested([9007199254740993]).
        \\number(X), X = 9007199254740993?
    , null);
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try std.testing.expectEqual(
        @as(i64, 9007199254740993),
        try result.query.answers.items[0].getInteger("X"),
    );
    result.deinit();

    result = try db.execute("nested([X]), X = 9007199254740992?", null);
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
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). seed(X), X < 1?", null));
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). [] < 1?", null));
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). [1] < 2?", null));
    try std.testing.expectError(errors.Error.NumericType, db.execute("seed(ok). cons(1, 2) < 3?", null));
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

    var result = try db.query(&.{input.relation("adult", &.{person})}, &.{});
    try std.testing.expectEqual(@as(usize, 1), result.answers.items.len);
    try std.testing.expectEqualStrings("alice", try result.answers.items[0].getAtom("person"));
    result.deinit();

    const head = input.atom("head");
    const tail = input.atom("tail");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    try db.addFact("improper", &.{input.cons(&pair)});
    result = try db.query(&.{input.relation("improper", &.{input.variable("value")})}, &.{});
    try test_support.expectBindingValue(&result.answers.items[0], "value", "cons(head, tail)");
    result.deinit();

    try db.addFact("items", &.{input.list(&.{ input.integer(1), input.integer(2) })});
    const list_head = input.variable("list_head");
    const list_tail = input.variable("list_tail");
    const list_pair: input.Term.Cons = .{ .head = &list_head, .tail = &list_tail };
    try db.addRule(
        input.relation("tail", &.{list_tail}),
        &.{input.relation("items", &.{input.cons(&list_pair)})},
    );
    result = try db.query(&.{input.relation("tail", &.{input.variable("result")})}, &.{});
    try test_support.expectBindingValue(&result.answers.items[0], "result", "[2]");
    result.deinit();

    try std.testing.expect(try db.retract(&.{input.relation("age", &.{
        input.atom("bob"),
        input.integer(17),
    })}));
    result = try db.query(&.{input.relation("age", &.{ input.atom("bob"), input.variable("n") })}, &.{});
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
    }, &.{});
    defer result.deinit();
    try std.testing.expectEqual(@as(i64, 1), try result.answers.items[0].getInteger("value"));
    try std.testing.expectEqual(@as(i64, 3), try result.answers.items[0].getInteger("sum"));

    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.query(&.{input.add(
            sum,
            input.integer(std.math.maxInt(i64)),
            input.integer(1),
        )}, &.{}),
    );
    try std.testing.expectError(
        errors.Error.NumericType,
        db.query(&.{input.subtract(sum, input.atom("one"), input.integer(1))}, &.{}),
    );

    var difference = try db.query(&.{input.subtract(
        input.variable("difference"),
        input.integer(-2),
        input.integer(3),
    )}, &.{});
    try std.testing.expectEqual(
        @as(i64, -5),
        try difference.answers.items[0].getInteger("difference"),
    );
    difference.deinit();

    var mismatch = try db.query(&.{input.add(input.integer(0), input.integer(1), input.integer(2))}, &.{});
    try std.testing.expectEqual(@as(usize, 0), mismatch.answers.items.len);
    mismatch.deinit();
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.query(&.{input.subtract(
            sum,
            input.integer(std.math.minInt(i64)),
            input.integer(1),
        )}, &.{}),
    );
}

test "malformed and cyclic typed descriptors are rejected transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.atom("yes")});

    var cyclic: input.Term = undefined;
    var pair: input.Term.Cons = .{ .head = &cyclic, .tail = &cyclic };
    cyclic = input.cons(&pair);
    try std.testing.expectError(errors.Error.InvalidTerm, db.addFact("broken", &.{cyclic}));

    var cyclic_items: [1]input.Term = undefined;
    cyclic_items[0] = input.list(&cyclic_items);
    try std.testing.expectError(errors.Error.InvalidTerm, db.addFact("broken", &cyclic_items));

    var cyclic_goals: [1]input.Goal = undefined;
    cyclic_goals[0] = input.setof(input.integer(1), &cyclic_goals, input.variable("values"));
    try std.testing.expectError(errors.Error.InvalidTerm, db.query(&cyclic_goals, &.{}));

    try std.testing.expectError(errors.Error.InvalidTerm, db.addFact("", &.{input.atom("value")}));
    try std.testing.expectError(
        errors.Error.InvalidTerm,
        db.query(&.{input.relation("kept", &.{input.variable("")})}, &.{}),
    );

    const shared_items = [_]input.Term{input.atom("shared")};
    const shared_list = input.list(&shared_items);
    try db.addFact("shared", &.{ shared_list, shared_list });

    var result = try db.query(&.{input.relation("kept", &.{input.variable("value")})}, &.{});
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
        }, &.{});
        db.deinit();
        break :blk query_result;
    };
    defer result.deinit();

    const value = try result.answers.items[0].getValue("value");
    const text = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("[x, 42]", text);
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getAtom("value"));
    try std.testing.expectError(errors.Error.UnknownVariable, result.answers.items[0].getInteger("missing"));
    try std.testing.expectEqualStrings("atom", try result.answers.items[0].getAtom("atom"));
    try std.testing.expectEqual(@as(i64, 7), try result.answers.items[0].getInteger("integer"));
    try std.testing.expectEqual(@as(f64, 2.5), try result.answers.items[0].getFloat("float"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getInteger("atom"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getAtom("integer"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getFloat("integer"));
    try std.testing.expectError(errors.Error.TypeMismatch, result.answers.items[0].getInteger("float"));
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
        var result = try db.query(&.{input.relation("missing", &.{input.atom(novel)})}, &.{});
        try std.testing.expectEqual(@as(usize, 0), result.answers.items.len);
        result.deinit();
        try std.testing.expectEqual(
            persistent_bytes,
            tracking.allocated_bytes - tracking.freed_bytes,
        );
    }

    for (0..100) |index| {
        const novel = @as(f64, @floatFromInt(index)) + 0.5;
        var result = try db.query(&.{input.relation("missing", &.{input.float(novel)})}, &.{});
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
        errors.Error.InvalidFact,
        db.execute("kept(ok). rejected(X).", null),
    );
    var result = try db.execute("kept(X)?", null);
    try std.testing.expectEqualStrings("ok", try result.query.answers.items[0].getAtom("X"));
    result.deinit();
    result = try db.execute("rejected(X)?", null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.query.answers.items.len);
}

test "a literal that does not fit is a parse error, so nothing runs" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var diagnostic: Diagnostic = .{};
    try std.testing.expectError(
        errors.Error.NumericOverflow,
        db.execute("kept(ok). rejected(9223372036854775808).", &diagnostic),
    );
    try std.testing.expectEqual(@as(?usize, 1), diagnostic.statement);
    try std.testing.expectEqual(@as(u32, 20), diagnostic.column);
    try expectAnswerCount(&db, "kept(X)?", 0);
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
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})}, &.{});
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
                var kept = try db.query(&.{input.relation("kept", &.{input.variable("x")})}, &.{});
                defer kept.deinit();
                try std.testing.expectEqual(@as(i64, 1), try kept.answers.items[0].getInteger("x"));
                var absent = try db.query(&.{input.relation("derived", &.{input.variable("x")})}, &.{});
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
                var present = try db.query(&.{input.relation("removed", &.{input.variable("x")})}, &.{});
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
        const operation = db.execute("added(fresh).", null);
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
                var absent = try db.query(&.{input.relation("added", &.{input.variable("x")})}, &.{});
                defer absent.deinit();
                try std.testing.expectEqual(@as(usize, 0), absent.answers.items.len);
            },
            else => return err,
        }
    }
    try std.testing.expect(observed_success);
}

/// Which of `n0 … n{count-1}` the database holds under `node/1`, as one bit
/// per index. Enough to say exactly which statements of a program reached the
/// database and which did not.
fn nodesPresent(db: *Jatalog, count: usize) !u32 {
    var answers = try db.query(&.{input.relation("node", &.{input.variable("X")})}, &.{});
    defer answers.deinit();
    var present: u32 = 0;
    var buffer: [8]u8 = undefined;
    for (answers.answers.items) |*answer| {
        const atom = try answer.getAtom("X");
        for (0..count) |index| {
            const name = try std.fmt.bufPrint(&buffer, "n{d}", .{index});
            if (std.mem.eql(u8, atom, name)) present |= @as(u32, 1) << @intCast(index);
        }
    }
    return present;
}

/// Renders a query's answers one per line, so two databases can be compared
/// by what they answer.
fn renderAnswers(allocator: std.mem.Allocator, result: *const QueryResult) ![]u8 {
    var output: std.Io.Writer.Allocating = .init(allocator);
    defer output.deinit();
    for (result.answers.items) |answer| {
        for (answer.bindings.items) |binding| {
            try output.writer.print("{s}=", .{binding.name});
            try binding.value.write(&output.writer);
            try output.writer.writeByte(' ');
        }
        try output.writer.writeByte('\n');
    }
    return output.toOwnedSlice();
}

test "running parsed statements is running the source" {
    // `execute` is `parseProgram` followed by `executeStatements`; this checks
    // the two spellings leave identical databases, down to what was interned.
    const programs = [_][]const u8{
        \\edge(a, b). edge(b, c). edge(c, d).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\edge(b, c)~
        \\path(a, X)?
        ,
        \\item(g1, 3). item(g1, 1.5). item(g2, 7). item(g2, -2e0).
        \\tag(g1, 'x'). tag(g2, [a, b]).
        \\group(g1). group(g2).
        \\members(G, S) :- group(G), setof([V, W], (item(G, V), tag(G, W)), S).
        \\small(G, V) :- item(G, V), not V >= 2, not V = 7.
        \\members(G, S), setof(V, small(G, V), T)?
        ,
        \\n(1). n(2). total(S) :- setof(X, n(X), L), sum(L, S).
        \\sum([], 0).
        \\sum(H!T, N) :- sum(T, M), N = M + H.
        \\total(S)?
    };
    for (programs) |source| {
        var executed: Jatalog = .init(std.testing.allocator);
        defer executed.deinit();
        var from_source = try executed.execute(source, null);
        defer from_source.deinit();

        var stepped: Jatalog = .init(std.testing.allocator);
        defer stepped.deinit();
        const parsed = try parseProgram(std.testing.allocator, source, null);
        defer parsed.deinit();
        var from_statements = try stepped.executeStatements(parsed.value.statements, null, null);
        defer from_statements.deinit();

        const expected = try renderAnswers(std.testing.allocator, &from_source.query);
        defer std.testing.allocator.free(expected);
        const actual = try renderAnswers(std.testing.allocator, &from_statements.query);
        defer std.testing.allocator.free(actual);
        try std.testing.expect(expected.len > 0);
        try std.testing.expectEqualStrings(expected, actual);
        try std.testing.expectEqual(executed.state.facts.len(), stepped.state.facts.len());
        try std.testing.expectEqualDeep(executed.internStats(), stepped.internStats());
    }
}

test "contributions are made through setContribution and statements, and a clone keeps them" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try std.testing.expect(try db.setContribution("a.dl", &.{
        input.fact("p", &.{input.atom("a")}),
        input.fact("p", &.{input.integer(1)}),
    }));
    const statements = try parseProgram(std.testing.allocator, "p(1.0). p(b).", null);
    defer statements.deinit();
    var loaded = try db.executeStatements(statements.value.statements, null, "b.dl");
    loaded.deinit();

    var copy = try db.clone();
    defer copy.deinit();
    try std.testing.expect(try db.setContribution("a.dl", &.{}));
    try expectAnswerCount(&db, "p(X)?", 2);
    // The copy's `a.dl` still asserts `a`, and withdrawing it there is what
    // takes `a` out of the copy.
    try expectAnswerCount(&copy, "p(X)?", 3);
    try std.testing.expect(try copy.setContribution("a.dl", &.{}));
    try expectAnswerCount(&copy, "p(X)?", 2);
}

test "parsed rules and goals feed the descriptor interface" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const facts = try parseProgram(std.testing.allocator, "edge(a, b). edge(b, c).", null);
    defer facts.deinit();
    var loaded = try db.executeStatements(facts.value.statements, null, null);
    loaded.deinit();

    const rules = [_][]const u8{
        "reach(X, Y) :- edge(X, Y)",
        "reach(X, Z) :- edge(X, Y), reach(Y, Z).",
    };
    for (rules) |text| {
        const rule = try parseRule(std.testing.allocator, text, null);
        defer rule.deinit();
        try db.addRule(.{ .relation = rule.value.head }, rule.value.body);
    }
    const goals = try parseGoals(std.testing.allocator, "reach(a, X), X != b?", null);
    defer goals.deinit();
    var result = try db.query(goals.value, &.{});
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.answers.items.len);
    try std.testing.expectEqualStrings("c", try result.answers.items[0].getAtom("X"));
}

test "a failing statement is named whether it was parsed or built by hand" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var diagnostic: Diagnostic = .{};
    try std.testing.expectError(Error.NotStratified, db.execute(
        \\p(a).
        \\q(X) :- p(X), not r(X).
        \\  r(X) :- q(X).
    , &diagnostic));
    try std.testing.expectEqual(@as(?usize, 2), diagnostic.statement);
    try std.testing.expectEqual(@as(u32, 3), diagnostic.line);
    try std.testing.expectEqual(@as(u32, 3), diagnostic.column);
    try std.testing.expectEqual(@as(?[]const u8, null), diagnostic.expected);

    try std.testing.expectError(Error.InvalidSyntax, db.execute("p(b).\np(c", &diagnostic));
    try std.testing.expectEqual(@as(?usize, 1), diagnostic.statement);
    try std.testing.expectEqual(@as(u32, 2), diagnostic.line);
    try std.testing.expectEqual(@as(u32, 4), diagnostic.column);
    try std.testing.expectEqualStrings("','", diagnostic.expected.?);

    const statements = [_]input.Statement{
        .{ .fact = input.fact("p", &.{input.atom("d")}) },
        .{ .fact = input.fact("p", &.{input.variable("X")}) },
    };
    diagnostic = .{};
    try std.testing.expectError(Error.InvalidFact, db.executeStatements(&statements, &diagnostic, null));
    try std.testing.expectEqual(@as(?usize, 1), diagnostic.statement);
    try std.testing.expectEqual(@as(?Span, null), diagnostic.span);
    try expectAnswerCount(&db, "p(X)?", 2);
}

test "a source program commits and rolls back one statement at a time" {
    // Assertions, a query and a retraction interleaved. Each statement either
    // lands completely or not at all, whatever its neighbours are, and the
    // ones that share a transaction are no exception.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var program = try db.execute(
        \\node(n0). node(n1).
        \\reachable(X) :- node(X).
        \\reachable(n0)?
        \\node(n2). node(n3).
        \\node(n1) ~
        \\node(n4).
    , null);
    program.deinit();
    try std.testing.expectEqual(@as(u32, 0b11101), try nodesPresent(&db, 5));
    var derived = try db.query(&.{input.relation("reachable", &.{input.variable("X")})}, &.{});
    defer derived.deinit();
    try std.testing.expectEqual(@as(usize, 4), derived.answers.items.len);

    // A statement that fails part-way through a run of assertions keeps every
    // earlier statement and none of its own — including what it interned.
    // What a rolled-back statement interned is observable rather than merely
    // untidy: a novel ground structure joins the seed set of admissible
    // structural recursion, so a value left behind can derive facts.
    var partial: Jatalog = .init(std.testing.allocator);
    defer partial.deinit();
    var prefix = try partial.execute("node(n0). node(n1).", null);
    prefix.deinit();
    const before = partial.internStats();
    try std.testing.expectError(
        Error.InvalidFact,
        partial.execute("node(n2). oops(n9, [n8, n7], X). node(n3).", null),
    );
    try std.testing.expectEqual(@as(u32, 0b111), try nodesPresent(&partial, 5));
    const after = partial.internStats();
    // Exactly `n2`, and nothing the failing statement named.
    try std.testing.expectEqual(before.scalar_entries + 1, after.scalar_entries);
    try std.testing.expectEqual(before.value_entries + 1, after.value_entries);

    // A syntax error is found before anything runs, so even the statements
    // ahead of it leave nothing behind.
    try std.testing.expectError(
        Error.InvalidSyntax,
        partial.execute("node(n3). oops(n9, [n8, n7] . node(n4).", null),
    );
    try std.testing.expectEqual(@as(u32, 0b111), try nodesPresent(&partial, 5));
    try std.testing.expectEqual(after.scalar_entries, partial.internStats().scalar_entries);
}

test "an allocation failure leaves a source program's statements as a prefix" {
    // The guarantee under the one failure that can strike anywhere: whatever
    // the database ends up holding, it is the result of some number of the
    // program's leading statements, never a partial one and never a later one
    // without an earlier one.
    var observed_success = false;
    for (0..512) |offset| {
        var failing: std.testing.FailingAllocator = .init(std.testing.allocator, .{});
        var db: Jatalog = .init(failing.allocator());
        defer db.deinit();
        var seed = try db.execute("node(n0).", null);
        seed.deinit();

        failing.fail_index = failing.alloc_index + offset;
        const operation = db.execute("node(n1). node(n2). node(n3). node(n4).", null);
        failing.fail_index = std.math.maxInt(usize);
        if (operation) |value| {
            var result = value;
            result.deinit();
            try std.testing.expectEqual(@as(u32, 0b11111), try nodesPresent(&db, 5));
            observed_success = true;
            break;
        } else |err| switch (err) {
            error.OutOfMemory => {
                const present = try nodesPresent(&db, 5);
                // A prefix is exactly a run of low bits: the statement that
                // failed stopped the program, so no later one can have run.
                try std.testing.expect(present & (present + 1) == 0);
                try std.testing.expect(present >= 0b1);
            },
            else => return err,
        }
    }
    try std.testing.expect(observed_success);
}

// ---------------------------------------------------------------------------
// Evaluation, maintenance and aggregate tests.
//
// These build their database from source, so they need the parser and the
// interface above it — which is above the modules they cover. They live here
// rather than in `evaluator.zig`, `maintenance.zig` and `aggregate_view.zig`
// so that those modules never import the interface built on top of them.
// ---------------------------------------------------------------------------

test "semi-naive and naive closures agree across rule classes" {
    // Non-recursive joins.
    var joins: Jatalog = .init(std.testing.allocator);
    defer joins.deinit();
    var joins_setup = try joins.execute(
        \\parent(a, b). parent(b, c). parent(c, d).
        \\grand(X, Z) :- parent(X, Y), parent(Y, Z).
    , null);
    joins_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&joins.state);

    // Direct recursion.
    var direct: Jatalog = .init(std.testing.allocator);
    defer direct.deinit();
    var direct_setup = try direct.execute(
        \\edge(a, b). edge(b, c). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    direct_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&direct.state);

    // Mutual recursion across two predicates in one stratum.
    var mutual: Jatalog = .init(std.testing.allocator);
    defer mutual.deinit();
    var mutual_setup = try mutual.execute(
        \\start(n0). step(n0, n1). step(n1, n2). step(n2, n3). step(n3, n4).
        \\even(X) :- start(X).
        \\even(X) :- odd(Y), step(Y, X).
        \\odd(X) :- even(Y), step(Y, X).
    , null);
    mutual_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&mutual.state);

    // Seeded structural recursion feeding a same-stratum consumer.
    var structural: Jatalog = .init(std.testing.allocator);
    defer structural.deinit();
    var structural_setup = try structural.execute(
        \\person(alice). person(bob). parent(alice, bob).
        \\children(X, S) :- person(X), setof(Y, parent(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\numchildren(X, N) :- children(X, S), length(S, N).
    , null);
    structural_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&structural.state);

    // Stratified negation above a recursive stratum.
    var negated: Jatalog = .init(std.testing.allocator);
    defer negated.deinit();
    var negated_setup = try negated.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\reachable(X) :- edge(a, X).
        \\reachable(X) :- reachable(Y), edge(Y, X).
        \\isolated(X) :- node(X), not reachable(X).
    , null);
    negated_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&negated.state);

    // Aggregation over a recursive relation.
    var aggregated: Jatalog = .init(std.testing.allocator);
    defer aggregated.deinit();
    var aggregated_setup = try aggregated.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\summary(S) :- edge(a, b), setof([X, Y], path(X, Y), S).
    , null);
    aggregated_setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&aggregated.state);
}

test "multiple recursive body occurrences miss no derivations" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(n1, n2). edge(n2, n3). edge(n3, n4). edge(n4, n5).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- path(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&db.state);

    // The doubling rule needs delta joins on both occurrences: n1 to n5
    // only exists by combining two derived paths.
    try expectAnswerCount(&db, "path(n1, n5)?", 1);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
}

test "duplicate derivations create no duplicate facts or endless rounds" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // A diamond plus a cycle derives many facts through multiple proofs.
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, d). edge(c, d). edge(d, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try test_support.expectSemiNaiveMatchesNaive(&db.state);
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
    , null);
    setup.deinit();

    // Bound-position patterns over atoms.
    try expectAnswerCount(&db, "edge(a, X)?", 2);
    try expectAnswerCount(&db, "edge(X, Y)?", 3);
    try expectAnswerCount(&db, "edge(a, b)?", 1);
    try expectAnswerCount(&db, "edge(c, X)?", 0);

    // Answers arrive in the default answer order, not fact insertion order.
    var ordered = try db.execute("edge(X, c)?", null);
    defer ordered.deinit();
    try std.testing.expectEqual(@as(usize, 2), ordered.query.answers.items.len);
    try std.testing.expectEqualStrings("a", try ordered.query.answers.items[0].getAtom("X"));
    try std.testing.expectEqualStrings("b", try ordered.query.answers.items[1].getAtom("X"));

    // Bound structural values: proper, nested, improper, and empty lists.
    var proper = try db.execute("holds([1, 2], X)?", null);
    defer proper.deinit();
    try std.testing.expectEqualStrings("a", try proper.query.answers.items[0].getAtom("X"));
    var nested = try db.execute("holds([1, [2, 3]], X)?", null);
    defer nested.deinit();
    try std.testing.expectEqualStrings("b", try nested.query.answers.items[0].getAtom("X"));
    var improper = try db.execute("holds(cons(1, 2), X)?", null);
    defer improper.deinit();
    try std.testing.expectEqualStrings("c", try improper.query.answers.items[0].getAtom("X"));
    var empty = try db.execute("holds([], X)?", null);
    defer empty.deinit();
    try std.testing.expectEqualStrings("d", try empty.query.answers.items[0].getAtom("X"));

    // A structural value bound through the second position.
    var reverse = try db.execute("holds(X, c)?", null);
    defer reverse.deinit();
    try test_support.expectBindingValue(&reverse.query.answers.items[0], "X", "cons(1, 2)");

    // A partially ground structure is unbound for indexing and still unifies.
    try expectAnswerCount(&db, "holds([1, T], X)?", 2);

    // One predicate name at two arities never shares matches.
    try expectAnswerCount(&db, "p(X)?", 1);
    try expectAnswerCount(&db, "p(X, Y)?", 1);

    // Retraction through the same lookup interface removes exactly one fact.
    var retract = try db.execute("edge(a, X)~", null);
    defer retract.deinit();
    try expectAnswerCount(&db, "edge(X, Y)?", 1);
    try expectAnswerCount(&db, "edge(b, c)?", 1);
}

test "stratification distinguishes predicate arities" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\p(a, b). seed(k).
        \\p(S) :- seed(k), setof([X, Y], p(X, Y), S).
        \\p(S)?
    , null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[[a, b]]");
}
test "insert-only batches propagate incrementally and match full rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(n0, n1). edge(n1, n2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "path(n0, n2)?", 1);
    const expansions_after_build = db.state.eval.expansions;

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
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    try std.testing.expect(db.state.propagated_facts > 0);
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
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "path(X, Y)?", 6);

    // Inserting edge(d, e) derives exactly the four new paths a-e, b-e,
    // c-e, and d-e; each is propagated and counted exactly once.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
    try std.testing.expectEqual(@as(usize, 4), db.state.propagated_facts);
    try expectAnswerCount(&db, "path(X, Y)?", 10);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "duplicate base insertions produce no derived delta" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "path(a, b)?", 1);
    const closure_len = db.state.closure.?.len();
    const propagated = db.state.propagated_facts;

    try std.testing.expect(!try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }, &.{}));
    try std.testing.expectEqual(closure_len, db.state.closure.?.len());
    try std.testing.expectEqual(propagated, db.state.propagated_facts);
    try std.testing.expect(db.state.materialization == .clean);
}

test "propagation reaching negation or setof falls back to dirty rebuild" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\edge(a, b). flag(a). flag(b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\note(X) :- flag(X), not path(a, X).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "note(X)?", 1);
    const expansions_after_build = db.state.eval.expansions;

    // flag is only read positively, so its insertion propagates through the
    // negation stratum without any rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("flag", &.{input.atom("c")}),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "note(c)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // An edge insertion grows path, which the negation reads, so the
    // negation stratum rebuilds while the positive stratum stays
    // incremental.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }, &.{}));
    try std.testing.expectEqual(expansions_after_build + 1, db.state.eval.expansions);
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "note(c)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "batch deletions and mixed batches maintain the closure correctly" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "path(a, c)?", 1);

    // Deleting an absent fact alone is a no-op that commits nothing.
    try std.testing.expect(!try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("x"), input.atom("y") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);

    // A mixed batch deletes one edge and inserts another as one transition.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
    }, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try expectAnswerCount(&db, "path(b, d)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expectError(errors.Error.InvalidFact, db.applyChanges(&.{
        input.fact("edge", &.{ input.variable("x"), input.atom("y") }),
    }, &.{}));
    try std.testing.expectError(errors.Error.InvalidFact, db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.variable("x"), input.atom("y") }),
    }));
}

test "over-deletion reaches a seeded rule fed by values from a higher stratum" {
    // `length` is a seeded structural rule: it is driven by the value table
    // rather than by a fact relation, so it sits in stratum zero while the
    // lists it consumes are interned by `collected` in a higher stratum. That
    // is the one case where a rule keeps deriving facts above its own stratum,
    // and it is why `expandLevel` and `propagateLevel` select rules with
    // `ruleActiveAt` while `overdeleteLevel` uses `ruleStratum`.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2).
        \\member(g1, a). member(g1, b). member(g2, c).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
    , null);
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "size(g1, 2)?", 1);

    // Removing a member shortens g1's list. The old list value stays interned,
    // so `length` keeps deriving its length — a rebuild does the same, because
    // the value table is monotone and nothing withdraws a structural value.
    // What must disappear is `size(g1, 2)`, whose support went with the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("b") }),
    }));
    try expectAnswerCount(&db, "size(g1, 2)?", 0);
    try expectAnswerCount(&db, "size(g1, 1)?", 1);
    try expectAnswerCount(&db, "size(g2, 1)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting the structural rule's own base case removes the whole chain,
    // and with it every `size`. Over-deletion cannot *build* `length(H!T, N)`
    // backwards from `length(T, M)` — nothing there names `H` — so it looks the
    // head up in the closure instead, and the stratum is maintained rather than
    // rebuilt.
    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try std.testing.expectEqual(before.rebuild_fallbacks, db.maintenanceStats().rebuild_fallbacks);
    try std.testing.expectEqual(before.stratum_expansions, db.state.eval.expansions);
    try std.testing.expect(db.maintenanceStats().removed_facts > before.removed_facts);
    try expectAnswerCount(&db, "size(G, N)?", 0);
    try expectAnswerCount(&db, "length(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "deleting a structural base case unwinds the whole chain incrementally" {
    // The shape M7 exists for: the deleted fact is the seeded rule's own base
    // case, so every derived length in the value table loses its support at
    // once. Over-deletion cannot build `length(H!T, N)` from `length(T, M)` —
    // nothing in that body names `H` — so it enumerates the head out of the
    // closure instead.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\chain([a, b, c]). chain([d]).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
    , null);
    setup.deinit();
    try db.materialize();
    // [a, b, c], [b, c], [c], [d] and [] are interned, and each has a length:
    // the base fact plus four derived.
    try expectAnswerCount(&db, "length(L, N)?", 5);

    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try expectAnswerCount(&db, "length(L, N)?", 0);
    const after = db.maintenanceStats();
    try std.testing.expectEqual(before.rebuild_fallbacks, after.rebuild_fallbacks);
    try std.testing.expectEqual(before.stratum_expansions, after.stratum_expansions);
    // The four derived lengths, and none of them rederivable.
    try std.testing.expectEqual(before.overdeleted_facts + 4, after.overdeleted_facts);
    try std.testing.expectEqual(before.rederived_facts, after.rederived_facts);
    // The removal count nets the base fact in with them.
    try std.testing.expectEqual(before.removed_facts + 5, after.removed_facts);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting a leaf instead of the base case is the other shape: putting the
    // base case back rebuilds the chain, and removing the fact that interned
    // the long list leaves the derived lengths standing, because the value
    // table is monotone and a rebuild keeps them too.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    }, &.{}));
    try expectAnswerCount(&db, "length(L, N)?", 5);
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("chain", &.{input.list(&.{input.atom("d")})}),
    }));
    try expectAnswerCount(&db, "length(L, N)?", 5);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a seeded rule whose body consumes the seed over-deletes correctly" {
    // `H` appears in the body as well as the head here, so the candidate head
    // has to be unified into the binding *before* the remaining goals run.
    // Solving `N = M + H` first would report UnboundVariable, which is the
    // defect that sent this whole class to the rebuild path.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\item([1, 2, 4]).
        \\total([], 0).
        \\total(H!T, N) :- total(T, M), N = M + H.
    , null);
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "total([1, 2, 4], 7)?", 1);

    const fallbacks_before = db.maintenanceStats().rebuild_fallbacks;
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("total", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try std.testing.expectEqual(fallbacks_before, db.maintenanceStats().rebuild_fallbacks);
    try expectAnswerCount(&db, "total(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a chain fact with an alternative proof survives its support's deletion" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\list([a, b]). list([q]). unit([q]).
        \\len([], 0).
        \\len(H!T, N) :- len(T, M), N = M + 1.
        \\len(H!T, N) :- unit(H!T), N = 1.
    , null);
    setup.deinit();
    try db.materialize();
    // [], [b], [a, b] and [q] all have lengths, and [q] has two proofs.
    try expectAnswerCount(&db, "len(L, N)?", 4);

    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("len", &.{ input.list(&.{}), input.integer(0) }),
    }));
    const after = db.maintenanceStats();
    try std.testing.expectEqual(before.rebuild_fallbacks, after.rebuild_fallbacks);
    // len([q], 1) is rederived from the unit rule; len([b], 1) and
    // len([a, b], 2) had only the chain, and go.
    try std.testing.expectEqual(before.overdeleted_facts + 3, after.overdeleted_facts);
    try std.testing.expectEqual(before.rederived_facts + 1, after.rederived_facts);
    try expectAnswerCount(&db, "len(L, N)?", 1);
    try expectAnswerCount(&db, "len([q], 1)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "several seeded occurrences over-delete each head once" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\list([a, b, c]).
        \\twice([], 0).
        \\twice(H!T, N) :- twice(T, M), twice(T, K), N = M + K.
    , null);
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "twice(L, N)?", 4);

    // Both occurrences of `twice(T, _)` reach the same heads. `deleted` is a
    // set, so the second pinning finds each head already queued; a head taken
    // twice would double the removal count.
    const before = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("twice", &.{ input.list(&.{}), input.integer(0) }),
    }));
    try std.testing.expectEqual(before.rebuild_fallbacks, db.maintenanceStats().rebuild_fallbacks);
    try std.testing.expectEqual(
        before.removed_facts + 4,
        db.maintenanceStats().removed_facts,
    );
    try expectAnswerCount(&db, "twice(L, N)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

/// Deletes a structural base case incrementally, which is the path that
/// enumerates head candidates out of the closure and unwinds the chain.
fn seededDeletionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\chain([a, b]).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\longest(N) :- length(L, N), N > 1.
    , null);
    setup.deinit();
    try db.materialize();
    _ = try db.applyChanges(&.{}, &.{
        input.fact("length", &.{ input.list(&.{}), input.integer(0) }),
    });
    var result = try db.execute("length(L, N)?", null);
    defer result.deinit();
    if (result.query.answers.items.len != 0) return error.UnexpectedAnswer;
}

test "seeded over-deletion releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(seededDeletionAllocationScenario);
}

test "randomized structural deletions match a clean rebuild under shadow verification" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\tag(t).
        \\box(k1, [a, b]). box(k2, [c]).
        \\len([], 0).
        \\len(H!T, N) :- len(T, M), N = M + 1.
        \\size(K, N) :- box(K, L), len(L, N).
        \\big(K) :- size(K, N), N > 1.
        \\quiet(K) :- box(K, L), not big(K).
        \\spread(S) :- tag(t), setof(N, size(K, N), S).
    , null);
    setup.deinit();
    try db.materialize();

    const keys = [_][]const u8{ "k1", "k2", "k3" };
    const lists = [_][]const input.Term{
        &.{ input.atom("a"), input.atom("b") },
        &.{input.atom("c")},
        &.{ input.atom("d"), input.atom("e"), input.atom("f") },
    };
    var prng = std.Random.DefaultPrng.init(0x5eeded5eeded);
    const random = prng.random();
    for (0..30) |step| {
        var box_terms: [2]input.Term = .{
            input.atom(keys[random.uintLessThan(usize, keys.len)]),
            input.list(lists[random.uintLessThan(usize, lists.len)]),
        };
        var base_terms: [2]input.Term = .{ input.list(&.{}), input.integer(0) };
        var inserts: [2]input.Relation = undefined;
        var deletes: [2]input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (random.boolean()) {
            inserts[insert_count] = input.fact("box", &box_terms);
            insert_count += 1;
        } else {
            deletes[delete_count] = input.fact("box", &box_terms);
            delete_count += 1;
        }
        // Toggling the seeded rule's base case is what drives the whole chain
        // in and out of the closure.
        if (step % 3 == 0) {
            if (random.boolean()) {
                inserts[insert_count] = input.fact("len", &base_terms);
                insert_count += 1;
            } else {
                deletes[delete_count] = input.fact("len", &base_terms);
                delete_count += 1;
            }
        }
        // Shadow verification asserts rebuild equality inside the call.
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

test "deleting the only base support removes the entire unsupported cycle" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    // The full cycle reaches every node from every node.
    try expectAnswerCount(&db, "path(X, Y)?", 9);
    const expansions_after_build = db.state.eval.expansions;

    // After deleting edge(a, b) the cyclically self-supporting facts such
    // as path(a, a) must all disappear; reference counts alone would keep
    // them alive. The deletion is incremental: no stratum expansion runs.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    try std.testing.expect(db.state.removed_facts > 0);
    try expectAnswerCount(&db, "path(a, a)?", 0);
    try expectAnswerCount(&db, "path(X, Y)?", 3);
    try test_support.expectClosureMatchesRebuild(&db.state);
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
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try expectAnswerCount(&db, "special(b)?", 1);

    // path(a, d) survives the deletion through the c branch of the diamond,
    // while path(b, d) and with it special(b) lose their only test_support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("d") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "path(a, d)?", 1);
    try expectAnswerCount(&db, "special(b)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // special(a) loses its non-recursive derivation but survives through
    // the recursive path(a, d) alternative.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("marked", &.{input.atom("a")}),
    }));
    try expectAnswerCount(&db, "special(a)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a deletion falling back to rebuild leaves the batch's insertions a clean closure" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\node(a). node(b). node(c). edge(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
    , null);
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "isolated(b)?", 0);

    // Deleting the edge over-deletes path(a, b), which reaches `isolated`
    // through negation and forces delete-and-rederive to abandon the
    // incremental path. The insertion in the same batch then has to find a
    // clean closure to propagate into: the fallback repairs the closure
    // through `ensureMaterialized` rather than leaving it dirty, which is
    // the invariant `applyInsertions` asserts.
    const before = db.maintenanceStats().rebuild_fallbacks;
    try std.testing.expect(try db.applyChanges(
        &.{input.fact("edge", &.{ input.atom("b"), input.atom("c") })},
        &.{input.fact("edge", &.{ input.atom("a"), input.atom("b") })},
    ));
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before);

    try expectAnswerCount(&db, "isolated(b)?", 1);
    try expectAnswerCount(&db, "path(b, c)?", 1);
    try expectAnswerCount(&db, "path(a, c)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "adding and removing a fact toggles negation-dependent conclusions" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\item(a). item(b).
        \\blocked(b).
        \\allowed(X) :- item(X), not blocked(X).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "allowed(a)?", 1);
    try expectAnswerCount(&db, "allowed(b)?", 0);

    try std.testing.expect(try db.applyChanges(&.{
        input.fact("blocked", &.{input.atom("a")}),
    }, &.{}));
    try expectAnswerCount(&db, "allowed(a)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("blocked", &.{input.atom("a")}),
    }));
    try expectAnswerCount(&db, "allowed(a)?", 1);
    try expectAnswerCount(&db, "allowed(b)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "projection counts change without prematurely deleting supported tuples" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\holds(a, b1). holds(a, b2).
        \\present(X) :- holds(X, Y).
    , null);
    setup.deinit();
    try expectAnswerCount(&db, "present(a)?", 1);
    const present_id = db.state.strings.get("present").?;
    const support_before = blk: {
        for (0..db.state.closure.?.len()) |index| {
            const fact = db.state.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.state.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_before >= 2);

    // Removing one of two supports keeps the tuple with changed test_support.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("holds", &.{ input.atom("a"), input.atom("b1") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "present(a)?", 1);
    const support_after = blk: {
        for (0..db.state.closure.?.len()) |index| {
            const fact = db.state.closure.?.factAt(index);
            if (fact.predicate == present_id) break :blk db.state.closure.?.supportAt(index);
        }
        return error.MissingFact;
    };
    try std.testing.expect(support_after != support_before);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Removing the last support deletes the tuple.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("holds", &.{ input.atom("a"), input.atom("b2") }),
    }));
    try expectAnswerCount(&db, "present(a)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "random mixed update traces match a clean rebuild after every batch" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e).
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
        \\summary(S) :- node(a), setof([X, Y], path(X, Y), S).
    , null);
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
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

test "a cloned database interns to the same identifiers as the database it came from" {
    // Three things rest on this, and the hash index beside each value table
    // is why it is worth restating. A retraction resolves its goals against a
    // copy and lets only the facts it resolved to cross back, which they can
    // because the copy shares the original's identifiers. A view catalog's
    // constants are this database's scalars — its predicate names are string
    // table entries, which nothing here touches — and `Jatalog.clone` hands
    // out the catalog and the database together, so what `Catalog.clone`
    // recorded has to mean the same thing in what `Database.clone` returns.
    // And a cached folded plan holds lowered rules interned against the
    // database that cached it. The index is a lookup accelerator over an
    // unchanged ordered table, so identifiers stay insertion positions and a
    // copy assigns them exactly as the original did.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var loaded = try db.execute(
        \\edge(a, b).
        \\edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Y) :- path(X, Z), edge(Z, Y).
        \\reach(X, S) :- path(X, Y), setof(Y, path(X, Y), S).
    , null);
    loaded.deinit();
    try db.materialize();

    var copy = try db.clone();
    defer copy.deinit();

    const scalars = &db.state.eval.scalars;
    const copied_scalars = &copy.state.eval.scalars;
    for ([_][]const u8{ "a", "b", "c" }) |atom| {
        try std.testing.expectEqual(
            try scalars.internAtom(atom),
            try copied_scalars.internAtom(atom),
        );
    }

    const values = &db.state.eval.values;
    const copied_values = &copy.state.eval.values;
    for (values.values.items, 0..) |value, id| {
        try std.testing.expectEqual(@as(syntax.ValueId, @intCast(id)), try values.intern(value));
        try std.testing.expectEqual(
            @as(syntax.ValueId, @intCast(id)),
            try copied_values.intern(value),
        );
    }

    // A value neither has seen lands at the same identifier on both sides,
    // which is what makes a fact resolved on the copy nameable here.
    const fresh_scalar = try copied_scalars.internAtom("d");
    try std.testing.expectEqual(fresh_scalar, try scalars.internAtom("d"));
    const head = try values.intern(.{ .scalar = fresh_scalar });
    try std.testing.expectEqual(head, try copied_values.intern(.{ .scalar = fresh_scalar }));
    const tail = try values.intern(.nil);
    try std.testing.expectEqual(tail, try copied_values.intern(.nil));
    const fresh_value: evaluator.Value = .{ .cons = .{ .head = head, .tail = tail } };
    try std.testing.expectEqual(
        try values.intern(fresh_value),
        try copied_values.intern(fresh_value),
    );
    try std.testing.expectEqual(values.values.items.len, copied_values.values.items.len);
}

test "retraction maintains the closure incrementally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, a). edge(x, y).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try db.materialize();
    try expectAnswerCount(&db, "path(X, Y)?", 10);
    const after_build = db.maintenanceStats();

    // A typed retraction runs delete-and-rederive rather than dirtying the
    // stratum, so no rule expansion happens and the closure stays clean.
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("x"), input.atom("y") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().removed_facts > after_build.removed_facts);
    try expectAnswerCount(&db, "path(x, y)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Retracting the only base support of a cycle removes the whole
    // unsupported cycle, still without a rebuild.
    const before_cycle = db.maintenanceStats();
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("c"), input.atom("a") }),
    }));
    try std.testing.expectEqual(before_cycle.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "path(a, a)?", 0);
    try expectAnswerCount(&db, "path(a, c)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "pattern retraction removes every matching fact incrementally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(a, d). edge(b, e).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // One goal with a variable retracts all three outgoing edges of a.
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("a"), input.variable("target") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "edge(a, X)?", 0);
    try expectAnswerCount(&db, "path(a, X)?", 0);
    try expectAnswerCount(&db, "path(b, e)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Source-level retraction takes the same path.
    const before_source = db.maintenanceStats();
    var retracted = try db.execute("edge(b, e)~", null);
    retracted.deinit();
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(before_source.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try expectAnswerCount(&db, "path(X, Y)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "retraction maintains aggregate groups and negation strata" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a). member(g1, b). member(g2, z).
        \\banned(g2).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\allowed(G) :- group(G), not banned(G).
    , null);
    setup.deinit();
    try db.materialize();
    const after_build = db.maintenanceStats();

    // Retracting a member updates only the affected group's list.
    try std.testing.expect(try db.retract(&.{
        input.relation("member", &.{ input.atom("g1"), input.atom("a") }),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(after_build.stratum_expansions, db.maintenanceStats().stratum_expansions);
    try std.testing.expect(db.maintenanceStats().maintained_groups > after_build.maintained_groups);
    var collected = try db.execute("collected(g1, S)?", null);
    try test_support.expectBindingValue(&collected.query.answers.items[0], "S", "[b]");
    collected.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Retracting the last member leaves the enumerated group empty.
    try std.testing.expect(try db.retract(&.{
        input.relation("member", &.{ input.atom("g1"), input.atom("b") }),
    }));
    var emptied = try db.execute("collected(g1, S)?", null);
    try test_support.expectBindingValue(&emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Retracting a negated predicate is the documented rebuild category.
    const before_negation = db.maintenanceStats();
    try expectAnswerCount(&db, "allowed(g2)?", 0);
    try std.testing.expect(try db.retract(&.{
        input.relation("banned", &.{input.atom("g2")}),
    }));
    try expectAnswerCount(&db, "allowed(g2)?", 1);
    try std.testing.expect(db.maintenanceStats().rebuild_fallbacks > before_negation.rebuild_fallbacks);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

fn retractionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(a, c). edge(b, c). group(g). member(g, m1). member(g, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    , null);
    setup.deinit();
    try db.materialize();
    _ = try db.retract(&.{
        input.relation("edge", &.{ input.atom("a"), input.variable("target") }),
    });
    _ = try db.retract(&.{
        input.relation("member", &.{ input.atom("g"), input.atom("m1") }),
    });
    var result = try db.execute("collected(g, S)?", null);
    defer result.deinit();
    const formatted = try (try result.query.answers.items[0].getValue("S")).formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[m2]")) return error.UnexpectedAggregate;
}

test "incremental retraction releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(retractionAllocationScenario);
}

/// Runs one deterministic update trace under a fixed policy and returns the
/// materialized database for comparison.
fn batchUpdateAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    setup.deinit();
    var first = try db.execute("path(a, c)?", null);
    first.deinit();
    _ = try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("c"), input.atom("d") }),
    }, &.{});
    _ = try db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    });
    var second = try db.execute("path(b, e)?", null);
    defer second.deinit();
    if (second.query.answers.items.len != 1) return error.UnexpectedAnswer;
}

test "batch updates roll back completely on failure" {
    try test_support.expectEveryAllocationFailureReleased(batchUpdateAllocationScenario);
}

fn runPolicyTrace(db: *Jatalog, policy: cost_model.MaintenancePolicy) !void {
    db.setMaintenancePolicy(policy);
    var setup = try db.execute(
        \\node(a). node(b). node(c). group(g1). group(g2).
        \\edge(a, b). member(g1, m1). member(g2, m2).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\isolated(X) :- node(X), not path(a, X).
    , null);
    setup.deinit();
    try db.materialize();

    const nodes = [_][]const u8{ "a", "b", "c" };
    const groups = [_][]const u8{ "g1", "g2" };
    const members = [_][]const u8{ "m1", "m2", "m3" };
    var prng = std.Random.DefaultPrng.init(0xc05715c05715);
    const random = prng.random();
    for (0..40) |step| {
        var edge_terms: [2]input.Term = .{
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
            input.atom(nodes[random.uintLessThan(usize, nodes.len)]),
        };
        var member_terms: [2]input.Term = .{
            input.atom(groups[random.uintLessThan(usize, groups.len)]),
            input.atom(members[random.uintLessThan(usize, members.len)]),
        };
        if (step % 4 == 3) {
            // Exercise pattern retraction as well as the batch API.
            _ = try db.retract(&.{input.relation("member", &.{
                input.atom(groups[random.uintLessThan(usize, groups.len)]),
                input.variable("any"),
            })});
            continue;
        }
        var inserts: [2]input.Relation = undefined;
        var deletes: [2]input.Relation = undefined;
        var insert_count: usize = 0;
        var delete_count: usize = 0;
        if (random.boolean()) {
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
        _ = try db.applyChanges(inserts[0..insert_count], deletes[0..delete_count]);
    }
    try db.materialize();
}

/// Program used by the cost-attribution tests below: a transitive closure
/// small enough that one edge change is cheap to maintain.
const cost_attribution_program =
    \\edge(a, b). edge(b, c).
    \\path(X, Y) :- edge(X, Y).
    \\path(X, Z) :- edge(X, Y), path(Y, Z).
;

test "the maintenance estimate counts facts changed, not facts named" {
    const new_edge = input.fact("edge", &.{ input.atom("c"), input.atom("d") });

    var lean: Jatalog = .init(std.testing.allocator);
    defer lean.deinit();
    lean.setMaintenancePolicy(.incremental);
    var lean_setup = try lean.execute(cost_attribution_program, null);
    lean_setup.deinit();
    try lean.materialize();
    _ = try lean.applyChanges(&.{new_edge}, &.{});

    var padded: Jatalog = .init(std.testing.allocator);
    defer padded.deinit();
    padded.setMaintenancePolicy(.incremental);
    var padded_setup = try padded.execute(cost_attribution_program, null);
    padded_setup.deinit();
    try padded.materialize();
    // The same single real insertion, named alongside deletions of facts the
    // database does not hold. Deleting an absent fact is a no-op, so the cost
    // per changed fact must match the lean batch rather than being divided by
    // the number of relations the caller happened to name.
    _ = try padded.applyChanges(&.{new_edge}, &.{
        input.fact("edge", &.{ input.atom("p"), input.atom("q") }),
        input.fact("edge", &.{ input.atom("q"), input.atom("r") }),
        input.fact("edge", &.{ input.atom("r"), input.atom("s") }),
        input.fact("edge", &.{ input.atom("s"), input.atom("t") }),
        input.fact("edge", &.{ input.atom("t"), input.atom("u") }),
        input.fact("edge", &.{ input.atom("u"), input.atom("v") }),
        input.fact("edge", &.{ input.atom("v"), input.atom("w") }),
    });

    try std.testing.expectEqual(
        lean.maintenanceStats().maintenance_work_per_fact,
        padded.maintenanceStats().maintenance_work_per_fact,
    );
}

test "a rebuild fallback is charged to the rebuild estimate, not to maintenance" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\node(a). node(b). node(c). node(d). node(e). edge(a, b). edge(b, c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\isolated(X) :- node(X), not path(a, X).
    , null);
    setup.deinit();
    try db.materialize();

    // Deleting this edge over-deletes path facts that reach `isolated`
    // through negation, so delete-and-rederive abandons the incremental path
    // and rebuilds. The rebuild is real work, but it is recomputation work:
    // charging it to the maintenance estimate as well would let one event
    // push both estimates in opposite directions.
    const before = db.state.eval.cost.work;
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
    }));
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.rebuild_fallbacks > 0);
    try std.testing.expect(stats.rebuild_work != null);
    try std.testing.expect(stats.maintenance_work_per_fact != null);
    // Both estimates are this database's first, so each is the raw
    // observation. One base fact changed, so the per-fact estimate is the
    // whole maintenance measurement — and the two together must account for
    // the batch exactly once. Were the rebuild counted on both sides, this sum
    // would exceed the work the batch actually did.
    try std.testing.expectEqual(
        db.state.eval.cost.work - before,
        stats.rebuild_work.? + stats.maintenance_work_per_fact.?,
    );
}

test "the cost model changes the path taken but never the result" {
    var automatic: Jatalog = .init(std.testing.allocator);
    defer automatic.deinit();
    try runPolicyTrace(&automatic, .automatic);

    var incremental: Jatalog = .init(std.testing.allocator);
    defer incremental.deinit();
    try runPolicyTrace(&incremental, .incremental);

    var recompute: Jatalog = .init(std.testing.allocator);
    defer recompute.deinit();
    try runPolicyTrace(&recompute, .recompute);

    // Every policy must leave the same base facts and the same closure.
    for ([_]*Jatalog{ &incremental, &recompute }) |other| {
        try std.testing.expectEqual(automatic.state.facts.len(), other.state.facts.len());
        for (0..automatic.state.facts.len()) |index|
            try std.testing.expect(try other.state.facts.contains(automatic.state.facts.factAt(index)));
        try std.testing.expectEqual(automatic.state.closure.?.len(), other.state.closure.?.len());
        for (0..automatic.state.closure.?.len()) |index|
            try std.testing.expect(try other.state.closure.?.contains(automatic.state.closure.?.factAt(index)));
    }
    try test_support.expectClosureMatchesRebuild(&automatic.state);

    // The pinned policies really did take different paths, and the
    // automatic one made a real decision rather than defaulting.
    const automatic_stats = automatic.maintenanceStats();
    try std.testing.expectEqual(@as(usize, 0), incremental.maintenanceStats().recompute_choices);
    try std.testing.expectEqual(@as(usize, 0), recompute.maintenanceStats().maintain_choices);
    try std.testing.expect(automatic_stats.maintain_choices > 0);
    try std.testing.expect(automatic_stats.rebuild_work != null);
    try std.testing.expect(automatic_stats.maintenance_work_per_fact != null);
}

test "the cost model learns to prefer the cheaper path per workload" {
    // A recursive closure over a chain: one new edge derives a handful of
    // paths, while recomputing re-derives the entire transitive closure.
    var closure_db: Jatalog = .init(std.testing.allocator);
    defer closure_db.deinit();
    var chain_source: std.ArrayList(u8) = .empty;
    defer chain_source.deinit(std.testing.allocator);
    for (0..30) |index| {
        var buffer: [64]u8 = undefined;
        const line = try std.fmt.bufPrint(&buffer, "edge(n{d}, n{d}). ", .{ index, index + 1 });
        try chain_source.appendSlice(std.testing.allocator, line);
    }
    try chain_source.appendSlice(
        std.testing.allocator,
        "path(X, Y) :- edge(X, Y). path(X, Z) :- edge(X, Y), path(Y, Z).",
    );
    var chain_setup = try closure_db.execute(chain_source.items, null);
    chain_setup.deinit();
    try closure_db.materialize();
    for (0..8) |index| {
        var from: [16]u8 = undefined;
        var to: [16]u8 = undefined;
        const source = try std.fmt.bufPrint(&from, "s{d}", .{index});
        const target = try std.fmt.bufPrint(&to, "n{d}", .{index});
        const terms: [2]input.Term = .{ input.atom(source), input.atom(target) };
        _ = try closure_db.applyChanges(&.{input.fact("edge", &terms)}, &.{});
        // Query between batches so a recompute decision is actually paid and
        // the closure is clean again when the next decision is made.
        var query = try closure_db.execute("path(n0, X)?", null);
        query.deinit();
    }
    const closure_stats = closure_db.maintenanceStats();
    try std.testing.expect(closure_stats.maintain_choices > closure_stats.recompute_choices);
    try test_support.expectClosureMatchesRebuild(&closure_db.state);

    // A shallow program whose closure is cheap to recompute: maintenance
    // has no recursion to save and the model should stop choosing it.
    var flat_db: Jatalog = .init(std.testing.allocator);
    defer flat_db.deinit();
    var flat_setup = try flat_db.execute(
        \\item(a). item(b). item(c).
        \\present(X) :- item(X).
    , null);
    flat_setup.deinit();
    try flat_db.materialize();
    for (0..8) |index| {
        var buffer: [16]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "i{d}", .{index});
        const terms: [1]input.Term = .{input.atom(name)};
        _ = try flat_db.applyChanges(&.{input.fact("item", &terms)}, &.{});
        var query = try flat_db.execute("present(X)?", null);
        query.deinit();
    }
    try test_support.expectClosureMatchesRebuild(&flat_db.state);
    const flat_stats = flat_db.maintenanceStats();
    try std.testing.expect(flat_stats.recompute_choices > 0);
}

test "shadow verification accepts maintained closures and reports corruption" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). group(g). member(g, m1).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\reachable(X) :- path(a, X).
        \\unreachable(X) :- edge(X, Y), not reachable(X).
    , null);
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
    try test_support.expectClosureMatchesRebuild(&db.state);

    // A closure corrupted behind the maintenance engine's back is caught:
    // this path tuple has no derivation from any base fact.
    const terms = try std.testing.allocator.alloc(relation_store.ValueId, 2);
    var terms_owned = true;
    defer if (terms_owned) std.testing.allocator.free(terms);
    terms[0] = try db.state.eval.values.intern(.{ .scalar = try db.state.eval.scalars.internAtom("phantom1") });
    terms[1] = try db.state.eval.values.intern(.{ .scalar = try db.state.eval.scalars.internAtom("phantom2") });
    const added = try db.state.closure.?.insert(.{
        .predicate = db.state.strings.get("path").?,
        .terms = terms,
    }, true);
    terms_owned = false;
    try std.testing.expect(added);
    try std.testing.expectError(errors.Error.MaintenanceMismatch, db.applyChanges(&.{
        input.fact("edge", &.{ input.atom("d"), input.atom("e") }),
    }, &.{}));
}

test "randomized mixed traces hold under shadow verification" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
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
    , null);
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
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}
test "aggregate groups are maintained incrementally across member changes" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2).
        \\member(g1, b). member(g1, a). member(g2, z).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    , null);
    setup.deinit();
    var initial = try db.execute("collected(g1, S)?", null);
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[a, b]");
    initial.deinit();
    const expansions_after_build = db.state.eval.expansions;

    // Member insertion updates only the affected group, with no rebuild.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g1"), input.atom("c") }),
    }, &.{}));
    try std.testing.expect(db.state.materialization == .clean);
    try std.testing.expectEqual(expansions_after_build, db.state.eval.expansions);
    var inserted = try db.execute("collected(g1, S)?", null);
    try test_support.expectBindingValue(&inserted.query.answers.items[0], "S", "[a, b, c]");
    inserted.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // The untouched group keeps its list and there is exactly one tuple
    // per group after the change.
    var untouched = try db.execute("collected(g2, S)?", null);
    try test_support.expectBindingValue(&untouched.query.answers.items[0], "S", "[z]");
    untouched.deinit();
    try expectAnswerCount(&db, "collected(G, S)?", 2);

    // Member deletion shrinks the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("a") }),
    }));
    var deleted = try db.execute("collected(g1, S)?", null);
    try test_support.expectBindingValue(&deleted.query.answers.items[0], "S", "[b, c]");
    deleted.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting the last member leaves the enumerated group with an empty
    // list, because its outer goal still derives the group.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g2"), input.atom("z") }),
    }));
    var emptied = try db.execute("collected(g2, S)?", null);
    try test_support.expectBindingValue(&emptied.query.answers.items[0], "S", "[]");
    emptied.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting the group key removes the tuple entirely.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("group", &.{input.atom("g2")}),
    }));
    try expectAnswerCount(&db, "collected(g2, S)?", 0);
    try expectAnswerCount(&db, "collected(G, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Restoring the group key brings back an empty group.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("group", &.{input.atom("g2")}),
    }, &.{}));
    var restored = try db.execute("collected(g2, S)?", null);
    try test_support.expectBindingValue(&restored.query.answers.items[0], "S", "[]");
    restored.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "duplicate member derivations do not disturb a maintained group" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g). direct(g, a). mirrored(g, a). direct(g, b).
        \\member(G, X) :- direct(G, X).
        \\member(G, X) :- mirrored(G, X).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    , null);
    setup.deinit();
    var initial = try db.execute("collected(g, S)?", null);
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[a, b]");
    initial.deinit();

    // Removing one of two derivations of member(g, a) keeps the member.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("mirrored", &.{ input.atom("g"), input.atom("a") }),
    }));
    var kept = try db.execute("collected(g, S)?", null);
    try test_support.expectBindingValue(&kept.query.answers.items[0], "S", "[a, b]");
    kept.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Removing the last derivation drops it from the list.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("direct", &.{ input.atom("g"), input.atom("a") }),
    }));
    var dropped = try db.execute("collected(g, S)?", null);
    try test_support.expectBindingValue(&dropped.query.answers.items[0], "S", "[b]");
    dropped.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
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
        , null);
        setup.deinit();
        var empty = try db.execute("collected(g, S)?", null);
        try test_support.expectBindingValue(&empty.query.answers.items[0], "S", "[]");
        empty.deinit();

        for (order) |name| {
            _ = try db.applyChanges(&.{
                input.fact("member", &.{ input.atom("g"), input.atom(name) }),
            }, &.{});
        }
        var result = try db.execute("collected(g, S)?", null);
        try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[a, b, c]");
        result.deinit();
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

test "bag emulation retains equal values with distinct discriminators" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g). reading(g, r1, 5). reading(g, r2, 5). reading(g, r3, 7).
        \\bag(G, S) :- group(G), setof([V, D], reading(G, D, V), S).
    , null);
    setup.deinit();
    var initial = try db.execute("bag(g, S)?", null);
    try test_support.expectBindingValue(
        &initial.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [7, r3]]",
    );
    initial.deinit();

    try std.testing.expect(try db.applyChanges(&.{
        input.fact("reading", &.{ input.atom("g"), input.atom("r4"), input.integer(5) }),
    }, &.{}));
    var added = try db.execute("bag(g, S)?", null);
    try test_support.expectBindingValue(
        &added.query.answers.items[0],
        "S",
        "[[5, r1], [5, r2], [5, r4], [7, r3]]",
    );
    added.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Removing one duplicate value keeps the others.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("reading", &.{ input.atom("g"), input.atom("r2"), input.integer(5) }),
    }));
    var removed = try db.execute("bag(g, S)?", null);
    try test_support.expectBindingValue(
        &removed.query.answers.items[0],
        "S",
        "[[5, r1], [5, r4], [7, r3]]",
    );
    removed.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
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
    , null);
    setup.deinit();
    var initial = try db.execute("numchildren(alice, N)?", null);
    try std.testing.expectEqual(@as(i64, 1), try initial.query.answers.items[0].getInteger("N"));
    initial.deinit();

    // A new child changes the aggregate list, which must flow through the
    // downstream structural list function.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("person", &.{input.atom("carol")}),
        input.fact("parent", &.{ input.atom("alice"), input.atom("carol") }),
    }, &.{}));
    var grown = try db.execute("numchildren(alice, N)?", null);
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    try expectAnswerCount(&db, "numchildren(X, N)?", 3);
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("parent", &.{ input.atom("alice"), input.atom("bob") }),
    }));
    var shrunk = try db.execute("numchildren(alice, N)?", null);
    try std.testing.expectEqual(@as(i64, 1), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "multiple and nested aggregates stay correct through the rebuild path" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). item(g1, a). item(g2, b). tag(g1, t1). tag(g2, t2).
        \\both(G, S, T) :- group(G), setof(X, item(G, X), S), setof(Y, tag(G, Y), T).
        \\nested(S) :- group(g1), setof([G, T], (group(G), setof(X, item(G, X), T)), S).
    , null);
    setup.deinit();
    var initial = try db.execute("both(g1, S, T)?", null);
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[a]");
    try test_support.expectBindingValue(&initial.query.answers.items[0], "T", "[t1]");
    initial.deinit();

    // Rules outside the maintainable class fall back to the stratum
    // rebuild, which must still produce rebuild-equivalent results.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("item", &.{ input.atom("g1"), input.atom("c") }),
        input.fact("tag", &.{ input.atom("g1"), input.atom("t3") }),
    }, &.{}));
    var updated = try db.execute("both(g1, S, T)?", null);
    try test_support.expectBindingValue(&updated.query.answers.items[0], "S", "[a, c]");
    try test_support.expectBindingValue(&updated.query.answers.items[0], "T", "[t1, t3]");
    updated.deinit();
    var nested = try db.execute("nested(S)?", null);
    try test_support.expectBindingValue(
        &nested.query.answers.items[0],
        "S",
        "[[g1, [a, c]], [g2, [b]]]",
    );
    nested.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);

    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("item", &.{ input.atom("g1"), input.atom("a") }),
    }));
    var reduced = try db.execute("both(g1, S, T)?", null);
    try test_support.expectBindingValue(&reduced.query.answers.items[0], "S", "[c]");
    reduced.deinit();
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "random aggregate update traces match a clean rebuild after every batch" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\group(g1). group(g2). group(g3).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(G, N) :- collected(G, S), length(S, N).
        \\empty(G) :- group(G), not member(G, m1), not member(G, m2), not member(G, m3).
    , null);
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
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);
    }
}

/// Derivation count the auxiliary view records for the single tuple of
/// `predicate` whose first argument is the atom `first_atom`.
fn derivationCountOf(
    db: *Jatalog,
    predicate: []const u8,
    first_atom: []const u8,
) !u32 {
    const predicate_id = db.state.strings.get(predicate) orelse return error.MissingPredicate;
    const scalar_id = try db.state.eval.scalars.internAtom(first_atom);
    const first_value = try db.state.eval.values.intern(.{ .scalar = scalar_id });
    for (db.state.eval.rules.items) |rule| {
        if (rule.head.predicate != predicate_id) continue;
        const view = materialization.auxiliaryFor(&db.state, rule.id) orelse return error.NotProjected;
        const closure = &db.state.closure.?;
        for (0..closure.len()) |index| {
            const fact = closure.factAt(index);
            if (fact.predicate != predicate_id or fact.terms[0] != first_value) continue;
            return view.derivationCount(fact.terms);
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
    , null);
    setup.deinit();

    // The materialization contains v(a, [1]) and v(b, []).
    var initial = try db.execute("v(a, S)?", null);
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[1]");
    initial.deinit();
    var empty = try db.execute("v(b, S)?", null);
    try test_support.expectBindingValue(&empty.query.answers.items[0], "S", "[]");
    empty.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 2);

    // Deleting p(a) and inserting r(b, 2) deletes v(a, [1]) and updates
    // v(b, []) to v(b, [2]).
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("r", &.{ input.atom("b"), input.integer(2) }),
    }, &.{
        input.fact("p", &.{input.atom("a")}),
    }));
    try std.testing.expect(db.state.materialization == .clean);
    try expectAnswerCount(&db, "v(a, S)?", 0);
    var updated = try db.execute("v(b, S)?", null);
    try test_support.expectBindingValue(&updated.query.answers.items[0], "S", "[2]");
    updated.deinit();
    try expectAnswerCount(&db, "v(X, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);

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
    , null);
    setup.deinit();

    var initial = try db.execute("v(a, S)?", null);
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[1, 2]");
    initial.deinit();
    var other = try db.execute("v(b, S)?", null);
    try test_support.expectBindingValue(&other.query.answers.items[0], "S", "[2]");
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
    try std.testing.expect(db.state.materialization == .clean);
    var retained = try db.execute("v(a, S)?", null);
    try test_support.expectBindingValue(&retained.query.answers.items[0], "S", "[1, 2]");
    retained.deinit();
    try std.testing.expectEqual(@as(u32, 1), try derivationCountOf(&db, "v", "a"));
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Deleting p(a, 1) removes the last derivation, so the tuple goes.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("p", &.{ input.atom("a"), input.integer(1) }),
    }));
    try expectAnswerCount(&db, "v(a, S)?", 0);
    try std.testing.expectEqual(@as(u32, 0), try derivationCountOf(&db, "v", "a"));
    try expectAnswerCount(&db, "v(X, S)?", 1);
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "a changed aggregate list transfers support to the new tuple" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\p(a, 1). p(a, 2). p(a, 3). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    , null);
    setup.deinit();
    var initial = try db.execute("v(a, S)?", null);
    try test_support.expectBindingValue(&initial.query.answers.items[0], "S", "[1]");
    initial.deinit();
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));

    // Growing the member set replaces the old tuple with the new one and
    // carries all three derivations across in the same batch.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("r", &.{ input.atom("a"), input.integer(2) }),
    }, &.{}));
    try std.testing.expect(db.state.materialization == .clean);
    var moved = try db.execute("v(a, S)?", null);
    try test_support.expectBindingValue(&moved.query.answers.items[0], "S", "[1, 2]");
    moved.deinit();
    try expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try std.testing.expectEqual(@as(usize, 3), db.maintenanceStats().auxiliary_tuples);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Shrinking it back transfers the support again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("r", &.{ input.atom("a"), input.integer(1) }),
    }));
    var shrunk = try db.execute("v(a, S)?", null);
    try test_support.expectBindingValue(&shrunk.query.answers.items[0], "S", "[2]");
    shrunk.deinit();
    try expectAnswerCount(&db, "v(a, S)?", 1);
    try std.testing.expectEqual(@as(u32, 3), try derivationCountOf(&db, "v", "a"));
    try test_support.expectClosureMatchesRebuild(&db.state);
}

test "projected view counts agree with explicit proof enumeration" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    var setup = try db.execute(
        \\p(a, 1). r(a, 1).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
    , null);
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
        try std.testing.expect(db.state.materialization == .clean);
        try test_support.expectClosureMatchesRebuild(&db.state);

        // Every proof of v(k, S) comes from one p(k, Z) fact, so the stored
        // derivation count must equal the number of such base facts.
        for (keys) |key| {
            var proofs = try db.execute("p(K, Z)?", null);
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

test "aggregate changes propagate through downstream list functions and arithmetic" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    // Pinned: this test asserts the incremental mechanism itself.
    db.setMaintenancePolicy(.incremental);
    db.setShadowVerification(true);
    var setup = try db.execute(
        \\team(red). team(blue).
        \\roster(T, S) :- team(T), setof(P, plays(T, P), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\size(T, N) :- roster(T, S), length(S, N).
        \\headcount(T, N) :- size(T, M), N = M + 1.
        \\staffed(T) :- size(T, N), N > 1.
    , null);
    setup.deinit();
    try db.materialize();

    // Empty rosters flow through length, arithmetic, and the comparison.
    var initial = try db.execute("headcount(red, N)?", null);
    try std.testing.expectEqual(@as(i64, 1), try initial.query.answers.items[0].getInteger("N"));
    initial.deinit();
    try expectAnswerCount(&db, "staffed(T)?", 0);

    // Growing one group must reach every downstream stratum.
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("plays", &.{ input.atom("red"), input.atom("ann") }),
        input.fact("plays", &.{ input.atom("red"), input.atom("bo") }),
    }, &.{}));
    var grown = try db.execute("size(red, N)?", null);
    try std.testing.expectEqual(@as(i64, 2), try grown.query.answers.items[0].getInteger("N"));
    grown.deinit();
    var counted = try db.execute("headcount(red, N)?", null);
    try std.testing.expectEqual(@as(i64, 3), try counted.query.answers.items[0].getInteger("N"));
    counted.deinit();
    try expectAnswerCount(&db, "staffed(red)?", 1);
    try expectAnswerCount(&db, "staffed(blue)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // Shrinking it retracts the downstream conclusions again.
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("plays", &.{ input.atom("red"), input.atom("bo") }),
    }));
    var shrunk = try db.execute("headcount(red, N)?", null);
    try std.testing.expectEqual(@as(i64, 2), try shrunk.query.answers.items[0].getInteger("N"));
    shrunk.deinit();
    try expectAnswerCount(&db, "staffed(T)?", 0);
    try test_support.expectClosureMatchesRebuild(&db.state);

    // A downstream structural-recursive component recomputes within its own
    // stratum rather than forcing a whole-closure rebuild.
    const stats = db.maintenanceStats();
    try std.testing.expect(stats.maintained_groups > 0);
}

fn aggregateMaintenanceAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\group(g1). group(g2). member(g1, a).
        \\collected(G, S) :- group(G), setof(X, member(G, X), S).
    , null);
    setup.deinit();
    var first = try db.execute("collected(G, S)?", null);
    first.deinit();
    _ = try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g1"), input.atom("b") }),
        input.fact("member", &.{ input.atom("g2"), input.atom("c") }),
    }, &.{});
    _ = try db.applyChanges(&.{}, &.{
        input.fact("member", &.{ input.atom("g1"), input.atom("a") }),
    });
    var second = try db.execute("collected(g1, S)?", null);
    defer second.deinit();
    const formatted = try (try second.query.answers.items[0].getValue("S"))
        .formatAlloc(allocator);
    defer allocator.free(formatted);
    if (!std.mem.eql(u8, formatted, "[b]")) return error.UnexpectedAggregate;
}

test "aggregate maintenance releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(aggregateMaintenanceAllocationScenario);
}

// Join planning (P3). The planner reorders goals whose bindings allow it, so
// the properties worth pinning are that it never reorders past a binding, that
// reordering does not change what a program means, and that the order it chose
// can be inspected.

/// The program the planning tests query: two relations of very different size,
/// a filter over each, and one correlated aggregate.
const planning_program =
    \\few(a). few(b). few(c).
    \\many(a). many(b). many(c). many(d). many(e). many(f). many(g). many(h).
    \\skip(c).
    \\member(a, one). member(a, two). member(b, three).
;

test "the planner solves the smaller relation first" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(planning_program, null);
    setup.deinit();

    // Written most-selective-last on purpose: `many` has eight facts and no
    // bound argument, `few` has one. Solving `few` first turns the second goal
    // into a one-candidate index lookup instead of an eight-fact scan.
    const explained = try db.explainQuery(&.{
        input.relation("many", &.{input.variable("X")}),
        input.relation("few", &.{input.variable("X")}),
    });
    defer std.testing.allocator.free(explained);
    try std.testing.expectEqualStrings(
        \\few/1 join scan ~3
        \\many/1 join index {0} ~8
        \\
    , explained);
}

test "planning never moves a goal before the bindings it needs" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(planning_program, null);
    setup.deinit();

    // Every goal but the first is cheaper than `many(X)` and would be hoisted
    // on cost alone: the negation and the comparison examine nothing, the
    // arithmetic examines nothing, and the aggregate's inner relation is
    // smaller. None of them may move, because each consumes a variable only
    // the goals before it bind.
    const explained = try db.explainQuery(&.{
        input.relation("many", &.{input.variable("X")}),
        input.not("skip", &.{input.variable("X")}),
        input.setof(
            input.variable("T"),
            &.{input.relation("member", &.{ input.variable("X"), input.variable("T") })},
            input.variable("S"),
        ),
        input.relation("few", &.{input.variable("Y")}),
        input.notEqual(input.variable("X"), input.variable("Y")),
    });
    defer std.testing.allocator.free(explained);
    try std.testing.expectEqualStrings(
        \\few/1 join scan ~3
        \\many/1 join scan ~8
        \\<>/2 filter
        \\skip/1 anti-join index {0} ~1
        \\setof aggregate
        \\  member/2 join index {0} ~3
        \\
    , explained);
}

test "a plan chosen on cost answers exactly what the stored order answers" {
    // The two policies are the same program solved in two different orders.
    // Nothing else about the databases differs, so any disagreement in the
    // answers or in the closure is a planning bug rather than a cost decision.
    const program =
        \\edge(a, b). edge(b, c). edge(c, d). edge(d, e). edge(b, e).
        \\node(a). node(b). node(c). node(d). node(e). node(f).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\unreached(X) :- node(X), not path(a, X).
        \\reach(X, S) :- node(X), setof(Y, path(X, Y), S).
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\breadth(X, N) :- reach(X, S), length(S, N).
    ;
    const question = "breadth(X, N), unreached(U), N < 4?";

    var planned: Jatalog = .init(std.testing.allocator);
    defer planned.deinit();
    var stored: Jatalog = .init(std.testing.allocator);
    defer stored.deinit();
    stored.setPlanPolicy(.source_order);
    for ([_]*Jatalog{ &planned, &stored }) |db| {
        var setup = try db.execute(program, null);
        setup.deinit();
        try db.materialize();
    }

    try std.testing.expectEqual(
        stored.state.closure.?.len(),
        planned.state.closure.?.len(),
    );
    for (0..stored.state.closure.?.len()) |index|
        try std.testing.expect(try planned.state.closure.?.contains(stored.state.closure.?.factAt(index)));

    var planned_result = try planned.execute(question, null);
    defer planned_result.deinit();
    var stored_result = try stored.execute(question, null);
    defer stored_result.deinit();
    const planned_lines = try answerLines(&planned_result.query);
    defer freeLines(planned_lines);
    const stored_lines = try answerLines(&stored_result.query);
    defer freeLines(stored_lines);
    try std.testing.expectEqual(stored_lines.len, planned_lines.len);
    for (stored_lines, planned_lines) |expected, actual|
        try std.testing.expectEqualStrings(expected, actual);
}

/// One line per answer, sorted, so two runs can be compared as sets. Answers
/// name their variables in the order the query does, which is what makes the
/// lines comparable across plans in the first place.
fn answerLines(result: *const results.QueryResult) ![][]u8 {
    const allocator = std.testing.allocator;
    const lines = try allocator.alloc([]u8, result.answers.items.len);
    var written: usize = 0;
    errdefer {
        for (lines[0..written]) |line| allocator.free(line);
        allocator.free(lines);
    }
    for (result.answers.items, lines) |*answer, *line| {
        var text: std.Io.Writer.Allocating = .init(allocator);
        defer text.deinit();
        for (answer.bindings.items) |binding| {
            const value = try binding.value.formatAlloc(allocator);
            defer allocator.free(value);
            text.writer.print("{s}={s};", .{ binding.name, value }) catch return error.OutOfMemory;
        }
        line.* = try text.toOwnedSlice();
        written += 1;
    }
    std.mem.sort([]u8, lines, {}, struct {
        fn lessThan(_: void, a: []u8, b: []u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.lessThan);
    return lines;
}

fn freeLines(lines: [][]u8) void {
    for (lines) |line| std.testing.allocator.free(line);
    std.testing.allocator.free(lines);
}

test "an answer names its variables in the query's order, not the plan's" {
    // The plan is a cost decision and moves with the data; what a caller reads
    // must not. Here the planner solves `few` first, and the answer still
    // leads with the variable the query leads with.
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var setup = try db.execute(planning_program, null);
    setup.deinit();
    var result = try db.execute("many(X), few(Y)?", null);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 24), result.query.answers.items.len);
    for (result.query.answers.items) |answer| {
        try std.testing.expectEqualStrings("X", answer.bindings.items[0].name);
        try std.testing.expectEqualStrings("Y", answer.bindings.items[1].name);
    }
}

/// The even-length-path problem of Chapter 6, stated through the public
/// interface: three stored pairs, a view saying what they are pairs of, and a
/// recursive query over a relation nothing holds any more. What folding it
/// means is tested beside the code that does it; these check what `Jatalog`
/// adds, which is owning the views and handing them its own state.
fn declareEvenPathViews(db: *Jatalog) !ViewId {
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    try db.addFact("v", &.{ input.atom("a"), input.atom("c") });
    try db.addFact("v", &.{ input.atom("b"), input.atom("d") });
    try db.addFact("v", &.{ input.atom("c"), input.atom("e") });
    return db.defineView(input.fact("v", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("edge", &.{ y, z }),
    }, .materialized);
}

fn evenPathQuery(db: *Jatalog) !Fold {
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    return db.foldQuery(&.{input.relation("q", &.{ x, y })}, &.{
        input.rule(input.fact("q", &.{ x, y }), &.{input.relation("edge", &.{ x, y })}),
        input.rule(input.fact("q", &.{ x, z }), &.{
            input.relation("edge", &.{ x, y }),
            input.relation("q", &.{ y, z }),
        }),
    });
}

test "query lists answers in the order the caller asks for" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("score", &.{ input.atom("ann"), input.integer(3) });
    try db.addFact("score", &.{ input.atom("bob"), input.integer(5) });
    try db.addFact("score", &.{ input.atom("cat"), input.integer(3) });
    const goals = [_]input.Goal{input.relation("score", &.{ input.variable("P"), input.variable("S") })};
    var ranked = try db.query(&goals, &.{input.descending("S")});
    defer ranked.deinit();
    try std.testing.expectEqual(@as(usize, 3), ranked.answers.items.len);
    for ([_][]const u8{ "bob", "ann", "cat" }, ranked.answers.items) |name, answer|
        try std.testing.expectEqualStrings(name, try answer.getAtom("P"));
}

test "the fold interface defines, folds and answers against the database it belongs to" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    const view = try declareEvenPathViews(&db);

    const fold = try evenPathQuery(&db);
    defer fold.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, fold.guarantee);
    var answers = try db.answerFolded(fold, &.{input.descending("X")});
    defer answers.deinit();
    try std.testing.expectEqual(@as(usize, 4), answers.answers.items.len);
    try std.testing.expectEqualStrings("c", try answers.answers.items[0].getAtom("X"));

    var reconstructed = try db.foldReconstructions(fold);
    defer reconstructed.deinit();
    try std.testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try std.testing.expectEqualStrings("edge", reconstructed.items[0].predicate);
    const explanation = try db.explainFold(fold);
    defer allocator.free(explanation);
    try std.testing.expect(std.mem.startsWith(u8, explanation, "guarantee: maximally contained"));

    // The names a fold interned were committed to this database, and nothing
    // a plan reconstructed was.
    try std.testing.expect(db.state.strings.get("q") != null);
    try expectAnswerCount(&db, "edge(X, Y)?", 0);

    var stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 1), stats.views);
    try std.testing.expectEqual(@as(usize, 1), stats.cached_plans);
    try std.testing.expectEqual(@as(usize, 1), stats.kept_reconstructions);

    db.setViewAvailability(view, .withheld);
    try std.testing.expectError(error.StalePlan, db.explainFold(fold));
    db.clearPlanCache();
    stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 0), stats.cached_plans);
    try std.testing.expectEqual(@as(usize, 0), stats.kept_reconstructions);
}

test "a published rule and a declared base relation are this database's own" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). edge(c, d). label(a, red).
        \\two(X, Z) :- edge(X, Y), edge(Y, Z).
    , null);
    setup.deinit();
    try db.materialize();

    // The definition is the rule this database holds, and the extension the
    // closure this database maintains.
    _ = try db.publishView("two", 2, .materialized);
    const fold = try evenPathQuery(&db);
    defer fold.deinit();
    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    try std.testing.expectEqual(@as(usize, 2), answers.answers.items.len);

    try db.declareBaseAvailable("label", 2);
    const read = try db.foldQuery(&.{input.relation("label", &.{ x, z })}, &.{});
    defer read.deinit();
    try std.testing.expectEqual(Guarantee.equivalent, read.guarantee);
    var labels = try db.answerFolded(read, &.{});
    defer labels.deinit();
    try std.testing.expectEqual(@as(usize, 1), labels.answers.items.len);

    // A rule the database adds is one the views notice.
    try db.addRule(input.relation("two", &.{ x, y }), &.{input.relation("edge", &.{ x, y })});
    try std.testing.expectError(error.StaleViewDefinition, evenPathQuery(&db));
}

test "a copy of a database keeps its views and folds afresh" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const view = try declareEvenPathViews(&db);
    const fold = try evenPathQuery(&db);
    defer fold.deinit();
    var answers = try db.answerFolded(fold, &.{});
    answers.deinit();

    // The views belong to the database, so a copy of it has them: the same
    // question folds to the same guarantee and the same answers without being
    // declared again. The folded plans do not come with it — a cache is not
    // state — so the copy folds afresh.
    var copy = try db.clone();
    defer copy.deinit();
    try std.testing.expectEqual(@as(usize, 1), copy.foldStats().views);
    try std.testing.expectEqual(@as(usize, 0), copy.foldStats().cached_plans);
    const copied = try evenPathQuery(&copy);
    defer copied.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, copied.guarantee);
    try std.testing.expect(!copied.reused);
    var copied_answers = try copy.answerFolded(copied, &.{});
    defer copied_answers.deinit();
    try std.testing.expectEqual(@as(usize, 4), copied_answers.answers.items.len);

    // And the two go their own ways: a view withheld in the copy is still
    // readable here.
    copy.setViewAvailability(view, .withheld);
    try std.testing.expectError(error.StalePlan, copy.answerFolded(copied, &.{}));
    var still = try db.answerFolded(fold, &.{});
    defer still.deinit();
    try std.testing.expectEqual(@as(usize, 4), still.answers.items.len);
}

test "a membership goal answers each element once, and nothing for a list that never ends" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute("items(twice, [a, b, a]). items(open, a!b).", null);
    setup.deinit();

    const cases = [_]struct { element: input.Term, negated: bool, answers: usize }{
        // `a` is held twice and answered once; the list that ends in `b`
        // holds nothing at all, however many cells it has.
        .{ .element = input.variable("X"), .negated = false, .answers = 2 },
        // Negated, the question is only whether the element is there, and a
        // list that never ends does not hold one.
        .{ .element = input.atom("a"), .negated = true, .answers = 1 },
        .{ .element = input.atom("c"), .negated = true, .answers = 2 },
    };
    for (cases) |case| {
        var goals: [2]syntax.Clause = undefined;
        goals[0] = .{ .relational = try compile.compileRelation(&db.state, "items", &.{
            input.variable("N"),
            input.variable("S"),
        }, false) };
        defer syntax.freeClauseTree(allocator, goals[0]);
        var membership = try compile.compileBuiltin(&db.state, .member, &.{
            case.element,
            input.variable("S"),
        });
        membership.negated = case.negated;
        goals[1] = if (case.negated) .{ .negated = membership } else .{ .builtin = membership };
        defer syntax.freeClauseTree(allocator, goals[1]);
        var result = try transaction.queryClauses(&db.state, &goals, &.{});
        defer result.deinit();
        try std.testing.expectEqual(case.answers, result.answers.items.len);
    }
}

const age_schema = input.schema("age", &.{
    input.column("Person", .atom),
    input.column("Years", .int),
});

test "declareSchema enforces a schema through every interface that adds facts" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.declareSchema(age_schema);
    try db.declareSchema(age_schema);
    try std.testing.expectError(
        errors.Error.SchemaConflict,
        db.declareSchema(input.schema("age", &.{ input.column(null, .atom), input.column(null, .int) })),
    );
    try db.addFact("age", &.{ input.atom("alice"), input.integer(36) });
    try std.testing.expectError(
        errors.Error.SchemaViolation,
        db.addFact("age", &.{ input.atom("bob"), input.atom("old") }),
    );

    // One bad insertion rejects the whole batch, deletions included.
    try std.testing.expectError(errors.Error.SchemaViolation, db.applyChanges(&.{
        input.fact("age", &.{ input.atom("bob"), input.integer(17) }),
        input.fact("age", &.{ input.atom("carol"), input.float(2.5) }),
    }, &.{
        input.fact("age", &.{ input.atom("alice"), input.integer(36) }),
    }));
    try std.testing.expectEqual(@as(usize, 1), db.state.facts.len());
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("age", &.{ input.atom("bob"), input.integer(17) }),
    }, &.{}));

    try std.testing.expectError(errors.Error.IllTyped, db.addRule(
        input.relation("age", &.{ input.variable("P"), input.variable("P") }),
        &.{input.relation("person", &.{input.variable("P")})},
    ));
    try std.testing.expectError(errors.Error.IllTyped, db.query(
        &.{input.relation("age", &.{ input.variable("P"), input.atom("old") })},
        &.{},
    ));
    try std.testing.expectError(errors.Error.IllTyped, db.retract(
        &.{input.relation("age", &.{input.variable("P")})},
    ));

    // A copy is a database, and its schemas come with it.
    var copy = try db.clone();
    defer copy.deinit();
    try std.testing.expectError(
        errors.Error.SchemaViolation,
        copy.addFact("age", &.{ input.atom("dan"), input.atom("old") }),
    );
}

test "countFacts separates base facts from the facts only rules derive" {
    var db = Jatalog.init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). path(a, b).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
    , null);
    result.deinit();

    try std.testing.expectEqual(FactCount{ .base = 2 }, try db.countFacts("edge", 2));
    // path(a, b) is base and derived, and counts once, as base.
    try std.testing.expectEqual(FactCount{ .base = 1, .derived = 2 }, try db.countFacts("path", 2));
    try std.testing.expectEqual(FactCount{}, try db.countFacts("path", 3));
    try std.testing.expectEqual(FactCount{}, try db.countFacts("unknown", 1));

    // An update leaves the closure dirty; counting brings it up to date.
    try db.addFact("edge", &.{ input.atom("c"), input.atom("d") });
    try std.testing.expectEqual(FactCount{ .base = 1, .derived = 5 }, try db.countFacts("path", 2));
}

test "predicates lists facts, rule heads and schemas, with their columns" {
    var db = Jatalog.init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\schema age(Who: atom, int).
        \\schema empty(Thing: atom).
        \\edge(a, b). edge(b, c). path(a, b). edge(z).
        \\path(X, Y) :- edge(X, Y).
        \\never(X) :- edge(X, X).
        \\age(ada, 36).
    , null);
    result.deinit();

    const listed = try db.predicates(std.testing.allocator);
    defer std.testing.allocator.free(listed);
    const expected = [_]struct { []const u8, usize, FactCount, bool, bool }{
        .{ "age", 2, .{ .base = 1 }, false, true },
        .{ "edge", 1, .{ .base = 1 }, false, false },
        .{ "edge", 2, .{ .base = 2 }, false, false },
        .{ "empty", 1, .{}, false, true },
        .{ "never", 1, .{}, true, false },
        .{ "path", 2, .{ .base = 1, .derived = 1 }, true, false },
    };
    try std.testing.expectEqual(expected.len, listed.len);
    for (expected, listed) |want, got| {
        try std.testing.expectEqualStrings(want[0], got.name);
        try std.testing.expectEqual(want[1], got.arity);
        try std.testing.expectEqual(want[2], got.facts);
        try std.testing.expectEqual(want[3], got.has_rules);
        try std.testing.expectEqual(want[4], got.typed);
    }

    const columns = (try db.schemaColumns(std.testing.allocator, "age")).?;
    defer std.testing.allocator.free(columns);
    try std.testing.expectEqual(@as(usize, 2), columns.len);
    try std.testing.expectEqualStrings("Who", columns[0].name.?);
    try std.testing.expect(columns[0].type.eql(.atom));
    try std.testing.expectEqual(@as(?[]const u8, null), columns[1].name);
    try std.testing.expect(columns[1].type.eql(.int));
    try std.testing.expectEqual(@as(?[]SchemaColumn, null), try db.schemaColumns(std.testing.allocator, "edge"));
}

test "quoted atoms escape line breaks and tabs, and reparse to themselves" {
    var db = Jatalog.init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("p('two\\nlines\\tand\\ra \\\\ and \\'').", null);
    result.deinit();

    var answers = try db.query(&.{input.relation("p", &.{input.variable("X")})}, &.{});
    defer answers.deinit();
    const value = answers.answers.items[0].bindings.items[0].value;
    try std.testing.expectEqualStrings("two\nlines\tand\ra \\ and '", try value.getAtom());
    const written = try value.formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(written);
    try std.testing.expectEqualStrings("'two\\nlines\\tand\\ra \\\\ and \\''", written);

    // Writing it back into a program names the same atom.
    const source = try std.fmt.allocPrint(std.testing.allocator, "p({s})~", .{written});
    defer std.testing.allocator.free(source);
    var retracted = try db.execute(source, null);
    retracted.deinit();
    try std.testing.expectEqual(FactCount{}, try db.countFacts("p", 1));
}

test "baseFacts lists what was asserted, including facts a rule derives too" {
    var db = Jatalog.init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\edge(a, b). edge(b, c). path(a, b).
        \\path(X, Y) :- edge(X, Y).
    , null);
    result.deinit();

    var base = try db.baseFacts("path", 2);
    defer base.deinit();
    try std.testing.expectEqual(@as(usize, 1), base.answers.items.len);
    try std.testing.expectEqualStrings("a", try base.answers.items[0].getAtom("1"));
    try std.testing.expectEqualStrings("b", try base.answers.items[0].getAtom("2"));

    var none = try db.baseFacts("unknown", 2);
    defer none.deinit();
    try std.testing.expectEqual(@as(usize, 0), none.answers.items.len);
    try std.testing.expectEqual(@as(usize, 2), none.variables.items.len);
}
