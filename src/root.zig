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
/// One statement's transaction: what a front end runs a statement in.
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

/// An embeddable Datalog database.
///
/// The engine's state is `state`, and every operation here is expressed in
/// terms of the layers that act on it. Those layers are not part of this
/// interface: an embedder drives the database through these methods, and a
/// statement front end additionally through `Transaction`.
pub const Jatalog = struct {
    state: database.Database,
    /// What a fold of a query against this database is allowed to read.
    ///
    /// The catalog is owned here rather than held beside a database because it
    /// cannot outlive one: its predicate names and its constants are this
    /// database's identifiers, so a catalog paired with the wrong database
    /// resolves to nothing and a catalog paired with none resolves to nothing
    /// at all. Owning it is what makes that pairing impossible to get wrong,
    /// and it is also the only way a view can be declared from the borrowed
    /// descriptors this interface speaks, since compiling them needs the
    /// database that will hold them.
    views: view_catalog.Catalog,
    /// Plans already folded against those views.
    plans: PlanCache,

    pub fn init(allocator: std.mem.Allocator) Jatalog {
        return .{
            .state = .init(allocator),
            .views = .init(allocator),
            .plans = .{ .allocator = allocator },
        };
    }

    pub fn deinit(self: *Jatalog) void {
        self.plans.deinit();
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
            .plans = .{ .allocator = self.state.allocator },
        };
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const input.Term) !void {
        var staging = try self.state.clone();
        defer staging.deinit();
        try program_runner.addFact(&staging, input.fact(predicate, terms));
        self.state.commit(&staging);
    }

    pub fn addRule(self: *Jatalog, head: input.Goal, body: []const input.Goal) !void {
        const relation = switch (head) {
            .relation => |relation| relation,
            else => return errors.Error.InvalidRule,
        };
        var staging = try self.state.clone();
        defer staging.deinit();
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
        defer staging.deinit();
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
        try materialization.ensureMaterialized(&self.state);
        // The copy is discarded and the instrument is not: a query's
        // candidates are this database's candidates whichever copy examined
        // them. See `evaluationWork`.
        const work_before = self.state.eval.cost.work;
        var staging = try self.state.clone();
        defer {
            self.noteStagedWork(work_before, &staging);
            staging.deinit();
        }
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        return transaction.queryClauses(&staging, compiled, order);
    }

    /// Charges this database with what evaluating on a staging copy cost,
    /// before the copy goes. `baseline` is where the counter stood when the
    /// copy was taken, so what is charged is what the copy did rather than
    /// what it inherited — and it is added to wherever the counter stands
    /// now, which need not be the baseline if the operation also committed
    /// work of its own.
    fn noteStagedWork(
        self: *Jatalog,
        baseline: u64,
        staging: *const database.Database,
    ) void {
        self.state.eval.cost.work +|= staging.eval.cost.work -| baseline;
    }

    pub fn retract(self: *Jatalog, goals: []const input.Goal) !bool {
        try materialization.ensureMaterialized(&self.state);
        const work_before = self.state.eval.cost.work;
        var staging = try self.state.clone();
        defer {
            self.noteStagedWork(work_before, &staging);
            staging.deinit();
        }
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        var removed = try transaction.resolveRetraction(&staging, compiled);
        defer removed.deinit();
        if (removed.len() == 0) return false;
        try transaction.commitRetraction(&self.state, &removed);
        return true;
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
        defer staging.deinit();
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
        defer staging.deinit();
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
        defer staging.deinit();
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
        try materialization.ensureMaterialized(&self.state);
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        return transaction.explainClauses(&staging, compiled);
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
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled = try compileProgramRule(&staging, head, body);
        defer syntax.freeRule(staging.allocator, compiled);
        const id = try self.views.define(compiled, availability);
        self.state.commit(&staging);
        return id;
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
        const name = self.state.strings.get(predicate) orelse return error.UndefinedView;
        var found: ?syntax.Rule = null;
        for (self.state.eval.rules.items) |rule| {
            if (rule.head.predicate != name or rule.head.terms.len != arity) continue;
            if (found != null) return error.UndefinedView;
            found = rule;
        }
        const definition = found orelse return error.UndefinedView;
        return self.views.defineFrom(
            definition,
            availability,
            .{ .materialized_rule = self.state.eval.next_rule_id },
        );
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
        const name = try self.state.strings.intern(predicate);
        try self.views.declareBaseAvailable(.{ .name = name, .arity = arity });
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
        if (self.views.ambiguity() != null) return error.AmbiguousViewName;
        if (self.views.staleAt(self.state.eval.next_rule_id) != null)
            return error.StaleViewDefinition;
        self.plans.refresh(self.views.generation, self.state.eval.next_rule_id);
        // Sizes are read off the stored extensions, and a maintained view's
        // are derived, so this materializes exactly as `explainQuery` does.
        // It changes no answer either way: what is being decided is which of
        // two interchangeable views to read.
        try materialization.ensureMaterialized(&self.state);

        const allocator = self.state.allocator;
        var staging = try self.state.clone();
        defer staging.deinit();
        const compiled_goals = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled_goals) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled_goals);
        }
        const compiled_rules = try compileProgramRules(&staging, rules);
        defer freeProgramRules(staging.allocator, compiled_rules);
        try typing.checkGoals(&staging, compiled_goals);
        for (compiled_rules) |rule| try typing.checkRule(&staging, rule.head, rule.body);

        const key = try folding.normalizeQuery(allocator, compiled_goals, compiled_rules);
        var key_owned = true;
        defer if (key_owned) allocator.free(key);
        // A hit needs nothing the staged copy interned, so the copy is
        // dropped: asking the same question twice must not grow the database.
        if (self.plans.find(key)) |index| {
            self.plans.hits += 1;
            return self.handle(index, true, try answerNames(&staging, compiled_goals));
        }
        self.plans.misses += 1;

        const goal_scope = try self.views.symbols.openScope(.query);
        const lowered_goals = try fold_ir.lowerClauses(
            allocator,
            &self.views.symbols,
            goal_scope,
            compiled_goals,
        );
        defer fold_ir.freeGoals(allocator, lowered_goals);
        const lowered_rules = try lowerProgramRules(allocator, &self.views.symbols, compiled_rules);
        defer {
            for (lowered_rules) |rule| fold_ir.freeRule(allocator, rule);
            allocator.free(lowered_rules);
        }

        // Sizes, for the one decision cost is allowed to make: which of
        // several views that reconstruct one relation exactly to read. Pointed
        // at the staged copy for the length of the fold and taken away after,
        // so the catalog never holds a store that has gone.
        self.views.extensions = staging.closureStore();
        defer self.views.extensions = null;
        var outcome = try folding.foldQuery(allocator, &self.views, .{
            .goals = lowered_goals,
            .rules = lowered_rules,
        });
        var outcome_owned = true;
        defer if (outcome_owned) outcome.deinit();

        var executable: ?folding.Executable = null;
        if (outcome.plan()) |plan| {
            executable = folding.lowerPlan(
                allocator,
                &staging.strings,
                &self.views.symbols,
                plan,
            ) catch |err| switch (err) {
                // A plan still holding a term the evaluator has no meaning for
                // is not lowered and not discarded: it can still be read, and
                // saying so is more use than refusing the fold.
                error.PlanNotExecutable => null,
                else => |other| return other,
            };
        }
        errdefer if (executable) |*value| value.deinit();

        // Where the query's own answer variables went in the plan, in the
        // order the query mentions them. A later caller asking the same
        // question with other names mentions its variables in this same
        // order, because the key it matched is the question with variables
        // numbered by first mention.
        const surface = try transaction.answerVariables(&staging, compiled_goals);
        defer allocator.free(surface);
        const answer_variables = try allocator.alloc(syntax.Id, surface.len);
        var answer_variables_owned = true;
        defer if (answer_variables_owned) allocator.free(answer_variables);
        for (surface, answer_variables) |name, *slot| slot.* = try folding.executableVariableName(
            allocator,
            &staging.strings,
            &self.views.symbols,
            try self.views.symbols.userVariable(goal_scope, name),
        );

        const names = try answerNames(&staging, compiled_goals);
        errdefer freeNames(allocator, names);

        const index = try self.plans.insert(key, outcome, executable, answer_variables);
        key_owned = false;
        outcome_owned = false;
        answer_variables_owned = false;
        self.state.commit(&staging);
        return self.handle(index, false, names);
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
    /// are not here afterwards. It is *kept* — in the plan cache, beside the
    /// plan that built it — so that asking the same question again solves the
    /// goals against a reconstruction that is already derived instead of
    /// deriving it a second time. Deriving it is 63% to 99% of what a folded
    /// answer costs, and it is the same derivation every time until the
    /// database underneath it changes.
    ///
    /// What "changes" means is three stamps and not two. The catalog's
    /// generation and the rule generation are the plan's, and a move in
    /// either discards the plan itself. A base fact moves neither — the plan
    /// is still the right plan, and `Fold` handles stay live across an
    /// insertion on purpose — but it moves the extension the plan reads, so
    /// `Database.fact_generation` discards the reconstruction without
    /// touching the plans. Conflating the two would re-fold on every
    /// insertion and undo the plan cache to fix a problem the plan cache does
    /// not have.
    ///
    /// Answers list the caller's own variables under the caller's own names,
    /// even when another caller's question folded the plan first, and nothing
    /// the plan introduced for itself. `order` lists them as `query` would: the order
    /// is presentation, so it is not part of the fold and the same plan
    /// serves every order.
    pub fn answerFolded(self: *Jatalog, fold: Fold, order: []const input.SortKey) !results.QueryResult {
        const cached = try self.planAt(fold);
        if (cached.executable == null) return error.PlanNotExecutable;
        // Before anything is read from a kept reconstruction, and after the
        // handle is known to be live: a fact under a readable name is the one
        // change that gets this far.
        self.plans.refreshReconstructions(self.state.fact_generation);
        if (self.plans.entries.items[fold.entry].reconstruction == null) {
            // A view whose extension the engine derives has to have derived
            // it before the copy is taken, or the copy keeps a name with
            // nothing under it.
            try materialization.ensureMaterialized(&self.state);
            const baseline = self.state.eval.cost.work;
            const staged = try self.deriveReconstruction(
                &self.plans.entries.items[fold.entry].executable.?,
            );
            // Past here the cache owns it, and taking it in allocates
            // nothing, so there is no window where it belongs to neither.
            self.plans.keep(fold.entry, staged);
            self.noteStagedWork(
                baseline,
                &self.plans.entries.items[fold.entry].reconstruction.?,
            );
        } else {
            self.plans.reconstruction_hits += 1;
            self.plans.touch(fold.entry);
        }

        const entry = &self.plans.entries.items[fold.entry];
        // Solving interns the goals' ground structures into the
        // reconstruction and can expand its closure, so a failure part-way
        // leaves a database no later answer may be read from. It goes, and
        // the next call derives a fresh one.
        errdefer self.plans.discardReconstruction(fold.entry);
        // The reconstruction is kept, so its counter is cumulative and only
        // this call's share of it belongs here.
        const work_before = entry.reconstruction.?.eval.cost.work;
        const answers = try transaction.queryClausesAs(
            &entry.reconstruction.?,
            entry.executable.?.goals,
            .{ .variables = entry.answer_variables, .names = fold.names },
            order,
        );
        self.state.eval.cost.work +|=
            entry.reconstruction.?.eval.cost.work -| work_before;
        return answers;
    }

    /// Builds what a folded plan reads from: a copy of this database holding
    /// exactly what the catalog admits, the plan's own rules installed in it,
    /// and the relations those rules reconstruct already derived.
    ///
    /// Deriving here rather than leaving it to `queryClauses` is the whole of
    /// the split. `transaction.evaluateClauses` materializes on its way to
    /// solving, so a caller that lets it do both cannot tell the two phases
    /// apart, let alone keep one of them; done here, the closure is clean
    /// before any goal is solved and a later call finds it that way.
    /// The caller materializes this database first: a view whose extension the
    /// engine derives has to have derived it before the copy is taken, or the
    /// copy keeps a name with nothing under it.
    fn deriveReconstruction(
        self: *Jatalog,
        executable: *const folding.Executable,
    ) !database.Database {
        var staged = try self.viewOnlyCopy();
        errdefer staged.deinit();
        for (executable.rules) |rule| {
            const copy = try syntax.cloneRule(staged.allocator, rule);
            transaction.addRuleClauses(&staged, copy.head, copy.body) catch |err| {
                syntax.freeRule(staged.allocator, copy);
                return err;
            };
            staged.allocator.free(copy.body);
        }
        try materialization.ensureMaterialized(&staged);
        return staged;
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
        const entry = try self.planAt(fold);
        return entry.outcome.explainAlloc(self.state.allocator, .{
            .symbols = &self.views.symbols,
            .strings = &self.state.strings,
            .scalars = &self.state.eval.scalars,
        });
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
        const entry = try self.planAt(fold);
        var result: Reconstructions = .{ .allocator = self.state.allocator, .items = &.{} };
        errdefer result.deinit();
        const plan = entry.outcome.plan() orelse return result;
        var found: std.ArrayList(Reconstruction) = .empty;
        errdefer {
            for (found.items) |item| self.state.allocator.free(item.predicate);
            found.deinit(self.state.allocator);
        }
        for (plan.transformations) |transformation| {
            const exact = switch (transformation.kind) {
                .relation_reconstructed => false,
                .relation_reconstructed_exactly => true,
                else => continue,
            };
            const subject = transformation.subject orelse continue;
            const key = switch (subject) {
                .base => |value| value,
                else => continue,
            };
            const name = try self.state.allocator.dupe(u8, self.state.strings.resolve(key.name));
            found.append(self.state.allocator, .{
                .predicate = name,
                .arity = key.arity,
                .exact = exact,
            }) catch |err| {
                self.state.allocator.free(name);
                return err;
            };
        }
        result.items = try found.toOwnedSlice(self.state.allocator);
        return result;
    }

    /// How many views are declared and how the plan cache has been doing.
    pub fn foldStats(self: *const Jatalog) FoldStats {
        return .{
            .views = self.views.views.items.len,
            .cached_plans = self.plans.entries.items.len,
            .plan_hits = self.plans.hits,
            .plan_misses = self.plans.misses,
            .plan_invalidations = self.plans.invalidations,
            .kept_reconstructions = self.plans.kept,
            .reconstruction_hits = self.plans.reconstruction_hits,
            .reconstruction_misses = self.plans.reconstruction_misses,
        };
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
        self.plans.clear();
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

    /// The cached plan a handle names, or `StalePlan` when the views or the
    /// rules have moved on since it was folded.
    ///
    /// Checked against the catalog and the program as they stand now rather
    /// than against the cache's own stamp, because a caller can change either
    /// without folding anything, and a handle that survived such a change
    /// would name whichever plan later took its place.
    fn planAt(self: *Jatalog, fold: Fold) !*const CachedPlan {
        if (fold.catalog_generation != self.views.generation) return error.StalePlan;
        if (fold.rule_generation != self.state.eval.next_rule_id) return error.StalePlan;
        if (fold.catalog_generation != self.plans.catalog_generation) return error.StalePlan;
        if (fold.rule_generation != self.plans.rule_generation) return error.StalePlan;
        if (fold.entry >= self.plans.entries.items.len) return error.StalePlan;
        return &self.plans.entries.items[fold.entry];
    }

    /// A handle on plan `index` for a caller who calls its answer variables
    /// `names`, which the handle takes.
    fn handle(self: *const Jatalog, index: usize, reused: bool, names: []const []const u8) Fold {
        return .{
            .allocator = self.state.allocator,
            .guarantee = self.plans.entries.items[index].outcome.guarantee(),
            .reused = reused,
            .entry = index,
            .catalog_generation = self.plans.catalog_generation,
            .rule_generation = self.plans.rule_generation,
            .names = names,
        };
    }

    /// A copy of this database holding only what a plan is allowed to read.
    ///
    /// The extensions are taken from the closure rather than from the base
    /// facts, because a view the engine maintains stores its tuples there and
    /// nowhere else; they arrive in the copy as base facts, which is what they
    /// are to a plan. Everything else goes: the other facts, the derived
    /// closure, the auxiliary views, and the database's own rules — one of
    /// those deriving a withheld relation would put it straight back, and the
    /// plan brings every rule it needs.
    fn viewOnlyCopy(self: *Jatalog) !database.Database {
        var copy = try self.state.clone();
        errdefer copy.deinit();

        var kept: std.ArrayList(relation_store.Fact) = .empty;
        defer {
            for (kept.items) |fact| copy.allocator.free(fact.terms);
            kept.deinit(copy.allocator);
        }
        const stored = copy.closureStore();
        for (0..stored.len()) |index| {
            const fact = stored.factAt(index);
            if (!self.readableByPlans(.{ .name = fact.predicate, .arity = fact.terms.len }))
                continue;
            try relation_store.appendFactCopy(copy.allocator, &kept, fact);
        }

        if (copy.closure) |*closure| {
            closure.deinit();
            copy.closure = null;
        }
        copy.materialization = .uninitialized;
        // The plan was checked against the schemas when it was folded. The
        // rules it installs here are its own — inverse rules the caller never
        // wrote — and hold facts a plan reconstructs rather than asserts.
        copy.schemas.deinit(copy.allocator);
        copy.schemas = .{};
        materialization.dropAuxiliaryViews(&copy);
        for (copy.eval.rules.items) |rule| syntax.freeRule(copy.allocator, rule);
        copy.eval.rules.clearRetainingCapacity();
        copy.eval.invalidateAnalysis();
        copy.facts.clear();
        for (kept.items) |fact|
            try relation_store.copyFactInto(copy.allocator, &copy.facts, fact, false);
        return copy;
    }

    /// Whether a plan may read facts stored under this name and arity: a base
    /// relation the policy declared, or a readable view's extension.
    fn readableByPlans(self: *const Jatalog, key: relation_store.PredicateKey) bool {
        if (self.views.baseAvailable(key)) return true;
        for (self.views.views.items) |defined| {
            if (!defined.readable()) continue;
            if (defined.name == key.name and defined.column_kinds.arity() == key.arity) return true;
        }
        return false;
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
        );
    }

    /// Runs statements — parsed by `parseProgram` or built by hand — in
    /// order, returning the last one's result. Consecutive facts and rules
    /// share one transaction, which is what makes loading many facts cheap; a
    /// statement that fails keeps every statement before it and none of
    /// itself, and `diagnostic` names it by index.
    pub fn executeStatements(
        self: *Jatalog,
        statements: []const input.Statement,
        diagnostic: ?*Diagnostic,
    ) !results.ExecutionResult {
        return program_runner.execute(&self.state, statements, null, diagnostic);
    }
};

/// A plan a fold produced, and what it was folded against.
///
/// It is a handle rather than the plan itself, because the plan belongs to the
/// database's cache and the same question asked twice is the same plan. Every
/// operation taking one checks that the views and the rules it was folded
/// against are still the ones the database has, and reports `StalePlan` if
/// they are not — a plan folded under other definitions is a different
/// program, and quietly running it would be the one mistake this whole
/// interface exists to prevent.
pub const Fold = struct {
    /// What this plan's answers are worth, relative to the query's. See
    /// `foldQuery`. `unsupported` means there is no plan at all — not an empty
    /// one — and only `explainFold` has anything to say about it.
    guarantee: Guarantee,
    /// Whether an already-folded plan answered this rather than a fresh fold.
    reused: bool,
    entry: usize,
    catalog_generation: u64,
    rule_generation: u32,
    /// The names this caller gave its answer variables, in the order its
    /// query mentions them. A cached plan is shared by every caller asking
    /// the same question, whatever they called its variables, so the names
    /// belong to the handle rather than to the plan.
    names: []const []const u8,
    allocator: std.mem.Allocator,

    /// Releases the names. A handle copied by value shares them, so only one
    /// copy is released.
    pub fn deinit(self: Fold) void {
        freeNames(self.allocator, self.names);
    }
};

/// What `goals` call their answer variables, in the order they mention them.
fn answerNames(staging: *database.Database, goals: []const syntax.Clause) ![]const []const u8 {
    const allocator = staging.allocator;
    const surface = try transaction.answerVariables(staging, goals);
    defer allocator.free(surface);
    const names = try allocator.alloc([]const u8, surface.len);
    var built: usize = 0;
    errdefer {
        for (names[0..built]) |name| allocator.free(name);
        allocator.free(names);
    }
    for (surface, names) |variable, *slot| {
        slot.* = try allocator.dupe(u8, staging.strings.resolve(variable));
        built += 1;
    }
    return names;
}

fn freeNames(allocator: std.mem.Allocator, names: []const []const u8) void {
    for (names) |name| allocator.free(name);
    allocator.free(names);
}

/// A relation a plan derives instead of reading, and how much of it.
pub const Reconstruction = struct {
    predicate: []const u8,
    arity: usize,
    /// Whether the plan derives the whole relation rather than as much of it
    /// as the views prove.
    exact: bool,
};

/// The relations one plan reconstructs. Owned by the caller.
pub const Reconstructions = struct {
    allocator: std.mem.Allocator,
    items: []Reconstruction,

    pub fn deinit(self: *Reconstructions) void {
        for (self.items) |item| self.allocator.free(item.predicate);
        self.allocator.free(self.items);
        self.* = undefined;
    }
};

pub const FoldStats = struct {
    views: usize,
    cached_plans: usize,
    plan_hits: usize,
    plan_misses: usize,
    /// Times every cached plan was discarded at once because the views or the
    /// rules changed.
    plan_invalidations: usize,
    /// Reconstructions held right now: databases the cached plans last ran
    /// against, kept so that running one again only solves goals. Bounded,
    /// unlike the plans; see `clearPlanCache`.
    kept_reconstructions: usize,
    /// How often a folded answer found the reconstruction already derived,
    /// and how often it had to derive one — the first time a plan is run, and
    /// after every change to the base facts.
    reconstruction_hits: usize,
    reconstruction_misses: usize,
};

/// One folded plan, kept so that asking the same question again does not fold
/// it again — and, once it has been run, what it ran against, kept so that
/// asking again does not derive that again either.
const CachedPlan = struct {
    /// The normalized question. Two callers asking it differently — other
    /// variable names, the same relations — key to the same bytes.
    key: []u8,
    outcome: folding.Outcome,
    /// The plan in the executable language, or null when there is nothing to
    /// run: an unsupported fold, or a plan still holding a term the evaluator
    /// has no meaning for. The rendering is available either way.
    executable: ?folding.Executable,
    /// The database this plan last ran against: what the catalog admits, with
    /// the plan's rules installed and their consequences derived. Null until
    /// the plan has been run, and again whenever the base facts move.
    ///
    /// This is a whole database hanging off a cache entry, which is a
    /// memory-for-time trade the plan cache has never made before — a plan is
    /// small and this is a copy of every readable extension plus its closure.
    /// It is why `PlanCache` bounds how many of these it holds while leaving
    /// the plans themselves unbounded.
    reconstruction: ?database.Database = null,
    /// When this entry's reconstruction was last read, on the cache's own
    /// clock, so the bound above knows which one to drop.
    last_used: u64 = 0,
    /// The names the plan's answers carry the query's answer variables
    /// under, in the order the query mentions them. `Fold.names` says what
    /// each caller calls them.
    answer_variables: []syntax.Id,

    fn deinit(self: *CachedPlan, allocator: std.mem.Allocator) void {
        allocator.free(self.answer_variables);
        self.discardReconstruction();
        if (self.executable) |*value| value.deinit();
        self.outcome.deinit();
        allocator.free(self.key);
        self.* = undefined;
    }

    fn discardReconstruction(self: *CachedPlan) void {
        if (self.reconstruction) |*staged| staged.deinit();
        self.reconstruction = null;
    }
};

/// The plans folded so far, and what they were folded against.
///
/// A plan is a function of two things and no others: the question, and the
/// catalog — its definitions together with its availability policy. So the key
/// is the normalized question, and the *cache as a whole* carries the
/// catalog's generation, because a definition added or an availability
/// withdrawn changes every plan folded under it rather than one of them.
/// Publishing a view from a database rule brings the rule generation into that
/// stamp for the same reason: such a definition is the rule's, and a rule
/// addition can change what the predicate means.
///
/// A plan's *reconstruction* is a function of one more thing — the facts —
/// and that is a third stamp rather than a third component of the key, for
/// the same reason: a fact changes what every reconstruction here was derived
/// from rather than which plan answers a question. It is kept apart from the
/// other two because it invalidates something else. The catalog and the rules
/// discard the plans; the facts discard only what the plans ran against.
///
/// Cardinalities are deliberately not in the key, and that is what costing
/// only provably interchangeable plans buys. Sizes move with every fact
/// inserted, and index availability moves with every query run — P1 builds a
/// pattern index on the *second* request for it — so a plan keyed on either
/// would be a plan whose identity depended on when it was asked for. Since
/// cost here only ever chooses between plans already proved to answer the
/// same, a stale choice is a slower plan and never a different answer, which
/// is the same licence the join planner runs on.
const PlanCache = struct {
    /// How many reconstructions this cache will hold at once.
    ///
    /// The plans are unbounded because a plan is small and discarding one
    /// costs a fold. A reconstruction is a database, so a cache holding one
    /// per entry would grow with the number of distinct questions ever asked,
    /// which is not a bound at all. Small, because the workload this exists
    /// for is a question asked repeatedly and one entry answers it; more than
    /// one, because an embedder with a handful of standing questions would
    /// otherwise get nothing from the cache but the cost of filling it.
    const reconstruction_limit: usize = 4;

    allocator: std.mem.Allocator,
    entries: std.ArrayList(CachedPlan) = .empty,
    catalog_generation: u64 = 0,
    rule_generation: u32 = 0,
    /// The base facts the kept reconstructions were derived from. Separate
    /// from the two above because it invalidates something else: a fact
    /// leaves every plan here valid and every reconstruction stale.
    fact_generation: u64 = 0,
    hits: usize = 0,
    misses: usize = 0,
    invalidations: usize = 0,
    reconstruction_hits: usize = 0,
    reconstruction_misses: usize = 0,
    kept: usize = 0,
    /// Orders reads of kept reconstructions, so the bound can drop the one
    /// that has gone longest unread.
    use_clock: u64 = 0,

    fn deinit(self: *PlanCache) void {
        self.clear();
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    fn clear(self: *PlanCache) void {
        for (self.entries.items) |*entry| entry.deinit(self.allocator);
        self.entries.clearRetainingCapacity();
        self.kept = 0;
    }

    /// Discards every kept reconstruction when the facts they were derived
    /// from have moved, leaving the plans alone.
    ///
    /// The stamp is one counter over the whole fact store, so there is no
    /// such thing as refreshing one of these either: every reconstruction
    /// here was derived from the facts the database now holds, or none was.
    fn refreshReconstructions(self: *PlanCache, fact_generation: u64) void {
        if (self.fact_generation == fact_generation) return;
        for (self.entries.items) |*entry| entry.discardReconstruction();
        self.kept = 0;
        self.fact_generation = fact_generation;
    }

    /// Takes ownership of a reconstruction, making room for it first. Cannot
    /// fail, which is what lets the caller hand one over without a window
    /// where it belongs to neither of them.
    fn keep(self: *PlanCache, index: usize, staged: database.Database) void {
        self.reconstruction_misses += 1;
        if (self.kept >= reconstruction_limit) self.evictLeastRecentlyUsed();
        self.entries.items[index].reconstruction = staged;
        self.kept += 1;
        self.touch(index);
    }

    fn touch(self: *PlanCache, index: usize) void {
        self.use_clock += 1;
        self.entries.items[index].last_used = self.use_clock;
    }

    fn discardReconstruction(self: *PlanCache, index: usize) void {
        if (self.entries.items[index].reconstruction == null) return;
        self.entries.items[index].discardReconstruction();
        self.kept -= 1;
    }

    fn evictLeastRecentlyUsed(self: *PlanCache) void {
        var victim: ?usize = null;
        for (self.entries.items, 0..) |*entry, index| {
            if (entry.reconstruction == null) continue;
            if (victim) |chosen| {
                if (entry.last_used >= self.entries.items[chosen].last_used) continue;
            }
            victim = index;
        }
        self.discardReconstruction(victim orelse return);
    }

    /// Discards every plan when what they were folded against has changed.
    /// Both stamps are counters over the whole catalog and the whole program,
    /// so there is no such thing as invalidating one entry: either every plan
    /// here was folded against what the database now holds, or none was.
    fn refresh(self: *PlanCache, catalog_generation: u64, rule_generation: u32) void {
        if (self.catalog_generation == catalog_generation and
            self.rule_generation == rule_generation) return;
        if (self.entries.items.len != 0) {
            self.clear();
            self.invalidations += 1;
        }
        self.catalog_generation = catalog_generation;
        self.rule_generation = rule_generation;
    }

    fn find(self: *const PlanCache, key: []const u8) ?usize {
        for (self.entries.items, 0..) |entry, index| {
            if (std.mem.eql(u8, entry.key, key)) return index;
        }
        return null;
    }

    /// Takes ownership of `key`, `outcome` and `executable`.
    fn insert(
        self: *PlanCache,
        key: []u8,
        outcome: folding.Outcome,
        executable: ?folding.Executable,
        answer_variables: []syntax.Id,
    ) !usize {
        try self.entries.append(self.allocator, .{
            .key = key,
            .outcome = outcome,
            .executable = executable,
            .answer_variables = answer_variables,
        });
        return self.entries.items.len - 1;
    }
};

/// Compiles and admits one rule of a program a fold is given: a view's
/// definition, or a rule the query defines a predicate of its own by.
///
/// Admission is the same check `addRule` runs, and it is run here for the same
/// reason — an unsafe rule has no meaning to invert — but the clauses keep the
/// order they were written in rather than the order admission would store. A
/// definition is read structurally by the catalog, and a reordered body is a
/// different shape to read.
fn compileProgramRule(
    db: *database.Database,
    head: input.Relation,
    body: []const input.Goal,
) !syntax.Rule {
    const compiled_head = try compile.compileRelation(db, head.predicate, head.terms, false);
    errdefer syntax.freeExpr(db.allocator, compiled_head);
    const compiled_body = try compile.compileGoals(db, body);
    errdefer {
        for (compiled_body) |clause| syntax.freeClauseTree(db.allocator, clause);
        db.allocator.free(compiled_body);
    }
    const seed_argument = try validation.validateRule(db, compiled_head, compiled_body);
    return .{ .head = compiled_head, .body = compiled_body, .seed_argument = seed_argument };
}

fn compileProgramRules(db: *database.Database, rules: []const input.Rule) ![]syntax.Rule {
    const compiled = try db.allocator.alloc(syntax.Rule, rules.len);
    var built: usize = 0;
    errdefer {
        for (compiled[0..built]) |rule| syntax.freeRule(db.allocator, rule);
        db.allocator.free(compiled);
    }
    for (rules, compiled) |rule, *slot| {
        slot.* = try compileProgramRule(db, rule.head, rule.body);
        built += 1;
    }
    return compiled;
}

fn freeProgramRules(allocator: std.mem.Allocator, rules: []syntax.Rule) void {
    for (rules) |rule| syntax.freeRule(allocator, rule);
    allocator.free(rules);
}

/// Lowers the query's own rules into the folding IR, each in a scope of its
/// own: two rules spelling a variable alike mean two variables.
fn lowerProgramRules(
    allocator: std.mem.Allocator,
    symbols: *fold_ir.Symbols,
    rules: []const syntax.Rule,
) ![]fold_ir.Rule {
    const lowered = try allocator.alloc(fold_ir.Rule, rules.len);
    var built: usize = 0;
    errdefer {
        for (lowered[0..built]) |rule| fold_ir.freeRule(allocator, rule);
        allocator.free(lowered);
    }
    for (rules, lowered) |rule, *slot| {
        slot.* = try fold_ir.lowerRule(allocator, symbols, try symbols.openScope(.query), rule);
        built += 1;
    }
    return lowered;
}

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
        var from_statements = try stepped.executeStatements(parsed.value.statements, null);
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

test "parsed rules and goals feed the descriptor interface" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const facts = try parseProgram(std.testing.allocator, "edge(a, b). edge(b, c).", null);
    defer facts.deinit();
    var loaded = try db.executeStatements(facts.value.statements, null);
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
    try std.testing.expectError(Error.InvalidFact, db.executeStatements(&statements, &diagnostic));
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

fn planningAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var setup = try db.execute(
        \\edge(a, b). edge(b, c). node(a). node(b). node(c).
        \\path(X, Y) :- edge(X, Y).
        \\path(X, Z) :- edge(X, Y), path(Y, Z).
        \\reach(X, S) :- node(X), setof(Y, path(X, Y), S).
    , null);
    setup.deinit();
    var result = try db.execute("reach(a, S), not path(a, a)?", null);
    result.deinit();
    const explained = try db.explainQuery(&.{
        input.relation("reach", &.{ input.variable("X"), input.variable("S") }),
        input.not("path", &.{ input.variable("X"), input.variable("X") }),
    });
    allocator.free(explained);
}

test "planning and explaining release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(planningAllocationScenario);
}

/// Compiles a rule against `db`.
///
/// A fold's input is written in the language the database speaks and lowered
/// from there, because lowering only goes one way: the IR has no source form,
/// and a rule written directly in it would be one nothing had admitted.
fn compiledRule(
    db: *database.Database,
    head: input.Relation,
    body: []const input.Goal,
) !syntax.Rule {
    const compiled = try compile.compileRelation(db, head.predicate, head.terms, false);
    errdefer syntax.freeExpr(db.allocator, compiled);
    return .{ .head = compiled, .body = try compile.compileGoals(db, body) };
}

/// One rule of the query program, in the folding IR and in a scope of its own.
fn foldingRule(
    db: *database.Database,
    symbols: *fold_ir.Symbols,
    head: input.Relation,
    body: []const input.Goal,
) !fold_ir.Rule {
    const compiled = try compiledRule(db, head, body);
    defer syntax.freeRule(db.allocator, compiled);
    return fold_ir.lowerRule(db.allocator, symbols, try symbols.openScope(.query), compiled);
}

fn foldingGoals(
    db: *database.Database,
    symbols: *fold_ir.Symbols,
    goals: []const input.Goal,
) ![]fold_ir.Goal {
    const compiled = try compile.compileGoals(db, goals);
    defer {
        for (compiled) |clause| syntax.freeClauseTree(db.allocator, clause);
        db.allocator.free(compiled);
    }
    return fold_ir.lowerClauses(db.allocator, symbols, try symbols.openScope(.query), compiled);
}

fn defineView(
    db: *database.Database,
    catalog: *view_catalog.Catalog,
    head: input.Relation,
    body: []const input.Goal,
    availability: view_catalog.Availability,
) !fold_ir.ViewId {
    const compiled = try compiledRule(db, head, body);
    defer syntax.freeRule(db.allocator, compiled);
    return catalog.define(compiled, availability);
}

/// Installs a lowered plan's rules in `db` and answers its goals there.
///
/// Installing a rule hands its head and its clauses to the database, which is
/// what `takeRule` records: releasing the plan afterwards must not release
/// them a second time.
fn installPlan(db: *database.Database, executable: *folding.Executable) !void {
    for (0..executable.rules.len) |index| {
        const rule = executable.takeRule(index);
        defer db.allocator.free(rule.body);
        transaction.addRuleClauses(db, rule.head, rule.body) catch |err| {
            syntax.freeExpr(db.allocator, rule.head);
            for (rule.body) |clause| syntax.freeClauseTree(db.allocator, clause);
            return err;
        };
    }
}

fn runPlan(db: *database.Database, executable: *folding.Executable) !results.QueryResult {
    try installPlan(db, executable);
    return transaction.queryClauses(db, executable.goals, &.{});
}

/// Adds one fact without staging a copy of the database, which is what the
/// public interface would do. A sweep over hundreds of small databases cannot
/// afford a clone per fact.
fn addFactTerms(
    db: *database.Database,
    predicate: []const u8,
    terms: []const input.Term,
) !void {
    const expression = try compile.compileRelation(db, predicate, terms, false);
    defer syntax.freeExpr(db.allocator, expression);
    try transaction.addFactExpr(db, expression);
}

fn addAtomPair(
    db: *database.Database,
    predicate: []const u8,
    left: []const u8,
    right: []const u8,
) !void {
    return addFactTerms(db, predicate, &.{ input.atom(left), input.atom(right) });
}

/// One line per answer, sorted, holding the values only.
///
/// Unlike `answerLines` these carry no variable names, because the two results
/// being compared are a query's and a plan's: a plan's variables are not the
/// query's, and printing their names would be printing the difference this is
/// meant to see past.
fn answerTuples(result: *const results.QueryResult) ![][]u8 {
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
        for (answer.bindings.items, 0..) |binding, index| {
            if (index != 0) text.writer.writeByte(' ') catch return error.OutOfMemory;
            binding.value.write(&text.writer) catch return error.OutOfMemory;
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

/// Chapter 6's Example 6.2.1, as a program: the transitive closure of a
/// relation that is gone, over a view holding the pairs two edges apart.
///
/// The query rules are recursive and the view definition is not, which is the
/// case the Inverse Method exists for — the reconstructed relation feeds a
/// query the views know nothing about.
fn evenPathProblem(
    db: *database.Database,
    catalog: *view_catalog.Catalog,
    rules: *[2]fold_ir.Rule,
) ![]fold_ir.Goal {
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    _ = try defineView(db, catalog, input.fact("v", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("edge", &.{ y, z }),
    }, .materialized);
    rules[0] = try foldingRule(db, &catalog.symbols, input.fact("q", &.{ x, y }), &.{
        input.relation("edge", &.{ x, y }),
    });
    errdefer fold_ir.freeRule(db.allocator, rules[0]);
    rules[1] = try foldingRule(db, &catalog.symbols, input.fact("q", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("q", &.{ y, z }),
    });
    errdefer fold_ir.freeRule(db.allocator, rules[1]);
    return foldingGoals(db, &catalog.symbols, &.{input.relation("q", &.{ x, y })});
}

test "an inverted view answers Chapter 6's even-length paths from its extension alone" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    // Everything the plan may read: what the view stored. The graph behind it
    // is gone, which is the situation a fold exists for — a test that folded
    // and then read the original edges would prove nothing.
    try db.addFact("v", &.{ input.atom("a"), input.atom("c") });
    try db.addFact("v", &.{ input.atom("b"), input.atom("d") });
    try db.addFact("v", &.{ input.atom("c"), input.atom("e") });

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    var rules: [2]fold_ir.Rule = undefined;
    const goals = try evenPathProblem(&db.state, &catalog, &rules);
    defer fold_ir.freeGoals(allocator, goals);
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    // A view remembers pairs two edges apart and nothing else, so no plan over
    // it can answer every path. Maximal containment is the whole claim.
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();

    // The paths of even length in the dissertation's graph, and only those:
    // a→c, b→d and c→e are two edges each, and a→e is four.
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);
    try std.testing.expectEqual(@as(usize, 4), tuples.len);
    for ([_][]const u8{ "a c", "a e", "b d", "c e" }, tuples) |expected, actual|
        try std.testing.expectEqualStrings(expected, actual);
}

test "a comparison a reconstructed value cannot answer costs answers, not soundness" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("v", &.{ input.atom("a"), input.atom("c") });
    try db.addFact("v", &.{ input.atom("b"), input.atom("d") });
    try db.addFact("v", &.{ input.atom("c"), input.atom("e") });

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("edge", &.{ y, z }),
    }, .materialized);

    // q(X, Z) :- edge(X, Y), edge(Y, Z), X != Z. The middle node is
    // reconstructed and has no name, so the instances that would compare it
    // cannot be run; the one that compares the two ends can.
    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ x, z }),
        &.{
            input.relation("edge", &.{ x, y }),
            input.relation("edge", &.{ y, z }),
            input.notEqual(x, z),
        },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{input.relation("q", &.{ x, z })});
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    // Dropping an instance answers less, which is sound and is not maximal.
    try std.testing.expectEqual(folding.Guarantee.contained, outcome.guarantee());
    const explained = try outcome.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    });
    defer allocator.free(explained);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        explained,
        1,
        "instances that would have read a reconstructed value were dropped",
    ));

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();

    // What survives is the pairs the view itself stores, which are the ones
    // whose two ends the plan can name.
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);
    try std.testing.expectEqual(@as(usize, 3), tuples.len);
    for ([_][]const u8{ "a c", "b d", "c e" }, tuples) |expected, actual|
        try std.testing.expectEqualStrings(expected, actual);
}

/// A graph on three nodes as one bit per possible edge, and the two relations
/// over it the containment sweep needs.
///
/// The oracle is computed here rather than by the engine on purpose: a sweep
/// that asked the engine what the answers were and then asked it again through
/// a plan would agree with itself whatever either one did.
const Graph = struct {
    const nodes = 3;

    fn bit(row: usize, column: usize) u9 {
        return @as(u9, 1) << @intCast(row * nodes + column);
    }

    fn has(mask: u9, row: usize, column: usize) bool {
        return mask & bit(row, column) != 0;
    }

    /// The pairs joined by one edge of `left` followed by one of `right`.
    fn compose(left: u9, right: u9) u9 {
        var result: u9 = 0;
        for (0..nodes) |from| for (0..nodes) |middle| for (0..nodes) |to| {
            if (has(left, from, middle) and has(right, middle, to)) result |= bit(from, to);
        };
        return result;
    }

    fn closure(mask: u9) u9 {
        var reached = mask;
        while (true) {
            const grown = reached | compose(mask, reached);
            if (grown == reached) return reached;
            reached = grown;
        }
    }
};

test "every answer a folded plan returns is one the query would have returned" {
    // The containment claim, checked by exhaustion rather than by argument:
    // over every graph on three nodes, work out what the query answers and
    // what the view stores, then answer the folded plan from the view alone
    // and confirm it invented nothing.
    const allocator = std.testing.allocator;

    // A plan does not depend on the data, so it is folded once. Its predicate
    // and variable names are this database's, which is why the per-graph
    // databases are clones of it rather than fresh ones.
    var planned: Jatalog = .init(allocator);
    defer planned.deinit();
    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    var rules: [2]fold_ir.Rule = undefined;
    const goals = try evenPathProblem(&planned.state, &catalog, &rules);
    defer fold_ir.freeGoals(allocator, goals);
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    var executable = try folding.lowerPlan(
        allocator,
        &planned.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    try installPlan(&planned.state, &executable);

    const names = [_][]const u8{ "a", "b", "c" };
    var answered: usize = 0;
    for (0..512) |value| {
        const edges: u9 = @intCast(value);
        const reachable = Graph.closure(edges);
        const stored = Graph.compose(edges, edges);

        var folded = try planned.clone();
        defer folded.deinit();
        for (0..Graph.nodes) |from| for (0..Graph.nodes) |to| {
            if (Graph.has(stored, from, to))
                try addAtomPair(&folded.state, "v", names[from], names[to]);
        };

        var produced = try transaction.queryClauses(&folded.state, executable.goals, &.{});
        defer produced.deinit();
        for (produced.answers.items) |answer| {
            const from = (try answer.bindings.items[0].value.getAtom())[0] - 'a';
            const to = (try answer.bindings.items[1].value.getAtom())[0] - 'a';
            if (!Graph.has(reachable, from, to)) {
                std.debug.print("\ngraph {b}: the plan answered {c} to {c}\n", .{
                    edges,
                    'a' + from,
                    'a' + to,
                });
                return error.AnswerNotContained;
            }
            answered += 1;
        }
    }
    // A plan that answers nothing is contained in anything, so the sweep has
    // to have seen answers for its agreement to mean anything.
    try std.testing.expect(answered > 0);
}

/// Folds and runs one small even-length-path problem: a catalog built from a
/// definition, a recursive query program, the inverse rules the fold produced,
/// the split relations that made them runnable, and the answers.
///
/// The folding modules need nothing above `relation_store`, but a sweep needs
/// `test_support` and running a plan needs `statement`, so this lives up here
/// with the other lifecycle sweeps rather than in the modules it covers.
fn foldingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("v", &.{ input.atom("a"), input.atom("c") });

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    var rules: [2]fold_ir.Rule = undefined;
    const goals = try evenPathProblem(&db.state, &catalog, &rules);
    defer fold_ir.freeGoals(allocator, goals);
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);

    const names: fold_ir.Names = .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    };
    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    allocator.free(try outcome.explainAlloc(allocator, names));
    if (outcome.guarantee() != .maximally_contained) return error.UnexpectedGuarantee;

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    answers.deinit();
}

test "folding, lowering and running a plan release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(foldingAllocationScenario);
}

test "a predicate the query derives from a reconstruction is no more exact than it is" {
    // The hole a relation-by-relation check leaves. `reach` is the query's own
    // predicate, so nothing about it is reconstructed — but it is derived from
    // `edge`, which is, so the plan knows less of `reach` than the query does
    // and `not reach(...)` is therefore true of more. With edges a->x, x->b and
    // a->b the view stores only (a, b), the query answers nothing, and a plan
    // that let this through would answer (a, b).
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try db.addFact("v", &.{ input.atom("a"), input.atom("b") });

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const view = try defineView(&db.state, &catalog, input.fact("v", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("edge", &.{ y, z }),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("reach", &.{ x, y }),
        &.{input.relation("edge", &.{ x, y })},
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("v", &.{ x, y }),
        input.not("reach", &.{ x, y }),
    });
    defer fold_ir.freeGoals(allocator, goals);
    // Lowering points every goal at a base relation, because which of them is
    // a view is the catalog's business rather than the language's. A query
    // that means the view says so here.
    goals[0].relation.predicate = catalog.view(view).predicate();

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.unsupported, outcome.guarantee());
    try std.testing.expectEqual(
        folding.PreconditionKind.relation_read_non_positively,
        outcome.unsupported.unmet[0].kind,
    );
}

test "inverting a view that collected a list reads the values back out of it" {
    // Chapter 6's Example 6.3.1. The view keeps a list of everything `r`
    // related each key to, so inverting it recovers `r` one list element at a
    // time, and recovers `p` only as far as saying a tuple was there.
    const allocator = std.testing.allocator;

    // The database behind the view, kept only to say what the query really
    // answers and what the view really stores. The plan never sees it.
    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\p(a, 1). p(b, 2). p(c, 3).
        \\r(a, b). r(a, c). r(c, a). r(c, c).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
        \\q(X, Y) :- r(X, Y), p(Y, Z).
    , null);
    program.deinit();
    var extension = try source.execute("v(X, S)?", null);
    defer extension.deinit();
    const stored = try answerTuples(&extension.query);
    defer freeLines(stored);
    for ([_][]const u8{ "a [b, c]", "b []", "c [a, c]" }, stored) |expected, actual|
        try std.testing.expectEqualStrings(expected, actual);

    var wanted = try source.execute("q(X, Y)?", null);
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);

    // The folded side holds that extension and nothing else.
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(a, [b, c]). v(b, []). v(c, [a, c]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const s = input.variable("S");
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{ x, z }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ x, y }),
        &.{ input.relation("r", &.{ x, y }), input.relation("p", &.{ y, z }) },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{input.relation("q", &.{ x, y })});
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();

    // On this database the plan loses nothing: what the view kept is enough to
    // answer the query exactly. The dissertation's printed answer list omits
    // q(a, b), which both the query and the plan produce — `p(b, 2)` is what
    // makes `b` a value `p` relates, and the empty list `v(b, [])` is what
    // records it.
    const actual = try answerTuples(&answers);
    defer freeLines(actual);
    try std.testing.expectEqual(@as(usize, 4), actual.len);
    try std.testing.expectEqual(expected.len, actual.len);
    for (expected, actual) |wanted_tuple, produced|
        try std.testing.expectEqualStrings(wanted_tuple, produced);
}

test "a value projected out of an aggregate is a witness per element, not per tuple" {
    // The join a shared name would invent. `W` is projected out of the
    // aggregate's own body, so the definition claims a witness for each value
    // the list collected — not one witness for the whole list. Naming them all
    // alike would let the query below join two elements through a `W` the
    // database never had in common.
    const allocator = std.testing.allocator;
    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\p(a).
        \\r(a, b, 1). r(a, c, 2).
        \\v(X, S) :- p(X), setof(Y, r(X, Y, W), S).
        \\q(Y1, Y2) :- r(X, Y1, W), r(X, Y2, W), Y1 != Y2.
    , null);
    program.deinit();
    var wanted = try source.execute("q(A, B)?", null);
    defer wanted.deinit();
    try std.testing.expectEqual(@as(usize, 0), wanted.query.answers.items.len);

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(a, [b, c]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const w = input.variable("W");
    const s = input.variable("S");
    const first = input.variable("Y1");
    const second = input.variable("Y2");
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y, w })}, s),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ first, second }),
        &.{
            input.relation("r", &.{ x, first, w }),
            input.relation("r", &.{ x, second, w }),
            input.notEqual(first, second),
        },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(
        &db.state,
        &catalog.symbols,
        &.{input.relation("q", &.{ first, second })},
    );
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    try std.testing.expectEqual(@as(usize, 0), answers.answers.items.len);
}

test "an aggregate nested in another is read by chaining into the list it collected" {
    // The dissertation reaches this case by rewriting the view into one rule
    // per aggregate. Reading it directly is what the shape already says: the
    // outer list collects `Y!T` pairs, so binding one of them binds `T`, and
    // `T` is the inner list to read the next value out of.
    const allocator = std.testing.allocator;
    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\p(a).
        \\r(a, b). r(a, c).
        \\s(b, 1). s(b, 2). s(c, 3).
        \\v(X, S) :- p(X), setof(Y!T, (r(X, Y), setof(Z, s(Y, Z), T)), S).
        \\q(Y, Z) :- s(Y, Z), r(X, Y).
    , null);
    program.deinit();
    var extension = try source.execute("v(X, S)?", null);
    defer extension.deinit();
    const stored = try answerTuples(&extension.query);
    defer freeLines(stored);
    try std.testing.expectEqualStrings("a [[b, 1, 2], [c, 3]]", stored[0]);
    var wanted = try source.execute("q(A, B)?", null);
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(a, [[b, 1, 2], [c, 3]]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const s = input.variable("S");
    const t = input.variable("T");
    const pair: input.Term.Cons = .{ .head = &y, .tail = &t };
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{x}),
        input.setof(input.cons(&pair), &.{
            input.relation("r", &.{ x, y }),
            input.setof(z, &.{input.relation("s", &.{ y, z })}, t),
        }, s),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ y, z }),
        &.{ input.relation("s", &.{ y, z }), input.relation("r", &.{ x, y }) },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{input.relation("q", &.{ y, z })});
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();

    // Everything the query answers, from the nested list alone.
    const actual = try answerTuples(&answers);
    defer freeLines(actual);
    try std.testing.expectEqual(expected.len, actual.len);
    for (expected, actual) |wanted_tuple, produced|
        try std.testing.expectEqualStrings(wanted_tuple, produced);
}

test "two aggregates side by side collect for themselves, not for each other" {
    // Both aggregates spell the collected value `Y` and the projected value
    // `W`, and the language says each means its own — a value the surrounding
    // goals do not bind belongs to the aggregate that mentions it. Inverting
    // them as one would name both witnesses alike and join `r` to `t` through
    // a `W` the database never had in common.
    const allocator = std.testing.allocator;
    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\p(a).
        \\r(a, b, 1). t(a, b, 2).
        \\v(X, S1, S2) :- p(X), setof(Y, r(X, Y, W), S1), setof(Y, t(X, Y, W), S2).
        \\q(Y1, Y2) :- r(X, Y1, W), t(X, Y2, W).
    , null);
    program.deinit();
    var wanted = try source.execute("q(A, B)?", null);
    defer wanted.deinit();
    try std.testing.expectEqual(@as(usize, 0), wanted.query.answers.items.len);

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(a, [b], [b]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const w = input.variable("W");
    const first = input.variable("S1");
    const second = input.variable("S2");
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{ x, first, second }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y, w })}, first),
        input.setof(y, &.{input.relation("t", &.{ x, y, w })}, second),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ input.variable("Y1"), input.variable("Y2") }),
        &.{
            input.relation("r", &.{ x, input.variable("Y1"), w }),
            input.relation("t", &.{ x, input.variable("Y2"), w }),
        },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{ input.variable("Y1"), input.variable("Y2") }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    try std.testing.expectEqual(@as(usize, 0), answers.answers.items.len);
}

/// Folds and runs one small collecting view: a definition with an aggregate,
/// the membership rules the plan defines to read its list, the Skolem term the
/// projected outer value needs, and the answers.
fn collectingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(a, [b]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const s = input.variable("S");
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{ x, z }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ x, y }),
        &.{ input.relation("r", &.{ x, y }), input.relation("p", &.{ y, z }) },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{input.relation("q", &.{ x, y })});
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    allocator.free(try outcome.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    }));

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    answers.deinit();
}

test "inverting a collecting view releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(collectingAllocationScenario);
}

/// Example 6.4.1's setting: `v(X, S) :- p(X), setof(Y, r(X, Y), S).`
///
/// The view remembers, for each `X` that `p` admits, everything `r` related it
/// to. It is not a canonical aggregate view of `r`, because `p` decides which
/// keys get a list at all, so what inverting it recovers of `r` is whatever
/// `p` let through.
fn defineCollectingView(
    db: *database.Database,
    catalog: *view_catalog.Catalog,
    availability: view_catalog.Availability,
) !fold_ir.ViewId {
    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");
    return defineView(db, catalog, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, availability);
}

/// `c(X, S) :- r(X, Y), setof(Y2, r(X, Y2), S).`
///
/// Definition 6.4.3's canonical aggregate view of a binary `r`, grouped by its
/// first column. Every key `r` mentions gets a list, and the list holds every
/// value under that key, so reading the lists back out returns `r` itself.
fn defineCanonicalView(
    db: *database.Database,
    catalog: *view_catalog.Catalog,
    availability: view_catalog.Availability,
) !fold_ir.ViewId {
    const x = input.variable("X");
    const y = input.variable("Y");
    const collected = input.variable("Y2");
    const s = input.variable("S");
    return defineView(db, catalog, input.fact("c", &.{ x, s }), &.{
        input.relation("r", &.{ x, y }),
        input.setof(collected, &.{input.relation("r", &.{ x, collected })}, s),
    }, availability);
}

/// `q(<key>) :- setof(Y, r(<key>, Y), <output>).`
///
/// Section 6.4.1's pair of queries, whose only difference is the collected
/// output they ask for, and whose containment differs entirely because of it.
fn collectingQueryRule(
    db: *database.Database,
    symbols: *fold_ir.Symbols,
    key: input.Term,
    output: input.Term,
) !fold_ir.Rule {
    const y = input.variable("Y");
    return foldingRule(db, symbols, input.fact("q", &.{key}), &.{
        input.setof(y, &.{input.relation("r", &.{ key, y })}, output),
    });
}

test "Chapter 6's empty-set counterexample is refused and the query beside it is not" {
    // Example 6.4.1 and the contrast of Section 6.4.1, together, because a
    // refusal only says something next to the query it does not refuse.
    //
    // Both queries count what `r` holds. The plan knows `r` only as far as the
    // view proves it, so its `r` is a subset. Asking for the collected set to
    // be *empty* turns a subset into an answer the query does not have; asking
    // for it to be non-empty cannot, because a subset of a non-empty set is
    // either non-empty or absent.
    const allocator = std.testing.allocator;

    // What is really there, and what the two queries really answer. The plan
    // never sees this database.
    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\p(b). p(c).
        \\r(a, 1). r(c, 2).
        \\v(X, S) :- p(X), setof(Y, r(X, Y), S).
        \\empty(a) :- setof(Y, r(a, Y), []).
        \\nonempty(c) :- setof(Y, r(c, Y), H!T).
    , null);
    program.deinit();
    var refused_answers = try source.execute("empty(X)?", null);
    defer refused_answers.deinit();
    try std.testing.expectEqual(@as(usize, 0), refused_answers.query.answers.items.len);
    var admitted_answers = try source.execute("nonempty(X)?", null);
    defer admitted_answers.deinit();
    try std.testing.expectEqual(@as(usize, 1), admitted_answers.query.answers.items.len);

    // The folded side holds the view's extension and nothing else: `b` was
    // admitted by `p` and related to nothing, `c` was admitted and related
    // to 2. That `r` also holds (a, 1) is exactly what is no longer there.
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(b, []). v(c, [2]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    _ = try defineCollectingView(&db.state, &catalog, .materialized);

    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{input.variable("X")}),
    });
    defer fold_ir.freeGoals(allocator, goals);

    // q(a) :- setof(Y, r(a, Y), []). Nothing discharges the refusal: the view
    // is not a canonical aggregate view of `r`, and a query asking for an
    // empty set is not monotonic.
    var refused_rules = [_]fold_ir.Rule{try collectingQueryRule(
        &db.state,
        &catalog.symbols,
        input.atom("a"),
        input.list(&.{}),
    )};
    defer for (refused_rules) |rule| fold_ir.freeRule(allocator, rule);
    var refused = try folding.foldQuery(allocator, &catalog, .{
        .goals = goals,
        .rules = &refused_rules,
    });
    defer refused.deinit();
    try std.testing.expectEqual(folding.Guarantee.unsupported, refused.guarantee());
    try std.testing.expectEqual(@as(usize, 1), refused.unsupported.unmet.len);
    try std.testing.expectEqual(
        folding.PreconditionKind.relation_read_non_positively,
        refused.unsupported.unmet[0].kind,
    );

    // q(c) :- setof(Y, r(c, Y), H!T). The same view, the same relation read
    // the same way, and this one folds — the query is monotonic.
    const head = input.variable("H");
    const tail = input.variable("T");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    var admitted_rules = [_]fold_ir.Rule{try collectingQueryRule(
        &db.state,
        &catalog.symbols,
        input.atom("c"),
        input.cons(&pair),
    )};
    defer for (admitted_rules) |rule| fold_ir.freeRule(allocator, rule);
    var admitted = try folding.foldQuery(allocator, &catalog, .{
        .goals = goals,
        .rules = &admitted_rules,
    });
    defer admitted.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, admitted.guarantee());
    const explained = try admitted.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    });
    defer allocator.free(explained);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        explained,
        1,
        "the query is monotonic",
    ));

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        admitted.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);
    try std.testing.expectEqual(@as(usize, 1), tuples.len);
    try std.testing.expectEqualStrings("c", tuples[0]);

    // And the refusal is load-bearing rather than decorative. The inverse
    // rules a plan is built from do not depend on which query is being folded,
    // so the plan just installed *is* the one Example 6.4.1 warns about. Ask
    // it the refused question and it answers `a`, which the query does not.
    var counterexample = try db.execute(
        \\bad(a) :- setof(Y, r(a, Y), []).
        \\bad(X)?
    , null);
    defer counterexample.deinit();
    try std.testing.expectEqual(@as(usize, 1), counterexample.query.answers.items.len);
}

test "a canonical aggregate view folds a query no monotonicity argument covers" {
    // Theorem 6.4.2. The query is Example 6.4.1's, unchanged and still not
    // monotonic, and it folds anyway — because the catalog holds a canonical
    // aggregate view of the relation it counts, and Lemma 6.4.2 makes reading
    // that view's lists back out equivalent to reading the relation.
    const allocator = std.testing.allocator;

    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\r(a, 1). r(c, 2).
        \\c(X, S) :- r(X, Y), setof(Y2, r(X, Y2), S).
        \\w(X) :- r(X, Y).
        \\empty(a) :- setof(Y, r(a, Y), []).
        \\gone(d) :- setof(Y, r(d, Y), []).
    , null);
    program.deinit();
    var wanted = try source.execute("empty(X)?", null);
    defer wanted.deinit();
    try std.testing.expectEqual(@as(usize, 0), wanted.query.answers.items.len);
    var elsewhere = try source.execute("gone(X)?", null);
    defer elsewhere.deinit();
    try std.testing.expectEqual(@as(usize, 1), elsewhere.query.answers.items.len);

    // The folded side holds both view extensions and no base relation.
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("c(a, [1]). c(c, [2]). w(a). w(c).", null);
    facts.deinit();

    const x = input.variable("X");
    const y = input.variable("Y");

    // Two catalogs over the same database, differing in one view. `w(X) :-
    // r(X, Y)` mentions `r` and remembers only that a key had some value, so
    // it can reconstruct `r` and cannot prove it complete.
    var without: view_catalog.Catalog = .init(allocator);
    defer without.deinit();
    _ = try defineView(&db.state, &without, input.fact("w", &.{x}), &.{
        input.relation("r", &.{ x, y }),
    }, .materialized);

    var with: view_catalog.Catalog = .init(allocator);
    defer with.deinit();
    _ = try defineView(&db.state, &with, input.fact("w", &.{x}), &.{
        input.relation("r", &.{ x, y }),
    }, .materialized);
    _ = try defineCanonicalView(&db.state, &with, .materialized);

    // Without the canonical view the fold has nothing to offer, and says so as
    // the read it could not allow rather than as a missing relation.
    {
        const goals = try foldingGoals(&db.state, &without.symbols, &.{
            input.relation("q", &.{x}),
        });
        defer fold_ir.freeGoals(allocator, goals);
        var rules = [_]fold_ir.Rule{try collectingQueryRule(
            &db.state,
            &without.symbols,
            input.atom("a"),
            input.list(&.{}),
        )};
        defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
        var outcome = try folding.foldQuery(allocator, &without, .{
            .goals = goals,
            .rules = &rules,
        });
        defer outcome.deinit();
        try std.testing.expectEqual(folding.Guarantee.unsupported, outcome.guarantee());
        try std.testing.expectEqual(
            folding.PreconditionKind.relation_read_non_positively,
            outcome.unsupported.unmet[0].kind,
        );
    }

    const goals = try foldingGoals(&db.state, &with.symbols, &.{
        input.relation("q", &.{x}),
    });
    defer fold_ir.freeGoals(allocator, goals);
    var rules = [_]fold_ir.Rule{try collectingQueryRule(
        &db.state,
        &with.symbols,
        input.atom("a"),
        input.list(&.{}),
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    var outcome = try folding.foldQuery(allocator, &with, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());
    const explained = try outcome.explainAlloc(allocator, .{
        .symbols = &with.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    });
    defer allocator.free(explained);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        explained,
        1,
        "reconstructed exactly, from a canonical aggregate view of it: r/2",
    ));

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &with.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    // The query's own answer, from the view extensions alone: `r` does relate
    // `a` to something, so the empty set is not what was collected.
    try std.testing.expectEqual(@as(usize, 0), answers.answers.items.len);

    // The other half of exactness, which containment alone would not show: the
    // plan derives all of `r`, so a key `r` never mentions still collects the
    // empty set and still answers.
    var absent = try db.execute(
        \\gone(d) :- setof(Y, r(d, Y), []).
        \\gone(X)?
    , null);
    defer absent.deinit();
    try std.testing.expectEqual(@as(usize, 1), absent.query.answers.items.len);
}

test "a view that projected its collected list away still remembers its outer goals" {
    // Section 6.3.2. The head of `v(X) :- p(X, S), setof(Y, r(X, Y), S)` keeps
    // neither the set nor anything collected into it, so the plan names that
    // set with a Skolem term. A name is enough to reconstruct the goals
    // *outside* the aggregate — they held for some set, and this is which —
    // and it is not enough to reach the values inside it, because those were
    // never stored anywhere.
    const allocator = std.testing.allocator;

    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\p(a, [1]). p(b, []).
        \\r(a, 1).
        \\v(X) :- p(X, S), setof(Y, r(X, Y), S).
        \\q(X) :- p(X, S).
    , null);
    program.deinit();
    var extension = try source.execute("v(X)?", null);
    defer extension.deinit();
    const stored = try answerTuples(&extension.query);
    defer freeLines(stored);
    try std.testing.expectEqual(@as(usize, 2), stored.len);
    var wanted = try source.execute("q(X)?", null);
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v(a). v(b).", null);
    facts.deinit();

    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");

    // What the outer goal remembers comes back exactly: every key `p` had a
    // tuple for is a key the plan produces.
    {
        var catalog: view_catalog.Catalog = .init(allocator);
        defer catalog.deinit();
        _ = try defineView(&db.state, &catalog, input.fact("v", &.{x}), &.{
            input.relation("p", &.{ x, s }),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        }, .materialized);

        var rules = [_]fold_ir.Rule{try foldingRule(
            &db.state,
            &catalog.symbols,
            input.fact("q", &.{x}),
            &.{input.relation("p", &.{ x, s })},
        )};
        defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
        const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
            input.relation("q", &.{x}),
        });
        defer fold_ir.freeGoals(allocator, goals);

        var outcome = try folding.foldQuery(allocator, &catalog, .{
            .goals = goals,
            .rules = &rules,
        });
        defer outcome.deinit();
        try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

        var executable = try folding.lowerPlan(
            allocator,
            &db.state.strings,
            &catalog.symbols,
            outcome.plan().?,
        );
        defer executable.deinit();
        var answers = try runPlan(&db.state, &executable);
        defer answers.deinit();
        const actual = try answerTuples(&answers);
        defer freeLines(actual);
        try std.testing.expectEqual(expected.len, actual.len);
        for (expected, actual) |one, other| try std.testing.expectEqualStrings(one, other);
    }

    // What the aggregate collected does not, and the plan says so by answering
    // nothing rather than by guessing. A second database, because the first
    // now holds the rules of the first plan.
    var second: Jatalog = .init(allocator);
    defer second.deinit();
    var more = try second.execute("v(a). v(b).", null);
    more.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    _ = try defineView(&second.state, &catalog, input.fact("v", &.{x}), &.{
        input.relation("p", &.{ x, s }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try foldingRule(
        &second.state,
        &catalog.symbols,
        input.fact("t", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&second.state, &catalog.symbols, &.{
        input.relation("t", &.{ x, y }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{
        .goals = goals,
        .rules = &rules,
    });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

    var executable = try folding.lowerPlan(
        allocator,
        &second.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&second.state, &executable);
    defer answers.deinit();
    // The source database has r(a, 1), so the query's own answer is one tuple.
    // Nothing derives membership in a set that was never stored, so the plan
    // has none — which is containment, and the most a plan over this view can
    // do.
    try std.testing.expectEqual(@as(usize, 0), answers.answers.items.len);
}

/// Two keys and two values, as one bit per possible `r` tuple and one per
/// possible `p` tuple.
///
/// The bound is chosen rather than inherited. Everything the two discharges
/// turn on occurs somewhere in this space — a key whose collected set is empty
/// and one whose is not, a key `p` admits and one it withholds, a value
/// reachable only through a key that was withheld, and a set that grows by one
/// element — and a configuration outside it is one of these with more names.
/// Three of each would be `2^3 · 2^9` databases, sixty-four times the work for
/// the same shapes; the exhaustive sweep over graphs on three nodes already
/// costs more than half the suite's running time, and this one is meant to sit
/// beside it rather than double it.
const Model = struct {
    const size = 2;
    const names = [size][]const u8{ "a", "b" };
    /// Every `r` over the domain, and every `p` over it.
    const relations = 1 << (size * size);
    const subsets = 1 << size;

    fn tuple(row: usize, column: usize) u4 {
        return @as(u4, 1) << @intCast(row * size + column);
    }

    fn relates(mask: u4, row: usize, column: usize) bool {
        return mask & tuple(row, column) != 0;
    }

    fn admits(mask: u2, index: usize) bool {
        return mask & (@as(u2, 1) << @intCast(index)) != 0;
    }

    /// Whether anything is related to `column`, which is what the monotonic
    /// query asks and what a plan reading a subset of `r` can only under-report.
    fn reaches(mask: u4, column: usize) bool {
        for (0..size) |row| if (relates(mask, row, column)) return true;
        return false;
    }

    /// Adds one stored tuple whose last column is the list of everything the
    /// row is related to.
    fn addCollected(
        db: *database.Database,
        predicate: []const u8,
        mask: u4,
        row: usize,
    ) !void {
        var values: [size]input.Term = undefined;
        var held: usize = 0;
        for (0..size) |column| if (relates(mask, row, column)) {
            values[held] = input.atom(names[column]);
            held += 1;
        };
        try addFactTerms(db, predicate, &.{
            input.atom(names[row]),
            input.list(values[0..held]),
        });
    }

    fn indexOf(answer: results.Answer, position: usize) !usize {
        const text = try answer.bindings.items[position].value.getAtom();
        return text[0] - 'a';
    }
};

test "bounded exhaustive models find no counterexample to either discharge" {
    // Both guarantees, checked by exhaustion rather than by argument, with the
    // oracle computed by bit operations: a sweep that asked the engine what
    // the answers were and then asked it again through a plan would agree with
    // itself whatever either one did.
    const allocator = std.testing.allocator;

    // The monotonic discharge. `q(X) :- p(X), setof(Y, r(Y, X), H!T)` asks for
    // some value to reach `X`, and the plan knows `r` only for the keys `p`
    // admitted, so it can miss a value and can never invent one.
    var planned: Jatalog = .init(allocator);
    defer planned.deinit();
    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    _ = try defineCollectingView(&planned.state, &catalog, .materialized);

    const x = input.variable("X");
    const y = input.variable("Y");
    const head = input.variable("H");
    const tail = input.variable("T");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    var rules = [_]fold_ir.Rule{try foldingRule(
        &planned.state,
        &catalog.symbols,
        input.fact("q", &.{x}),
        &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ y, x })}, input.cons(&pair)),
        },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&planned.state, &catalog.symbols, &.{
        input.relation("q", &.{x}),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{
        .goals = goals,
        .rules = &rules,
    });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());
    var executable = try folding.lowerPlan(
        allocator,
        &planned.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    try installPlan(&planned.state, &executable);

    var answered: usize = 0;
    for (0..Model.subsets) |admitted| {
        const keys: u2 = @intCast(admitted);
        for (0..Model.relations) |related| {
            const edges: u4 = @intCast(related);
            var folded = try planned.clone();
            defer folded.deinit();
            for (0..Model.size) |key| {
                if (Model.admits(keys, key))
                    try Model.addCollected(&folded.state, "v", edges, key);
            }

            var produced = try transaction.queryClauses(&folded.state, executable.goals, &.{});
            defer produced.deinit();
            for (produced.answers.items) |answer| {
                const column = try Model.indexOf(answer, 0);
                if (!Model.admits(keys, column) or !Model.reaches(edges, column)) {
                    std.debug.print("\np {b} r {b}: the plan answered {s}\n", .{
                        keys,
                        edges,
                        Model.names[column],
                    });
                    return error.AnswerNotContained;
                }
                answered += 1;
            }
        }
    }
    // A plan that answers nothing is contained in anything, so the sweep has
    // to have seen answers for its agreement to mean anything.
    try std.testing.expect(answered > 0);

    // The canonical-view discharge, held to the stronger claim its proof
    // makes. Lemma 6.4.2 says the reconstruction of `r` is *equivalent* rather
    // than merely contained, so `q(a) :- setof(Y, r(a, Y), [])` must answer
    // exactly when the query does — including when it answers and a merely
    // contained plan would have been allowed to stay silent.
    var canonical: Jatalog = .init(allocator);
    defer canonical.deinit();
    var exact: view_catalog.Catalog = .init(allocator);
    defer exact.deinit();
    _ = try defineCanonicalView(&canonical.state, &exact, .materialized);

    var counting = [_]fold_ir.Rule{try collectingQueryRule(
        &canonical.state,
        &exact.symbols,
        input.atom("a"),
        input.list(&.{}),
    )};
    defer for (counting) |rule| fold_ir.freeRule(allocator, rule);
    const asked = try foldingGoals(&canonical.state, &exact.symbols, &.{
        input.relation("q", &.{x}),
    });
    defer fold_ir.freeGoals(allocator, asked);

    var folding_outcome = try folding.foldQuery(allocator, &exact, .{
        .goals = asked,
        .rules = &counting,
    });
    defer folding_outcome.deinit();
    try std.testing.expectEqual(
        folding.Guarantee.maximally_contained,
        folding_outcome.guarantee(),
    );
    var counted = try folding.lowerPlan(
        allocator,
        &canonical.state.strings,
        &exact.symbols,
        folding_outcome.plan().?,
    );
    defer counted.deinit();
    try installPlan(&canonical.state, &counted);

    for (0..Model.relations) |related| {
        const edges: u4 = @intCast(related);
        var folded = try canonical.clone();
        defer folded.deinit();
        for (0..Model.size) |key| {
            var holds = false;
            for (0..Model.size) |column| holds = holds or Model.relates(edges, key, column);
            if (holds) try Model.addCollected(&folded.state, "c", edges, key);
        }

        var produced = try transaction.queryClauses(&folded.state, counted.goals, &.{});
        defer produced.deinit();
        var empty = true;
        for (0..Model.size) |column| empty = empty and !Model.relates(edges, 0, column);
        const expected: usize = if (empty) 1 else 0;
        if (produced.answers.items.len != expected) {
            std.debug.print("\nr {b}: the plan answered {d}, the query {d}\n", .{
                edges,
                produced.answers.items.len,
                expected,
            });
            return error.AnswersDiffer;
        }
    }
}

/// Folds and runs the smallest problem that exercises both of F4's discharges
/// at once: a canonical aggregate view making a relation exact, a second view
/// that projects its collected list away and names the set instead, and a
/// query counting the relation that neither is monotonic about.
///
/// Deliberately one fact and one rule. An allocation-failure sweep runs the
/// scenario once per allocation it makes, so its cost is quadratic in its own
/// size and two larger ones already exist.
fn restrictedFoldingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("c(a, [1]). v(a).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    _ = try defineCanonicalView(&db.state, &catalog, .materialized);
    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");
    _ = try defineView(&db.state, &catalog, input.fact("v", &.{x}), &.{
        input.relation("p", &.{ x, s }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    var rules = [_]fold_ir.Rule{try collectingQueryRule(
        &db.state,
        &catalog.symbols,
        input.atom("a"),
        input.list(&.{}),
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{x}),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    allocator.free(try outcome.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    }));
    if (outcome.guarantee() != .maximally_contained) return error.UnexpectedGuarantee;

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    answers.deinit();
}

test "folding under the restricted classes releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(restrictedFoldingAllocationScenario);
}

/// Example 6.5.2's setting, restated over the arithmetic this language has.
///
/// The dissertation's list function is `avg(X, A) :- sum(X, S), length(X, C),
/// A = S / C`, and DatalogA here has `+` and `-` and no `/` — adding division
/// is a Project S decision about the finite-`f64` policy, mixed numeric
/// canonicalization and division by zero, and none of that is what this phase
/// is about. So the example is restated with the same shape and a different
/// operator: `excess(L, E) :- sum(L, T), length(L, C), E = T - C` is a list
/// function the views do not expose, defined as a conjunctive view over two
/// they do, combined arithmetically. Everything the folding turns on — the
/// expansion, the two auxiliary layers, the identity of the two sets — is the
/// same; only the last goal differs.
const Excess = struct {
    /// `sum` and `length` as Appendix B defines them, plus the data.
    ///
    /// `seed` names the lists the aggregate will collect. It is there because
    /// the structural rules deriving `sum` and `length` are *seeded*: they
    /// derive over the lists the database holds, and a list that only ever
    /// exists as an aggregate's output inside a higher stratum is not one of
    /// them. That is a property of this engine's list functions and not of the
    /// folding — the plan needs no such seeding, because it holds no
    /// structural rules at all — but the query has to be answerable for its
    /// answers to be worth comparing against.
    const program =
        \\sum([], 0).
        \\sum(H!T, S) :- sum(T, A), S = A + H.
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\p(a). p(b).
        \\r(a, 1). r(a, 2). r(b, 5).
        \\seed([1, 2]). seed([5]).
        \\v1(X, T) :- p(X), setof(Y, r(X, Y), S), sum(S, T).
        \\v2(X, C) :- p(X), setof(Y, r(X, Y), S), length(S, C).
        \\cr(X, S) :- r(X, Y0), setof(Y, r(X, Y), S).
        \\excess(L, E) :- sum(L, T), length(L, C), E = T - C.
        \\q(X, E) :- p(X), setof(Y, r(X, Y), S), excess(S, E).
    ;

    /// What the three view extensions come to over that data, and nothing
    /// else. `p`, `r`, `sum` and `length` are gone.
    const extensions = "v1(a, 3). v1(b, 5). v2(a, 2). v2(b, 1). cr(a, [1, 2]). cr(b, [5]).";

    /// Defines the three views, in the order their names suggest.
    fn catalog(db: *database.Database, into: *view_catalog.Catalog) !void {
        const x = input.variable("X");
        const y = input.variable("Y");
        const y0 = input.variable("Y0");
        const s = input.variable("S");
        const t = input.variable("T");
        const c = input.variable("C");
        _ = try defineView(db, into, input.fact("v1", &.{ x, t }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
        }, .materialized);
        _ = try defineView(db, into, input.fact("v2", &.{ x, c }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("length", &.{ s, c }),
        }, .materialized);
        _ = try defineView(db, into, input.fact("cr", &.{ x, s }), &.{
            input.relation("r", &.{ x, y0 }),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        }, .materialized);
    }

    /// `excess(L, E) :- sum(L, T), length(L, C), E = T - C.` and
    /// `q(X, E) :- p(X), setof(Y, r(X, Y), S), excess(S, E).`
    fn query(db: *database.Database, symbols: *fold_ir.Symbols, into: *[2]fold_ir.Rule) !void {
        const x = input.variable("X");
        const y = input.variable("Y");
        const s = input.variable("S");
        const t = input.variable("T");
        const c = input.variable("C");
        const l = input.variable("L");
        const e = input.variable("E");
        into[0] = try foldingRule(db, symbols, input.fact("excess", &.{ l, e }), &.{
            input.relation("sum", &.{ l, t }),
            input.relation("length", &.{ l, c }),
            input.subtract(e, t, c),
        });
        errdefer fold_ir.freeRule(db.allocator, into[0]);
        into[1] = try foldingRule(db, symbols, input.fact("q", &.{ x, e }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("excess", &.{ s, e }),
        });
    }
};

test "a list function no view exposes is folded through the two that do" {
    // Example 6.5.2, restated over subtraction. The query asks for something
    // computed from a collected set, and every relation it names is gone: the
    // plan has two views that each read *their* set with one list function,
    // and a canonical aggregate view of the relation inside the set.
    //
    // What makes it work is the identity of two sets nothing stored. Each view
    // is split at its aggregate into an auxiliary view that collects and a
    // layer that reads, both views turn out to collect the same set, and the
    // Skolem set each layer's inverse would have named is therefore the set
    // the auxiliary view derives. That is Section 6.5's functional dependency,
    // and without it the plan has a sum of one unnameable set and a length of
    // another and can say nothing about either.
    const allocator = std.testing.allocator;

    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(Excess.program, null);
    program.deinit();
    var wanted = try source.execute("q(X, E)?", null);
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);
    // a is related to 1 and 2, so its set sums to 3 and holds 2; b to 5 alone.
    try std.testing.expectEqual(@as(usize, 2), expected.len);
    try std.testing.expectEqualStrings("a 1", expected[0]);
    try std.testing.expectEqualStrings("b 4", expected[1]);

    // The folded side holds the three view extensions and nothing else. It has
    // no `p`, no `r`, and — this is what Section 6.5 turns on — no definition
    // of `sum` or of `length` either.
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute(Excess.extensions, null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    try Excess.catalog(&db.state, &catalog);
    var rules: [2]fold_ir.Rule = undefined;
    try Excess.query(&db.state, &catalog.symbols, &rules);
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{ input.variable("X"), input.variable("E") }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

    const explained = try outcome.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    });
    defer allocator.free(explained);
    for ([_][]const u8{
        "expanded into the list functions the views expose: excess/2",
        "split into the set it collects and the list functions reading it: v1@0/2",
        "split into the set it collects and the list functions reading it: v2@1/2",
        "views proved to have collected one set",
        "reconstructed exactly, from a canonical aggregate view of it: r/2",
    }) |note| {
        if (!std.mem.containsAtLeast(u8, explained, 1, note)) {
            std.debug.print("\nnot in the explanation: {s}\n{s}\n", .{ note, explained });
            return error.TransformationNotReported;
        }
    }

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    const actual = try answerTuples(&answers);
    defer freeLines(actual);
    try std.testing.expectEqual(expected.len, actual.len);
    for (expected, actual) |one, other| try std.testing.expectEqualStrings(one, other);
}

test "Example 6.5.1's recursive list function is refused rather than merely survived" {
    // The view of Example 6.5.1 is `v(X, A) :- p(X), setof(Y, r(X, Y), S),
    // sum(S, A)`, and there is nothing wrong with it: inverting it gives
    // Definition 6.5.1's rules. What cannot go into the plan is `sum`'s own
    // definition. Coupled with `sum(f(X, A), A) :- v(X, A)` the recursive case
    // derives a sum of a one-element list holding that Skolem set, then of a
    // two-element one, and never stops.
    //
    // Skolem elimination happens to prevent the nesting — a list holding a
    // reconstructed value cannot be split, so the instance is dropped — and
    // that is not a rejection. It is an accident of the machinery that leaves
    // the plan quietly answering less than it looks like it answers. The
    // refusal is stated instead, and it is the query's *rules* that state it,
    // because a caller can hand `sum`'s definition over as part of the query.
    const allocator = std.testing.allocator;

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute(Excess.extensions, null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    try Excess.catalog(&db.state, &catalog);

    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");
    const t = input.variable("T");
    const e = input.variable("E");
    const head = input.variable("H");
    const tail = input.variable("T2");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };

    // sum(H!T2, S) :- sum(T2, A), S = A + H. Appendix B's definition, handed
    // to the fold as one of the query's own rules.
    var rules: [3]fold_ir.Rule = undefined;
    try Excess.query(&db.state, &catalog.symbols, rules[0..2]);
    rules[2] = try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("sum", &.{ input.cons(&pair), s }),
        &.{
            input.relation("sum", &.{ tail, t }),
            input.add(s, t, head),
        },
    );
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{ x, e }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.unsupported, outcome.guarantee());
    var refused = false;
    for (outcome.unsupported.unmet) |precondition| {
        if (precondition.kind == .query_list_function_recursive) refused = true;
    }
    try std.testing.expect(refused);
    const explained = try outcome.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    });
    defer allocator.free(explained);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        explained,
        1,
        "sum/2: the query defines it by structural recursion",
    ));

    // The same query without that rule is the one the phase folds, so the
    // refusal is the rule and not the setting.
    var without = try folding.foldQuery(allocator, &catalog, .{
        .goals = goals,
        .rules = rules[0..2],
    });
    defer without.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, without.guarantee());

    // And the other way such a definition could reach a plan is closed
    // already: a view whose head holds a list is outside the class F2 inverts,
    // because a list outside an aggregate is not something the Inverse Method
    // has a rule for.
    var recursive: view_catalog.Catalog = .init(allocator);
    defer recursive.deinit();
    _ = try defineView(&db.state, &recursive, input.fact("sum", &.{ input.cons(&pair), s }), &.{
        input.relation("sum", &.{ tail, t }),
    }, .materialized);
    const rules_only = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &recursive.symbols,
        input.fact("total", &.{ y, s }),
        &.{input.relation("sum", &.{ y, s })},
    )};
    defer for (rules_only) |rule| fold_ir.freeRule(allocator, rule);
    const asking = try foldingGoals(&db.state, &recursive.symbols, &.{
        input.relation("total", &.{ y, s }),
    });
    defer fold_ir.freeGoals(allocator, asking);
    var view_side = try folding.foldQuery(allocator, &recursive, .{
        .goals = asking,
        .rules = &rules_only,
    });
    defer view_side.deinit();
    try std.testing.expectEqual(folding.Guarantee.unsupported, view_side.guarantee());
    try std.testing.expectEqual(
        folding.PreconditionKind.view_definition_uses_lists,
        view_side.unsupported.unmet[0].kind,
    );
}

/// `v1` over a set collected one link away, with the head keeping either end.
///
/// Which end it keeps is the whole difference. Keeping `Z` makes the collected
/// set a function of the stored tuple — one `Z`, one set — so the auxiliary
/// view is functional in its key and the layer's Skolem set is that key's set.
/// Keeping `X` does not: two links out of one `X` collect two different sets,
/// and a `va(X, S)` written from that definition would hold both. There is
/// then nothing the set a stored `v1(x, t)` was the sum of can be identified
/// with, and the plan has no rule to derive `sum` from.
fn defineLinkedView(
    db: *database.Database,
    catalog: *view_catalog.Catalog,
    keeps: enum { collected_end, linking_end },
) !void {
    const x = input.variable("X");
    const z = input.variable("Z");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");
    _ = try defineView(&db.*, catalog, input.fact("cr", &.{ z, s }), &.{
        input.relation("r", &.{ z, y0 }),
        input.setof(y, &.{input.relation("r", &.{ z, y })}, s),
    }, .materialized);
    _ = try defineView(&db.*, catalog, input.fact("v1", &.{
        if (keeps == .collected_end) z else x,
        t,
    }), &.{
        input.relation("link", &.{ x, z }),
        input.setof(y, &.{input.relation("r", &.{ z, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
}

test "a plan whose views leave the collected set undetermined is unsupported" {
    // The last of Theorem 6.5.1's parts. A query's list function may be one
    // the views expose rather than a conjunction over them — here it is `sum`
    // itself — and that is enough only when the set the view read is a set the
    // plan can name. The auxiliary view is what names it, and it names
    // nothing unless the definition determines its set from what the head
    // kept.
    const allocator = std.testing.allocator;

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v1(a, 3). cr(a, [1, 2]). link(w, a).", null);
    facts.deinit();

    const x = input.variable("X");
    const z = input.variable("Z");
    const y = input.variable("Y");
    const s = input.variable("S");
    const t = input.variable("T");

    // q(Z, T) :- link(X, Z), setof(Y, r(Z, Y), S), sum(S, T). The same
    // question of both catalogs; only the view differs.
    inline for (.{ .linking_end, .collected_end }) |keeps| {
        var catalog: view_catalog.Catalog = .init(allocator);
        defer catalog.deinit();
        try defineLinkedView(&db.state, &catalog, keeps);

        const rules = [_]fold_ir.Rule{try foldingRule(
            &db.state,
            &catalog.symbols,
            input.fact("q", &.{ z, t }),
            &.{
                input.relation("link", &.{ x, z }),
                input.setof(y, &.{input.relation("r", &.{ z, y })}, s),
                input.relation("sum", &.{ s, t }),
            },
        )};
        defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
        const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
            input.relation("q", &.{ z, t }),
        });
        defer fold_ir.freeGoals(allocator, goals);

        var outcome = try folding.foldQuery(allocator, &catalog, .{
            .goals = goals,
            .rules = &rules,
        });
        defer outcome.deinit();
        if (keeps == .linking_end) {
            try std.testing.expectEqual(folding.Guarantee.unsupported, outcome.guarantee());
            try std.testing.expectEqual(@as(usize, 1), outcome.unsupported.unmet.len);
            try std.testing.expectEqual(
                folding.PreconditionKind.list_function_set_unidentified,
                outcome.unsupported.unmet[0].kind,
            );
            const explained = try outcome.explainAlloc(allocator, .{
                .symbols = &catalog.symbols,
                .strings = &db.state.strings,
                .scalars = &db.state.eval.scalars,
            });
            defer allocator.free(explained);
            try std.testing.expect(std.mem.containsAtLeast(
                u8,
                explained,
                1,
                "sum/2: no view read the collected set with it",
            ));
            continue;
        }

        // The same query, the same relations, one variable different in the
        // view's head — and now the set has a name, so the plan has a rule for
        // `sum` and answers what the stored tuple says.
        try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());
        var executable = try folding.lowerPlan(
            allocator,
            &db.state.strings,
            &catalog.symbols,
            outcome.plan().?,
        );
        defer executable.deinit();
        var answers = try runPlan(&db.state, &executable);
        defer answers.deinit();
        const tuples = try answerTuples(&answers);
        defer freeLines(tuples);
        try std.testing.expectEqual(@as(usize, 1), tuples.len);
        try std.testing.expectEqualStrings("a 3", tuples[0]);
    }
}

test "a set collected from a relation the plan half knows is refused, monotonic or not" {
    // Where Section 6.5's dependency stops being a containment argument.
    //
    // Everywhere else a reconstruction being a subset costs answers: the plan
    // reads less of a relation and returns less. Here the plan does not read
    // the set, it *asserts* something about it — `sum(S, T) :- v1(X, T),
    // va(X, S)` says the stored `T` is the sum of whatever the auxiliary view
    // collected. Collect a shorter set and the plan holds a `sum` fact that is
    // false, and a query reading a false fact answers wrongly however
    // monotonic it is.
    //
    // This query is monotonic — it has no aggregate of its own and negates
    // nothing — so nothing but the exactness of what the auxiliary view
    // collects stands between it and a wrong answer.
    const allocator = std.testing.allocator;

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v1(a, 3). cr(a, [1, 2]). asked(a, [1, 2]).", null);
    facts.deinit();

    const x = input.variable("X");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");

    // q(X, T) :- asked(X, S), sum(S, T). `asked` is the caller's own relation,
    // declared available, so the query itself never reads `r` at all — only
    // the auxiliary view does.
    inline for (.{ false, true }) |canonical| {
        var catalog: view_catalog.Catalog = .init(allocator);
        defer catalog.deinit();
        try catalog.declareBaseAvailable(.{
            .name = try db.state.strings.intern("asked"),
            .arity = 2,
        });
        _ = try defineView(&db.state, &catalog, input.fact("v1", &.{ x, t }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
        }, .materialized);
        if (canonical) _ = try defineView(&db.state, &catalog, input.fact("cr", &.{ x, s }), &.{
            input.relation("r", &.{ x, y0 }),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        }, .materialized);

        const rules = [_]fold_ir.Rule{try foldingRule(
            &db.state,
            &catalog.symbols,
            input.fact("q", &.{ x, t }),
            &.{
                input.relation("asked", &.{ x, s }),
                input.relation("sum", &.{ s, t }),
            },
        )};
        defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
        const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
            input.relation("q", &.{ x, t }),
        });
        defer fold_ir.freeGoals(allocator, goals);

        var outcome = try folding.foldQuery(allocator, &catalog, .{
            .goals = goals,
            .rules = &rules,
        });
        defer outcome.deinit();
        if (!canonical) {
            // Only `v1` mentions `r`, and what it remembers of it is whatever
            // its own outer goals admitted. The refusal names the relation the
            // auxiliary view collects rather than one the query reads, because
            // the query reads none of it.
            try std.testing.expectEqual(folding.Guarantee.unsupported, outcome.guarantee());
            var refused = false;
            for (outcome.unsupported.unmet) |precondition| {
                if (precondition.kind == .set_collected_from_inexact_relation) refused = true;
            }
            try std.testing.expect(refused);
            continue;
        }

        // With a canonical aggregate view of `r` the auxiliary view collects
        // exactly what `r` held, so the stored `3` really is the sum of the
        // set the query asked about.
        try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());
        var executable = try folding.lowerPlan(
            allocator,
            &db.state.strings,
            &catalog.symbols,
            outcome.plan().?,
        );
        defer executable.deinit();
        var answers = try runPlan(&db.state, &executable);
        defer answers.deinit();
        const tuples = try answerTuples(&answers);
        defer freeLines(tuples);
        try std.testing.expectEqual(@as(usize, 1), tuples.len);
        try std.testing.expectEqualStrings("a 3", tuples[0]);
    }
}

/// Two keys and two values, as one bit per possible `r` tuple and one per
/// possible `p` tuple: 64 databases for Section 6.5's folding.
///
/// The bound is chosen for what it contains rather than inherited. A key `p`
/// admits whose collected set is empty and one whose is not; a key `r` relates
/// that `p` withholds, so the canonical view has a tuple where the two layers
/// have none; two keys collecting *different* sets, which is what an auxiliary
/// view shared wrongly would confuse; and sets of size zero, one and two, so
/// that the sum and the length disagree in more than one way. The two values
/// are 2 and 5 because that makes all four reachable answers distinct — a plan
/// that paired one key's sum with another key's length would have to answer a
/// number the query never does, rather than coincidentally the right one.
///
/// Three keys or three values would be sixteen or sixty-four times the work
/// for the same shapes, and the exhaustive three-node sweep already costs more
/// than half of the suite's running time.
const ExcessModel = struct {
    const size = 2;
    const keys = [size][]const u8{ "a", "b" };
    const values = [size]i64{ 2, 5 };
    const relations = 1 << (size * size);
    const subsets = 1 << size;

    fn relates(mask: u4, key: usize, value: usize) bool {
        return mask & (@as(u4, 1) << @intCast(key * size + value)) != 0;
    }

    fn admits(mask: u2, key: usize) bool {
        return mask & (@as(u2, 1) << @intCast(key)) != 0;
    }

    fn total(mask: u4, key: usize) i64 {
        var sum: i64 = 0;
        for (0..size) |value| if (relates(mask, key, value)) {
            sum += values[value];
        };
        return sum;
    }

    fn count(mask: u4, key: usize) i64 {
        var held: i64 = 0;
        for (0..size) |value| if (relates(mask, key, value)) {
            held += 1;
        };
        return held;
    }

    /// The three view extensions this database comes to. The two layers have a
    /// tuple for every key `p` admits, including one whose set is empty; the
    /// canonical view has one for every key `r` relates, whatever `p` said.
    fn extend(db: *database.Database, admitted: u2, related: u4) !void {
        for (0..size) |key| {
            if (admits(admitted, key)) {
                try addFactTerms(db, "v1", &.{
                    input.atom(keys[key]),
                    input.integer(total(related, key)),
                });
                try addFactTerms(db, "v2", &.{
                    input.atom(keys[key]),
                    input.integer(count(related, key)),
                });
            }
            if (count(related, key) == 0) continue;
            var held: [size]input.Term = undefined;
            var written: usize = 0;
            for (0..size) |value| if (relates(related, key, value)) {
                held[written] = input.integer(values[value]);
                written += 1;
            };
            try addFactTerms(db, "cr", &.{ input.atom(keys[key]), input.list(held[0..written]) });
        }
    }
};

test "bounded exhaustive models find no counterexample to the folded list function" {
    // The claim, checked by exhaustion rather than by argument, and held to
    // *equality* rather than to containment. The reconstruction of `r` is
    // exact — a canonical aggregate view is what Theorem 6.5.1 requires — so
    // Lemma 6.4.2 makes the auxiliary view's set the set the query collects,
    // and the two views between them know every key. A containment check would
    // pass a plan that had simply gone quiet.
    //
    // The oracle is arithmetic here rather than a second run of the engine: a
    // sweep that asked the engine what the answers were and then asked it
    // again through a plan would agree with itself whatever either one did.
    const allocator = std.testing.allocator;

    var planned: Jatalog = .init(allocator);
    defer planned.deinit();
    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    try Excess.catalog(&planned.state, &catalog);
    var rules: [2]fold_ir.Rule = undefined;
    try Excess.query(&planned.state, &catalog.symbols, &rules);
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&planned.state, &catalog.symbols, &.{
        input.relation("q", &.{ input.variable("X"), input.variable("E") }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());
    var executable = try folding.lowerPlan(
        allocator,
        &planned.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    try installPlan(&planned.state, &executable);

    var answered: usize = 0;
    for (0..ExcessModel.subsets) |admitted| {
        for (0..ExcessModel.relations) |related| {
            const keys: u2 = @intCast(admitted);
            const edges: u4 = @intCast(related);
            var folded = try planned.clone();
            defer folded.deinit();
            try ExcessModel.extend(&folded.state, keys, edges);

            var produced = try transaction.queryClauses(&folded.state, executable.goals, &.{});
            defer produced.deinit();
            var seen: usize = 0;
            for (produced.answers.items) |answer| {
                const text = try answer.bindings.items[0].value.getAtom();
                const key = text[0] - 'a';
                const excess = try answer.bindings.items[1].value.getInteger();
                const wanted = ExcessModel.total(edges, key) - ExcessModel.count(edges, key);
                if (!ExcessModel.admits(keys, key) or excess != wanted) {
                    std.debug.print("\np {b} r {b}: the plan answered {s} {d}, the query {d}\n", .{
                        keys,
                        edges,
                        text,
                        excess,
                        wanted,
                    });
                    return error.AnswerNotContained;
                }
                seen += 1;
                answered += 1;
            }
            // Equality, not containment: every key `p` admitted has an answer,
            // including one whose collected set is empty.
            var expected: usize = 0;
            for (0..ExcessModel.size) |key| {
                if (ExcessModel.admits(keys, key)) expected += 1;
            }
            if (seen != expected) {
                std.debug.print("\np {b} r {b}: the plan answered {d}, the query {d}\n", .{
                    keys,
                    edges,
                    seen,
                    expected,
                });
                return error.AnswersDiffer;
            }
        }
    }
    try std.testing.expect(answered > 0);
}

/// Folds and runs the smallest problem that exercises all three of F5's parts:
/// a query list function expanded into one a view exposes, a view split at its
/// aggregate, and the chase identifying the set its layer read with the set
/// the auxiliary view derives.
///
/// Deliberately two facts, two views and two rules. An allocation-failure
/// sweep runs the scenario once per allocation it makes, so its cost is
/// quadratic in its own size and three larger ones already exist.
fn listFunctionFoldingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v1(a, 1). cr(a, [1]).", null);
    facts.deinit();

    const x = input.variable("X");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");
    const l = input.variable("L");

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    _ = try defineView(&db.state, &catalog, input.fact("v1", &.{ x, t }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
    _ = try defineView(&db.state, &catalog, input.fact("cr", &.{ x, s }), &.{
        input.relation("r", &.{ x, y0 }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    // Built one at a time, because an array initializer whose second element
    // fails never assigns the array and never reaches the `defer` that would
    // have released the first.
    var rules: [2]fold_ir.Rule = undefined;
    var built: usize = 0;
    defer for (rules[0..built]) |rule| fold_ir.freeRule(allocator, rule);
    rules[0] = try foldingRule(&db.state, &catalog.symbols, input.fact("total", &.{ l, t }), &.{
        input.relation("sum", &.{ l, t }),
    });
    built = 1;
    rules[1] = try foldingRule(&db.state, &catalog.symbols, input.fact("q", &.{ x, t }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("total", &.{ s, t }),
    });
    built = 2;
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{ x, t }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    allocator.free(try outcome.explainAlloc(allocator, .{
        .symbols = &catalog.symbols,
        .strings = &db.state.strings,
        .scalars = &db.state.eval.scalars,
    }));
    if (outcome.guarantee() != .maximally_contained) return error.UnexpectedGuarantee;

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    answers.deinit();
}

test "folding a query's list functions releases every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(listFunctionFoldingAllocationScenario);
}

test "identifying two collected sets that were never one answers more than the query" {
    // The chase's own containment claim. `va` is functional in its key, so two
    // views written against *one* auxiliary view have collected one set — and
    // that is a claim about their definitions, not a convenience. Three views
    // here read a set with a list function and only two of them read the same
    // set: `v1` and `v3` group `r` by its first column, `v2` by its second.
    //
    // Get that wrong and the plan holds `length(the successors of X, how many
    // predecessors X has)`, which never held of anything, and the query built
    // on it answers a number it does not have. Merging the two classes in
    // `collectTheSameSet` is what this test breaks, and it then answers twice.
    const allocator = std.testing.allocator;

    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\sum([], 0).
        \\sum(H!T, S) :- sum(T, A), S = A + H.
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\p(a).
        \\r(a, 2). r(a, 5). r(b, a).
        \\seed([2, 5]). seed([b]).
        \\q(X, E) :- p(X), setof(Y, r(X, Y), S), sum(S, T), length(S, C), E = T - C.
    , null);
    program.deinit();
    var wanted = try source.execute("q(X, E)?", null);
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);
    // The successors of `a` are 2 and 5, so seven less two of them is five.
    try std.testing.expectEqual(@as(usize, 1), expected.len);
    try std.testing.expectEqualStrings("a 5", expected[0]);

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    // v1 sums the successors, v3 counts them, v2 counts the predecessors — and
    // `a` has two successors and one predecessor, so a plan confusing the two
    // sets answers six as well as five.
    var facts = try db.execute("v1(a, 7). v3(a, 2). v2(a, 1). cr(a, [2, 5]). cr(b, [a]).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");
    const c = input.variable("C");
    const e = input.variable("E");
    _ = try defineView(&db.state, &catalog, input.fact("v1", &.{ x, t }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
    _ = try defineView(&db.state, &catalog, input.fact("v3", &.{ x, c }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("length", &.{ s, c }),
    }, .materialized);
    _ = try defineView(&db.state, &catalog, input.fact("v2", &.{ x, c }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ y, x })}, s),
        input.relation("length", &.{ s, c }),
    }, .materialized);
    _ = try defineView(&db.state, &catalog, input.fact("cr", &.{ x, s }), &.{
        input.relation("r", &.{ x, y0 }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ x, e }),
        &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
            input.relation("length", &.{ s, c }),
            input.subtract(e, t, c),
        },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{ x, e }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    try std.testing.expectEqual(folding.Guarantee.maximally_contained, outcome.guarantee());

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    const actual = try answerTuples(&answers);
    defer freeLines(actual);
    // Exactly the query's answers: the view counting predecessors reports
    // about its own set, which the query never asks about, so it contributes
    // nothing rather than contributing a second answer.
    try std.testing.expectEqual(expected.len, actual.len);
    for (expected, actual) |one, other| try std.testing.expectEqualStrings(one, other);
}

test "an auxiliary view whose group a plan cannot name derives nothing rather than crashing" {
    // What an auxiliary view makes reachable that nothing before it did. `va`
    // is the first head a fold derives into that is neither a base relation
    // nor a split of one, and its body is the only place where an aggregate
    // stands beside goals that bind values for it. Both of those meet Skolem
    // elimination for the first time here.
    //
    // Two views project a column of the relations `va` groups by, so the plan
    // reconstructs `p` and `g` partly as splits holding values it cannot name.
    // A group keyed by such a value is a group with no name: the aggregate
    // beside it would read a variable that elimination spread across several
    // columns, and the head would be a split of a relation that has no parts.
    // Those instances are dropped — which costs answers and keeps containment,
    // like every other drop — and the plan answers from the groups it can name.
    const allocator = std.testing.allocator;

    var source: Jatalog = .init(allocator);
    defer source.deinit();
    var program = try source.execute(
        \\sum([], 0).
        \\sum(H!T, S) :- sum(T, A), S = A + H.
        \\p(a). g(w). m(z).
        \\r(a, 2). r(a, 5).
        \\seed([2, 5]).
        \\q(X, W, T) :- p(X), g(W), setof(Y, r(X, Y), S), sum(S, T).
    , null);
    program.deinit();
    var wanted = try source.execute("q(X, W, T)?", null);
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);
    try std.testing.expectEqual(@as(usize, 1), expected.len);
    try std.testing.expectEqualStrings("a w 7", expected[0]);

    var db: Jatalog = .init(allocator);
    defer db.deinit();
    var facts = try db.execute("v1(a, w, 7). cr(a, [2, 5]). hp(z). hg(z). m(z).", null);
    facts.deinit();

    var catalog: view_catalog.Catalog = .init(allocator);
    defer catalog.deinit();
    try catalog.declareBaseAvailable(.{ .name = try db.state.strings.intern("m"), .arity = 1 });
    const x = input.variable("X");
    const w = input.variable("W");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const z = input.variable("Z");
    const s = input.variable("S");
    const t = input.variable("T");
    _ = try defineView(&db.state, &catalog, input.fact("v1", &.{ x, w, t }), &.{
        input.relation("p", &.{x}),
        input.relation("g", &.{w}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
    // `hp` remembers that `p` held of something and not of what, so inverting
    // it reconstructs `p` at a value the plan can only name. `hg` does the
    // same to `g` — the difference that matters is that the auxiliary view's
    // aggregate reads its `p` column and not its `g` column.
    _ = try defineView(&db.state, &catalog, input.fact("hp", &.{z}), &.{
        input.relation("p", &.{x}),
        input.relation("m", &.{z}),
    }, .materialized);
    _ = try defineView(&db.state, &catalog, input.fact("hg", &.{z}), &.{
        input.relation("g", &.{w}),
        input.relation("m", &.{z}),
    }, .materialized);
    _ = try defineView(&db.state, &catalog, input.fact("cr", &.{ x, s }), &.{
        input.relation("r", &.{ x, y0 }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const rules = [_]fold_ir.Rule{try foldingRule(
        &db.state,
        &catalog.symbols,
        input.fact("q", &.{ x, w, t }),
        &.{
            input.relation("p", &.{x}),
            input.relation("g", &.{w}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
        },
    )};
    defer for (rules) |rule| fold_ir.freeRule(allocator, rule);
    const goals = try foldingGoals(&db.state, &catalog.symbols, &.{
        input.relation("q", &.{ x, w, t }),
    });
    defer fold_ir.freeGoals(allocator, goals);

    var outcome = try folding.foldQuery(allocator, &catalog, .{ .goals = goals, .rules = &rules });
    defer outcome.deinit();
    // Dropping an instance answers less, which is sound and is not maximal.
    try std.testing.expectEqual(folding.Guarantee.contained, outcome.guarantee());

    var executable = try folding.lowerPlan(
        allocator,
        &db.state.strings,
        &catalog.symbols,
        outcome.plan().?,
    );
    defer executable.deinit();
    var answers = try runPlan(&db.state, &executable);
    defer answers.deinit();
    const actual = try answerTuples(&answers);
    defer freeLines(actual);
    try std.testing.expectEqual(expected.len, actual.len);
    for (expected, actual) |one, other| try std.testing.expectEqualStrings(one, other);
}

/// The even-length-path problem of Chapter 6, stated through the public
/// interface: three stored pairs, a view saying what they are pairs of, and a
/// recursive query over a relation nothing holds any more.
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

/// The query those views are folded against: `q` is the transitive closure of
/// a relation only the view remembers.
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

/// The answers' values, one line per answer, in the order they are listed.
fn orderedTuples(result: *const results.QueryResult) ![][]u8 {
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
        for (answer.bindings.items, 0..) |binding, index| {
            if (index != 0) text.writer.writeByte(' ') catch return error.OutOfMemory;
            binding.value.write(&text.writer) catch return error.OutOfMemory;
        }
        line.* = try text.toOwnedSlice();
        written += 1;
    }
    return lines;
}

fn expectOrderedTuples(result: *const results.QueryResult, expected: []const []const u8) !void {
    const tuples = try orderedTuples(result);
    defer freeLines(tuples);
    try std.testing.expectEqual(expected.len, tuples.len);
    for (expected, tuples) |want, actual| try std.testing.expectEqualStrings(want, actual);
}

test "query and answerFolded list answers in the order the caller asks for, under its names" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    _ = try declareEvenPathViews(&db);
    const fold = try evenPathQuery(&db);
    defer fold.deinit();

    // One plan serves every order: the order is not part of the fold.
    var by_default = try db.answerFolded(fold, &.{});
    defer by_default.deinit();
    try expectOrderedTuples(&by_default, &.{ "a c", "a e", "b d", "c e" });
    try std.testing.expectEqualStrings("b", try by_default.answers.items[2].getAtom("X"));
    try std.testing.expectEqualStrings("d", try by_default.answers.items[2].getAtom("Y"));
    var descending = try db.answerFolded(fold, &.{input.descending("X")});
    defer descending.deinit();
    try expectOrderedTuples(&descending, &.{ "c e", "b d", "a c", "a e" });
    // `Z` is the query's too, but only its rules say it: no answer lists it.
    try std.testing.expectError(
        errors.Error.UnknownVariable,
        db.answerFolded(fold, &.{input.ascending("Z")}),
    );

    // The same question in other names reuses the plan and gets its own
    // names back, not the ones the plan was first folded under.
    const a = input.variable("A");
    const b = input.variable("B");
    const c = input.variable("C");
    const renamed = try db.foldQuery(&.{input.relation("q", &.{ a, b })}, &.{
        input.rule(input.fact("q", &.{ a, b }), &.{input.relation("edge", &.{ a, b })}),
        input.rule(input.fact("q", &.{ a, c }), &.{
            input.relation("edge", &.{ a, b }),
            input.relation("q", &.{ b, c }),
        }),
    });
    defer renamed.deinit();
    try std.testing.expect(renamed.reused);
    var reused = try db.answerFolded(renamed, &.{input.descending("B")});
    defer reused.deinit();
    try expectOrderedTuples(&reused, &.{ "a e", "c e", "b d", "a c" });
    try std.testing.expectEqualStrings("A", reused.answers.items[0].bindings.items[0].name);
    try std.testing.expectEqualStrings("B", reused.answers.items[0].bindings.items[1].name);

    var plain: Jatalog = .init(allocator);
    defer plain.deinit();
    try plain.addFact("score", &.{ input.atom("ann"), input.integer(3) });
    try plain.addFact("score", &.{ input.atom("bob"), input.integer(5) });
    try plain.addFact("score", &.{ input.atom("cat"), input.integer(3) });
    const goals = [_]input.Goal{input.relation("score", &.{ input.variable("P"), input.variable("S") })};
    var ranked = try plain.query(&goals, &.{input.descending("S")});
    defer ranked.deinit();
    try expectOrderedTuples(&ranked, &.{ "bob 5", "ann 3", "cat 3" });
}

test "a declared view answers a query about relations the database no longer has" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    _ = try declareEvenPathViews(&db);

    const fold = try evenPathQuery(&db);
    defer fold.deinit();
    // A view remembers pairs two edges apart and nothing else, so no plan over
    // it answers every path. Maximal containment is the whole claim, and it is
    // the caller's to accept.
    try std.testing.expectEqual(Guarantee.maximally_contained, fold.guarantee);
    try std.testing.expect(!fold.reused);

    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);
    try std.testing.expectEqual(@as(usize, 4), tuples.len);
    for ([_][]const u8{ "a c", "a e", "b d", "c e" }, tuples) |expected, actual|
        try std.testing.expectEqualStrings(expected, actual);

    // What the guarantee does not say on its own: where the loss is. One
    // relation is derived rather than read, and no canonical aggregate view of
    // it was available, so that is the place an answer could have gone.
    var reconstructed = try db.foldReconstructions(fold);
    defer reconstructed.deinit();
    try std.testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try std.testing.expectEqualStrings("edge", reconstructed.items[0].predicate);
    try std.testing.expectEqual(@as(usize, 2), reconstructed.items[0].arity);
    try std.testing.expect(!reconstructed.items[0].exact);

    const explanation = try db.explainFold(fold);
    defer allocator.free(explanation);
    try std.testing.expect(std.mem.startsWith(u8, explanation, "guarantee: maximally contained"));

    // The views belong to the database, so a copy of it has them: the same
    // question folds to the same guarantee and the same answers without being
    // declared again. The folded plans do not come with it — a cache is not
    // state — so the copy folds afresh.
    var copy = try db.clone();
    defer copy.deinit();
    const copied = try evenPathQuery(&copy);
    defer copied.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, copied.guarantee);
    try std.testing.expect(!copied.reused);
    var copied_answers = try copy.answerFolded(copied, &.{});
    defer copied_answers.deinit();
    try std.testing.expectEqual(@as(usize, 4), copied_answers.answers.items.len);

    // Running a plan changes nothing here. It ran on a copy, so none of the
    // relations it reconstructed joined this database.
    var direct = try db.query(&.{input.relation("v", &.{
        input.variable("X"),
        input.variable("Y"),
    })}, &.{});
    defer direct.deinit();
    try std.testing.expectEqual(@as(usize, 3), direct.answers.items.len);
}

test "a query inside the availability boundary is its own plan, and a hybrid one is not" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const c = input.variable("C");

    // The caller still has `label` and says so. `r` is gone, and a canonical
    // aggregate view of it — the relation copied — is what remains.
    try db.addFact("label", &.{ input.atom("a"), input.atom("red") });
    try db.addFact("label", &.{ input.atom("b"), input.atom("blue") });
    try db.addFact("copy", &.{ input.atom("a"), input.atom("one") });
    try db.addFact("copy", &.{ input.atom("b"), input.atom("two") });
    try db.declareBaseAvailable("label", 2);
    _ = try db.defineView(
        input.fact("copy", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
        .materialized,
    );

    // Two things the plan is not allowed to see, left here on purpose. A
    // canonical view reconstructs `r` under its own name, so anything this
    // database happens to hold or derive under that name would join the plan's
    // reconstruction and answer more than the views can account for. One is a
    // leftover fact and the other a rule that manufactures more of them out of
    // a relation the plan *is* allowed to read, so neither is stopped by the
    // other's absence.
    try db.addFact("r", &.{ input.atom("a"), input.atom("three") });
    try db.addRule(
        input.relation("r", &.{ x, x }),
        &.{input.relation("copy", &.{ x, y })},
    );

    // Nothing was reconstructed, because nothing had to be: the query reads
    // what the policy declared. That is the only way to earn `equivalent`.
    const plain = try db.foldQuery(&.{input.relation("label", &.{ x, c })}, &.{});
    defer plain.deinit();
    try std.testing.expectEqual(Guarantee.equivalent, plain.guarantee);
    var plain_answers = try db.answerFolded(plain, &.{});
    defer plain_answers.deinit();
    try std.testing.expectEqual(@as(usize, 2), plain_answers.answers.items.len);

    // Half read and half reconstructed. The guarantee falls to maximal
    // containment because a reconstruction is in general a subset — and here
    // it happens not to be, which is what the per-relation account says and
    // the guarantee alone cannot.
    const hybrid = try db.foldQuery(&.{
        input.relation("r", &.{ x, y }),
        input.relation("label", &.{ x, c }),
    }, &.{});
    defer hybrid.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, hybrid.guarantee);
    var reconstructed = try db.foldReconstructions(hybrid);
    defer reconstructed.deinit();
    try std.testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try std.testing.expectEqualStrings("r", reconstructed.items[0].predicate);
    try std.testing.expect(reconstructed.items[0].exact);

    var joined = try db.answerFolded(hybrid, &.{});
    defer joined.deinit();
    const tuples = try answerTuples(&joined);
    defer freeLines(tuples);
    try std.testing.expectEqual(@as(usize, 2), tuples.len);
    try std.testing.expectEqualStrings("a one red", tuples[0]);
    try std.testing.expectEqualStrings("b two blue", tuples[1]);

    // The leftover fact and the rule's two derivations are all still here, and
    // all three would have joined the plan's reconstruction of `r` had the
    // plan run against this database rather than against a copy of what the
    // catalog admits.
    var here = try db.query(&.{input.relation("r", &.{ x, y })}, &.{});
    defer here.deinit();
    try std.testing.expectEqual(@as(usize, 3), here.answers.items.len);
}

/// Two canonical aggregate views of one relation: `wide` is the relation
/// copied and `narrow` is it grouped by its first column. Both remember all of
/// `r` — Lemma 6.4.2 — so a plan may read either and get `r` itself back,
/// which is exactly what makes choosing between them a cost question and only
/// a cost question. `wide` is declared first, so preferring `narrow` can only
/// be cost and never declaration order.
fn declareInterchangeableViews(db: *Jatalog) !void {
    const x1 = input.variable("X1");
    const x2 = input.variable("X2");
    const y2 = input.variable("Y2");
    const s = input.variable("S");
    _ = try db.defineView(
        input.fact("wide", &.{ x1, x2 }),
        &.{input.relation("r", &.{ x1, x2 })},
        .materialized,
    );
    _ = try db.defineView(input.fact("narrow", &.{ x1, s }), &.{
        input.relation("r", &.{ x1, x2 }),
        input.setof(y2, &.{input.relation("r", &.{ x1, y2 })}, s),
    }, .materialized);
}

test "cost picks between views that reconstruct one relation exactly, and picks the same way twice" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try declareInterchangeableViews(&db);

    // `r` holds two values for one key, so the grouped view stores one tuple
    // where the copy stores two. Both give `r` back whole.
    try db.addFact("wide", &.{ input.atom("a"), input.atom("one") });
    try db.addFact("wide", &.{ input.atom("a"), input.atom("two") });
    try db.addFact("narrow", &.{
        input.atom("a"),
        input.list(&.{ input.atom("one"), input.atom("two") }),
    });

    const goals = [_]input.Goal{input.relation("r", &.{
        input.atom("a"),
        input.variable("V"),
    })};
    const fold = try db.foldQuery(&goals, &.{});
    defer fold.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, fold.guarantee);

    const explanation = try db.explainFold(fold);
    defer allocator.free(explanation);
    // The smaller extension is read and the larger is left out of the plan.
    try std.testing.expect(std.mem.indexOf(
        u8,
        explanation,
        "being the smallest of them: narrow@1/2",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, explanation, "wide@0/2") == null);

    // Cost chose, and it did not choose a weaker plan to do it: the relation
    // is still reconstructed exactly, and the answers are the ones `r` has.
    var reconstructed = try db.foldReconstructions(fold);
    defer reconstructed.deinit();
    try std.testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try std.testing.expect(reconstructed.items[0].exact);

    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);
    try std.testing.expectEqual(@as(usize, 2), tuples.len);
    try std.testing.expectEqualStrings("one", tuples[0]);
    try std.testing.expectEqualStrings("two", tuples[1]);

    // Folded again from nothing — no cached plan to hand back — the same
    // catalog over the same data reaches the same decisions in the same order.
    // A cost decision that did not would be a plan cache holding one of two
    // programs depending on when it was asked. What is compared is the record
    // of what the fold did rather than the whole rendering, because a plan's
    // variables carry their identities and a second fold opens a scope of its
    // own: the same plan twice prints different numbers by construction.
    db.clearPlanCache();
    const again = try db.foldQuery(&goals, &.{});
    defer again.deinit();
    const repeated = try db.explainFold(again);
    defer allocator.free(repeated);
    const marker = "transformations:\n";
    const decisions = explanation[std.mem.indexOf(u8, explanation, marker).?..];
    const decisions_again = repeated[std.mem.indexOf(u8, repeated, marker).?..];
    try std.testing.expectEqualStrings(decisions, decisions_again);
}

test "a folded plan walks a stored list and answers what the membership rules derive" {
    // `$member` reaches the evaluator as a walk over the one list a stored
    // tuple bound, not as the three rules the plan renders. The two have to
    // agree on every list an extension can hold, and an embedder's stored
    // extension can hold lists no `setof` would have collected: one holding a
    // value twice, one that never reaches `[]`, one that is empty, and one
    // whose elements are lists themselves. The same rules, written as a
    // program over the same tuples, say what the answers must be.
    const allocator = std.testing.allocator;
    var folded: Jatalog = .init(allocator);
    defer folded.deinit();
    const x1 = input.variable("X1");
    _ = try folded.defineView(input.fact("narrow", &.{ x1, input.variable("S") }), &.{
        input.relation("r", &.{ x1, input.variable("X2") }),
        input.setof(input.variable("Y2"), &.{input.relation("r", &.{
            x1,
            input.variable("Y2"),
        })}, input.variable("S")),
    }, .materialized);
    const head = input.atom("a");
    const tail = input.atom("b");
    const improper: input.Term.Cons = .{ .head = &head, .tail = &tail };
    const stored = [_][2]input.Term{
        .{ input.atom("k1"), input.list(&.{ input.atom("a"), input.atom("b"), input.atom("a") }) },
        .{ input.atom("k2"), input.cons(&improper) },
        .{ input.atom("k3"), input.list(&.{}) },
        .{ input.atom("k4"), input.list(&.{
            input.list(&.{ input.atom("a"), input.atom("b") }),
            input.atom("c"),
        }) },
        .{ input.atom("k5"), input.list(&.{input.atom("b")}) },
    };
    for (stored) |terms| try folded.addFact("narrow", &terms);

    const fold = try folded.foldQuery(&.{input.relation("r", &.{
        input.variable("K"),
        input.variable("V"),
    })}, &.{});
    defer fold.deinit();
    var answers = try folded.answerFolded(fold, &.{});
    defer answers.deinit();
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);

    var direct: Jatalog = .init(allocator);
    defer direct.deinit();
    var expected = try direct.execute(
        \\narrow(k1, [a, b, a]). narrow(k2, a!b). narrow(k3, []).
        \\narrow(k4, [[a, b], c]). narrow(k5, [b]).
        \\member(X, X!R) :- R = [].
        \\member(X, X!R) :- member(O, R).
        \\member(O, F!R) :- member(O, R).
        \\r(K, V) :- narrow(K, S), member(V, S).
        \\r(K, V)?
    , null);
    defer expected.deinit();
    const expected_tuples = try answerTuples(&expected.query);
    defer freeLines(expected_tuples);

    try std.testing.expectEqual(@as(usize, 5), expected_tuples.len);
    try std.testing.expectEqual(expected_tuples.len, tuples.len);
    for (expected_tuples, tuples) |want, got| try std.testing.expectEqualStrings(want, got);
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

test "views that reconstruct one relation equally well are chosen between by declaration order" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try declareInterchangeableViews(&db);

    // One value for the one key, so the copy and the grouping store one tuple
    // each and cost has nothing to say. Something still has to decide, and it
    // has to decide the same way every time, so it is the first declaration.
    try db.addFact("wide", &.{ input.atom("a"), input.atom("one") });
    try db.addFact("narrow", &.{ input.atom("a"), input.list(&.{input.atom("one")}) });

    const fold = try db.foldQuery(&.{input.relation("r", &.{
        input.atom("a"),
        input.variable("V"),
    })}, &.{});
    defer fold.deinit();
    const explanation = try db.explainFold(fold);
    defer allocator.free(explanation);
    try std.testing.expect(std.mem.indexOf(
        u8,
        explanation,
        "being the smallest of them: wide@0/2",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, explanation, "narrow@1/2") == null);

    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    try std.testing.expectEqual(@as(usize, 1), answers.answers.items.len);
}

test "a folded plan is reused until the views or the rules it was folded against move on" {
    const allocator = std.testing.allocator;
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    const view = try declareEvenPathViews(&db);

    const first = try evenPathQuery(&db);
    defer first.deinit();
    try std.testing.expect(!first.reused);
    const second = try evenPathQuery(&db);
    defer second.deinit();
    try std.testing.expect(second.reused);
    var stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 1), stats.cached_plans);
    try std.testing.expectEqual(@as(usize, 1), stats.plan_hits);
    try std.testing.expectEqual(@as(usize, 1), stats.plan_misses);
    try std.testing.expectEqual(@as(usize, 0), stats.plan_invalidations);

    // Withdrawing the extension changes what every plan folded against this
    // catalog was allowed to read, so both handles stop naming anything. A
    // handle that survived would name whichever plan later took its place.
    db.setViewAvailability(view, .withheld);
    try std.testing.expectError(error.StalePlan, db.explainFold(first));
    try std.testing.expectError(error.StalePlan, db.answerFolded(second, &.{}));

    const withheld = try evenPathQuery(&db);
    defer withheld.deinit();
    try std.testing.expectEqual(Guarantee.unsupported, withheld.guarantee);
    // No plan at all rather than an empty one, which is the distinction the
    // whole interface is shaped around: there is nothing to run.
    try std.testing.expectError(error.PlanNotExecutable, db.answerFolded(withheld, &.{}));
    const refusal = try db.explainFold(withheld);
    defer allocator.free(refusal);
    try std.testing.expect(std.mem.indexOf(u8, refusal, "unmet preconditions") != null);
    stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 1), stats.plan_invalidations);

    // Restoring it does not restore the discarded plan: the question is folded
    // again, and it comes back with the guarantee it had.
    db.setViewAvailability(view, .materialized);
    const restored = try evenPathQuery(&db);
    defer restored.deinit();
    try std.testing.expect(!restored.reused);
    try std.testing.expectEqual(Guarantee.maximally_contained, restored.guarantee);

    // A rule addition invalidates for a different reason — a published
    // definition is a rule's, and this cache cannot tell which plans read one
    // — so it discards them all.
    try db.addRule(
        input.relation("reachable", &.{input.variable("X")}),
        &.{input.relation("v", &.{ input.variable("X"), input.variable("Y") })},
    );
    try std.testing.expectError(error.StalePlan, db.explainFold(restored));
    (try evenPathQuery(&db)).deinit();
    // Three discards: the withdrawal, the restoration, and the rule. Restoring
    // an availability is a change like any other — the cache cannot tell that
    // it undid the previous one, and a stamp that could would be a stamp that
    // had to understand what it was counting.
    try std.testing.expectEqual(@as(usize, 3), db.foldStats().plan_invalidations);
}

/// One folded answer, as sorted tuples. The error is passed through rather
/// than caught, because a change can make a question unanswerable and *which*
/// error comes back is part of what a kept reconstruction has to reproduce.
fn foldedTuples(db: *Jatalog, goals: []const input.Goal) ![][]u8 {
    const fold = try db.foldQuery(goals, &.{});
    defer fold.deinit();
    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    return answerTuples(&answers);
}

/// Asks the question twice: once against whatever the database has kept, and
/// once with the plan cache cleared, which is the reference path — nothing
/// cached, everything rebuilt from current state. The two must agree.
///
/// This is the shared rule the whole engine rests on, applied to folding: a
/// full rebuild stays available and an incremental path is only ever allowed
/// to be faster than it.
fn expectKeptMatchesRebuilt(db: *Jatalog, goals: []const input.Goal) !void {
    const kept = foldedTuples(db, goals);
    defer if (kept) |lines| freeLines(lines) else |_| {};
    db.clearPlanCache();
    const rebuilt = foldedTuples(db, goals);
    defer if (rebuilt) |lines| freeLines(lines) else |_| {};
    if (kept) |kept_lines| {
        const rebuilt_lines = try rebuilt;
        try std.testing.expectEqual(rebuilt_lines.len, kept_lines.len);
        for (kept_lines, rebuilt_lines) |mine, theirs|
            try std.testing.expectEqualStrings(theirs, mine);
    } else |kept_error| {
        try std.testing.expectError(kept_error, rebuilt);
    }
}

fn expectFoldedRowCount(db: *Jatalog, goals: []const input.Goal, expected: usize) !void {
    const lines = try foldedTuples(db, goals);
    defer freeLines(lines);
    try std.testing.expectEqual(expected, lines.len);
}

test "a kept reconstruction answers exactly what a rebuilt one answers, after each kind of change" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const question = [_]input.Goal{input.relation("r", &.{ x, y })};

    // A canonical aggregate view of a relation that is gone, so a plan reading
    // it gets `r` itself back — Lemma 6.4.2. Beside it, a withheld view of a
    // relation this question never mentions, which is where a fact can arrive
    // under a name no plan is allowed to read.
    const copied = try db.defineView(
        input.fact("copied", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
        .materialized,
    );
    _ = try db.defineView(
        input.fact("linked", &.{ x, y }),
        &.{input.relation("s", &.{ x, y })},
        .withheld,
    );
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });

    const first = try db.foldQuery(&question, &.{});
    defer first.deinit();
    try std.testing.expect(!first.reused);
    {
        var answers = try db.answerFolded(first, &.{});
        defer answers.deinit();
        try std.testing.expectEqual(@as(usize, 1), answers.answers.items.len);
    }

    // A fact under a name the catalog already admits, which is the one change
    // nothing a folded plan is stamped against can see. The plan is still the
    // right plan — it is reused, nothing was invalidated, and the handle from
    // before the fact still names it — and the extension it reads is one tuple
    // larger, so the answer is one row larger. Everything kept between two
    // calls has to notice a change that moves no stamp.
    try db.addFact("copied", &.{ input.atom("b"), input.atom("two") });
    const again = try db.foldQuery(&question, &.{});
    defer again.deinit();
    try std.testing.expect(again.reused);
    try std.testing.expectEqual(@as(usize, 0), db.foldStats().plan_invalidations);
    {
        var answers = try db.answerFolded(first, &.{});
        defer answers.deinit();
        try std.testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
    try expectKeptMatchesRebuilt(&db, &question);

    // A fact under a withheld name changes nothing, and has to change nothing
    // for the same reason the first one had to change something: the boundary
    // is what the catalog admits, not what the database holds.
    try db.addFact("linked", &.{ input.atom("z"), input.atom("zed") });
    try expectFoldedRowCount(&db, &question, 2);
    try expectKeptMatchesRebuilt(&db, &question);

    try db.addFact("copied", &.{ input.atom("c"), input.atom("three") });
    try expectFoldedRowCount(&db, &question, 3);
    try expectKeptMatchesRebuilt(&db, &question);

    // A retraction, which moves the same nothing an insertion does.
    try std.testing.expect(try db.retract(&.{input.relation(
        "copied",
        &.{ input.atom("c"), input.atom("three") },
    )}));
    try expectFoldedRowCount(&db, &question, 2);
    try expectKeptMatchesRebuilt(&db, &question);

    // A view made unreadable. The one extension that remembers `r` is
    // withdrawn, so there is no plan at all — not a plan answering from what
    // was readable a moment ago.
    db.setViewAvailability(copied, .withheld);
    try std.testing.expectError(error.PlanNotExecutable, foldedTuples(&db, &question));
    try expectKeptMatchesRebuilt(&db, &question);

    // And made readable again, which folds the question afresh rather than
    // restoring what was discarded.
    db.setViewAvailability(copied, .materialized);
    try expectFoldedRowCount(&db, &question, 2);
    try expectKeptMatchesRebuilt(&db, &question);

    // A definition added, over a relation this question never mentions.
    _ = try db.defineView(
        input.fact("marked", &.{x}),
        &.{input.relation("mark", &.{x})},
        .withheld,
    );
    try expectFoldedRowCount(&db, &question, 2);
    try expectKeptMatchesRebuilt(&db, &question);

    // A rule added to the database, which the plan runs without.
    try db.addRule(
        input.relation("pair", &.{ x, y }),
        &.{input.relation("copied", &.{ x, y })},
    );
    try expectFoldedRowCount(&db, &question, 2);
    try expectKeptMatchesRebuilt(&db, &question);

    // And that rule published as a view, which is a definition arriving from
    // the program rather than from the caller.
    try db.materialize();
    _ = try db.publishView("pair", 2, .materialized);
    try expectFoldedRowCount(&db, &question, 2);
    try expectKeptMatchesRebuilt(&db, &question);
}

test "asking a folded question twice grows neither the database nor what it interned" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const question = [_]input.Goal{input.relation("r", &.{ x, y })};

    _ = try db.defineView(
        input.fact("copied", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
        .materialized,
    );
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });
    try db.addFact("copied", &.{ input.atom("b"), input.atom("two") });

    const fold = try db.foldQuery(&question, &.{});
    defer fold.deinit();
    var warmup = try db.answerFolded(fold, &.{});
    warmup.deinit();

    const facts = db.state.facts.len();
    const closure = db.maintenanceStats().closure_facts;
    const interned = db.internStats();
    for (0..4) |_| {
        (try db.foldQuery(&question, &.{})).deinit();
        var answers = try db.answerFolded(fold, &.{});
        defer answers.deinit();
        try std.testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
    // A folded plan reconstructs relations this database deliberately does not
    // have. Whatever it keeps between calls to avoid rebuilding them is kept
    // somewhere else: the same question asked five times leaves this database
    // holding exactly what one question left it holding.
    try std.testing.expectEqual(facts, db.state.facts.len());
    try std.testing.expectEqual(closure, db.maintenanceStats().closure_facts);
    try std.testing.expectEqual(interned.value_entries, db.internStats().value_entries);
    try std.testing.expectEqual(interned.scalar_entries, db.internStats().scalar_entries);
}

test "a maintained predicate published as a view answers without its own base facts" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");

    try db.addFact("edge", &.{ input.atom("a"), input.atom("b") });
    try db.addFact("edge", &.{ input.atom("b"), input.atom("c") });
    try db.addFact("edge", &.{ input.atom("c"), input.atom("d") });
    try db.addRule(input.relation("two", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("edge", &.{ y, z }),
    });
    try db.materialize();

    // The definition comes from the rule; the extension is what maintenance
    // already keeps under `two/2`. Nothing is copied and nothing is declared
    // twice.
    _ = try db.publishView("two", 2, .materialized);
    const fold = try evenPathQuery(&db);
    defer fold.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, fold.guarantee);

    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    const tuples = try answerTuples(&answers);
    defer freeLines(tuples);
    // `edge` is still in this database and the rule deriving `two` still runs
    // in it, and neither is in the copy the plan ran on. Had either been, the
    // answers would have been the real transitive closure — six pairs — rather
    // than the paths of even length the view remembers.
    try std.testing.expectEqual(@as(usize, 2), tuples.len);
    try std.testing.expectEqualStrings("a c", tuples[0]);
    try std.testing.expectEqualStrings("b d", tuples[1]);

    var real = try db.query(&.{input.relation("two", &.{ x, y })}, &.{});
    defer real.deinit();
    try std.testing.expectEqual(@as(usize, 2), real.answers.items.len);

    // The definition was the rule's, and the rules have moved on. Folding
    // against it now would reason from something the database no longer says.
    try db.addRule(
        input.relation("two", &.{ x, y }),
        &.{input.relation("edge", &.{ x, y })},
    );
    try std.testing.expectError(error.StaleViewDefinition, evenPathQuery(&db));
}

test "two readable extensions of one name are refused at selection, not after a fold" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");

    try db.addFact("v", &.{ input.atom("a"), input.atom("b") });
    _ = try db.defineView(
        input.fact("v", &.{ x, y }),
        &.{input.relation("edge", &.{ x, y })},
        .materialized,
    );
    const rival = try db.defineView(
        input.fact("v", &.{ x, y }),
        &.{input.relation("link", &.{ x, y })},
        .materialized,
    );

    // A lowered plan names what it reads by the name the extension is stored
    // under, so a selection holding two of them under `v/2` cannot be executed
    // whatever is asked of it. That makes it the selection's fault rather than
    // the query's, and it is reported without folding anything — including for
    // a query that would never have touched either view.
    const goals = [_]input.Goal{input.relation("edge", &.{ x, y })};
    try std.testing.expectError(error.AmbiguousViewName, db.foldQuery(&goals, &.{}));
    try std.testing.expectError(
        error.AmbiguousViewName,
        db.foldQuery(&.{input.relation("unrelated", &.{x})}, &.{}),
    );
    try std.testing.expectEqual(@as(usize, 0), db.foldStats().plan_misses);

    // Withholding one leaves one readable extension of that name.
    db.setViewAvailability(rival, .withheld);
    const fold = try db.foldQuery(&goals, &.{});
    defer fold.deinit();
    try std.testing.expectEqual(Guarantee.maximally_contained, fold.guarantee);
}

/// The public folding path end to end on the smallest database that exercises
/// it: one view, one stored tuple, one fold, and the three things a caller can
/// do with what comes back.
fn publicFoldingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    try db.addFact("v", &.{ input.atom("a"), input.atom("b") });
    _ = try db.defineView(
        input.fact("v", &.{ x, y }),
        &.{input.relation("edge", &.{ x, y })},
        .materialized,
    );

    const fold = try db.foldQuery(&.{input.relation("edge", &.{ x, y })}, &.{});
    defer fold.deinit();
    if (fold.guarantee != .maximally_contained) return error.UnexpectedGuarantee;
    allocator.free(try db.explainFold(fold));
    var reconstructed = try db.foldReconstructions(fold);
    reconstructed.deinit();
    var answers = try db.answerFolded(fold, &.{});
    answers.deinit();
}

test "declaring a view, folding and running the plan release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(publicFoldingAllocationScenario);
}

/// One view, one fact, and a question folded against it. Used by the tests
/// below that care about what a plan keeps rather than about what it answers.
fn declareCopiedView(db: *Jatalog) !void {
    const x = input.variable("X");
    const y = input.variable("Y");
    _ = try db.defineView(
        input.fact("copied", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
        .materialized,
    );
}

const copied_question = [_]input.Goal{input.relation("r", &.{
    input.variable("X"),
    input.variable("Y"),
})};

test "a folded plan derives its reconstruction once and reuses it until the facts move" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try declareCopiedView(&db);
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });

    const fold = try db.foldQuery(&copied_question, &.{});
    defer fold.deinit();
    // Nothing is kept until a plan is run: folding decides what to read, and
    // deciding does not read it.
    try std.testing.expectEqual(@as(usize, 0), db.foldStats().kept_reconstructions);

    for (0..3) |_| {
        var answers = try db.answerFolded(fold, &.{});
        defer answers.deinit();
        try std.testing.expectEqual(@as(usize, 1), answers.answers.items.len);
    }
    var stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 1), stats.kept_reconstructions);
    try std.testing.expectEqual(@as(usize, 1), stats.reconstruction_misses);
    try std.testing.expectEqual(@as(usize, 2), stats.reconstruction_hits);

    // A fact under a readable name leaves the plan alone and takes the
    // reconstruction: the handle still names the plan, the plan cache reports
    // no invalidation, and the next answer is derived again.
    try db.addFact("copied", &.{ input.atom("b"), input.atom("two") });
    {
        var answers = try db.answerFolded(fold, &.{});
        defer answers.deinit();
        try std.testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
    stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 0), stats.plan_invalidations);
    try std.testing.expectEqual(@as(usize, 2), stats.reconstruction_misses);
    try std.testing.expectEqual(@as(usize, 2), stats.reconstruction_hits);

    // A catalog change takes both, and the handle with them, which is the
    // distinction the two stamps exist to draw.
    _ = try db.defineView(
        input.fact("marked", &.{input.variable("X")}),
        &.{input.relation("mark", &.{input.variable("X")})},
        .withheld,
    );
    try std.testing.expectError(error.StalePlan, db.answerFolded(fold, &.{}));
    (try db.foldQuery(&copied_question, &.{})).deinit();
    stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, 1), stats.plan_invalidations);
    try std.testing.expectEqual(@as(usize, 0), stats.kept_reconstructions);

    // And clearing the cache is what gives the memory back, which is the one
    // control an embedder has over reconstructions it is no longer asking for.
    const refolded = try db.foldQuery(&copied_question, &.{});
    defer refolded.deinit();
    var again = try db.answerFolded(refolded, &.{});
    again.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.foldStats().kept_reconstructions);
    db.clearPlanCache();
    try std.testing.expectEqual(@as(usize, 0), db.foldStats().kept_reconstructions);
}

test "the cache holds a bounded number of reconstructions and drops the coldest" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    const y = input.variable("Y");
    try declareCopiedView(&db);
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });

    // Six questions of one plan's shape, each keyed on its own constant, so
    // each folds to a plan of its own and each plan wants a reconstruction.
    const constants = [_][]const u8{ "a", "b", "c", "d", "e", "f" };
    var folds: [constants.len]Fold = undefined;
    var folded: usize = 0;
    defer for (folds[0..folded]) |fold| fold.deinit();
    for (constants, &folds) |constant, *slot| {
        const goals = [_]input.Goal{input.relation("r", &.{ input.atom(constant), y })};
        slot.* = try db.foldQuery(&goals, &.{});
        folded += 1;
        var answers = try db.answerFolded(slot.*, &.{});
        answers.deinit();
    }
    const stats = db.foldStats();
    try std.testing.expectEqual(@as(usize, constants.len), stats.cached_plans);
    // The plans are all still here — a plan is small and discarding one costs
    // a fold — and the reconstructions are not, because each is a database.
    try std.testing.expect(stats.kept_reconstructions < constants.len);
    try std.testing.expectEqual(@as(usize, 6), stats.reconstruction_misses);

    // Every plan still answers, whether or not its reconstruction survived.
    for (constants, folds) |constant, fold| {
        var answers = try db.answerFolded(fold, &.{});
        defer answers.deinit();
        const expected: usize = if (std.mem.eql(u8, constant, "a")) 1 else 0;
        try std.testing.expectEqual(expected, answers.answers.items.len);
    }
}

/// A fold, an answer, a fact under the name the plan reads, and another
/// answer: the whole of what F7 added, in the smallest database that has it.
fn keptReconstructionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: Jatalog = .init(allocator);
    defer db.deinit();
    try declareCopiedView(&db);
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });

    const fold = try db.foldQuery(&copied_question, &.{});
    defer fold.deinit();
    var first = try db.answerFolded(fold, &.{});
    first.deinit();

    try db.addFact("copied", &.{ input.atom("b"), input.atom("two") });
    var refreshed = try db.answerFolded(fold, &.{});
    const rows = refreshed.answers.items.len;
    refreshed.deinit();
    if (rows != 2) return error.UnexpectedResult;

    var reused = try db.answerFolded(fold, &.{});
    reused.deinit();
}

test "refreshing and reusing a kept reconstruction release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(keptReconstructionAllocationScenario);
}

test "an allocation failure answering a folded question leaves the next answer correct" {
    // The sweep above says a failure releases what it allocated. This says
    // what the database is afterwards, which a sweep cannot: a half-derived
    // reconstruction must not be the thing a later call answers from.
    var failing: std.testing.FailingAllocator = .init(std.testing.allocator, .{});
    var db: Jatalog = .init(failing.allocator());
    defer db.deinit();
    try declareCopiedView(&db);
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });
    try db.addFact("copied", &.{ input.atom("b"), input.atom("two") });
    const fold = try db.foldQuery(&copied_question, &.{});
    defer fold.deinit();

    var offset: usize = 0;
    while (offset < 400) : (offset += 1) {
        // Fail one allocation of the next answer, wherever in it that lands:
        // deriving the reconstruction the first time round the loop, solving
        // against a kept one afterwards.
        failing.fail_index = failing.alloc_index + offset;
        if (db.answerFolded(fold, &.{})) |result| {
            var answers = result;
            answers.deinit();
        } else |_| {}
        failing.fail_index = std.math.maxInt(usize);

        var answers = try db.answerFolded(fold, &.{});
        defer answers.deinit();
        try std.testing.expectEqual(@as(usize, 2), answers.answers.items.len);
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

test "a fold's question and program are checked against the schemas" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try declareCopiedView(&db);
    try db.declareSchema(input.schema("r", &.{ input.column(null, .atom), input.column(null, .atom) }));
    try db.addFact("copied", &.{ input.atom("a"), input.atom("one") });

    try std.testing.expectError(errors.Error.IllTyped, db.foldQuery(
        &.{input.relation("r", &.{input.variable("X")})},
        &.{},
    ));
    try std.testing.expectError(errors.Error.IllTyped, db.foldQuery(
        &.{input.relation("r", &.{ input.variable("X"), input.integer(1) })},
        &.{},
    ));
    const fold = try db.foldQuery(&.{
        input.relation("r", &.{ input.variable("X"), input.variable("Y") }),
        input.typeTest(input.variable("Y"), .atom),
    }, &.{});
    defer fold.deinit();
    var answers = try db.answerFolded(fold, &.{});
    defer answers.deinit();
    try std.testing.expectEqual(@as(usize, 1), answers.answers.items.len);
}
