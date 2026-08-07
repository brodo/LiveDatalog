//! A small, embeddable Datalog engine modeled after Jatalog.
const std = @import("std");
pub const input = @import("input.zig");
const errors = @import("errors.zig");
const relation_store = @import("relation_store.zig");
const cost_model = @import("cost_model.zig");
const syntax = @import("syntax.zig");
const results = @import("results.zig");
const evaluator = @import("evaluator.zig");
const test_support = @import("test_support.zig");
const parser = @import("parser.zig");
const maintenance = @import("maintenance.zig");
const compile = @import("compile.zig");
const materialization = @import("materialization.zig");
const validation = @import("validation.zig");
const aggregate_view = @import("aggregate_view.zig");

/// Re-exported so embedders name one error set, whichever layer produced it.
pub const Error = errors.Error;
pub const ResultValue = results.ResultValue;
pub const Answer = results.Answer;
pub const QueryResult = results.QueryResult;
pub const ExecutionResult = results.ExecutionResult;
/// Re-exported so callers select a policy without importing the model.
pub const MaintenancePolicy = cost_model.MaintenancePolicy;

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
    policy: MaintenancePolicy,
    /// Updates the cost model sent down each path.
    maintain_choices: usize,
    recompute_choices: usize,
    /// Learned cost estimates in candidate facts examined, null until the
    /// database has observed one of each.
    rebuild_work: ?u64,
    maintenance_work_per_fact: ?u64,
    /// Maintained aggregate views whose head retains every outer variable.
    self_maintainable_views: usize,
    /// Maintained aggregate views whose head projects outer variables away
    /// and therefore need auxiliary derivation counts.
    projected_views: usize,
    auxiliary_tuples: usize,
};

pub const Jatalog = struct {
    allocator: std.mem.Allocator,
    strings: compile.StringTable,
    /// The program: interned values, rules, their analysis, and the
    /// machinery that evaluates them against a fact store.
    eval: evaluator.Evaluator,
    facts: relation_store.RelationStore,
    /// Persistent derived closure: the base facts plus every derived fact,
    /// exposed to evaluation as one unified read view. Null until the first
    /// evaluation on a database with rules.
    closure: ?relation_store.RelationStore = null,
    materialization: materialization.Materialization = .uninitialized,
    /// Auxiliary views for maintained aggregate rules with projected heads.
    auxiliary: std.ArrayList(aggregate_view.AuxiliaryView) = .empty,
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
            .eval = .init(allocator),
            .facts = .init(allocator),
        };
    }

    pub fn deinit(self: *Jatalog) void {
        for (self.auxiliary.items) |*view| view.deinit(self.allocator);
        self.auxiliary.deinit(self.allocator);
        if (self.closure) |*closure| closure.deinit();
        self.facts.deinit();
        self.eval.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const Jatalog) !Jatalog {
        var result: Jatalog = .{
            .allocator = self.allocator,
            .strings = try self.strings.clone(),
            .eval = undefined,
            .facts = undefined,
        };
        errdefer result.strings.deinit();
        result.eval = try self.eval.clone();
        errdefer result.eval.deinit();
        result.facts = try self.facts.clone();
        errdefer result.facts.deinit();
        if (self.closure) |*closure| result.closure = try closure.clone();
        errdefer if (result.closure) |*closure| closure.deinit();
        result.materialization = self.materialization;
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
        var removed: relation_store.RelationStore = .init(committed.allocator);
        defer removed.deinit();
        var index = committed.facts.len();
        while (index > 0) {
            index -= 1;
            const fact = committed.facts.factAt(index);
            if (try staging.facts.contains(fact)) continue;
            try relation_store.copyFactInto(committed.allocator, &removed, fact, false);
            committed.facts.removeAt(index);
        }
        // Retraction resolves its goals before deciding, so unlike a batch it
        // knows exactly how many base facts it changes: the estimate the
        // model decides on and the count it later measures are the same.
        const delta = removed.len();
        const maintain = materialization.canMaintain(
            &committed,
        ) and
            committed.eval.cost.decide(delta) == .maintain;
        if (maintain and delta > 0) {
            const span = committed.eval.cost.begin();
            try maintenance.propagateDeletions(&committed, &removed);
            var touched: relation_store.RelationStore = .init(committed.allocator);
            defer touched.deinit();
            for (0..removed.len()) |position|
                try relation_store.copyFactInto(committed.allocator, &touched, removed.factAt(position), false);
            if (touched.len() > 0) try aggregate_view.maintainAggregates(&committed, &touched);
            committed.eval.cost.noteMaintenance(delta, span);
        } else {
            for (0..removed.len()) |position| {
                const fact = removed.factAt(position);
                try materialization.markBaseChanged(&committed, .{ .name = fact.predicate, .arity = fact.terms.len });
            }
        }
        try materialization.verifyShadow(
            &committed,
        );
        self.commit(&committed);
    }

    pub fn addFact(self: *Jatalog, predicate: []const u8, terms: []const input.Term) !void {
        var staging = try self.clone();
        defer staging.deinit();
        const expression = try compile.compileRelation(&staging, predicate, terms, false);
        defer syntax.freeExpr(staging.allocator, expression);
        try staging.addFactExpr(expression);
        self.commit(&staging);
    }

    pub fn addRule(self: *Jatalog, head: input.Goal, body: []const input.Goal) !void {
        var staging = try self.clone();
        defer staging.deinit();
        const compiled_head = switch (head) {
            .relation => |relation| try compile.compileRelation(&staging, relation.predicate, relation.terms, false),
            else => return Error.InvalidRule,
        };
        var head_owned = true;
        defer if (head_owned) syntax.freeExpr(staging.allocator, compiled_head);
        const compiled_body = try compile.compileGoals(&staging, body);
        var body_owned = true;
        defer {
            if (body_owned) for (compiled_body) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled_body);
        }
        try staging.addRuleClauses(compiled_head, compiled_body);
        head_owned = false;
        body_owned = false;
        self.commit(&staging);
    }

    pub fn query(self: *Jatalog, goals: []const input.Goal) !QueryResult {
        try materialization.ensureMaterialized(
            self,
        );
        var staging = try self.clone();
        defer staging.deinit();
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        return staging.queryClauses(compiled);
    }

    pub fn retract(self: *Jatalog, goals: []const input.Goal) !bool {
        try materialization.ensureMaterialized(
            self,
        );
        var staging = try self.clone();
        defer staging.deinit();
        const compiled = try compile.compileGoals(&staging, goals);
        defer {
            for (compiled) |clause| syntax.freeClauseTree(staging.allocator, clause);
            staging.allocator.free(compiled);
        }
        const changed = try staging.deleteClauses(compiled);
        if (changed) try self.commitRetraction(&staging);
        return changed;
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
        var staging = try self.clone();
        defer staging.deinit();
        const changed = try staging.applyChangesCompiled(insertions, deletions);
        try materialization.verifyShadow(
            &staging,
        );
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
        try materialization.ensureMaterialized(
            &staging,
        );
        try materialization.verifyShadow(
            &staging,
        );
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
        aggregate_view.dropAuxiliaryViews(
            &staging,
        );
        staging.materialization = .uninitialized;
        try materialization.ensureMaterialized(
            &staging,
        );
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

    /// Selects how updates bring the closure up to date. The default is
    /// `.automatic`; pin `.incremental` or `.recompute` when a caller needs
    /// one specific path regardless of cost.
    pub fn setMaintenancePolicy(self: *Jatalog, policy: MaintenancePolicy) void {
        self.eval.cost.policy = policy;
    }

    fn applyChangesCompiled(
        self: *Jatalog,
        insertions: []const input.Relation,
        deletions: []const input.Relation,
    ) !bool {
        // Both phases follow the one decision. The batch size is only an
        // estimate of the work ahead; what it actually changed is measured
        // afterwards.
        const maintain = materialization.canMaintain(
            self,
        ) and
            self.eval.cost.decide(insertions.len + deletions.len) == .maintain;
        const span = self.eval.cost.begin();

        // Facts the aggregate phase must reconsider: every fact this batch
        // took out of the closure, and every fact it derived into it.
        var touched: relation_store.RelationStore = .init(self.allocator);
        defer touched.deinit();
        const deleted = try self.applyDeletions(deletions, maintain, &touched);
        const inserted = try self.applyInsertions(insertions, maintain, &touched);
        if (touched.len() > 0) try aggregate_view.maintainAggregates(self, &touched);

        const realized = deleted + inserted;
        if (maintain) self.eval.cost.noteMaintenance(realized, span);
        return realized > 0;
    }

    /// Removes this batch's deletions from the base facts. When maintaining,
    /// they take the delete-and-rederive path and everything that leaves the
    /// closure is added to `touched`; otherwise each removal dirties the
    /// strata that read its predicate. Returns how many base facts were
    /// really removed, which is fewer than `deletions.len()` whenever the
    /// batch names a fact the database does not hold.
    fn applyDeletions(
        self: *Jatalog,
        deletions: []const input.Relation,
        maintain: bool,
        touched: *relation_store.RelationStore,
    ) !usize {
        var removed: relation_store.RelationStore = .init(self.allocator);
        defer removed.deinit();
        var count: usize = 0;
        for (deletions) |relation| {
            const expression = try compile.compileRelation(self, relation.predicate, relation.terms, false);
            defer syntax.freeExpr(self.allocator, expression);
            if (!expression.isGround()) return error.InvalidFact;
            const terms = try self.allocator.alloc(syntax.ValueId, expression.terms.len);
            defer self.allocator.free(terms);
            for (expression.terms, terms) |term, *id| id.* = try self.eval.termToValue(term, null);
            const fact: relation_store.Fact = .{ .predicate = expression.predicate, .terms = terms };
            if (!try self.facts.removeFact(fact)) continue;
            count += 1;
            if (maintain) {
                try relation_store.copyFactInto(self.allocator, &removed, fact, false);
            } else {
                try materialization.markBaseChanged(self, .{ .name = fact.predicate, .arity = terms.len });
            }
        }
        // `removed` is only populated while maintaining. Delete-and-rederive
        // rewrites it in place into the set of facts that actually left the
        // closure: over-deleted consequences are added and rederived ones
        // removed, so it must be read for `touched` only afterwards.
        if (removed.len() > 0) {
            try maintenance.propagateDeletions(self, &removed);
            for (0..removed.len()) |index|
                try relation_store.copyFactInto(self.allocator, touched, removed.factAt(index), false);
        }
        return count;
    }

    /// Adds this batch's insertions to the base facts. When maintaining, each
    /// new fact also joins the clean closure and the batch propagates through
    /// the positive strata, with everything derived added to `touched`;
    /// otherwise each insertion dirties the strata that read its predicate.
    /// Returns how many base facts were really added, which is fewer than
    /// `insertions.len()` whenever the batch re-inserts a fact the database
    /// already holds.
    fn applyInsertions(
        self: *Jatalog,
        insertions: []const input.Relation,
        maintain: bool,
        touched: *relation_store.RelationStore,
    ) !usize {
        // Maintaining the deletions cannot have taken the closure out from
        // under this phase: a delete-and-rederive fallback repairs the
        // closure through `ensureMaterialized` rather than leaving it dirty.
        std.debug.assert(!maintain or
            (self.closure != null and self.materialization == .clean));
        const batch_start = if (maintain) self.closure.?.len() else 0;
        var count: usize = 0;
        for (insertions) |relation| {
            const expression = try compile.compileRelation(self, relation.predicate, relation.terms, false);
            defer syntax.freeExpr(self.allocator, expression);
            if (try self.applyInsertion(expression, maintain)) count += 1;
        }
        if (!maintain or self.closure.?.len() == batch_start) return count;
        try maintenance.propagateInsertions(self, batch_start);
        if (self.materialization == .clean) {
            for (batch_start..self.closure.?.len()) |index|
                try relation_store.copyFactInto(self.allocator, touched, self.closure.?.factAt(index), false);
        }
        return count;
    }

    pub fn addFactExpr(self: *Jatalog, value: syntax.Expr) !void {
        _ = try self.applyInsertion(value, false);
    }

    /// Inserts one ground base fact. When `propagate` is set the fact also
    /// joins the clean closure for incremental propagation; otherwise the
    /// first dependent stratum is marked dirty for the lazy rebuild path.
    fn applyInsertion(self: *Jatalog, value: syntax.Expr, propagate: bool) !bool {
        if (!value.isGround() or value.negated) return error.InvalidFact;
        const terms = try self.allocator.alloc(syntax.ValueId, value.terms.len);
        var terms_owned = true;
        errdefer if (terms_owned) self.allocator.free(terms);
        for (value.terms, terms) |term, *id| id.* = try self.eval.termToValue(term, null);
        const fact: relation_store.Fact = .{ .predicate = value.predicate, .terms = terms };
        const key: relation_store.PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
        const added = try self.facts.insert(fact, false);
        terms_owned = false;
        if (!added) return false;
        if (propagate) {
            try relation_store.copyFactInto(self.allocator, &self.closure.?, fact, false);
        } else {
            try materialization.markBaseChanged(self, key);
        }
        return true;
    }

    /// Adds a rule whose body may contain aggregate clauses. On success the
    /// database owns `head` and every clause in `body`; on failure the caller
    /// retains ownership. The body slice itself is only borrowed.
    pub fn addRuleClauses(self: *Jatalog, head: syntax.Expr, body: []const syntax.Clause) !void {
        const seed_argument = try validation.validateRule(self, head, body);
        const owned_body = try validation.orderClauses(self, body);
        errdefer self.allocator.free(owned_body);
        const id = self.eval.next_rule_id;
        self.eval.next_rule_id += 1;
        try self.eval.rules.append(self.allocator, .{
            .id = id,
            .head = head,
            .body = owned_body,
            .seed_argument = seed_argument,
        });
        validation.validateRecursiveArithmetic(
            self,
        ) catch |err| {
            _ = self.eval.rules.pop();
            return err;
        };
        validation.validateStratification(
            self,
        ) catch |err| {
            _ = self.eval.rules.pop();
            return err;
        };
        materialization.invalidateAnalysis(
            self,
        );
        if (self.closure != null) {
            // Lazy rebuild policy for rule additions: invalidate from the new
            // head's stratum now, rebuild at the next evaluation.
            const analysis = try self.eval.ensureAnalysis();
            materialization.markDirty(self, analysis.strata.get(syntax.predicateKey(head)) orelse 0);
        }
    }

    /// Evaluates relational, built-in, negated, or aggregate goals. Goals and
    /// their structural terms remain caller-owned and may be freed immediately
    /// after this function returns.
    pub fn queryClauses(self: *Jatalog, goals: []const syntax.Clause) !QueryResult {
        var internal_answers = try self.evaluateClauses(goals);
        defer {
            for (internal_answers.items) |*answer| answer.deinit(self.allocator);
            internal_answers.deinit(self.allocator);
        }
        return self.copyQueryResult(internal_answers.items);
    }

    fn evaluateClauses(self: *Jatalog, goals: []const syntax.Clause) !std.ArrayList(syntax.Binding) {
        if (goals.len == 0) return error.InvalidQuery;
        var outer_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
        defer outer_variables.deinit(self.allocator);
        for (goals) |clause| try syntax.collectClauseSurfaceVariables(self.allocator, clause, &outer_variables);
        var bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
        defer bound.deinit(self.allocator);
        const ordered = try validation.orderClauses(self, goals);
        defer self.allocator.free(ordered);
        for (ordered) |clause|
            try validation.validateClause(self, clause, &bound, &outer_variables, Error.InvalidQuery);

        try materialization.ensureMaterialized(
            self,
        );
        const values_before = self.eval.values.values.items.len;
        for (goals) |clause| try compile.internGroundStructuresInClause(self, clause);
        if (self.eval.values.values.items.len != values_before) {
            // Novel ground query structures must join the seed set of
            // admissible structural recursion, so derive their consequences
            // on this database's own (discardable) closure.
            if (self.closure) |*closure| {
                if ((try self.eval.ensureAnalysis()).has_seed_rules)
                    try self.eval.expandFrom(closure, 0);
            }
        }

        var internal_answers: std.ArrayList(syntax.Binding) = .empty;
        errdefer {
            for (internal_answers.items) |*answer| answer.deinit(self.allocator);
            internal_answers.deinit(self.allocator);
        }
        var initial: syntax.Binding = .{};
        defer initial.deinit(self.allocator);
        try self.eval.matchClauses(ordered, materialization.closureStore(
            self,
        ), 0, &initial, &internal_answers, null);
        return internal_answers;
    }

    fn copyQueryResult(self: *const Jatalog, bindings: []const syntax.Binding) !QueryResult {
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
                    results.freeResultNode(self.allocator, owned_value);
                    return err;
                };
            }
            try result.answers.append(self.allocator, answer);
        }
        return result;
    }

    fn copyResultNode(self: *const Jatalog, value: syntax.ValueId) !*results.ResultNode {
        const node = try self.allocator.create(results.ResultNode);
        errdefer self.allocator.destroy(node);
        node.* = switch (self.eval.values.get(value)) {
            .scalar => |scalar_id| switch (self.eval.scalars.get(scalar_id)) {
                .atom => |atom| .{ .atom = try self.allocator.dupe(u8, atom) },
                .integer => |integer| .{ .integer = integer },
                .float => |float| .{ .float = float },
            },
            .nil => .nil,
            .cons => |value_pair| blk: {
                const pair = try self.allocator.create(results.ResultCons);
                errdefer self.allocator.destroy(pair);
                pair.head = try self.copyResultNode(value_pair.head);
                errdefer results.freeResultNode(self.allocator, pair.head);
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
        for (self.eval.rules.items) |rule| {
            if (syntax.maintainableAggregateIndex(rule) == null) continue;
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
            .stratum_expansions = self.eval.expansions,
            .rebuild_fallbacks = self.rebuild_fallbacks,
            .maintained_groups = self.maintained_groups,
            .policy = self.eval.cost.policy,
            .maintain_choices = self.eval.cost.maintain_choices,
            .recompute_choices = self.eval.cost.recompute_choices,
            .rebuild_work = self.eval.cost.rebuild_work,
            .maintenance_work_per_fact = self.eval.cost.maintenance_work_per_fact,
            .self_maintainable_views = self_maintainable,
            .projected_views = projected,
            .auxiliary_tuples = auxiliary_tuples,
        };
    }

    pub fn execute(self: *Jatalog, source: []const u8) !ExecutionResult {
        var statement_parser: parser.Parser = .{ .jatalog = self, .source = source };
        return statement_parser.executeAll();
    }

    // Structural recursion is seeded from interned values during expansion, so
    // ground structures supplied by a query must join that seed set first.

    pub fn deleteClauses(self: *Jatalog, goals: []const syntax.Clause) !bool {
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
                for (try self.eval.lookupCandidates(&self.facts, goal, answer)) |candidate| {
                    if (seen.contains(candidate)) continue;
                    var matched = try answer.clone(self.allocator);
                    defer matched.deinit(self.allocator);
                    if (try self.eval.unify(self.facts.factAt(candidate), goal, &matched)) {
                        try seen.put(self.allocator, candidate, {});
                        try to_remove.append(self.allocator, candidate);
                    }
                }
            }
        }
        std.mem.sort(usize, to_remove.items, {}, std.sort.desc(usize));
        for (to_remove.items) |index| {
            const fact = self.facts.factAt(index);
            try materialization.markBaseChanged(self, .{ .name = fact.predicate, .arity = fact.terms.len });
            self.facts.removeAt(index);
        }
        return to_remove.items.len > 0;
    }

    fn writeValue(self: *const Jatalog, writer: *std.Io.Writer, value: syntax.ValueId) !void {
        switch (self.eval.values.get(value)) {
            .scalar => |scalar_id| try self.eval.scalars.write(writer, scalar_id),
            .nil => try writer.writeAll("[]"),
            .cons => |pair| if (self.isProperList(value)) {
                try writer.writeByte('[');
                var current = value;
                var first = true;
                while (true) {
                    switch (self.eval.values.get(current)) {
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

    fn isProperList(self: *const Jatalog, value: syntax.ValueId) bool {
        var current = value;
        while (true) switch (self.eval.values.get(current)) {
            .nil => return true,
            .cons => |pair| current = pair.tail,
            else => return false,
        };
    }
};

/// One statement's transaction.
///
/// A source program is a sequence of statements, each of which either commits
/// completely or leaves the database exactly as it was, so a failure part-way
/// through a program keeps every earlier statement and none of this one. A
/// front end executes a statement by beginning one of these, running the
/// statement against `target`, and committing the result.
///
/// This is deliberately the whole database interface a front end gets for
/// that. The primitives it is built from — cloning the database, replacing it
/// with a staged copy, replaying a retraction's removals through the deletion
/// engine — stay private, because committing a foreign staging database is
/// not an operation a caller should be able to name.
pub const Statement = struct {
    /// What the next statement will turn out to be, as far as scanning for
    /// its terminator can tell. Only whether it evaluates matters here.
    pub const Kind = enum { assertion, query, retraction, end };

    database: *Jatalog,
    staging: Jatalog,

    /// Opens a transaction for one statement. A statement that evaluates needs
    /// the committed closure materialized first, so that the staged copy
    /// shares its value identifiers and evaluation never expands.
    pub fn begin(database: *Jatalog, kind: Kind) !Statement {
        switch (kind) {
            .query, .retraction => try materialization.ensureMaterialized(database),
            .assertion, .end => {},
        }
        return .{ .database = database, .staging = try database.clone() };
    }

    /// The database to execute the statement against. Everything it interns —
    /// including values a query mentions but the database does not hold — stays
    /// here unless the statement commits.
    pub fn target(self: *Statement) *Jatalog {
        return &self.staging;
    }

    /// Commits according to what the statement turned out to be. A query
    /// changes nothing and keeps its query-local interning out of the
    /// database; an assertion installs the staged copy; a retraction that
    /// removed facts replays those removals so they take the incremental
    /// deletion path rather than committing the staged copy wholesale.
    pub fn commit(self: *Statement, result: ExecutionResult) !void {
        switch (result) {
            .query => {},
            .none => self.database.commit(&self.staging),
            .changed => |changed| if (changed) try self.database.commitRetraction(&self.staging),
        }
    }

    pub fn deinit(self: *Statement) void {
        self.staging.deinit();
        self.* = undefined;
    }
};

test "string table maps strings to stable ids and back" {
    var table: compile.StringTable = .init(std.testing.allocator);
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

test {
    _ = relation_store;
    _ = cost_model;
    _ = syntax;
    _ = results;
    _ = evaluator;
    _ = maintenance;
    _ = aggregate_view;
    _ = test_support;
    _ = parser;
    _ = validation;
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
    try std.testing.expectEqual(@as(usize, 0), db.eval.expansions);

    try test_support.expectAnswerCount(&db, "path(a, X)?", 3);
    const after_first = db.eval.expansions;
    try std.testing.expect(after_first > 0);
    try std.testing.expect(db.materialization == .clean);

    for (0..3) |_| try test_support.expectAnswerCount(&db, "path(a, X)?", 3);
    var typed = try db.query(&.{input.relation("path", &.{
        input.atom("a"),
        input.variable("target"),
    })});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 3), typed.answers.items.len);
    try std.testing.expectEqual(after_first, db.eval.expansions);
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
    try test_support.expectAnswerCount(&db, "numchildren(alice, 1)?", 1);
    try std.testing.expect(db.materialization == .clean);

    var staging = try db.clone();
    defer staging.deinit();
    var reference = try staging.facts.clone();
    defer reference.deinit();
    try staging.eval.expandNaive(&reference);
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
    try test_support.expectAnswerCount(&db, "path(a, c)?", 1);

    // A base insertion marks the closure dirty and the next query repairs it.
    var inserted = try db.execute("edge(c, d).");
    inserted.deinit();
    try std.testing.expect(db.materialization == .dirty_from_stratum);
    try test_support.expectAnswerCount(&db, "path(a, d)?", 1);
    try std.testing.expect(db.materialization == .clean);

    // Retraction removes derived consequences through the dirty rebuild.
    var retracted = try db.execute("edge(a, b)~");
    retracted.deinit();
    try test_support.expectAnswerCount(&db, "path(a, c)?", 0);
    try test_support.expectAnswerCount(&db, "path(b, d)?", 1);

    // Typed updates take the same paths.
    try db.addFact("edge", &.{ input.atom("d"), input.atom("e") });
    try test_support.expectAnswerCount(&db, "path(b, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try test_support.expectAnswerCount(&db, "path(b, e)?", 0);

    // Rule addition invalidates from the new head's stratum.
    var extended = try db.execute("reach(X) :- path(b, X).");
    extended.deinit();
    try std.testing.expect(db.materialization == .dirty_from_stratum);
    try test_support.expectAnswerCount(&db, "reach(d)?", 1);
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
    try test_support.expectAnswerCount(&db, "note(a)?", 1);
    const full_build = db.eval.expansions;
    try std.testing.expectEqual(@as(usize, 2), full_build);

    // Only the negation stratum reads flag, so its update rebuilds one level.
    var flagged = try db.execute("flag(c).");
    flagged.deinit();
    try test_support.expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 1, db.eval.expansions);

    // An edge update dirties the recursive stratum and rebuilds both levels.
    var edged = try db.execute("edge(c, d).");
    edged.deinit();
    try test_support.expectAnswerCount(&db, "note(X)?", 1);
    try std.testing.expectEqual(full_build + 3, db.eval.expansions);
}

test "a database without rules allocates no derived machinery" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    try test_support.expectAnswerCount(&db, "kept(1)?", 1);
    var typed = try db.query(&.{input.relation("kept", &.{input.variable("n")})});
    defer typed.deinit();
    try std.testing.expectEqual(@as(usize, 1), typed.answers.items.len);
    try std.testing.expect(db.closure == null);
    try std.testing.expect(db.materialization == .uninitialized);
    try std.testing.expect(db.eval.analysis == null);
    try std.testing.expectEqual(@as(usize, 0), db.eval.expansions);
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
    try test_support.expectClosureMatchesRebuild(&db);
    try test_support.expectAnswerCount(&db, "path(a, c)?", 1);

    // The single-statement entry points keep working alongside the batch
    // API. Pattern retraction is not a subset of it: it deletes every base
    // fact matching a goal, which exact-fact batch deletion cannot express.
    try db.addFact("edge", &.{ input.atom("c"), input.atom("d") });
    try test_support.expectAnswerCount(&db, "path(a, d)?", 1);
    var executed = try db.execute("edge(d, e).");
    executed.deinit();
    try test_support.expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(try db.retract(&.{
        input.relation("edge", &.{ input.atom("d"), input.atom("e") }),
    }));
    try test_support.expectAnswerCount(&db, "path(a, e)?", 0);

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
    try test_support.expectAnswerCount(&db, "path(a, e)?", 1);
    try std.testing.expect(db.maintenanceStats().propagated_facts > before_edge.propagated_facts);

    // An inserted member recomputes exactly the affected aggregate group.
    const before_member = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{
        input.fact("member", &.{ input.atom("g"), input.atom("m2") }),
    }, &.{}));
    var collected = try db.execute("collected(g, S)?");
    try test_support.expectBindingValue(&collected.query.answers.items[0], "S", "[m1, m2]");
    collected.deinit();
    try std.testing.expect(db.maintenanceStats().maintained_groups > before_member.maintained_groups);
    try test_support.expectClosureMatchesRebuild(&db);

    const before_delete = db.maintenanceStats();
    try std.testing.expect(try db.applyChanges(&.{}, &.{
        input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
    }));
    try test_support.expectAnswerCount(&db, "path(a, c)?", 0);
    try std.testing.expect(db.maintenanceStats().removed_facts > before_delete.removed_facts);
    try test_support.expectClosureMatchesRebuild(&db);

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
    );
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
    try test_support.expectBindingValue(&result.query.answers.items[0], "X", "cons(a, b)");
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
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), db.eval.rules.items.len);
    try std.testing.expect(db.eval.rules.items[0].body[0] == .relational);
    const aggregate = db.eval.rules.items[0].body[1].aggregate;
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
    const body = db.eval.rules.items[0].body;
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
    try std.testing.expectEqual(@as(usize, 1), db.eval.rules.items.len);
}

test "nested aggregates are represented directly and validate recursively" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute(
        \\seed(k).
        \\grouped(S) :- seed(k), setof(T, (group(G), setof(Y, parent(G, Y), T)), S).
    );
    defer result.deinit();
    const outer = db.eval.rules.items[0].body[1].aggregate;
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
    var levels = try db.eval.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const reachable: relation_store.PredicateKey = .{ .name = db.strings.get("reachable").?, .arity = 2 };
    const all_reachable: relation_store.PredicateKey = .{ .name = db.strings.get("all_reachable").?, .arity = 1 };
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
    var levels = try db.eval.computeStrata();
    defer levels.deinit(std.testing.allocator);
    const allowed: relation_store.PredicateKey = .{ .name = db.strings.get("allowed").?, .arity = 1 };
    const summary: relation_store.PredicateKey = .{ .name = db.strings.get("summary").?, .arity = 1 };
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
            try test_support.expectBindingValue(answer, "S", "[bob, carol]");
        } else if (std.mem.eql(u8, person, "bob")) {
            try test_support.expectBindingValue(answer, "S", "[]");
        } else return error.UnexpectedPerson;
    }
}

test "setof evaluates directly in queries" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    var result = try db.execute("item(c). item(a). setof(X, item(X), S)?");
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
    );
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
    );
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
    );
    result.deinit();
    result = try db.execute("items(S)?");
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

    const value_count_before_typed_query = db.eval.values.values.items.len;
    var query_result = try db.query(&.{input.relation("sum", &.{
        input.list(&.{ input.integer(4), input.integer(5) }),
        input.variable("total"),
    })});
    defer query_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), query_result.answers.items.len);
    try std.testing.expectEqual(@as(i64, 9), try query_result.answers.items[0].getInteger("total"));
    try std.testing.expectEqual(value_count_before_typed_query, db.eval.values.values.items.len);

    var open_result = try db.execute("sum(Input, Total)?");
    defer open_result.deinit();
    try std.testing.expectEqual(@as(usize, 1), open_result.query.answers.items.len);
    try test_support.expectBindingValue(&open_result.query.answers.items[0], "Input", "[]");
    try std.testing.expectEqual(@as(i64, 0), try open_result.query.answers.items[0].getInteger("Total"));

    var structural_result = try db.execute("Value = [a, b]?");
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
    );
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 1), result.query.answers.items.len);
    try test_support.expectBindingValue(&result.query.answers.items[0], "Value", "[a]");
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
    )});
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
    var result = try db.query(&.{input.setof(input.list(&.{x}), &body, output)});
    defer result.deinit();
    try test_support.expectBindingValue(&result.answers.items[0], "output", "[[a], [b]]");
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
    try test_support.expectBindingValue(&result.query.answers.items[0], "S", "[]");
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
    try test_support.expectBindingValue(
        &result.query.answers.items[0],
        "Values",
        "[-9223372036854775808, 0, 1, 9223372036854775807]",
    );

    try std.testing.expectError(Error.NumericOverflow, db.execute("number(9223372036854775808)."));
    try std.testing.expectError(Error.NumericOverflow, db.execute("number(-9223372036854775809)."));
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

    const scalar_count = db.eval.scalars.values.items.len;
    var bound = try db.execute("X = 2.5?");
    const spelled = try (try bound.query.answers.items[0].getValue("X"))
        .formatAlloc(std.testing.allocator);
    defer std.testing.allocator.free(spelled);
    try std.testing.expectEqualStrings("2.5", spelled);
    bound.deinit();
    try std.testing.expectEqual(scalar_count, db.eval.scalars.values.items.len);
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
    try test_support.expectAnswerCount(&db, "4 = 1.5 + 2.5?", 1);
    try test_support.expectAnswerCount(&db, "5 = 1.5 + 2?", 0);
    try test_support.expectAnswerCount(&db, "-2.5 = -1.5 - 1?", 1);
    try test_support.expectAnswerCount(&db, "2.5 = 1 - -1.5?", 1);

    // Gradual underflow keeps exact subnormal results.
    try test_support.expectAnswerCount(
        &db,
        "1.1125369292536007e-308 = 2.2250738585072014e-308 - 1.1125369292536007e-308?",
        1,
    );
    try test_support.expectAnswerCount(&db, "0 = 5e-324 - 5e-324?", 1);

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
    try test_support.expectAnswerCount(&db, "9007199254740993 > 9.007199254740992e15?", 1);
    try test_support.expectAnswerCount(&db, "9007199254740993 = 9.007199254740993e15?", 0);
    try test_support.expectAnswerCount(&db, "9007199254740992 = 9.007199254740992e15?", 1);

    // Both i64 limits against the adjacent representable floats.
    try test_support.expectAnswerCount(&db, "9223372036854775807 < 9.223372036854776e18?", 1);
    try test_support.expectAnswerCount(&db, "-9223372036854775808 = -9.223372036854775808e18?", 1);
    try test_support.expectAnswerCount(&db, "-9223372036854775807 > -9.223372036854776e18?", 1);

    // Adjacent representable floats around 1.
    try test_support.expectAnswerCount(&db, "1.0000000000000002 > 1?", 1);
    try test_support.expectAnswerCount(&db, "0.9999999999999999 < 1?", 1);
    try test_support.expectAnswerCount(&db, "1.0000000000000002 = 1?", 0);

    var ordered = try db.execute(
        \\near(0.9999999999999999). near(1). near(1.0000000000000002).
        \\setof(X, near(X), S)?
    );
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
    );
    defer dedup.deinit();
    try test_support.expectBindingValue(&dedup.query.answers.items[0], "S", "[1, '1', '1.0']");

    try test_support.expectAnswerCount(&db, "nested([1.0, 2.5]). nested([1, 2.5])?", 1);
    try test_support.expectAnswerCount(&db, "pair(cons(0.5, 1.0)). pair(cons(0.5, 1))?", 1);

    var grouped = try db.execute(
        \\kind(g). kind(h). item(g, 0.5). item(g, 1.0). item(g, 1). item(h, 2.5).
        \\grouped(Out) :- kind(g), setof([G, S], (kind(G), setof(V, item(G, V), S)), Out).
        \\grouped(Out)?
    );
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
    try test_support.expectAnswerCount(&db, "measure(a, 2.5)?", 1);
    try test_support.expectAnswerCount(&db, "measure(b, 1)?", 1);
    try test_support.expectAnswerCount(&db, "measure(c, 0)?", 1);
    try test_support.expectAnswerCount(&db, "items([0.5, 2])?", 1);

    // Typed retraction matches a fact added from source, and vice versa.
    var added = try db.execute("measure(d, 3.5).");
    added.deinit();
    try std.testing.expect(try db.retract(&.{
        input.relation("measure", &.{ input.atom("d"), input.float(3.5) }),
    }));
    try test_support.expectAnswerCount(&db, "measure(d, X)?", 0);
}

test "non-finite typed floats fail compilation transactionally" {
    var db: Jatalog = .init(std.testing.allocator);
    defer db.deinit();
    try db.addFact("kept", &.{input.integer(1)});
    const scalar_count = db.eval.scalars.values.items.len;
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

    try std.testing.expectEqual(scalar_count, db.eval.scalars.values.items.len);
    try std.testing.expectEqual(fact_count, db.facts.len());
    try std.testing.expectEqual(@as(usize, 0), db.eval.rules.items.len);
    try test_support.expectAnswerCount(&db, "kept(1)?", 1);
    try test_support.expectAnswerCount(&db, "bad(X)?", 0);
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
    result = try db.query(&.{input.relation("tail", &.{input.variable("result")})});
    try test_support.expectBindingValue(&result.answers.items[0], "result", "[2]");
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
