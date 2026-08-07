//! What a Datalog database *is*: the interned program, the facts, the derived
//! closure, and the primitive operations that read and replace them.
//!
//! Everything above this file operates on one of these. Keeping the state here
//! and the layers that act on it above is what makes the engine's imports a
//! DAG: compilation, evaluation, materialization and maintenance all point
//! down at this module, and none of them is pointed back at.

const std = @import("std");
const auxiliary_view = @import("auxiliary_view.zig");
const cost_model = @import("cost_model.zig");
const evaluator = @import("evaluator.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const string_table = @import("string_table.zig");
const syntax = @import("syntax.zig");

/// Whether the derived closure is valid, and from where it is not. This is the
/// pivot the whole maintenance layer turns on, so it lives on the database
/// rather than in the module that repairs it: an update sets it, and every
/// incremental path reads it before deciding whether it may start.
pub const Materialization = union(enum) {
    uninitialized,
    clean,
    dirty_from_stratum: usize,
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
    policy: cost_model.MaintenancePolicy,
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

/// The engine's state, and the operations that need nothing but it.
///
/// This is not the type an embedder holds — that is `Jatalog`, which owns one
/// of these and exposes the operations built on top of it. Every layer between
/// the two takes a `Database`.
pub const Database = struct {
    allocator: std.mem.Allocator,
    strings: string_table.StringTable,
    /// The program: interned values, rules, their analysis, and the
    /// machinery that evaluates them against a fact store.
    eval: evaluator.Evaluator,
    facts: relation_store.RelationStore,
    /// Persistent derived closure: the base facts plus every derived fact,
    /// exposed to evaluation as one unified read view. Null until the first
    /// evaluation on a database with rules.
    closure: ?relation_store.RelationStore = null,
    materialization: Materialization = .uninitialized,
    /// Auxiliary views for maintained aggregate rules with projected heads.
    auxiliary: std.ArrayList(auxiliary_view.AuxiliaryView) = .empty,
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

    pub fn init(allocator: std.mem.Allocator) Database {
        return .{
            .allocator = allocator,
            .strings = .init(allocator),
            .eval = .init(allocator),
            .facts = .init(allocator),
        };
    }

    pub fn deinit(self: *Database) void {
        for (self.auxiliary.items) |*view| view.deinit(self.allocator);
        self.auxiliary.deinit(self.allocator);
        if (self.closure) |*closure| closure.deinit();
        self.facts.deinit();
        self.eval.deinit();
        self.strings.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const Database) !Database {
        var result: Database = .{
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

    /// Installs a staged copy in place of this database, leaving the previous
    /// contents in `staging` for the caller's `deinit` to release. Every
    /// operation that can fail stages its work on a clone and ends here, which
    /// is what makes a failure part-way through leave the database untouched.
    pub fn commit(self: *Database, staging: *Database) void {
        const previous = self.*;
        self.* = staging.*;
        staging.* = previous;
    }

    /// Inserts one ground base fact with set semantics, returning it as the
    /// store now holds it, or null when the store already held it.
    ///
    /// What the new fact means for the derived closure is not decided here.
    /// This module holds the state; whether the fact goes on to join a clean
    /// closure or instead dirties the strata that read it is the update path's
    /// choice, and it makes it from what this returns.
    ///
    /// The returned terms are borrowed from `facts`. Further insertions can
    /// move the entry holding them but not the terms themselves; a removal
    /// frees them.
    pub fn applyInsertion(self: *Database, value: syntax.Expr) !?relation_store.Fact {
        if (!value.isGround() or value.negated) return error.InvalidFact;
        const terms = try self.allocator.alloc(syntax.ValueId, value.terms.len);
        var terms_owned = true;
        errdefer if (terms_owned) self.allocator.free(terms);
        for (value.terms, terms) |term, *id| id.* = try self.eval.termToValue(term, null);
        const fact: relation_store.Fact = .{ .predicate = value.predicate, .terms = terms };
        const added = try self.facts.insert(fact, false);
        terms_owned = false;
        if (!added) return null;
        return self.facts.factAt(self.facts.len() - 1);
    }

    pub fn copyQueryResult(self: *const Database, bindings: []const syntax.Binding) !results.QueryResult {
        var result: results.QueryResult = .{ .allocator = self.allocator };
        errdefer result.deinit();
        for (bindings) |binding| {
            var answer: results.Answer = .{ .allocator = self.allocator };
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

    fn copyResultNode(self: *const Database, value: syntax.ValueId) !*results.ResultNode {
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
    pub fn maintenanceStats(self: *const Database) MaintenanceStats {
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

    /// Whether the closure is in a state incremental maintenance can start
    /// from. A dirty closure has to be repaired regardless of cost, so the
    /// cost model is consulted only when this holds.
    pub fn canMaintain(self: *const Database) bool {
        return self.closure != null and self.materialization == .clean;
    }

    pub fn markDirty(self: *Database, level: usize) void {
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
    pub fn markBaseChanged(self: *Database, key: relation_store.PredicateKey) !void {
        if (self.closure == null) return;
        const analysis = try self.eval.ensureAnalysis();
        self.markDirty(analysis.first_dependent.get(key) orelse analysis.max_level + 1);
    }

    pub fn closureStore(self: *Database) *relation_store.RelationStore {
        if (self.closure) |*closure| return closure;
        return &self.facts;
    }
};
