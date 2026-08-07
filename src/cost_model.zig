//! The maintenance cost model: chooses between maintaining the derived
//! closure incrementally and recomputing the affected strata, and learns
//! what each costs from the database's own history.
//!
//! This module knows nothing about Datalog. It consumes a unit of work —
//! candidate facts examined, reported by the evaluator — and answers a
//! yes-or-no question about the next update, which keeps the policy
//! separable from the engine that carries it out.

const std = @import("std");

/// Chooses between maintaining the closure incrementally and recomputing
/// the affected strata. Both paths produce the same database, so this is
/// purely a cost decision.
pub const MaintenancePolicy = enum {
    /// Estimate both costs from observed work and take the cheaper path.
    automatic,
    /// Always maintain incrementally when the closure is clean.
    incremental,
    /// Always mark the affected strata dirty and recompute them.
    recompute,
};

/// Folds a new observation into a running estimate, halving the weight of
/// history each time so the model tracks a changing workload within a few
/// updates while still damping a single unusual batch.
fn blendWork(current: ?u64, observed: u64) u64 {
    const previous = current orelse return observed;
    return (previous +| observed) / 2;
}

/// Chooses between maintaining and recomputing, and learns what each costs
/// from this database's own history.
///
/// Work is counted in candidate facts examined, which makes the decision
/// deterministic and independent of the machine. Every candidate examined is
/// attributed to exactly one of the two estimates: a rebuild that happens
/// inside a maintenance attempt — the fallback an update takes when it
/// reaches negation or an unmaintainable aggregate — is charged to the
/// rebuild estimate and excluded from the maintenance one, so a single event
/// cannot move both estimates in opposite directions.
///
/// Estimates are fed the number of base facts an update *realized*, not the
/// number of relations its caller named, because a batch that re-inserts
/// facts the database already holds does proportionally less work than its
/// size suggests.
pub const CostModel = struct {
    /// How often the model takes the path it currently believes is more
    /// expensive, so that both estimates keep being refreshed.
    const explore_interval: usize = 16;

    pub const Decision = enum { maintain, recompute };

    /// The work counter at the start of an attempt, and how much of it had
    /// already been charged to the rebuild estimate.
    pub const Span = struct { work: u64, rebuilt: u64 };

    policy: MaintenancePolicy = .automatic,
    /// Monotonic count of candidate facts examined, this model's unit.
    work: u64 = 0,
    /// The part of `work` already attributed to the rebuild estimate.
    rebuilt_work: u64 = 0,
    /// Observed cost of a stratum rebuild, and of maintaining one changed
    /// base fact. Null until the database has observed one of each.
    rebuild_work: ?u64 = null,
    maintenance_work_per_fact: ?u64 = null,
    maintain_choices: usize = 0,
    recompute_choices: usize = 0,
    decisions: usize = 0,

    /// Counts one lookup's candidates. The extra unit prices the lookup
    /// itself, so that a lookup returning nothing is not free.
    pub fn noteCandidates(self: *CostModel, count: usize) void {
        self.work +|= count + 1;
    }

    pub fn begin(self: *const CostModel) Span {
        return .{ .work = self.work, .rebuilt = self.rebuilt_work };
    }

    /// Work observed during `span` that no nested rebuild already claimed.
    /// A rebuild can only claim work counted inside the span that encloses
    /// it, so the difference cannot go negative; it saturates rather than
    /// trapping in case a future caller nests spans some other way.
    fn elapsed(self: *const CostModel, span: Span) u64 {
        return (self.work - span.work) -| (self.rebuilt_work - span.rebuilt);
    }

    /// Chooses a path for an update expected to change `estimated_facts` base
    /// facts, and records the choice. Callers consult this only when
    /// maintenance is possible at all: a dirty closure must be repaired
    /// regardless of cost, and that repair is not a decision.
    ///
    /// Maintenance cost is unknown until one batch has been maintained, so
    /// the first decision always maintains in order to measure it. Scaling
    /// the per-fact estimate by the batch size overstates large batches,
    /// because maintenance also carries costs that do not grow with the
    /// batch; that bias favours recomputation for large batches, which is the
    /// safe direction.
    pub fn decide(self: *CostModel, estimated_facts: usize) Decision {
        const choice = self.choose(estimated_facts);
        // An update that changes nothing costs nothing either way, so it is
        // not a decision and must not be counted as one.
        if (estimated_facts > 0) switch (choice) {
            .maintain => self.maintain_choices += 1,
            .recompute => self.recompute_choices += 1,
        };
        return choice;
    }

    fn choose(self: *CostModel, estimated_facts: usize) Decision {
        switch (self.policy) {
            .incremental => return .maintain,
            .recompute => return .recompute,
            .automatic => {},
        }
        if (estimated_facts == 0) return .maintain;
        self.decisions += 1;
        // Bootstrap: measure each path once before trusting either estimate.
        if (self.maintenance_work_per_fact == null) return .maintain;
        const rebuild_estimate = self.rebuild_work orelse return .recompute;
        const per_fact = self.maintenance_work_per_fact.?;
        const cheaper: Decision = if (per_fact *| estimated_facts < rebuild_estimate)
            .maintain
        else
            .recompute;
        // Periodically take the rejected path so both estimates stay fresh.
        // Without this only the winner's estimate is ever updated, and an
        // initial full build permanently overstates what a dirty-stratum
        // rebuild would actually cost.
        if (self.decisions % explore_interval == 0)
            return if (cheaper == .maintain) .recompute else .maintain;
        return cheaper;
    }

    /// Records what maintaining `realized_facts` base changes cost.
    pub fn noteMaintenance(self: *CostModel, realized_facts: usize, span: Span) void {
        if (realized_facts == 0) return;
        self.maintenance_work_per_fact = blendWork(
            self.maintenance_work_per_fact,
            self.elapsed(span) / realized_facts,
        );
    }

    /// Records what a stratum rebuild cost, and claims that work so an
    /// enclosing maintenance attempt does not also count it.
    pub fn noteRebuild(self: *CostModel, span: Span) void {
        const observed = self.work - span.work;
        self.rebuilt_work +|= observed;
        self.rebuild_work = blendWork(self.rebuild_work, observed);
    }
};

test "an empty update is not a maintenance decision" {
    // Nothing to do costs nothing either way, so there is no cheaper path to
    // pick and nothing to learn from having picked it. Asserted against the
    // model directly: both callers wrap the decision in a transaction that is
    // discarded when the update changes nothing, so a miscount there would
    // never reach a committed database and no test through the public API can
    // tell the two behaviours apart.
    var model: CostModel = .{};
    try std.testing.expectEqual(CostModel.Decision.maintain, model.decide(0));
    try std.testing.expectEqual(@as(usize, 0), model.maintain_choices);
    try std.testing.expectEqual(@as(usize, 0), model.recompute_choices);
    try std.testing.expectEqual(@as(usize, 0), model.decisions);

    // A real update is a decision and is counted.
    _ = model.decide(1);
    try std.testing.expectEqual(@as(usize, 1), model.maintain_choices);
}
