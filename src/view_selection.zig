//! View selection: what a fold is allowed to read, the plans already folded
//! against it, and answering them. See "View selection" and "Plan cache" in
//! CONTEXT.md.
//!
//! `folding.zig` decides what a question becomes once the relations it reads
//! are gone, and it does that without a database: it reasons about a catalog
//! and a symbol table. Everything that needs the database is here — compiling
//! the caller's descriptors into it, checking them against its schemas,
//! keeping the plans a question folded to so that asking again folds nothing,
//! and running a plan against a copy holding exactly what the catalog admits.
//!
//! A `ViewSelection` never holds the database it selects over. Every operation
//! that needs one takes it, because a catalog's predicate names and constants
//! are identifiers in one database's tables and the pairing is the owner's to
//! keep, not this module's to assume: `Jatalog` owns one of these beside its
//! state and passes that state on every call. Nothing below this module names
//! it, and it sits above `program.zig` rather than beside it so that its tests
//! can build the databases they fold against from source.

const std = @import("std");
const compile = @import("compile.zig");
const database = @import("database.zig");
const fold_ir = @import("fold_ir.zig");
const folding = @import("folding.zig");
const input = @import("input.zig");
const materialization = @import("materialization.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const syntax = @import("syntax.zig");
const transaction = @import("transaction.zig");
const typing = @import("typing.zig");
const validation = @import("validation.zig");
const view_catalog = @import("view_catalog.zig");

/// A view a catalog holds, as `ViewSelection.define` handed it back.
pub const ViewId = fold_ir.ViewId;
/// Whether a folded plan may read a view's stored extension.
pub const Availability = view_catalog.Availability;
/// What a folded plan's answers are worth, relative to the query's.
pub const Guarantee = folding.Guarantee;

/// The views a fold may read, and the plans folded against them.
///
/// The catalog is what a fold reasons about, and the plan cache is what makes
/// asking the same question twice cheap. They live together because each is
/// stamped by the other: a plan is only as current as the catalog generation
/// it was folded under.
pub const ViewSelection = struct {
    /// What a fold of a query is allowed to read. Its identifiers are the
    /// database's the caller pairs it with, which is why it cannot be paired
    /// with any other.
    catalog: view_catalog.Catalog,
    /// Plans already folded against the catalog.
    plans: PlanCache,

    pub fn init(allocator: std.mem.Allocator) ViewSelection {
        return .{
            .catalog = .init(allocator),
            .plans = .{ .allocator = allocator },
        };
    }

    pub fn deinit(self: *ViewSelection) void {
        self.plans.deinit();
        self.catalog.deinit();
        self.* = undefined;
    }

    /// A copy of the views, for a copy of the database they belong to. The
    /// folded plans do not come with it: a cache is not state, and the copy
    /// folds what it is asked for.
    pub fn clone(self: *const ViewSelection) !ViewSelection {
        return .{
            .catalog = try self.catalog.clone(),
            .plans = .{ .allocator = self.plans.allocator },
        };
    }

    /// Compiles a view's definition into `db` and records it.
    ///
    /// The definition is compiled on a staged copy and the copy committed only
    /// once the catalog has taken it, so a definition that is refused leaves
    /// behind nothing it interned. It is admitted exactly as a rule would be —
    /// `InvalidRule` if it is unsafe — and nothing is added to the program.
    pub fn define(
        self: *ViewSelection,
        db: *database.Database,
        head: input.Relation,
        body: []const input.Goal,
        availability: Availability,
    ) !ViewId {
        var staging = try db.clone();
        defer db.release(&staging);
        const compiled = try compileProgramRule(&staging, head, body);
        defer syntax.freeRule(staging.allocator, compiled);
        const id = try self.catalog.define(compiled, availability);
        db.commit(&staging);
        return id;
    }

    /// Records the one rule of `db` that derives `predicate` at `arity` as a
    /// view's definition, with `UndefinedView` when no single rule does.
    ///
    /// The rule generation is recorded with it, because the definition is the
    /// rule's and stops being true when the rules change: a later fold reports
    /// `StaleViewDefinition` rather than reasoning from it.
    pub fn publish(
        self: *ViewSelection,
        db: *const database.Database,
        predicate: []const u8,
        arity: usize,
        availability: Availability,
    ) !ViewId {
        const name = db.strings.get(predicate) orelse return error.UndefinedView;
        var found: ?syntax.Rule = null;
        for (db.eval.rules.items) |rule| {
            if (rule.head.predicate != name or rule.head.terms.len != arity) continue;
            if (found != null) return error.UndefinedView;
            found = rule;
        }
        const definition = found orelse return error.UndefinedView;
        return self.catalog.defineFrom(
            definition,
            availability,
            .{ .materialized_rule = db.eval.next_rule_id },
        );
    }

    /// Withdraws or restores a view's stored extension. The definition stays
    /// known either way.
    pub fn setAvailability(self: *ViewSelection, id: ViewId, availability: Availability) void {
        self.catalog.setAvailability(id, availability);
    }

    /// Declares that a plan may read this base relation of `db` directly.
    pub fn declareBaseAvailable(
        self: *ViewSelection,
        db: *database.Database,
        predicate: []const u8,
        arity: usize,
    ) !void {
        const name = try db.strings.intern(predicate);
        try self.catalog.declareBaseAvailable(.{ .name = name, .arity = arity });
    }

    /// Folds a question against the catalog, or finds the plan an earlier
    /// fold of the same question left in the cache. Answers nothing.
    ///
    /// Two failures are the selection's rather than the question's, and are
    /// reported before anything is compiled: two readable extensions under
    /// one name (`AmbiguousViewName`), and a published definition the rules
    /// have moved on from (`StaleViewDefinition`). The question is then
    /// compiled and type-checked on a staged copy of `db`, which is committed
    /// only when a fresh plan needs what it interned — a cache hit drops it,
    /// so asking the same question twice does not grow the database.
    pub fn fold(
        self: *ViewSelection,
        db: *database.Database,
        goals: []const input.Goal,
        rules: []const input.Rule,
    ) !Fold {
        if (self.catalog.ambiguity() != null) return error.AmbiguousViewName;
        if (self.catalog.staleAt(db.eval.next_rule_id) != null)
            return error.StaleViewDefinition;
        self.plans.refresh(self.catalog.generation, db.eval.next_rule_id);
        // Sizes are read off the stored extensions, and a maintained view's
        // are derived, so this materializes exactly as explaining a query
        // does. It changes no answer either way: what is being decided is
        // which of two interchangeable views to read.
        try materialization.ensureMaterialized(db);

        const allocator = db.allocator;
        var staging = try db.clone();
        defer db.release(&staging);
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

        const surface = try transaction.answerVariables(&staging, compiled_goals);
        defer allocator.free(surface);
        // Sizes, for the one decision cost is allowed to make: which of
        // several views that reconstruct one relation exactly to read. Pointed
        // at the staged copy for the length of the fold and taken away after,
        // so the catalog never holds a store that has gone.
        self.catalog.extensions = staging.closureStore();
        defer self.catalog.extensions = null;
        var folded = try folding.foldQuery(allocator, &self.catalog, &staging.strings, .{
            .goals = compiled_goals,
            .rules = compiled_rules,
            .answers = surface,
        });
        var folded_owned = true;
        defer if (folded_owned) folded.deinit();

        var executable: ?folding.Executable = null;
        if (folded.outcome.plan()) |plan| {
            executable = folding.lowerPlan(
                allocator,
                &staging.strings,
                &self.catalog.symbols,
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

        const names = try answerNames(&staging, compiled_goals);
        errdefer freeNames(allocator, names);

        const index = try self.plans.insert(key, folded.outcome, executable, folded.answer_variables);
        key_owned = false;
        folded_owned = false;
        db.commit(&staging);
        return self.handle(index, false, names);
    }

    /// Runs a folded plan and returns its answers, listed as `order` asks.
    ///
    /// The plan runs against a copy of `db` holding exactly what the catalog
    /// admits, and the copy never joins `db`. It is *kept* — in the plan
    /// cache, beside the plan that built it — so that asking the same
    /// question again solves the goals against a reconstruction that is
    /// already derived instead of deriving it a second time. Deriving it is
    /// 63% to 99% of what a folded answer costs, and it is the same derivation
    /// every time until the database underneath it changes.
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
    /// All the work done on the reconstruction — deriving it and solving
    /// against it, whether or not either succeeds — is charged to `db`.
    pub fn answer(
        self: *ViewSelection,
        db: *database.Database,
        folded: Fold,
        order: []const input.SortKey,
    ) !results.QueryResult {
        const cached = try self.planAt(db, folded);
        if (cached.executable == null) return error.PlanNotExecutable;
        // Before anything is read from a kept reconstruction, and after the
        // handle is known to be live: a fact under a readable name is the one
        // change that gets this far.
        self.plans.refreshReconstructions(db.fact_generation);
        if (self.plans.entries.items[folded.entry].reconstruction == null) {
            // A view whose extension the engine derives has to have derived
            // it before the copy is taken, or the copy keeps a name with
            // nothing under it.
            try materialization.ensureMaterialized(db);
            const staged = try self.deriveReconstruction(
                db,
                &self.plans.entries.items[folded.entry].executable.?,
            );
            // Past here the cache owns it, and taking it in allocates
            // nothing, so there is no window where it belongs to neither.
            self.plans.keep(folded.entry, staged);
            const kept = &self.plans.entries.items[folded.entry].reconstruction.?;
            db.chargeWork(kept, kept.work_at_clone);
        } else {
            self.plans.reconstruction_hits += 1;
            self.plans.touch(folded.entry);
        }

        const entry = &self.plans.entries.items[folded.entry];
        // Solving interns the goals' ground structures into the
        // reconstruction and can expand its closure, so a failure part-way
        // leaves a database no later answer may be read from. It goes, and
        // the next call derives a fresh one.
        errdefer self.plans.discardReconstruction(folded.entry);
        // The reconstruction is kept, so its counter is cumulative and only
        // this call's share of it belongs here.
        const work_before = entry.reconstruction.?.eval.cost.work;
        defer db.chargeWork(&entry.reconstruction.?, work_before);
        return transaction.queryClausesAs(
            &entry.reconstruction.?,
            entry.executable.?.goals,
            .{ .variables = entry.answer_variables, .names = folded.names },
            order,
        );
    }

    /// Builds what a folded plan reads from: a copy of `db` holding exactly
    /// what the catalog admits, the plan's own rules installed in it, and the
    /// relations those rules reconstruct already derived.
    ///
    /// Deriving here rather than leaving it to `queryClauses` is the whole of
    /// the split. `transaction.evaluateClauses` materializes on its way to
    /// solving, so a caller that lets it do both cannot tell the two phases
    /// apart, let alone keep one of them; done here, the closure is clean
    /// before any goal is solved and a later call finds it that way.
    ///
    /// The caller materializes `db` first: a view whose extension the engine
    /// derives has to have derived it before the copy is taken, or the copy
    /// keeps a name with nothing under it. A copy that fails part-way is
    /// released rather than dropped, so what it did before failing is still
    /// charged to `db`.
    fn deriveReconstruction(
        self: *const ViewSelection,
        db: *database.Database,
        executable: *const folding.Executable,
    ) !database.Database {
        // What the catalog admits and nothing else: the other facts, the
        // derived closure and the database's own rules all go, since one of
        // those deriving a withheld relation would put it straight back, and
        // the plan brings every rule it needs.
        var staged = try db.cloneRetaining(*const ViewSelection, readableByPlans, self);
        errdefer db.release(&staged);
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
    pub fn explain(self: *ViewSelection, db: *database.Database, folded: Fold) ![]u8 {
        const entry = try self.planAt(db, folded);
        return entry.outcome.explainAlloc(db.allocator, .{
            .symbols = &self.catalog.symbols,
            .strings = &db.strings,
            .scalars = &db.eval.scalars,
        });
    }

    /// Which relations the plan derives instead of reading, and whether it
    /// gets each of them whole. Owned by the caller.
    pub fn reconstructions(
        self: *ViewSelection,
        db: *database.Database,
        folded: Fold,
    ) !Reconstructions {
        const entry = try self.planAt(db, folded);
        const allocator = db.allocator;
        var result: Reconstructions = .{ .allocator = allocator, .items = &.{} };
        errdefer result.deinit();
        const plan = entry.outcome.plan() orelse return result;
        var found: std.ArrayList(Reconstruction) = .empty;
        errdefer {
            for (found.items) |item| allocator.free(item.predicate);
            found.deinit(allocator);
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
            const name = try allocator.dupe(u8, db.strings.resolve(key.name));
            found.append(allocator, .{
                .predicate = name,
                .arity = key.arity,
                .exact = exact,
            }) catch |err| {
                allocator.free(name);
                return err;
            };
        }
        result.items = try found.toOwnedSlice(allocator);
        return result;
    }

    /// How many views are declared and how the plan cache has been doing.
    pub fn stats(self: *const ViewSelection) FoldStats {
        return .{
            .views = self.catalog.views.items.len,
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
    /// keeping. Folding and running again reproduces both.
    ///
    /// This is the memory control of the plan cache rather than a
    /// convenience. A cache entry can be a plan plus a copy of every readable
    /// extension and its closure, and while the number of those is bounded,
    /// their size is whatever the database is.
    pub fn clear(self: *ViewSelection) void {
        self.plans.clear();
    }

    /// The cached plan a handle names, or `StalePlan` when the views or the
    /// rules have moved on since it was folded.
    ///
    /// Checked against the catalog and the program as they stand now rather
    /// than against the cache's own stamp, because a caller can change either
    /// without folding anything, and a handle that survived such a change
    /// would name whichever plan later took its place.
    fn planAt(self: *ViewSelection, db: *const database.Database, folded: Fold) !*const CachedPlan {
        if (folded.catalog_generation != self.catalog.generation) return error.StalePlan;
        if (folded.rule_generation != db.eval.next_rule_id) return error.StalePlan;
        if (folded.catalog_generation != self.plans.catalog_generation) return error.StalePlan;
        if (folded.rule_generation != self.plans.rule_generation) return error.StalePlan;
        if (folded.entry >= self.plans.entries.items.len) return error.StalePlan;
        return &self.plans.entries.items[folded.entry];
    }

    /// A handle on plan `index` for a caller who calls its answer variables
    /// `names`, which the handle takes.
    fn handle(self: *const ViewSelection, index: usize, reused: bool, names: []const []const u8) Fold {
        return .{
            .allocator = self.plans.allocator,
            .guarantee = self.plans.entries.items[index].outcome.guarantee(),
            .reused = reused,
            .entry = index,
            .catalog_generation = self.plans.catalog_generation,
            .rule_generation = self.plans.rule_generation,
            .names = names,
        };
    }

    /// Whether a plan may read facts stored under this name and arity: a base
    /// relation the policy declared, or a readable view's extension.
    fn readableByPlans(self: *const ViewSelection, key: relation_store.PredicateKey) bool {
        if (self.catalog.baseAvailable(key)) return true;
        for (self.catalog.views.items) |defined| {
            if (!defined.readable()) continue;
            if (defined.name == key.name and defined.column_kinds.arity() == key.arity) return true;
        }
        return false;
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
    /// `ViewSelection.fold`. `unsupported` means there is no plan at all — not
    /// an empty one — and only `ViewSelection.explain` has anything to say
    /// about it.
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
    /// unlike the plans; see `ViewSelection.clear`.
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

// These tests drive the interface above and nothing below it. A fold's plan
// is not the caller's program, so the only things a test can hold one to are
// the ones a caller has: the guarantee, the rendering, the per-relation
// account, and the answers. What a fold refused and why is read off the
// rendering, where each unmet precondition prints its own text.

const testing = std.testing;
const errors = @import("errors.zig");
const parser = @import("parser.zig");
const program = @import("program.zig");
const test_support = @import("test_support.zig");

/// Parses and runs a source program against `db`, which is how a database is
/// built from source one layer up. Folding sits above running programs so
/// that its tests can say what a database holds the way a caller would.
fn runSource(db: *database.Database, text: []const u8) !results.ExecutionResult {
    const parsed = try parser.parseProgram(db.allocator, text, null);
    defer parsed.deinit();
    return program.execute(db, parsed.value.statements, null, null, null);
}

fn loadSource(db: *database.Database, text: []const u8) !void {
    var result = try runSource(db, text);
    result.deinit();
}

/// Adds one fact without staging a copy of the database, which is what the
/// public interface would do. A sweep over hundreds of databases cannot afford
/// a clone per fact.
fn addFact(db: *database.Database, predicate: []const u8, terms: []const input.Term) !void {
    return program.addFact(db, input.fact(predicate, terms), null);
}

/// One line per answer, sorted, holding the values only. A folded answer and
/// the query's own are compared by value, because which order a plan's
/// answers arrive in is not what is being checked.
fn answerTuples(result: *const results.QueryResult) ![][]u8 {
    const lines = try orderedTuples(result);
    std.mem.sort([]u8, lines, {}, struct {
        fn lessThan(_: void, a: []u8, b: []u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.lessThan);
    return lines;
}

/// The answers' values, one line per answer, in the order they are listed.
fn orderedTuples(result: *const results.QueryResult) ![][]u8 {
    const allocator = testing.allocator;
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

fn freeLines(lines: [][]u8) void {
    for (lines) |line| testing.allocator.free(line);
    testing.allocator.free(lines);
}

fn expectTuples(result: *const results.QueryResult, expected: []const []const u8) !void {
    const tuples = try answerTuples(result);
    defer freeLines(tuples);
    try testing.expectEqual(expected.len, tuples.len);
    for (expected, tuples) |want, actual| try testing.expectEqualStrings(want, actual);
}

fn expectOrderedTuples(result: *const results.QueryResult, expected: []const []const u8) !void {
    const tuples = try orderedTuples(result);
    defer freeLines(tuples);
    try testing.expectEqual(expected.len, tuples.len);
    for (expected, tuples) |want, actual| try testing.expectEqualStrings(want, actual);
}

/// Asserts that a fold's rendering says `expected` somewhere, and prints the
/// whole of it when it does not.
fn expectExplained(
    views: *ViewSelection,
    db: *database.Database,
    folded: Fold,
    expected: []const u8,
) !void {
    const explained = try views.explain(db, folded);
    defer testing.allocator.free(explained);
    if (std.mem.indexOf(u8, explained, expected) == null) {
        std.debug.print("\nnot in the explanation: {s}\n{s}\n", .{ expected, explained });
        return error.NotExplained;
    }
}

/// Asserts that a fold was refused, and that one reason it gives is `kind`.
fn expectRefused(
    views: *ViewSelection,
    db: *database.Database,
    folded: Fold,
    kind: folding.PreconditionKind,
) !void {
    try testing.expectEqual(Guarantee.unsupported, folded.guarantee);
    try expectExplained(views, db, folded, kind.text());
}

/// Chapter 6's Example 6.2.1: a view holding the pairs two edges apart, and
/// three stored pairs. The graph behind them is gone, which is the situation a
/// fold exists for — a test that folded and then read the original edges would
/// prove nothing.
fn declareEvenPathViews(views: *ViewSelection, db: *database.Database) !ViewId {
    try addFact(db, "v", &.{ input.atom("a"), input.atom("c") });
    try addFact(db, "v", &.{ input.atom("b"), input.atom("d") });
    try addFact(db, "v", &.{ input.atom("c"), input.atom("e") });
    return defineEvenPathView(views, db);
}

fn defineEvenPathView(views: *ViewSelection, db: *database.Database) !ViewId {
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    return views.define(db, input.fact("v", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("edge", &.{ y, z }),
    }, .materialized);
}

/// The query those views are folded against: `q` is the transitive closure of
/// a relation only the view remembers. The query rules are recursive and the
/// view definition is not, which is the case the Inverse Method exists for.
fn foldEvenPaths(views: *ViewSelection, db: *database.Database) !Fold {
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    return views.fold(db, &.{input.relation("q", &.{ x, y })}, &.{
        input.rule(input.fact("q", &.{ x, y }), &.{input.relation("edge", &.{ x, y })}),
        input.rule(input.fact("q", &.{ x, z }), &.{
            input.relation("edge", &.{ x, y }),
            input.relation("q", &.{ y, z }),
        }),
    });
}

test "an inverted view answers Chapter 6's even-length paths from its extension alone" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    _ = try declareEvenPathViews(&views, &db);

    const folded = try foldEvenPaths(&views, &db);
    defer folded.deinit();
    // A view remembers pairs two edges apart and nothing else, so no plan over
    // it can answer every path. Maximal containment is the whole claim.
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    // The paths of even length in the dissertation's graph, and only those:
    // a→c, b→d and c→e are two edges each, and a→e is four.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{ "a c", "a e", "b d", "c e" });
}

test "a comparison a reconstructed value cannot answer costs answers, not soundness" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    _ = try declareEvenPathViews(&views, &db);

    // q(X, Z) :- edge(X, Y), edge(Y, Z), X != Z. The middle node is
    // reconstructed and has no name, so the instances that would compare it
    // cannot be run; the one that compares the two ends can.
    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const folded = try views.fold(&db, &.{input.relation("q", &.{ x, z })}, &.{
        input.rule(input.fact("q", &.{ x, z }), &.{
            input.relation("edge", &.{ x, y }),
            input.relation("edge", &.{ y, z }),
            input.notEqual(x, z),
        }),
    });
    defer folded.deinit();
    // Dropping an instance answers less, which is sound and is not maximal.
    try testing.expectEqual(Guarantee.contained, folded.guarantee);
    try expectExplained(
        &views,
        &db,
        folded,
        "instances that would have read a reconstructed value were dropped",
    );

    // What survives is the pairs the view itself stores, which are the ones
    // whose two ends the plan can name.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{ "a c", "b d", "c e" });
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

/// Takes every fact of `predicate` out of `db`, so that a sweep can put the
/// next model's in. A fact moves no stamp a plan is folded under, so the plan
/// and its handle survive this and only the reconstruction is derived again.
fn retractAll(db: *database.Database, predicate: []const u8, arity: usize) !void {
    const names = [_][]const u8{ "A", "B", "C" };
    var terms: [names.len]input.Term = undefined;
    for (names[0..arity], terms[0..arity]) |name, *slot| slot.* = input.variable(name);
    _ = try transaction.retract(db, &.{input.relation(predicate, terms[0..arity])});
}

test "every answer a folded plan returns is one the query would have returned" {
    // The containment claim, checked by exhaustion rather than by argument:
    // over every graph on three nodes, work out what the query answers and
    // what the view stores, then answer the folded plan from the view alone
    // and confirm it invented nothing.
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();

    // A plan does not depend on the data, so it is folded once and asked again
    // of every graph.
    _ = try defineEvenPathView(&views, &db);
    const folded = try foldEvenPaths(&views, &db);
    defer folded.deinit();

    const names = [_][]const u8{ "a", "b", "c" };
    var answered: usize = 0;
    for (0..512) |value| {
        const edges: u9 = @intCast(value);
        const reachable = Graph.closure(edges);
        const stored = Graph.compose(edges, edges);

        try retractAll(&db, "v", 2);
        for (0..Graph.nodes) |from| for (0..Graph.nodes) |to| {
            if (Graph.has(stored, from, to))
                try addFact(&db, "v", &.{ input.atom(names[from]), input.atom(names[to]) });
        };

        var produced = try views.answer(&db, folded, &.{});
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
    try testing.expect(answered > 0);
}

/// Folds and runs one small even-length-path problem: a catalog built from a
/// definition, a recursive query program, the inverse rules the fold produced,
/// the split relations that made them runnable, and the answers.
fn foldingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try addFact(&db, "v", &.{ input.atom("a"), input.atom("c") });
    _ = try defineEvenPathView(&views, &db);

    const folded = try foldEvenPaths(&views, &db);
    defer folded.deinit();
    allocator.free(try views.explain(&db, folded));
    if (folded.guarantee != .maximally_contained) return error.UnexpectedGuarantee;
    var answers = try views.answer(&db, folded, &.{});
    answers.deinit();
}

test "folding, lowering and running a plan release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(foldingAllocationScenario);
}

test "a predicate the query derives from a reconstruction is no more exact than it is" {
    // The hole a relation-by-relation check leaves. `reach` is the query's own
    // predicate, so nothing about it is reconstructed — but it is derived from
    // `edge`, which is, so the plan knows less of `reach` than the query does
    // and `not reach(...)` is therefore true of more. Every edge is a pair
    // `reach` holds, so the query answers nothing; a plan that let this
    // through would answer whichever reconstructed edges its own `reach`
    // failed to derive.
    //
    // The positive goal reads `edge` rather than the view, because a goal
    // names a relation and which relations are views is the catalog's
    // business. Reading `edge` positively is no objection — a reconstruction
    // can stand in for it there — so the refusal is `reach`'s alone.
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try addFact(&db, "v", &.{ input.atom("a"), input.atom("b") });
    _ = try defineEvenPathView(&views, &db);

    const x = input.variable("X");
    const y = input.variable("Y");
    const folded = try views.fold(&db, &.{
        input.relation("edge", &.{ x, y }),
        input.not("reach", &.{ x, y }),
    }, &.{
        input.rule(input.fact("reach", &.{ x, y }), &.{input.relation("edge", &.{ x, y })}),
    });
    defer folded.deinit();
    try expectRefused(&views, &db, folded, .relation_read_non_positively);
    try expectExplained(&views, &db, folded, "reach/2: ");
}

test "inverting a view that collected a list reads the values back out of it" {
    // Chapter 6's Example 6.3.1. The view keeps a list of everything `r`
    // related each key to, so inverting it recovers `r` one list element at a
    // time, and recovers `p` only as far as saying a tuple was there.
    const allocator = testing.allocator;

    // The database behind the view, kept only to say what the query really
    // answers and what the view really stores. The plan never sees it.
    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\p(a, 1). p(b, 2). p(c, 3).
        \\r(a, b). r(a, c). r(c, a). r(c, c).
        \\v(X, S) :- p(X, Z), setof(Y, r(X, Y), S).
        \\q(X, Y) :- r(X, Y), p(Y, Z).
    );
    var extension = try runSource(&source, "v(X, S)?");
    defer extension.deinit();
    try expectTuples(&extension.query, &.{ "a [b, c]", "b []", "c [a, c]" });
    var wanted = try runSource(&source, "q(X, Y)?");
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);

    // The folded side holds that extension and nothing else.
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(a, [b, c]). v(b, []). v(c, [a, c]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const s = input.variable("S");
    _ = try views.define(&db, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{ x, z }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ x, y })}, &.{
        input.rule(input.fact("q", &.{ x, y }), &.{
            input.relation("r", &.{ x, y }),
            input.relation("p", &.{ y, z }),
        }),
    });
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    // On this database the plan loses nothing: what the view kept is enough to
    // answer the query exactly. The dissertation's printed answer list omits
    // q(a, b), which both the query and the plan produce — `p(b, 2)` is what
    // makes `b` a value `p` relates, and the empty list `v(b, [])` is what
    // records it.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 4), expected.len);
    try expectTuples(&answers, expected);
}

test "a value projected out of an aggregate is a witness per element, not per tuple" {
    // The join a shared name would invent. `W` is projected out of the
    // aggregate's own body, so the definition claims a witness for each value
    // the list collected — not one witness for the whole list. Naming them all
    // alike would let the query below join two elements through a `W` the
    // database never had in common.
    const allocator = testing.allocator;
    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\p(a).
        \\r(a, b, 1). r(a, c, 2).
        \\v(X, S) :- p(X), setof(Y, r(X, Y, W), S).
        \\q(Y1, Y2) :- r(X, Y1, W), r(X, Y2, W), Y1 != Y2.
    );
    var wanted = try runSource(&source, "q(A, B)?");
    defer wanted.deinit();
    try testing.expectEqual(@as(usize, 0), wanted.query.answers.items.len);

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(a, [b, c]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const w = input.variable("W");
    const s = input.variable("S");
    const first = input.variable("Y1");
    const second = input.variable("Y2");
    _ = try views.define(&db, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y, w })}, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ first, second })}, &.{
        input.rule(input.fact("q", &.{ first, second }), &.{
            input.relation("r", &.{ x, first, w }),
            input.relation("r", &.{ x, second, w }),
            input.notEqual(first, second),
        }),
    });
    defer folded.deinit();
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 0), answers.answers.items.len);
}

test "an aggregate nested in another is read by chaining into the list it collected" {
    // The dissertation reaches this case by rewriting the view into one rule
    // per aggregate. Reading it directly is what the shape already says: the
    // outer list collects `Y!T` pairs, so binding one of them binds `T`, and
    // `T` is the inner list to read the next value out of.
    const allocator = testing.allocator;
    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\p(a).
        \\r(a, b). r(a, c).
        \\s(b, 1). s(b, 2). s(c, 3).
        \\v(X, S) :- p(X), setof(Y!T, (r(X, Y), setof(Z, s(Y, Z), T)), S).
        \\q(Y, Z) :- s(Y, Z), r(X, Y).
    );
    var extension = try runSource(&source, "v(X, S)?");
    defer extension.deinit();
    try expectTuples(&extension.query, &.{"a [[b, 1, 2], [c, 3]]"});
    var wanted = try runSource(&source, "q(A, B)?");
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(a, [[b, 1, 2], [c, 3]]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const s = input.variable("S");
    const t = input.variable("T");
    const pair: input.Term.Cons = .{ .head = &y, .tail = &t };
    _ = try views.define(&db, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{x}),
        input.setof(input.cons(&pair), &.{
            input.relation("r", &.{ x, y }),
            input.setof(z, &.{input.relation("s", &.{ y, z })}, t),
        }, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ y, z })}, &.{
        input.rule(input.fact("q", &.{ y, z }), &.{
            input.relation("s", &.{ y, z }),
            input.relation("r", &.{ x, y }),
        }),
    });
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    // Everything the query answers, from the nested list alone.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, expected);
}

test "two aggregates side by side collect for themselves, not for each other" {
    // Both aggregates spell the collected value `Y` and the projected value
    // `W`, and the language says each means its own — a value the surrounding
    // goals do not bind belongs to the aggregate that mentions it. Inverting
    // them as one would name both witnesses alike and join `r` to `t` through
    // a `W` the database never had in common.
    const allocator = testing.allocator;
    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\p(a).
        \\r(a, b, 1). t(a, b, 2).
        \\v(X, S1, S2) :- p(X), setof(Y, r(X, Y, W), S1), setof(Y, t(X, Y, W), S2).
        \\q(Y1, Y2) :- r(X, Y1, W), t(X, Y2, W).
    );
    var wanted = try runSource(&source, "q(A, B)?");
    defer wanted.deinit();
    try testing.expectEqual(@as(usize, 0), wanted.query.answers.items.len);

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(a, [b], [b]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const w = input.variable("W");
    const first = input.variable("S1");
    const second = input.variable("S2");
    _ = try views.define(&db, input.fact("v", &.{ x, first, second }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y, w })}, first),
        input.setof(y, &.{input.relation("t", &.{ x, y, w })}, second),
    }, .materialized);

    const y1 = input.variable("Y1");
    const y2 = input.variable("Y2");
    const folded = try views.fold(&db, &.{input.relation("q", &.{ y1, y2 })}, &.{
        input.rule(input.fact("q", &.{ y1, y2 }), &.{
            input.relation("r", &.{ x, y1, w }),
            input.relation("t", &.{ x, y2, w }),
        }),
    });
    defer folded.deinit();
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 0), answers.answers.items.len);
}

/// Folds and runs one small collecting view: a definition with an aggregate,
/// the membership rules the plan defines to read its list, the Skolem term the
/// projected outer value needs, and the answers.
fn collectingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(a, [b]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const z = input.variable("Z");
    const s = input.variable("S");
    _ = try views.define(&db, input.fact("v", &.{ x, s }), &.{
        input.relation("p", &.{ x, z }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ x, y })}, &.{
        input.rule(input.fact("q", &.{ x, y }), &.{
            input.relation("r", &.{ x, y }),
            input.relation("p", &.{ y, z }),
        }),
    });
    defer folded.deinit();
    allocator.free(try views.explain(&db, folded));
    var answers = try views.answer(&db, folded, &.{});
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
    views: *ViewSelection,
    db: *database.Database,
    availability: Availability,
) !ViewId {
    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");
    return views.define(db, input.fact("v", &.{ x, s }), &.{
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
    views: *ViewSelection,
    db: *database.Database,
    availability: Availability,
) !ViewId {
    const x = input.variable("X");
    const y = input.variable("Y");
    const collected = input.variable("Y2");
    const s = input.variable("S");
    return views.define(db, input.fact("c", &.{ x, s }), &.{
        input.relation("r", &.{ x, y }),
        input.setof(collected, &.{input.relation("r", &.{ x, collected })}, s),
    }, availability);
}

/// Folds `q(X)?` under `<head>(<key>) :- setof(Y, r(<key>, Y), <output>).`
///
/// Section 6.4.1's pair of queries, whose only difference is the collected
/// output they ask for, and whose containment differs entirely because of it.
fn foldCollectingQuery(
    views: *ViewSelection,
    db: *database.Database,
    head: []const u8,
    key: input.Term,
    output: input.Term,
) !Fold {
    const y = input.variable("Y");
    return views.fold(db, &.{input.relation(head, &.{input.variable("X")})}, &.{
        input.rule(input.fact(head, &.{key}), &.{
            input.setof(y, &.{input.relation("r", &.{ key, y })}, output),
        }),
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
    const allocator = testing.allocator;

    // What is really there, and what the two queries really answer. The plan
    // never sees this database.
    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\p(b). p(c).
        \\r(a, 1). r(c, 2).
        \\v(X, S) :- p(X), setof(Y, r(X, Y), S).
        \\empty(a) :- setof(Y, r(a, Y), []).
        \\nonempty(c) :- setof(Y, r(c, Y), H!T).
    );
    var refused_answers = try runSource(&source, "empty(X)?");
    defer refused_answers.deinit();
    try testing.expectEqual(@as(usize, 0), refused_answers.query.answers.items.len);
    var admitted_answers = try runSource(&source, "nonempty(X)?");
    defer admitted_answers.deinit();
    try testing.expectEqual(@as(usize, 1), admitted_answers.query.answers.items.len);

    // The folded side holds the view's extension and nothing else: `b` was
    // admitted by `p` and related to nothing, `c` was admitted and related
    // to 2. That `r` also holds (a, 1) is exactly what is no longer there.
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(b, []). v(c, [2]).");
    _ = try defineCollectingView(&views, &db, .materialized);

    // q(a) :- setof(Y, r(a, Y), []). Nothing discharges the refusal: the view
    // is not a canonical aggregate view of `r`, and a query asking for an
    // empty set is not monotonic.
    const refused = try foldCollectingQuery(&views, &db, "q", input.atom("a"), input.list(&.{}));
    defer refused.deinit();
    try expectRefused(&views, &db, refused, .relation_read_non_positively);

    // q(c) :- setof(Y, r(c, Y), H!T). The same view, the same relation read
    // the same way, and this one folds — the query is monotonic.
    const head = input.variable("H");
    const tail = input.variable("T");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    const admitted = try foldCollectingQuery(&views, &db, "q", input.atom("c"), input.cons(&pair));
    defer admitted.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, admitted.guarantee);
    try expectExplained(&views, &db, admitted, "the query is monotonic");
    var answers = try views.answer(&db, admitted, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{"c"});

    // And the refusal is load-bearing rather than decorative. The inverse
    // rules a plan is built from do not depend on which query is being folded,
    // so the `r` the admitted plan reconstructs is the one Example 6.4.1 warns
    // about. Ask for it directly and it has nothing under `a` — which `r`
    // does have — so the set it collects for `a` is empty, and the refused
    // question run over it would have answered `a`.
    const reconstructed = try views.fold(&db, &.{input.relation("r", &.{
        input.atom("a"),
        input.variable("Y"),
    })}, &.{});
    defer reconstructed.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, reconstructed.guarantee);
    var under_a = try views.answer(&db, reconstructed, &.{});
    defer under_a.deinit();
    try testing.expectEqual(@as(usize, 0), under_a.answers.items.len);
    var really = try runSource(&source, "r(a, Y)?");
    defer really.deinit();
    try testing.expectEqual(@as(usize, 1), really.query.answers.items.len);
    // Asked as `bad` with its own rule, the question is the refused one under
    // another name, and it is refused again.
    const bad = try foldCollectingQuery(&views, &db, "bad", input.atom("a"), input.list(&.{}));
    defer bad.deinit();
    try expectRefused(&views, &db, bad, .relation_read_non_positively);
}

test "a canonical aggregate view folds a query no monotonicity argument covers" {
    // Theorem 6.4.2. The query is Example 6.4.1's, unchanged and still not
    // monotonic, and it folds anyway — because the catalog holds a canonical
    // aggregate view of the relation it counts, and Lemma 6.4.2 makes reading
    // that view's lists back out equivalent to reading the relation.
    const allocator = testing.allocator;

    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\r(a, 1). r(c, 2).
        \\c(X, S) :- r(X, Y), setof(Y2, r(X, Y2), S).
        \\w(X) :- r(X, Y).
        \\empty(a) :- setof(Y, r(a, Y), []).
        \\gone(d) :- setof(Y, r(d, Y), []).
    );
    var wanted = try runSource(&source, "empty(X)?");
    defer wanted.deinit();
    try testing.expectEqual(@as(usize, 0), wanted.query.answers.items.len);
    var elsewhere = try runSource(&source, "gone(X)?");
    defer elsewhere.deinit();
    try testing.expectEqual(@as(usize, 1), elsewhere.query.answers.items.len);

    // The folded side holds both view extensions and no base relation.
    var db: database.Database = .init(allocator);
    defer db.deinit();
    try loadSource(&db, "c(a, [1]). c(c, [2]). w(a). w(c).");

    const x = input.variable("X");
    const y = input.variable("Y");

    // Two selections over the same database, differing in one view. `w(X) :-
    // r(X, Y)` mentions `r` and remembers only that a key had some value, so
    // it can reconstruct `r` and cannot prove it complete.
    var without: ViewSelection = .init(allocator);
    defer without.deinit();
    _ = try without.define(&db, input.fact("w", &.{x}), &.{
        input.relation("r", &.{ x, y }),
    }, .materialized);

    var with: ViewSelection = .init(allocator);
    defer with.deinit();
    _ = try with.define(&db, input.fact("w", &.{x}), &.{
        input.relation("r", &.{ x, y }),
    }, .materialized);
    _ = try defineCanonicalView(&with, &db, .materialized);

    // Without the canonical view the fold has nothing to offer, and says so as
    // the read it could not allow rather than as a missing relation.
    {
        const refused = try foldCollectingQuery(&without, &db, "q", input.atom("a"), input.list(&.{}));
        defer refused.deinit();
        try expectRefused(&without, &db, refused, .relation_read_non_positively);
    }

    const folded = try foldCollectingQuery(&with, &db, "q", input.atom("a"), input.list(&.{}));
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
    try expectExplained(
        &with,
        &db,
        folded,
        "reconstructed exactly, from a canonical aggregate view of it: r/2",
    );
    // The query's own answer, from the view extensions alone: `r` does relate
    // `a` to something, so the empty set is not what was collected.
    var answers = try with.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 0), answers.answers.items.len);

    // The other half of exactness, which containment alone would not show: the
    // plan derives all of `r`, so a key `r` never mentions still collects the
    // empty set and still answers.
    const absent = try foldCollectingQuery(&with, &db, "gone", input.atom("d"), input.list(&.{}));
    defer absent.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, absent.guarantee);
    var gone = try with.answer(&db, absent, &.{});
    defer gone.deinit();
    try testing.expectEqual(@as(usize, 1), gone.answers.items.len);
}

test "a view that projected its collected list away still remembers its outer goals" {
    // Section 6.3.2. The head of `v(X) :- p(X, S), setof(Y, r(X, Y), S)` keeps
    // neither the set nor anything collected into it, so the plan names that
    // set with a Skolem term. A name is enough to reconstruct the goals
    // *outside* the aggregate — they held for some set, and this is which —
    // and it is not enough to reach the values inside it, because those were
    // never stored anywhere.
    const allocator = testing.allocator;

    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\p(a, [1]). p(b, []).
        \\r(a, 1).
        \\v(X) :- p(X, S), setof(Y, r(X, Y), S).
        \\q(X) :- p(X, S).
    );
    var extension = try runSource(&source, "v(X)?");
    defer extension.deinit();
    try testing.expectEqual(@as(usize, 2), extension.query.answers.items.len);
    var wanted = try runSource(&source, "q(X)?");
    defer wanted.deinit();
    const expected = try answerTuples(&wanted.query);
    defer freeLines(expected);

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v(a). v(b).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");
    _ = try views.define(&db, input.fact("v", &.{x}), &.{
        input.relation("p", &.{ x, s }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    // What the outer goal remembers comes back exactly: every key `p` had a
    // tuple for is a key the plan produces.
    {
        const folded = try views.fold(&db, &.{input.relation("q", &.{x})}, &.{
            input.rule(input.fact("q", &.{x}), &.{input.relation("p", &.{ x, s })}),
        });
        defer folded.deinit();
        try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try expectTuples(&answers, expected);
    }

    // What the aggregate collected does not, and the plan says so by answering
    // nothing rather than by guessing.
    const folded = try views.fold(&db, &.{input.relation("t", &.{ x, y })}, &.{
        input.rule(input.fact("t", &.{ x, y }), &.{input.relation("r", &.{ x, y })}),
    });
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
    // The source database has r(a, 1), so the query's own answer is one tuple.
    // Nothing derives membership in a set that was never stored, so the plan
    // has none — which is containment, and the most a plan over this view can
    // do.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 0), answers.answers.items.len);
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
        try addFact(db, predicate, &.{
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
    const allocator = testing.allocator;

    // The monotonic discharge. `q(X) :- p(X), setof(Y, r(Y, X), H!T)` asks for
    // some value to reach `X`, and the plan knows `r` only for the keys `p`
    // admitted, so it can miss a value and can never invent one.
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    _ = try defineCollectingView(&views, &db, .materialized);

    const x = input.variable("X");
    const y = input.variable("Y");
    const head = input.variable("H");
    const tail = input.variable("T");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    const folded = try views.fold(&db, &.{input.relation("q", &.{x})}, &.{
        input.rule(input.fact("q", &.{x}), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ y, x })}, input.cons(&pair)),
        }),
    });
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    var answered: usize = 0;
    for (0..Model.subsets) |admitted| {
        const keys: u2 = @intCast(admitted);
        for (0..Model.relations) |related| {
            const edges: u4 = @intCast(related);
            try retractAll(&db, "v", 2);
            for (0..Model.size) |key| {
                if (Model.admits(keys, key)) try Model.addCollected(&db, "v", edges, key);
            }

            var produced = try views.answer(&db, folded, &.{});
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
    try testing.expect(answered > 0);

    // The canonical-view discharge, held to the stronger claim its proof
    // makes. Lemma 6.4.2 says the reconstruction of `r` is *equivalent* rather
    // than merely contained, so `q(a) :- setof(Y, r(a, Y), [])` must answer
    // exactly when the query does — including when it answers and a merely
    // contained plan would have been allowed to stay silent.
    var canonical: database.Database = .init(allocator);
    defer canonical.deinit();
    var exact: ViewSelection = .init(allocator);
    defer exact.deinit();
    _ = try defineCanonicalView(&exact, &canonical, .materialized);
    const counted = try foldCollectingQuery(&exact, &canonical, "q", input.atom("a"), input.list(&.{}));
    defer counted.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, counted.guarantee);

    for (0..Model.relations) |related| {
        const edges: u4 = @intCast(related);
        try retractAll(&canonical, "c", 2);
        for (0..Model.size) |key| {
            var holds = false;
            for (0..Model.size) |column| holds = holds or Model.relates(edges, key, column);
            if (holds) try Model.addCollected(&canonical, "c", edges, key);
        }

        var produced = try exact.answer(&canonical, counted, &.{});
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
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "c(a, [1]). v(a).");

    _ = try defineCanonicalView(&views, &db, .materialized);
    const x = input.variable("X");
    const y = input.variable("Y");
    const s = input.variable("S");
    _ = try views.define(&db, input.fact("v", &.{x}), &.{
        input.relation("p", &.{ x, s }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const folded = try foldCollectingQuery(&views, &db, "q", input.atom("a"), input.list(&.{}));
    defer folded.deinit();
    allocator.free(try views.explain(&db, folded));
    if (folded.guarantee != .maximally_contained) return error.UnexpectedGuarantee;
    var answers = try views.answer(&db, folded, &.{});
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
    const source =
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
    fn define(views: *ViewSelection, db: *database.Database) !void {
        const x = input.variable("X");
        const y = input.variable("Y");
        const y0 = input.variable("Y0");
        const s = input.variable("S");
        const t = input.variable("T");
        const c = input.variable("C");
        _ = try views.define(db, input.fact("v1", &.{ x, t }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
        }, .materialized);
        _ = try views.define(db, input.fact("v2", &.{ x, c }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("length", &.{ s, c }),
        }, .materialized);
        _ = try views.define(db, input.fact("cr", &.{ x, s }), &.{
            input.relation("r", &.{ x, y0 }),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        }, .materialized);
    }

    /// Folds `q(X, E)?` under `excess(L, E) :- sum(L, T), length(L, C), E =
    /// T - C.` and `q(X, E) :- p(X), setof(Y, r(X, Y), S), excess(S, E).` —
    /// and, when asked, Appendix B's recursive case of `sum` beside them.
    fn fold(views: *ViewSelection, db: *database.Database, with_sum: bool) !Fold {
        const x = input.variable("X");
        const y = input.variable("Y");
        const s = input.variable("S");
        const t = input.variable("T");
        const c = input.variable("C");
        const l = input.variable("L");
        const e = input.variable("E");
        const head = input.variable("H");
        const tail = input.variable("T2");
        const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
        const rules = [_]input.Rule{
            input.rule(input.fact("excess", &.{ l, e }), &.{
                input.relation("sum", &.{ l, t }),
                input.relation("length", &.{ l, c }),
                input.subtract(e, t, c),
            }),
            input.rule(input.fact("q", &.{ x, e }), &.{
                input.relation("p", &.{x}),
                input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
                input.relation("excess", &.{ s, e }),
            }),
            // sum(H!T2, S) :- sum(T2, T), S = T + H.
            input.rule(input.fact("sum", &.{ input.cons(&pair), s }), &.{
                input.relation("sum", &.{ tail, t }),
                input.add(s, t, head),
            }),
        };
        const asked = [_]input.Goal{input.relation("q", &.{ x, e })};
        return views.fold(db, &asked, if (with_sum) &rules else rules[0..2]);
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
    const allocator = testing.allocator;

    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source, Excess.source);
    var wanted = try runSource(&source, "q(X, E)?");
    defer wanted.deinit();
    // a is related to 1 and 2, so its set sums to 3 and holds 2; b to 5 alone.
    try expectTuples(&wanted.query, &.{ "a 1", "b 4" });

    // The folded side holds the three view extensions and nothing else. It has
    // no `p`, no `r`, and — this is what Section 6.5 turns on — no definition
    // of `sum` or of `length` either.
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, Excess.extensions);
    try Excess.define(&views, &db);

    const folded = try Excess.fold(&views, &db, false);
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
    for ([_][]const u8{
        "expanded into the list functions the views expose: excess/2",
        "split into the set it collects and the list functions reading it: v1@0/2",
        "split into the set it collects and the list functions reading it: v2@1/2",
        "views proved to have collected one set",
        "reconstructed exactly, from a canonical aggregate view of it: r/2",
    }) |note| try expectExplained(&views, &db, folded, note);

    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{ "a 1", "b 4" });
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
    const allocator = testing.allocator;

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, Excess.extensions);
    try Excess.define(&views, &db);

    // sum(H!T2, S) :- sum(T2, A), S = A + H. Appendix B's definition, handed
    // to the fold as one of the query's own rules.
    const refused = try Excess.fold(&views, &db, true);
    defer refused.deinit();
    try expectRefused(&views, &db, refused, .query_list_function_recursive);
    try expectExplained(&views, &db, refused, "sum/2: the query defines it by structural recursion");

    // The same query without that rule is the one the phase folds, so the
    // refusal is the rule and not the setting.
    const without = try Excess.fold(&views, &db, false);
    defer without.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, without.guarantee);

    // And the other way such a definition could reach a plan is closed
    // already, twice over. Declared as a view, Appendix B's recursive case is
    // admitted as what it is — structural recursion, seeded like the rule —
    // and a definition reading what it defines is not one the Inverse Method
    // inverts.
    const y = input.variable("Y");
    const s = input.variable("S");
    const t = input.variable("T");
    const head = input.variable("H");
    const tail = input.variable("T2");
    const pair: input.Term.Cons = .{ .head = &head, .tail = &tail };
    const total = [_]input.Goal{input.relation("total", &.{ y, s })};
    const total_rules = [_]input.Rule{
        input.rule(input.fact("total", &.{ y, s }), &.{input.relation("sum", &.{ y, s })}),
    };
    {
        var recursive: ViewSelection = .init(allocator);
        defer recursive.deinit();
        _ = try recursive.define(&db, input.fact("sum", &.{ input.cons(&pair), s }), &.{
            input.relation("sum", &.{ tail, t }),
            input.add(s, t, head),
        }, .materialized);
        const view_side = try recursive.fold(&db, &total, &total_rules);
        defer view_side.deinit();
        try expectRefused(&recursive, &db, view_side, .view_definition_recursive);
    }

    // Nor does it take the recursion: a view reading `sum` whose head holds a
    // list is outside the class F2 inverts, because a list outside an
    // aggregate is not something the Inverse Method has a rule for.
    var listed: ViewSelection = .init(allocator);
    defer listed.deinit();
    _ = try listed.define(&db, input.fact("longer", &.{ input.cons(&pair), s }), &.{
        input.relation("sum", &.{ tail, s }),
        input.relation("element", &.{head}),
    }, .materialized);
    const view_side = try listed.fold(&db, &total, &total_rules);
    defer view_side.deinit();
    try expectRefused(&listed, &db, view_side, .view_definition_uses_lists);
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
    views: *ViewSelection,
    db: *database.Database,
    keeps: enum { collected_end, linking_end },
) !void {
    const x = input.variable("X");
    const z = input.variable("Z");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");
    _ = try views.define(db, input.fact("cr", &.{ z, s }), &.{
        input.relation("r", &.{ z, y0 }),
        input.setof(y, &.{input.relation("r", &.{ z, y })}, s),
    }, .materialized);
    _ = try views.define(db, input.fact("v1", &.{
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
    const allocator = testing.allocator;

    var db: database.Database = .init(allocator);
    defer db.deinit();
    try loadSource(&db, "v1(a, 3). cr(a, [1, 2]). link(w, a).");

    const x = input.variable("X");
    const z = input.variable("Z");
    const y = input.variable("Y");
    const s = input.variable("S");
    const t = input.variable("T");

    // q(Z, T) :- link(X, Z), setof(Y, r(Z, Y), S), sum(S, T). The same
    // question of both selections; only the view differs.
    inline for (.{ .linking_end, .collected_end }) |keeps| {
        var views: ViewSelection = .init(allocator);
        defer views.deinit();
        try defineLinkedView(&views, &db, keeps);

        const folded = try views.fold(&db, &.{input.relation("q", &.{ z, t })}, &.{
            input.rule(input.fact("q", &.{ z, t }), &.{
                input.relation("link", &.{ x, z }),
                input.setof(y, &.{input.relation("r", &.{ z, y })}, s),
                input.relation("sum", &.{ s, t }),
            }),
        });
        defer folded.deinit();
        if (keeps == .linking_end) {
            // One reason, and only that one.
            const explained = try views.explain(&db, folded);
            defer allocator.free(explained);
            try testing.expectEqualStrings(
                \\guarantee: unsupported
                \\unmet preconditions:
                \\  sum/2: no view read the collected set with it
                \\
            , explained);
            continue;
        }

        // The same query, the same relations, one variable different in the
        // view's head — and now the set has a name, so the plan has a rule for
        // `sum` and answers what the stored tuple says.
        try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try expectTuples(&answers, &.{"a 3"});
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
    const allocator = testing.allocator;

    var db: database.Database = .init(allocator);
    defer db.deinit();
    try loadSource(&db, "v1(a, 3). cr(a, [1, 2]). asked(a, [1, 2]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");

    // q(X, T) :- asked(X, S), sum(S, T). `asked` is the caller's own relation,
    // declared available, so the query itself never reads `r` at all — only
    // the auxiliary view does.
    inline for (.{ false, true }) |canonical| {
        var views: ViewSelection = .init(allocator);
        defer views.deinit();
        try views.declareBaseAvailable(&db, "asked", 2);
        _ = try views.define(&db, input.fact("v1", &.{ x, t }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
        }, .materialized);
        if (canonical) _ = try views.define(&db, input.fact("cr", &.{ x, s }), &.{
            input.relation("r", &.{ x, y0 }),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        }, .materialized);

        const folded = try views.fold(&db, &.{input.relation("q", &.{ x, t })}, &.{
            input.rule(input.fact("q", &.{ x, t }), &.{
                input.relation("asked", &.{ x, s }),
                input.relation("sum", &.{ s, t }),
            }),
        });
        defer folded.deinit();
        if (!canonical) {
            // Only `v1` mentions `r`, and what it remembers of it is whatever
            // its own outer goals admitted. The refusal names the relation the
            // auxiliary view collects rather than one the query reads, because
            // the query reads none of it.
            try expectRefused(&views, &db, folded, .set_collected_from_inexact_relation);
            continue;
        }

        // With a canonical aggregate view of `r` the auxiliary view collects
        // exactly what `r` held, so the stored `3` really is the sum of the
        // set the query asked about.
        try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try expectTuples(&answers, &.{"a 3"});
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

    /// The three view extensions this database comes to, in place of the
    /// previous model's. The two layers have a tuple for every key `p`
    /// admits, including one whose set is empty; the canonical view has one
    /// for every key `r` relates, whatever `p` said.
    fn extend(db: *database.Database, admitted: u2, related: u4) !void {
        try retractAll(db, "v1", 2);
        try retractAll(db, "v2", 2);
        try retractAll(db, "cr", 2);
        for (0..size) |key| {
            if (admits(admitted, key)) {
                try addFact(db, "v1", &.{
                    input.atom(keys[key]),
                    input.integer(total(related, key)),
                });
                try addFact(db, "v2", &.{
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
            try addFact(db, "cr", &.{ input.atom(keys[key]), input.list(held[0..written]) });
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
    const allocator = testing.allocator;

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try Excess.define(&views, &db);
    const folded = try Excess.fold(&views, &db, false);
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    var answered: usize = 0;
    for (0..ExcessModel.subsets) |admitted| {
        for (0..ExcessModel.relations) |related| {
            const keys: u2 = @intCast(admitted);
            const edges: u4 = @intCast(related);
            try ExcessModel.extend(&db, keys, edges);

            var produced = try views.answer(&db, folded, &.{});
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
    try testing.expect(answered > 0);
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
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v1(a, 1). cr(a, [1]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");
    const l = input.variable("L");
    _ = try views.define(&db, input.fact("v1", &.{ x, t }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
    _ = try views.define(&db, input.fact("cr", &.{ x, s }), &.{
        input.relation("r", &.{ x, y0 }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ x, t })}, &.{
        input.rule(input.fact("total", &.{ l, t }), &.{input.relation("sum", &.{ l, t })}),
        input.rule(input.fact("q", &.{ x, t }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("total", &.{ s, t }),
        }),
    });
    defer folded.deinit();
    allocator.free(try views.explain(&db, folded));
    if (folded.guarantee != .maximally_contained) return error.UnexpectedGuarantee;
    var answers = try views.answer(&db, folded, &.{});
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
    const allocator = testing.allocator;

    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\sum([], 0).
        \\sum(H!T, S) :- sum(T, A), S = A + H.
        \\length([], 0).
        \\length(H!T, N) :- length(T, M), N = M + 1.
        \\p(a).
        \\r(a, 2). r(a, 5). r(b, a).
        \\seed([2, 5]). seed([b]).
        \\q(X, E) :- p(X), setof(Y, r(X, Y), S), sum(S, T), length(S, C), E = T - C.
    );
    var wanted = try runSource(&source, "q(X, E)?");
    defer wanted.deinit();
    // The successors of `a` are 2 and 5, so seven less two of them is five.
    try expectTuples(&wanted.query, &.{"a 5"});

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    // v1 sums the successors, v3 counts them, v2 counts the predecessors — and
    // `a` has two successors and one predecessor, so a plan confusing the two
    // sets answers six as well as five.
    try loadSource(&db, "v1(a, 7). v3(a, 2). v2(a, 1). cr(a, [2, 5]). cr(b, [a]).");

    const x = input.variable("X");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const s = input.variable("S");
    const t = input.variable("T");
    const c = input.variable("C");
    const e = input.variable("E");
    _ = try views.define(&db, input.fact("v1", &.{ x, t }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
    _ = try views.define(&db, input.fact("v3", &.{ x, c }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("length", &.{ s, c }),
    }, .materialized);
    _ = try views.define(&db, input.fact("v2", &.{ x, c }), &.{
        input.relation("p", &.{x}),
        input.setof(y, &.{input.relation("r", &.{ y, x })}, s),
        input.relation("length", &.{ s, c }),
    }, .materialized);
    _ = try views.define(&db, input.fact("cr", &.{ x, s }), &.{
        input.relation("r", &.{ x, y0 }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ x, e })}, &.{
        input.rule(input.fact("q", &.{ x, e }), &.{
            input.relation("p", &.{x}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
            input.relation("length", &.{ s, c }),
            input.subtract(e, t, c),
        }),
    });
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    // Exactly the query's answers: the view counting predecessors reports
    // about its own set, which the query never asks about, so it contributes
    // nothing rather than contributing a second answer.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{"a 5"});
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
    const allocator = testing.allocator;

    var source: database.Database = .init(allocator);
    defer source.deinit();
    try loadSource(&source,
        \\sum([], 0).
        \\sum(H!T, S) :- sum(T, A), S = A + H.
        \\p(a). g(w). m(z).
        \\r(a, 2). r(a, 5).
        \\seed([2, 5]).
        \\q(X, W, T) :- p(X), g(W), setof(Y, r(X, Y), S), sum(S, T).
    );
    var wanted = try runSource(&source, "q(X, W, T)?");
    defer wanted.deinit();
    try expectTuples(&wanted.query, &.{"a w 7"});

    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try loadSource(&db, "v1(a, w, 7). cr(a, [2, 5]). hp(z). hg(z). m(z).");

    try views.declareBaseAvailable(&db, "m", 1);
    const x = input.variable("X");
    const w = input.variable("W");
    const y = input.variable("Y");
    const y0 = input.variable("Y0");
    const z = input.variable("Z");
    const s = input.variable("S");
    const t = input.variable("T");
    _ = try views.define(&db, input.fact("v1", &.{ x, w, t }), &.{
        input.relation("p", &.{x}),
        input.relation("g", &.{w}),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
        input.relation("sum", &.{ s, t }),
    }, .materialized);
    // `hp` remembers that `p` held of something and not of what, so inverting
    // it reconstructs `p` at a value the plan can only name. `hg` does the
    // same to `g` — the difference that matters is that the auxiliary view's
    // aggregate reads its `p` column and not its `g` column.
    _ = try views.define(&db, input.fact("hp", &.{z}), &.{
        input.relation("p", &.{x}),
        input.relation("m", &.{z}),
    }, .materialized);
    _ = try views.define(&db, input.fact("hg", &.{z}), &.{
        input.relation("g", &.{w}),
        input.relation("m", &.{z}),
    }, .materialized);
    _ = try views.define(&db, input.fact("cr", &.{ x, s }), &.{
        input.relation("r", &.{ x, y0 }),
        input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
    }, .materialized);

    const folded = try views.fold(&db, &.{input.relation("q", &.{ x, w, t })}, &.{
        input.rule(input.fact("q", &.{ x, w, t }), &.{
            input.relation("p", &.{x}),
            input.relation("g", &.{w}),
            input.setof(y, &.{input.relation("r", &.{ x, y })}, s),
            input.relation("sum", &.{ s, t }),
        }),
    });
    defer folded.deinit();
    // Dropping an instance answers less, which is sound and is not maximal.
    try testing.expectEqual(Guarantee.contained, folded.guarantee);
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{"a w 7"});
}

test "a folded answer lists answers in the order the caller asks for, under its names" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    _ = try declareEvenPathViews(&views, &db);
    const folded = try foldEvenPaths(&views, &db);
    defer folded.deinit();

    // One plan serves every order: the order is not part of the fold.
    var by_default = try views.answer(&db, folded, &.{});
    defer by_default.deinit();
    try expectOrderedTuples(&by_default, &.{ "a c", "a e", "b d", "c e" });
    try testing.expectEqualStrings("b", try by_default.answers.items[2].getAtom("X"));
    try testing.expectEqualStrings("d", try by_default.answers.items[2].getAtom("Y"));
    var descending = try views.answer(&db, folded, &.{input.descending("X")});
    defer descending.deinit();
    try expectOrderedTuples(&descending, &.{ "c e", "b d", "a c", "a e" });
    // `Z` is the query's too, but only its rules say it: no answer lists it.
    try testing.expectError(
        errors.Error.UnknownVariable,
        views.answer(&db, folded, &.{input.ascending("Z")}),
    );

    // The same question in other names reuses the plan and gets its own
    // names back, not the ones the plan was first folded under.
    const a = input.variable("A");
    const b = input.variable("B");
    const c = input.variable("C");
    const renamed = try views.fold(&db, &.{input.relation("q", &.{ a, b })}, &.{
        input.rule(input.fact("q", &.{ a, b }), &.{input.relation("edge", &.{ a, b })}),
        input.rule(input.fact("q", &.{ a, c }), &.{
            input.relation("edge", &.{ a, b }),
            input.relation("q", &.{ b, c }),
        }),
    });
    defer renamed.deinit();
    try testing.expect(renamed.reused);
    var reused = try views.answer(&db, renamed, &.{input.descending("B")});
    defer reused.deinit();
    try expectOrderedTuples(&reused, &.{ "a e", "c e", "b d", "a c" });
    try testing.expectEqualStrings("A", reused.answers.items[0].bindings.items[0].name);
    try testing.expectEqualStrings("B", reused.answers.items[0].bindings.items[1].name);
}

test "a declared view answers a query about relations the database no longer has" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    _ = try declareEvenPathViews(&views, &db);

    const folded = try foldEvenPaths(&views, &db);
    defer folded.deinit();
    // A view remembers pairs two edges apart and nothing else, so no plan over
    // it answers every path. Maximal containment is the whole claim, and it is
    // the caller's to accept.
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
    try testing.expect(!folded.reused);

    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{ "a c", "a e", "b d", "c e" });

    // What the guarantee does not say on its own: where the loss is. One
    // relation is derived rather than read, and no canonical aggregate view of
    // it was available, so that is the place an answer could have gone.
    var reconstructed = try views.reconstructions(&db, folded);
    defer reconstructed.deinit();
    try testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try testing.expectEqualStrings("edge", reconstructed.items[0].predicate);
    try testing.expectEqual(@as(usize, 2), reconstructed.items[0].arity);
    try testing.expect(!reconstructed.items[0].exact);

    const explanation = try views.explain(&db, folded);
    defer allocator.free(explanation);
    try testing.expect(std.mem.startsWith(u8, explanation, "guarantee: maximally contained"));

    // Running a plan changes nothing here. It ran on a copy, so none of the
    // relations it reconstructed joined this database.
    var direct = try transaction.query(&db, &.{input.relation("v", &.{
        input.variable("X"),
        input.variable("Y"),
    })}, &.{});
    defer direct.deinit();
    try testing.expectEqual(@as(usize, 3), direct.answers.items.len);
}

test "a query inside the availability boundary is its own plan, and a hybrid one is not" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const c = input.variable("C");

    // The caller still has `label` and says so. `r` is gone, and a canonical
    // aggregate view of it — the relation copied — is what remains.
    try loadSource(&db, "label(a, red). label(b, blue). copy(a, one). copy(b, two).");
    try views.declareBaseAvailable(&db, "label", 2);
    _ = try views.define(
        &db,
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
    try loadSource(&db, "r(a, three). r(X, X) :- copy(X, Y).");

    // Nothing was reconstructed, because nothing had to be: the query reads
    // what the policy declared. That is the only way to earn `equivalent`.
    const plain = try views.fold(&db, &.{input.relation("label", &.{ x, c })}, &.{});
    defer plain.deinit();
    try testing.expectEqual(Guarantee.equivalent, plain.guarantee);
    var plain_answers = try views.answer(&db, plain, &.{});
    defer plain_answers.deinit();
    try testing.expectEqual(@as(usize, 2), plain_answers.answers.items.len);

    // Half read and half reconstructed. The guarantee falls to maximal
    // containment because a reconstruction is in general a subset — and here
    // it happens not to be, which is what the per-relation account says and
    // the guarantee alone cannot.
    const hybrid = try views.fold(&db, &.{
        input.relation("r", &.{ x, y }),
        input.relation("label", &.{ x, c }),
    }, &.{});
    defer hybrid.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, hybrid.guarantee);
    var reconstructed = try views.reconstructions(&db, hybrid);
    defer reconstructed.deinit();
    try testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try testing.expectEqualStrings("r", reconstructed.items[0].predicate);
    try testing.expect(reconstructed.items[0].exact);

    var joined = try views.answer(&db, hybrid, &.{});
    defer joined.deinit();
    try expectTuples(&joined, &.{ "a one red", "b two blue" });

    // The leftover fact and the rule's two derivations are all still here, and
    // all three would have joined the plan's reconstruction of `r` had the
    // plan run against this database rather than against a copy of what the
    // catalog admits.
    var here = try transaction.query(&db, &.{input.relation("r", &.{ x, y })}, &.{});
    defer here.deinit();
    try testing.expectEqual(@as(usize, 3), here.answers.items.len);
}

/// Two canonical aggregate views of one relation: `wide` is the relation
/// copied and `narrow` is it grouped by its first column. Both remember all of
/// `r` — Lemma 6.4.2 — so a plan may read either and get `r` itself back,
/// which is exactly what makes choosing between them a cost question and only
/// a cost question. `wide` is declared first, so preferring `narrow` can only
/// be cost and never declaration order.
fn declareInterchangeableViews(views: *ViewSelection, db: *database.Database) !void {
    const x1 = input.variable("X1");
    const x2 = input.variable("X2");
    const y2 = input.variable("Y2");
    const s = input.variable("S");
    _ = try views.define(
        db,
        input.fact("wide", &.{ x1, x2 }),
        &.{input.relation("r", &.{ x1, x2 })},
        .materialized,
    );
    _ = try views.define(db, input.fact("narrow", &.{ x1, s }), &.{
        input.relation("r", &.{ x1, x2 }),
        input.setof(y2, &.{input.relation("r", &.{ x1, y2 })}, s),
    }, .materialized);
}

test "cost picks between views that reconstruct one relation exactly, and picks the same way twice" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try declareInterchangeableViews(&views, &db);

    // `r` holds two values for one key, so the grouped view stores one tuple
    // where the copy stores two. Both give `r` back whole.
    try loadSource(&db, "wide(a, one). wide(a, two). narrow(a, [one, two]).");

    const goals = [_]input.Goal{input.relation("r", &.{
        input.atom("a"),
        input.variable("V"),
    })};
    const folded = try views.fold(&db, &goals, &.{});
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    const explanation = try views.explain(&db, folded);
    defer allocator.free(explanation);
    // The smaller extension is read and the larger is left out of the plan.
    try testing.expect(std.mem.indexOf(
        u8,
        explanation,
        "being the smallest of them: narrow@1/2",
    ) != null);
    try testing.expect(std.mem.indexOf(u8, explanation, "wide@0/2") == null);

    // Cost chose, and it did not choose a weaker plan to do it: the relation
    // is still reconstructed exactly, and the answers are the ones `r` has.
    var reconstructed = try views.reconstructions(&db, folded);
    defer reconstructed.deinit();
    try testing.expectEqual(@as(usize, 1), reconstructed.items.len);
    try testing.expect(reconstructed.items[0].exact);

    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{ "one", "two" });

    // Folded again from nothing — no cached plan to hand back — the same
    // catalog over the same data reaches the same decisions in the same order.
    // A cost decision that did not would be a plan cache holding one of two
    // programs depending on when it was asked. What is compared is the record
    // of what the fold did rather than the whole rendering, because a plan's
    // variables carry their identities and a second fold opens a scope of its
    // own: the same plan twice prints different numbers by construction.
    views.clear();
    const again = try views.fold(&db, &goals, &.{});
    defer again.deinit();
    const repeated = try views.explain(&db, again);
    defer allocator.free(repeated);
    const marker = "transformations:\n";
    const decisions = explanation[std.mem.indexOf(u8, explanation, marker).?..];
    const decisions_again = repeated[std.mem.indexOf(u8, repeated, marker).?..];
    try testing.expectEqualStrings(decisions, decisions_again);
}

test "a folded plan walks a stored list and answers what the membership rules derive" {
    // `$member` reaches the evaluator as a walk over the one list a stored
    // tuple bound, not as the three rules the plan renders. The two have to
    // agree on every list an extension can hold, and an embedder's stored
    // extension can hold lists no `setof` would have collected: one holding a
    // value twice, one that never reaches `[]`, one that is empty, and one
    // whose elements are lists themselves. The same rules, written as a
    // program over the same tuples, say what the answers must be.
    const allocator = testing.allocator;
    const stored =
        \\narrow(k1, [a, b, a]). narrow(k2, a!b). narrow(k3, []).
        \\narrow(k4, [[a, b], c]). narrow(k5, [b]).
    ;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const x1 = input.variable("X1");
    _ = try views.define(&db, input.fact("narrow", &.{ x1, input.variable("S") }), &.{
        input.relation("r", &.{ x1, input.variable("X2") }),
        input.setof(input.variable("Y2"), &.{input.relation("r", &.{
            x1,
            input.variable("Y2"),
        })}, input.variable("S")),
    }, .materialized);
    try loadSource(&db, stored);

    const folded = try views.fold(&db, &.{input.relation("r", &.{
        input.variable("K"),
        input.variable("V"),
    })}, &.{});
    defer folded.deinit();
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();

    var direct: database.Database = .init(allocator);
    defer direct.deinit();
    try loadSource(&direct, stored);
    var expected = try runSource(&direct,
        \\member(X, X!R) :- R = [].
        \\member(X, X!R) :- member(O, R).
        \\member(O, F!R) :- member(O, R).
        \\r(K, V) :- narrow(K, S), member(V, S).
        \\r(K, V)?
    );
    defer expected.deinit();
    const expected_tuples = try answerTuples(&expected.query);
    defer freeLines(expected_tuples);

    try testing.expectEqual(@as(usize, 5), expected_tuples.len);
    try expectTuples(&answers, expected_tuples);
}

test "views that reconstruct one relation equally well are chosen between by declaration order" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try declareInterchangeableViews(&views, &db);

    // One value for the one key, so the copy and the grouping store one tuple
    // each and cost has nothing to say. Something still has to decide, and it
    // has to decide the same way every time, so it is the first declaration.
    try loadSource(&db, "wide(a, one). narrow(a, [one]).");

    const folded = try views.fold(&db, &.{input.relation("r", &.{
        input.atom("a"),
        input.variable("V"),
    })}, &.{});
    defer folded.deinit();
    const explanation = try views.explain(&db, folded);
    defer allocator.free(explanation);
    try testing.expect(std.mem.indexOf(
        u8,
        explanation,
        "being the smallest of them: wide@0/2",
    ) != null);
    try testing.expect(std.mem.indexOf(u8, explanation, "narrow@1/2") == null);

    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 1), answers.answers.items.len);
}

test "a folded plan is reused until the views or the rules it was folded against move on" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const view = try declareEvenPathViews(&views, &db);

    const first = try foldEvenPaths(&views, &db);
    defer first.deinit();
    try testing.expect(!first.reused);
    const second = try foldEvenPaths(&views, &db);
    defer second.deinit();
    try testing.expect(second.reused);
    var stats = views.stats();
    try testing.expectEqual(@as(usize, 1), stats.cached_plans);
    try testing.expectEqual(@as(usize, 1), stats.plan_hits);
    try testing.expectEqual(@as(usize, 1), stats.plan_misses);
    try testing.expectEqual(@as(usize, 0), stats.plan_invalidations);

    // Withdrawing the extension changes what every plan folded against this
    // catalog was allowed to read, so both handles stop naming anything. A
    // handle that survived would name whichever plan later took its place.
    views.setAvailability(view, .withheld);
    try testing.expectError(error.StalePlan, views.explain(&db, first));
    try testing.expectError(error.StalePlan, views.answer(&db, second, &.{}));

    const withheld = try foldEvenPaths(&views, &db);
    defer withheld.deinit();
    try testing.expectEqual(Guarantee.unsupported, withheld.guarantee);
    // No plan at all rather than an empty one, which is the distinction the
    // whole interface is shaped around: there is nothing to run.
    try testing.expectError(error.PlanNotExecutable, views.answer(&db, withheld, &.{}));
    try expectExplained(&views, &db, withheld, "unmet preconditions");
    stats = views.stats();
    try testing.expectEqual(@as(usize, 1), stats.plan_invalidations);

    // Restoring it does not restore the discarded plan: the question is folded
    // again, and it comes back with the guarantee it had.
    views.setAvailability(view, .materialized);
    const restored = try foldEvenPaths(&views, &db);
    defer restored.deinit();
    try testing.expect(!restored.reused);
    try testing.expectEqual(Guarantee.maximally_contained, restored.guarantee);

    // A rule addition invalidates for a different reason — a published
    // definition is a rule's, and this cache cannot tell which plans read one
    // — so it discards them all.
    try loadSource(&db, "reachable(X) :- v(X, Y).");
    try testing.expectError(error.StalePlan, views.explain(&db, restored));
    (try foldEvenPaths(&views, &db)).deinit();
    // Three discards: the withdrawal, the restoration, and the rule. Restoring
    // an availability is a change like any other — the cache cannot tell that
    // it undid the previous one, and a stamp that could would be a stamp that
    // had to understand what it was counting.
    try testing.expectEqual(@as(usize, 3), views.stats().plan_invalidations);
}

/// One folded answer, as sorted tuples. The error is passed through rather
/// than caught, because a change can make a question unanswerable and *which*
/// error comes back is part of what a kept reconstruction has to reproduce.
fn foldedTuples(
    views: *ViewSelection,
    db: *database.Database,
    goals: []const input.Goal,
) ![][]u8 {
    const folded = try views.fold(db, goals, &.{});
    defer folded.deinit();
    var answers = try views.answer(db, folded, &.{});
    defer answers.deinit();
    return answerTuples(&answers);
}

/// Asks the question twice: once against whatever the selection has kept,
/// and once with the plan cache cleared, which is the reference path —
/// nothing cached, everything rebuilt from current state. The two must agree.
///
/// This is the shared rule the whole engine rests on, applied to folding: a
/// full rebuild stays available and an incremental path is only ever allowed
/// to be faster than it.
fn expectKeptMatchesRebuilt(
    views: *ViewSelection,
    db: *database.Database,
    goals: []const input.Goal,
) !void {
    const kept = foldedTuples(views, db, goals);
    defer if (kept) |lines| freeLines(lines) else |_| {};
    views.clear();
    const rebuilt = foldedTuples(views, db, goals);
    defer if (rebuilt) |lines| freeLines(lines) else |_| {};
    if (kept) |kept_lines| {
        const rebuilt_lines = try rebuilt;
        try testing.expectEqual(rebuilt_lines.len, kept_lines.len);
        for (kept_lines, rebuilt_lines) |mine, theirs|
            try testing.expectEqualStrings(theirs, mine);
    } else |kept_error| {
        try testing.expectError(kept_error, rebuilt);
    }
}

fn expectFoldedRowCount(
    views: *ViewSelection,
    db: *database.Database,
    goals: []const input.Goal,
    expected: usize,
) !void {
    const lines = try foldedTuples(views, db, goals);
    defer freeLines(lines);
    try testing.expectEqual(expected, lines.len);
}

test "a kept reconstruction answers exactly what a rebuilt one answers, after each kind of change" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const question = [_]input.Goal{input.relation("r", &.{ x, y })};

    // A canonical aggregate view of a relation that is gone, so a plan reading
    // it gets `r` itself back — Lemma 6.4.2. Beside it, a withheld view of a
    // relation this question never mentions, which is where a fact can arrive
    // under a name no plan is allowed to read.
    const copied = try views.define(
        &db,
        input.fact("copied", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
        .materialized,
    );
    _ = try views.define(
        &db,
        input.fact("linked", &.{ x, y }),
        &.{input.relation("s", &.{ x, y })},
        .withheld,
    );
    try addFact(&db, "copied", &.{ input.atom("a"), input.atom("one") });

    const first = try views.fold(&db, &question, &.{});
    defer first.deinit();
    try testing.expect(!first.reused);
    {
        var answers = try views.answer(&db, first, &.{});
        defer answers.deinit();
        try testing.expectEqual(@as(usize, 1), answers.answers.items.len);
    }

    // A fact under a name the catalog already admits, which is the one change
    // nothing a folded plan is stamped against can see. The plan is still the
    // right plan — it is reused, nothing was invalidated, and the handle from
    // before the fact still names it — and the extension it reads is one tuple
    // larger, so the answer is one row larger. Everything kept between two
    // calls has to notice a change that moves no stamp.
    try addFact(&db, "copied", &.{ input.atom("b"), input.atom("two") });
    const again = try views.fold(&db, &question, &.{});
    defer again.deinit();
    try testing.expect(again.reused);
    try testing.expectEqual(@as(usize, 0), views.stats().plan_invalidations);
    {
        var answers = try views.answer(&db, first, &.{});
        defer answers.deinit();
        try testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // A fact under a withheld name changes nothing, and has to change nothing
    // for the same reason the first one had to change something: the boundary
    // is what the catalog admits, not what the database holds.
    try addFact(&db, "linked", &.{ input.atom("z"), input.atom("zed") });
    try expectFoldedRowCount(&views, &db, &question, 2);
    try expectKeptMatchesRebuilt(&views, &db, &question);

    try addFact(&db, "copied", &.{ input.atom("c"), input.atom("three") });
    try expectFoldedRowCount(&views, &db, &question, 3);
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // A retraction, which moves the same nothing an insertion does.
    try testing.expect(try transaction.retract(&db, &.{input.relation(
        "copied",
        &.{ input.atom("c"), input.atom("three") },
    )}));
    try expectFoldedRowCount(&views, &db, &question, 2);
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // A view made unreadable. The one extension that remembers `r` is
    // withdrawn, so there is no plan at all — not a plan answering from what
    // was readable a moment ago.
    views.setAvailability(copied, .withheld);
    try testing.expectError(error.PlanNotExecutable, foldedTuples(&views, &db, &question));
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // And made readable again, which folds the question afresh rather than
    // restoring what was discarded.
    views.setAvailability(copied, .materialized);
    try expectFoldedRowCount(&views, &db, &question, 2);
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // A definition added, over a relation this question never mentions.
    _ = try views.define(
        &db,
        input.fact("marked", &.{x}),
        &.{input.relation("mark", &.{x})},
        .withheld,
    );
    try expectFoldedRowCount(&views, &db, &question, 2);
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // A rule added to the database, which the plan runs without.
    try loadSource(&db, "pair(X, Y) :- copied(X, Y).");
    try expectFoldedRowCount(&views, &db, &question, 2);
    try expectKeptMatchesRebuilt(&views, &db, &question);

    // And that rule published as a view, which is a definition arriving from
    // the program rather than from the caller.
    try materialization.ensureMaterialized(&db);
    _ = try views.publish(&db, "pair", 2, .materialized);
    try expectFoldedRowCount(&views, &db, &question, 2);
    try expectKeptMatchesRebuilt(&views, &db, &question);
}

test "asking a folded question twice grows neither the database nor what it interned" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    const question = [_]input.Goal{input.relation("r", &.{ x, y })};

    _ = try views.define(
        &db,
        input.fact("copied", &.{ x, y }),
        &.{input.relation("r", &.{ x, y })},
        .materialized,
    );
    try loadSource(&db, "copied(a, one). copied(b, two).");

    const folded = try views.fold(&db, &question, &.{});
    defer folded.deinit();
    var warmup = try views.answer(&db, folded, &.{});
    warmup.deinit();

    const facts = db.facts.len();
    const closure = db.maintenanceStats().closure_facts;
    const interned = db.internStats();
    for (0..4) |_| {
        (try views.fold(&db, &question, &.{})).deinit();
        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
    // A folded plan reconstructs relations this database deliberately does not
    // have. Whatever it keeps between calls to avoid rebuilding them is kept
    // somewhere else: the same question asked five times leaves this database
    // holding exactly what one question left it holding.
    try testing.expectEqual(facts, db.facts.len());
    try testing.expectEqual(closure, db.maintenanceStats().closure_facts);
    try testing.expectEqual(interned.value_entries, db.internStats().value_entries);
    try testing.expectEqual(interned.scalar_entries, db.internStats().scalar_entries);
}

test "a maintained predicate published as a view answers without its own base facts" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();

    try loadSource(&db,
        \\edge(a, b). edge(b, c). edge(c, d).
        \\two(X, Z) :- edge(X, Y), edge(Y, Z).
    );
    try materialization.ensureMaterialized(&db);

    // The definition comes from the rule; the extension is what maintenance
    // already keeps under `two/2`. Nothing is copied and nothing is declared
    // twice.
    _ = try views.publish(&db, "two", 2, .materialized);
    const folded = try foldEvenPaths(&views, &db);
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);

    // `edge` is still in this database and the rule deriving `two` still runs
    // in it, and neither is in the copy the plan ran on. Had either been, the
    // answers would have been the real transitive closure — six pairs — rather
    // than the paths of even length the view remembers.
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try expectTuples(&answers, &.{ "a c", "b d" });

    var real = try runSource(&db, "two(X, Y)?");
    defer real.deinit();
    try testing.expectEqual(@as(usize, 2), real.query.answers.items.len);

    // The definition was the rule's, and the rules have moved on. Folding
    // against it now would reason from something the database no longer says.
    try loadSource(&db, "two(X, Y) :- edge(X, Y).");
    try testing.expectError(error.StaleViewDefinition, foldEvenPaths(&views, &db));
}

test "two readable extensions of one name are refused at selection, not after a fold" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");

    try addFact(&db, "v", &.{ input.atom("a"), input.atom("b") });
    _ = try views.define(
        &db,
        input.fact("v", &.{ x, y }),
        &.{input.relation("edge", &.{ x, y })},
        .materialized,
    );
    const rival = try views.define(
        &db,
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
    try testing.expectError(error.AmbiguousViewName, views.fold(&db, &goals, &.{}));
    try testing.expectError(
        error.AmbiguousViewName,
        views.fold(&db, &.{input.relation("unrelated", &.{x})}, &.{}),
    );
    try testing.expectEqual(@as(usize, 0), views.stats().plan_misses);

    // Withholding one leaves one readable extension of that name.
    views.setAvailability(rival, .withheld);
    const folded = try views.fold(&db, &goals, &.{});
    defer folded.deinit();
    try testing.expectEqual(Guarantee.maximally_contained, folded.guarantee);
}

/// The folding path end to end on the smallest database that exercises it:
/// one view, one stored tuple, one fold, and the three things a caller can do
/// with what comes back.
fn publicFoldingAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const x = input.variable("X");
    const y = input.variable("Y");
    try addFact(&db, "v", &.{ input.atom("a"), input.atom("b") });
    _ = try views.define(
        &db,
        input.fact("v", &.{ x, y }),
        &.{input.relation("edge", &.{ x, y })},
        .materialized,
    );

    const folded = try views.fold(&db, &.{input.relation("edge", &.{ x, y })}, &.{});
    defer folded.deinit();
    if (folded.guarantee != .maximally_contained) return error.UnexpectedGuarantee;
    allocator.free(try views.explain(&db, folded));
    var reconstructed = try views.reconstructions(&db, folded);
    reconstructed.deinit();
    var answers = try views.answer(&db, folded, &.{});
    answers.deinit();
}

test "declaring a view, folding and running the plan release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(publicFoldingAllocationScenario);
}

/// One view, and a question folded against it. Used by the tests below that
/// care about what a plan keeps rather than about what it answers.
fn declareCopiedView(views: *ViewSelection, db: *database.Database) !void {
    const x = input.variable("X");
    const y = input.variable("Y");
    _ = try views.define(
        db,
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
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try declareCopiedView(&views, &db);
    try addFact(&db, "copied", &.{ input.atom("a"), input.atom("one") });

    const folded = try views.fold(&db, &copied_question, &.{});
    defer folded.deinit();
    // Nothing is kept until a plan is run: folding decides what to read, and
    // deciding does not read it.
    try testing.expectEqual(@as(usize, 0), views.stats().kept_reconstructions);

    for (0..3) |_| {
        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try testing.expectEqual(@as(usize, 1), answers.answers.items.len);
    }
    var stats = views.stats();
    try testing.expectEqual(@as(usize, 1), stats.kept_reconstructions);
    try testing.expectEqual(@as(usize, 1), stats.reconstruction_misses);
    try testing.expectEqual(@as(usize, 2), stats.reconstruction_hits);

    // A fact under a readable name leaves the plan alone and takes the
    // reconstruction: the handle still names the plan, the plan cache reports
    // no invalidation, and the next answer is derived again.
    try addFact(&db, "copied", &.{ input.atom("b"), input.atom("two") });
    {
        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
    stats = views.stats();
    try testing.expectEqual(@as(usize, 0), stats.plan_invalidations);
    try testing.expectEqual(@as(usize, 2), stats.reconstruction_misses);
    try testing.expectEqual(@as(usize, 2), stats.reconstruction_hits);

    // A catalog change takes both, and the handle with them, which is the
    // distinction the two stamps exist to draw.
    _ = try views.define(
        &db,
        input.fact("marked", &.{input.variable("X")}),
        &.{input.relation("mark", &.{input.variable("X")})},
        .withheld,
    );
    try testing.expectError(error.StalePlan, views.answer(&db, folded, &.{}));
    (try views.fold(&db, &copied_question, &.{})).deinit();
    stats = views.stats();
    try testing.expectEqual(@as(usize, 1), stats.plan_invalidations);
    try testing.expectEqual(@as(usize, 0), stats.kept_reconstructions);

    // And clearing the cache is what gives the memory back, which is the one
    // control an embedder has over reconstructions it is no longer asking for.
    const refolded = try views.fold(&db, &copied_question, &.{});
    defer refolded.deinit();
    var again = try views.answer(&db, refolded, &.{});
    again.deinit();
    try testing.expectEqual(@as(usize, 1), views.stats().kept_reconstructions);
    views.clear();
    try testing.expectEqual(@as(usize, 0), views.stats().kept_reconstructions);
}

test "the cache holds a bounded number of reconstructions and drops the coldest" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    const y = input.variable("Y");
    try declareCopiedView(&views, &db);
    try addFact(&db, "copied", &.{ input.atom("a"), input.atom("one") });

    // Six questions of one plan's shape, each keyed on its own constant, so
    // each folds to a plan of its own and each plan wants a reconstruction.
    const constants = [_][]const u8{ "a", "b", "c", "d", "e", "f" };
    var folds: [constants.len]Fold = undefined;
    var folded: usize = 0;
    defer for (folds[0..folded]) |each| each.deinit();
    for (constants, &folds) |constant, *slot| {
        const goals = [_]input.Goal{input.relation("r", &.{ input.atom(constant), y })};
        slot.* = try views.fold(&db, &goals, &.{});
        folded += 1;
        var answers = try views.answer(&db, slot.*, &.{});
        answers.deinit();
    }
    const stats = views.stats();
    try testing.expectEqual(@as(usize, constants.len), stats.cached_plans);
    // The plans are all still here — a plan is small and discarding one costs
    // a fold — and the reconstructions are not, because each is a database.
    try testing.expect(stats.kept_reconstructions < constants.len);
    try testing.expectEqual(@as(usize, 6), stats.reconstruction_misses);

    // Every plan still answers, whether or not its reconstruction survived.
    for (constants, folds) |constant, each| {
        var answers = try views.answer(&db, each, &.{});
        defer answers.deinit();
        const expected: usize = if (std.mem.eql(u8, constant, "a")) 1 else 0;
        try testing.expectEqual(expected, answers.answers.items.len);
    }
}

/// A fold, an answer, a fact under the name the plan reads, and another
/// answer: the whole of what F7 added, in the smallest database that has it.
fn keptReconstructionAllocationScenario(allocator: std.mem.Allocator) !void {
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try declareCopiedView(&views, &db);
    try addFact(&db, "copied", &.{ input.atom("a"), input.atom("one") });

    const folded = try views.fold(&db, &copied_question, &.{});
    defer folded.deinit();
    var first = try views.answer(&db, folded, &.{});
    first.deinit();

    try addFact(&db, "copied", &.{ input.atom("b"), input.atom("two") });
    var refreshed = try views.answer(&db, folded, &.{});
    const rows = refreshed.answers.items.len;
    refreshed.deinit();
    if (rows != 2) return error.UnexpectedResult;

    var reused = try views.answer(&db, folded, &.{});
    reused.deinit();
}

test "refreshing and reusing a kept reconstruction release every allocation on failure" {
    try test_support.expectEveryAllocationFailureReleased(keptReconstructionAllocationScenario);
}

test "an allocation failure answering a folded question leaves the next answer correct" {
    // The sweep above says a failure releases what it allocated. This says
    // what the selection is afterwards, which a sweep cannot: a half-derived
    // reconstruction must not be the thing a later call answers from.
    var failing: std.testing.FailingAllocator = .init(testing.allocator, .{});
    var db: database.Database = .init(failing.allocator());
    defer db.deinit();
    var views: ViewSelection = .init(failing.allocator());
    defer views.deinit();
    try declareCopiedView(&views, &db);
    try addFact(&db, "copied", &.{ input.atom("a"), input.atom("one") });
    try addFact(&db, "copied", &.{ input.atom("b"), input.atom("two") });
    const folded = try views.fold(&db, &copied_question, &.{});
    defer folded.deinit();

    var offset: usize = 0;
    while (offset < 400) : (offset += 1) {
        // Fail one allocation of the next answer, wherever in it that lands:
        // deriving the reconstruction the first time round the loop, solving
        // against a kept one afterwards.
        failing.fail_index = failing.alloc_index + offset;
        if (views.answer(&db, folded, &.{})) |result| {
            var answers = result;
            answers.deinit();
        } else |_| {}
        failing.fail_index = std.math.maxInt(usize);

        var answers = try views.answer(&db, folded, &.{});
        defer answers.deinit();
        try testing.expectEqual(@as(usize, 2), answers.answers.items.len);
    }
}

test "a fold's question and program are checked against the schemas" {
    const allocator = testing.allocator;
    var db: database.Database = .init(allocator);
    defer db.deinit();
    var views: ViewSelection = .init(allocator);
    defer views.deinit();
    try declareCopiedView(&views, &db);
    try program.declareSchema(&db, input.schema("r", &.{
        input.column(null, .atom),
        input.column(null, .atom),
    }));
    try addFact(&db, "copied", &.{ input.atom("a"), input.atom("one") });

    try testing.expectError(errors.Error.IllTyped, views.fold(
        &db,
        &.{input.relation("r", &.{input.variable("X")})},
        &.{},
    ));
    try testing.expectError(errors.Error.IllTyped, views.fold(
        &db,
        &.{input.relation("r", &.{ input.variable("X"), input.integer(1) })},
        &.{},
    ));
    const folded = try views.fold(&db, &.{
        input.relation("r", &.{ input.variable("X"), input.variable("Y") }),
        input.typeTest(input.variable("Y"), .atom),
    }, &.{});
    defer folded.deinit();
    var answers = try views.answer(&db, folded, &.{});
    defer answers.deinit();
    try testing.expectEqual(@as(usize, 1), answers.answers.items.len);
}
