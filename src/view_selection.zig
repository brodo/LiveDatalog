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
        defer staging.deinit();
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
