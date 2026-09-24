//! What a statement does to a database, and the transaction it does it in.
//!
//! A program is a sequence of statements, each of which either commits
//! completely or leaves the database exactly as it was. Most of the
//! operations here are the compiled form of those statements — they take
//! clauses already compiled against the database rather than caller
//! descriptors. The exceptions are the statements that evaluate: `query`,
//! `retract` and `explain` take the caller's goals and run the whole
//! statement, copy and all, because every caller runs them the same way.
//! `Transaction` is what stages a run of assertions.

const std = @import("std");
const compile = @import("compile.zig");
const database = @import("database.zig");
const errors = @import("errors.zig");
const input = @import("input.zig");
const materialization = @import("materialization.zig");
const relation_store = @import("relation_store.zig");
const results = @import("results.zig");
const schema = @import("schema.zig");
const syntax = @import("syntax.zig");
const typing = @import("typing.zig");
const update = @import("update.zig");
const validation = @import("validation.zig");

/// Answers `goals`, listed in the order `order` asks for, without changing
/// `db`: what `Jatalog.query` and a program's query statement both are.
///
/// The goals are compiled and evaluated on a copy that is never committed, so
/// that the names and values they mention but `db` does not hold stay out of
/// it. What evaluating them cost does not stay out: see "Evaluation work" in
/// CONTEXT.md, which is why the copy goes through `Database.release` whether
/// or not the query succeeds.
pub fn query(
    db: *database.Database,
    goals: []const input.Goal,
    order: []const input.SortKey,
) !results.QueryResult {
    var staging = try stage(db);
    defer db.release(&staging);
    const compiled = try compile.compileGoals(&staging, goals);
    defer freeClauses(&staging, compiled);
    return queryClauses(&staging, compiled, order);
}

/// Removes the base facts `goals` resolve to, returning whether there were
/// any: what `Jatalog.retract` and a program's retraction both are.
///
/// Resolving the goals is a query, run on a copy that is released rather
/// than committed, and only the facts it finds cross back — through
/// `commitRetraction`, and so through the ordinary update path.
pub fn retract(db: *database.Database, goals: []const input.Goal) !bool {
    var staging = try stage(db);
    defer db.release(&staging);
    const compiled = try compile.compileGoals(&staging, goals);
    defer freeClauses(&staging, compiled);
    var removed = try resolveRetraction(&staging, compiled);
    defer removed.deinit();
    if (removed.len() == 0) return false;
    try commitRetraction(db, &removed);
    return true;
}

/// Renders the plan `goals` would be solved under, on a copy of `db` made
/// exactly as `query` makes one, and answers nothing. The caller owns the
/// returned text.
pub fn explain(db: *database.Database, goals: []const input.Goal) ![]u8 {
    var staging = try stage(db);
    defer db.release(&staging);
    const compiled = try compile.compileGoals(&staging, goals);
    defer freeClauses(&staging, compiled);
    return explainClauses(&staging, compiled);
}

/// The copy a statement that evaluates runs on. `db` is materialized first,
/// so that the copy starts from a clean closure and shares its value
/// identifiers: a closure materialized on the copy instead would be rebuilt
/// by every statement and thrown away with it.
fn stage(db: *database.Database) !database.Database {
    try materialization.ensureMaterialized(db);
    return db.clone();
}

fn freeClauses(db: *database.Database, clauses: []syntax.Clause) void {
    for (clauses) |clause| syntax.freeClauseTree(db.allocator, clause);
    db.allocator.free(clauses);
}

/// Applies the base facts a retraction resolved its goals to, which
/// `resolveRetraction` produced against a staging copy of `db`. They are
/// applied to a fresh clone rather than to `db` itself, so that a failure
/// part-way through leaves the database untouched — and they take the ordinary
/// update path, which is what makes a retraction and a batch deletion the same
/// operation on the closure.
///
/// Only the facts cross over. The staging copy the goals were evaluated on is
/// discarded with everything its evaluation interned, which is how values a
/// retraction mentions but the database does not hold stay out of it.
pub fn commitRetraction(db: *database.Database, removed: *const relation_store.RelationStore) !void {
    var committed = try db.clone();
    defer committed.deinit();
    _ = try update.apply(&committed, .{ .resolved = removed }, &.{});
    try materialization.verifyShadow(&committed);
    db.commit(&committed);
}

/// Asserts one ground fact on behalf of `contributor`, or of the direct
/// contributor when that is null (see "Contributor" in CONTEXT.md).
pub fn addFactExpr(db: *database.Database, value: syntax.Expr, contributor: ?[]const u8) !void {
    const fact = try db.applyInsertion(value, contributor) orelse return;
    const key: relation_store.PredicateKey = .{ .name = fact.predicate, .arity = fact.terms.len };
    db.markBaseChanged(key) catch |err| {
        // The insertion comes back out, and so does the record of who
        // asserted it. A statement leaves the fact store either as it was or
        // with its fact in it and nothing between, which is what lets a run
        // of assertions share one transaction and still be undone one
        // statement at a time: see `Database.rollback`, which has no way to
        // put a fact back.
        db.revokeInsertion();
        return err;
    };
}

/// Replaces what `contributor` asserts with `facts`, and returns whether the
/// base facts changed: what `Jatalog.setContribution` is. See "Contributor" in
/// CONTEXT.md.
///
/// Staged on a copy of `db` and committed only once it has succeeded, so a
/// contribution that fails — a fact that is not ground, one its schema
/// rejects — fails whole and changes neither the facts nor the records of who
/// asserts them. Only the facts that became present or absent take the update
/// path; see `update.contribute`.
pub fn contribute(db: *database.Database, contributor: []const u8, facts: []const input.Relation) !bool {
    var staging = try db.clone();
    defer staging.deinit();
    const compiled = try staging.allocator.alloc(syntax.Expr, facts.len);
    var built: usize = 0;
    defer {
        for (compiled[0..built]) |expression| syntax.freeExpr(staging.allocator, expression);
        staging.allocator.free(compiled);
    }
    for (facts, compiled) |fact, *slot| {
        slot.* = try compile.compileRelation(&staging, fact.predicate, fact.terms, false);
        built += 1;
    }
    const outcome = try update.contribute(&staging, contributor, compiled);
    try materialization.verifyShadow(&staging);
    if (outcome.recorded) db.commit(&staging);
    return outcome.changed > 0;
}

/// Adds a rule whose body may contain aggregate clauses. On success the
/// database owns `head` and every clause in `body`; on failure the caller
/// retains ownership. The body slice itself is only borrowed.
pub fn addRuleClauses(db: *database.Database, head: syntax.Expr, body: []const syntax.Clause) !void {
    const seed_argument = try validation.validateRule(db, head, body);
    try typing.checkRule(db, head, body);
    const owned_body = try validation.orderClauses(db, body);
    errdefer db.allocator.free(owned_body);
    try db.eval.rules.append(db.allocator, .{
        .id = db.eval.next_rule_id,
        .head = head,
        .body = owned_body,
        .seed_argument = seed_argument,
    });
    // Past here the rule is installed and every failure takes it back out,
    // which is both halves of what this promises: the caller keeps ownership
    // of `head` and `body`, and the rule set is left exactly as it was, since
    // `Database.rollback` has no way to put a rule back. The identifier is
    // spent only once the rule is certain to stay.
    errdefer _ = db.eval.rules.pop();
    try validation.validateRecursiveGeneration(db);
    try validation.validateStratification(db);
    materialization.invalidateAnalysis(db);
    if (db.closure != null) {
        // Lazy rebuild policy for rule additions: invalidate from the new
        // head's stratum now, rebuild at the next evaluation.
        const analysis = try db.eval.ensureAnalysis();
        db.markDirty(analysis.strata.get(syntax.predicateKey(head)) orelse 0);
    }
    db.eval.next_rule_id += 1;
}

/// Declares `declared` as the schema of the predicate `name`, taking
/// ownership of it whatever happens. Declaring the schema a predicate already
/// has changes nothing; any other schema for it is `SchemaConflict`. The
/// facts and rules the database already holds must fit, or the declaration
/// fails and the database is as it was.
pub fn declareSchema(db: *database.Database, name: syntax.Id, declared: schema.Schema) !void {
    if (db.schemas.get(name)) |existing| {
        defer declared.deinit(db.allocator);
        if (!existing.eql(declared)) return errors.Error.SchemaConflict;
        return;
    }
    db.schemas.put(db.allocator, name, declared) catch |err| {
        declared.deinit(db.allocator);
        return err;
    };
    errdefer db.schemas.remove(db.allocator, name);
    for (0..db.facts.len()) |index| {
        const fact = db.facts.factAt(index);
        if (fact.predicate == name and !db.fitsSchema(name, fact.terms))
            return errors.Error.SchemaViolation;
    }
    try typing.checkRules(db);
}

/// Evaluates relational, built-in, negated, or aggregate goals. Goals and
/// their structural terms remain caller-owned and may be freed immediately
/// after this function returns.
/// Answers `goals`, listed in the answer order `keys` asks for (see "Answer
/// order" in CONTEXT.md). A key naming a variable the answers do not list is
/// `UnknownVariable`, checked before anything is evaluated.
pub fn queryClauses(
    db: *database.Database,
    goals: []const syntax.Clause,
    keys: []const input.SortKey,
) !results.QueryResult {
    const variables = try answerVariables(db, goals);
    defer db.allocator.free(variables);
    return queryClausesAs(db, goals, .{ .variables = variables }, keys);
}

/// Which variables answers list, and under what names.
pub const Listing = struct {
    /// The variables answers list, in the order they list them.
    variables: []const syntax.Id,
    /// What each of `variables` is called in the answers. When given, answers
    /// list exactly `variables`, under these names, and an answer that
    /// differs from another only in a variable left out is listed once. When
    /// null, answers list each variable under its own name, and anything else
    /// a binding holds follows.
    names: ?[]const []const u8 = null,
};

/// Answers `goals` as `listing` says, in the order `keys` asks for. This is
/// `queryClauses` for a caller whose goals aren't the ones it asked, like a
/// folded plan, whose variables are spelled the plan's way.
pub fn queryClausesAs(
    db: *database.Database,
    goals: []const syntax.Clause,
    listing: Listing,
    keys: []const input.SortKey,
) !results.QueryResult {
    const resolved = try resolveSortKeys(db, keys, listing);
    defer db.allocator.free(resolved);
    var internal_answers = try evaluateClauses(db, goals);
    defer {
        for (internal_answers.items) |*binding| binding.deinit(db.allocator);
        internal_answers.deinit(db.allocator);
    }
    const order: AnswerOrder = .{ .db = db, .keys = resolved, .variables = listing.variables };
    std.sort.pdq(syntax.Binding, internal_answers.items, order, AnswerOrder.lessThan);
    const names = listing.names orelse
        return db.copyQueryResult(internal_answers.items, listing.variables);
    // Sorted on every listed variable, so answers that agree on all of them
    // are adjacent.
    var kept: usize = 0;
    for (internal_answers.items, 0..) |*binding, index| {
        if (kept != 0 and order.equal(internal_answers.items[kept - 1], binding.*)) {
            binding.deinit(db.allocator);
            continue;
        }
        if (kept != index) internal_answers.items[kept] = binding.*;
        kept += 1;
    }
    internal_answers.shrinkRetainingCapacity(kept);
    return db.copyProjectedResult(internal_answers.items, listing.variables, names);
}

const ResolvedKey = struct {
    variable: syntax.Id,
    direction: input.Direction,
};

/// The keys as identifiers, each checked against the variables the answers
/// list, by the names the answers list them under.
fn resolveSortKeys(
    db: *const database.Database,
    keys: []const input.SortKey,
    listing: Listing,
) ![]ResolvedKey {
    const resolved = try db.allocator.alloc(ResolvedKey, keys.len);
    errdefer db.allocator.free(resolved);
    for (keys, resolved) |key, *out| {
        const position = if (listing.names) |names|
            for (names, 0..) |name, index| {
                if (std.mem.eql(u8, name, key.variable)) break index;
            } else null
        else if (db.strings.get(key.variable)) |id|
            std.mem.findScalar(syntax.Id, listing.variables, id)
        else
            null;
        const index = position orelse return errors.Error.UnknownVariable;
        out.* = .{ .variable = listing.variables[index], .direction = key.direction };
    }
    return resolved;
}

/// The requested keys first, then every listed variable ascending, so that
/// answers the keys leave tied fall back to the default order and the whole
/// order is total over distinct answers.
const AnswerOrder = struct {
    db: *const database.Database,
    keys: []const ResolvedKey,
    variables: []const syntax.Id,

    fn lessThan(self: AnswerOrder, a: syntax.Binding, b: syntax.Binding) bool {
        for (self.keys) |key| {
            const order = self.compareAt(a, b, key.variable);
            if (order != .eq) return if (key.direction == .ascending) order == .lt else order == .gt;
        }
        for (self.variables) |variable| {
            const order = self.compareAt(a, b, variable);
            if (order != .eq) return order == .lt;
        }
        return false;
    }

    /// Whether two answers agree on every listed variable.
    fn equal(self: AnswerOrder, a: syntax.Binding, b: syntax.Binding) bool {
        for (self.variables) |variable|
            if (self.compareAt(a, b, variable) != .eq) return false;
        return true;
    }

    /// An answer that leaves the variable unbound sorts before one that
    /// binds it.
    fn compareAt(self: AnswerOrder, a: syntax.Binding, b: syntax.Binding, variable: syntax.Id) std.math.Order {
        const left = a.values.get(variable);
        const right = b.values.get(variable);
        if (left == null or right == null)
            return std.math.order(@intFromBool(left != null), @intFromBool(right != null));
        return self.db.eval.compareValues(left.?, right.?);
    }
};

/// The query's variables in the order it first mentions them, which is the
/// order its answers list them in. Built from the goals as written rather than
/// from the plan, so that what a caller sees does not move when the planner
/// picks a different join order.
pub fn answerVariables(db: *database.Database, goals: []const syntax.Clause) ![]syntax.Id {
    var order: std.ArrayList(syntax.Id) = .empty;
    errdefer order.deinit(db.allocator);
    var seen: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer seen.deinit(db.allocator);
    for (goals) |clause| try appendClauseVariables(db, clause, &seen, &order);
    return order.toOwnedSlice(db.allocator);
}

/// Appends the variables a goal binds at its surface — the ones that can reach
/// an answer — in the order the goal writes them.
fn appendClauseVariables(
    db: *database.Database,
    clause: syntax.Clause,
    seen: *std.AutoHashMapUnmanaged(syntax.Id, void),
    order: *std.ArrayList(syntax.Id),
) !void {
    switch (clause) {
        .relational, .builtin, .negated => |expression| for (expression.terms) |term|
            try appendTermVariables(db, term, seen, order),
        .aggregate => |aggregate| try appendTermVariables(db, aggregate.output, seen, order),
    }
}

fn appendTermVariables(
    db: *database.Database,
    term: syntax.Term,
    seen: *std.AutoHashMapUnmanaged(syntax.Id, void),
    order: *std.ArrayList(syntax.Id),
) !void {
    switch (term) {
        .variable => |variable| {
            const entry = try seen.getOrPut(db.allocator, variable);
            if (!entry.found_existing) try order.append(db.allocator, variable);
        },
        .cons => |pair| {
            try appendTermVariables(db, pair.head, seen, order);
            try appendTermVariables(db, pair.tail, seen, order);
        },
        else => {},
    }
}

pub fn evaluateClauses(db: *database.Database, goals: []const syntax.Clause) !std.ArrayList(syntax.Binding) {
    if (goals.len == 0) return error.InvalidQuery;
    var outer_variables: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer outer_variables.deinit(db.allocator);
    for (goals) |clause| try syntax.collectClauseSurfaceVariables(db.allocator, clause, &outer_variables);
    var bound: std.AutoHashMapUnmanaged(syntax.Id, void) = .empty;
    defer bound.deinit(db.allocator);
    const ordered = try validation.orderClauses(db, goals);
    defer db.allocator.free(ordered);
    for (ordered) |clause|
        try validation.validateClause(db, clause, &bound, &outer_variables, errors.Error.InvalidQuery);
    try typing.checkGoals(db, goals);

    try materialization.ensureMaterialized(db);
    const values_before = db.eval.values.values.items.len;
    for (goals) |clause| try compile.internGroundStructuresInClause(db, clause);
    if (db.eval.values.values.items.len != values_before) {
        // Novel ground query structures must join the seed set of
        // admissible structural recursion, so derive their consequences
        // on this database's own (discardable) closure.
        if (db.closure) |*closure| {
            if ((try db.eval.ensureAnalysis()).has_seed_rules)
                try db.eval.expandFrom(closure, 0);
        }
    }

    var internal_answers: std.ArrayList(syntax.Binding) = .empty;
    errdefer {
        for (internal_answers.items) |*answer| answer.deinit(db.allocator);
        internal_answers.deinit(db.allocator);
    }
    var initial: syntax.Binding = .{};
    defer initial.deinit(db.allocator);
    try db.eval.solve(db.closureStore(), null, ordered, &initial, &internal_answers, null);
    return internal_answers;
}

/// The plan a query's goals would be solved under, rendered for a caller that
/// wants to see the clause order and the indexes it chose. Planning reads the
/// materialized closure's statistics, so this materializes first, exactly as
/// evaluating the query would.
pub fn explainClauses(db: *database.Database, goals: []const syntax.Clause) ![]u8 {
    if (goals.len == 0) return error.InvalidQuery;
    const ordered = try validation.orderClauses(db, goals);
    defer db.allocator.free(ordered);
    try materialization.ensureMaterialized(db);
    var initial: syntax.Binding = .{};
    defer initial.deinit(db.allocator);
    var chosen = try db.eval.planFor(db.closureStore(), null, ordered, &initial);
    defer chosen.deinit();
    return chosen.explainAlloc(db.allocator, &db.strings);
}

/// Resolves a retraction's goals to the exact base facts they name, and hands
/// them back in a store of its own. Removes nothing: the goals are evaluated
/// against whichever database the caller points this at, and the facts are
/// copied out of that database's fact store rather than taken out of it.
///
/// A retraction is the one statement whose goals have to be evaluated
/// somewhere other than where its effect lands, because evaluating them can
/// intern values the database does not hold. The caller therefore points this
/// at a staging copy and hands what comes back to `commitRetraction`, which
/// applies it to the database that copy came from — the facts are that
/// database's own, so its value identifiers are what they carry.
pub fn resolveRetraction(
    db: *database.Database,
    goals: []const syntax.Clause,
) !relation_store.RelationStore {
    var answers = try evaluateClauses(db, goals);
    defer {
        for (answers.items) |*answer| answer.deinit(db.allocator);
        answers.deinit(db.allocator);
    }
    var resolved: relation_store.RelationStore = .init(db.allocator);
    errdefer resolved.deinit();
    // Deduplicating by entry rather than leaving it to the store's set
    // semantics: a fact reached twice is one removal, not one removal with a
    // second unit of support, and delete-and-rederive reads that support.
    var seen: std.AutoHashMapUnmanaged(usize, void) = .empty;
    defer seen.deinit(db.allocator);
    for (answers.items) |*answer| {
        for (goals) |clause| {
            const goal = switch (clause) {
                .relational => |expression| expression,
                else => continue,
            };
            for (try db.eval.lookupCandidates(&db.facts, goal, answer)) |candidate| {
                if (seen.contains(candidate)) continue;
                var matched = try answer.clone(db.allocator);
                defer matched.deinit(db.allocator);
                if (try db.eval.unify(db.facts.factAt(candidate), goal, &matched)) {
                    try seen.put(db.allocator, candidate, {});
                    try relation_store.copyFactInto(
                        db.allocator,
                        &resolved,
                        db.facts.factAt(candidate),
                        false,
                    );
                }
            }
        }
    }
    return resolved;
}

/// The transaction a run of assertions is staged in.
///
/// A source program is a sequence of statements, each of which either commits
/// completely or leaves the database exactly as it was, so a failure part-way
/// through a program keeps every earlier statement and none of this one. A
/// front end asserts facts, rules and schemas by beginning one of these,
/// running each statement against `target` under a savepoint of its own, and
/// committing the run.
///
/// Queries and retractions do not need one. Neither commits the copy it
/// evaluates on, so each is a single call — `query` or `retract` — that makes
/// and releases its own, which is also what keeps what it cost on the
/// database's books.
///
/// This is deliberately the whole transaction interface a front end gets for
/// that. The primitives it is built from — cloning the database and replacing
/// it with a staged copy — are not part of the public interface, because
/// committing a foreign staging database is not an operation an embedder
/// should be able to name.
pub const Transaction = struct {
    database: *database.Database,
    staging: database.Database,

    /// Opens a transaction for a run of consecutive assertions.
    pub fn begin(db: *database.Database) !Transaction {
        return .{ .database = db, .staging = try db.clone() };
    }

    /// The database to execute the statements against. Everything they intern
    /// stays here unless the run commits.
    pub fn target(self: *Transaction) *database.Database {
        return &self.staging;
    }

    /// Where the staging copy stands, to undo a statement back to.
    ///
    /// Cloning the database is what a transaction costs, and for a source file
    /// of facts it is nearly the whole cost of loading it: 2000 assertions one
    /// statement at a time copy 1,999,000 fact entries between them. A run of
    /// consecutive assertions therefore shares one of these. What a statement
    /// promises is unweakened, because a statement that fails inside a run is
    /// rolled back to its own savepoint and the run is committed without it —
    /// which leaves every earlier statement and none of the failing one,
    /// exactly as a transaction each would.
    pub fn savepoint(self: *Transaction) database.Savepoint {
        return self.staging.savepoint();
    }

    /// Takes a statement that failed back out of the staging copy the
    /// statements before it are on. Allocates nothing.
    pub fn rollback(self: *Transaction, mark: database.Savepoint) void {
        self.staging.rollback(mark);
    }

    /// Installs what a run of assertions has staged so far.
    ///
    /// Spelled as an operation that cannot fail. A run is committed both when
    /// it ends and when a statement inside it fails, and on that second path
    /// there is nothing to spend on an allocation and no room for a second
    /// error to report.
    pub fn commitAssertions(self: *Transaction) void {
        self.database.commit(&self.staging);
    }

    /// Releases the staging copy — after a commit, the database's previous
    /// contents, which the commit left there.
    pub fn deinit(self: *Transaction) void {
        self.staging.deinit();
        self.* = undefined;
    }
};

const testing = std.testing;

/// Installs `reachable(X) :- node(X)`, which is enough of a rule for a
/// retraction to have a derived consequence to lose. Built from descriptors
/// rather than parsed, because running parsed statements is the layer above
/// this one.
fn defineReachableRule(db: *database.Database) !void {
    const head = try compile.compileRelation(db, "reachable", &.{input.variable("X")}, false);
    const body = try compileGoal(db, "node", input.variable("X"));
    defer db.allocator.free(body);
    try addRuleClauses(db, head, body);
}

fn addAtomFact(db: *database.Database, predicate: []const u8, atom: []const u8) !void {
    const expression = try compile.compileRelation(db, predicate, &.{input.atom(atom)}, false);
    defer syntax.freeExpr(db.allocator, expression);
    try addFactExpr(db, expression, null);
}

/// Compiles one relational goal against `db`, interning whatever it names
/// there. The caller owns the returned slice and the clauses in it.
fn compileGoal(db: *database.Database, predicate: []const u8, term: input.Term) ![]syntax.Clause {
    return compile.compileGoals(db, &.{input.relation(predicate, &.{term})});
}

test "the facts a retraction resolves on a copy are the original database's own" {
    // This is the claim the retraction path rests on, and the only place it
    // is visible: a removal set crosses from the database its goals were
    // evaluated against to the database that copy was made from. The value
    // identifiers it carries are indexes into tables that cloning copies
    // verbatim and interning only appends to, so they mean the same facts on
    // both sides. Were that not so, nothing would be found on this side and
    // the retraction would silently remove nothing.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachableRule(&db);
    try addAtomFact(&db, "node", "a");
    try addAtomFact(&db, "node", "b");
    try materialization.ensureMaterialized(&db);
    try testing.expectEqual(@as(usize, 4), db.closure.?.len());

    var staging = try db.clone();
    defer staging.deinit();
    const goals = try compileGoal(&staging, "node", input.atom("a"));
    defer freeClauses(&staging, goals);
    var removed = try resolveRetraction(&staging, goals);
    defer removed.deinit();
    try testing.expectEqual(@as(usize, 1), removed.len());
    // Resolving is not removing: the copy still holds both facts.
    try testing.expectEqual(@as(usize, 2), staging.facts.len());

    try commitRetraction(&db, &removed);
    try testing.expectEqual(@as(usize, 1), db.facts.len());
    // And the fact took its derived consequence with it, which is what makes
    // this the deletion path rather than a fact store edit.
    try testing.expectEqual(@as(usize, 2), db.closure.?.len());
}

test "a retraction naming a value the database does not hold leaves it uninterned" {
    // The reason the goals are evaluated somewhere else at all. Evaluating
    // them interns what they name, and a retraction may name values the
    // database has never held; only the facts come back, so only facts the
    // database already had can reach it.
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    try defineReachableRule(&db);
    try addAtomFact(&db, "node", "a");
    try materialization.ensureMaterialized(&db);
    const scalars_before = db.eval.scalars.values.items.len;

    var staging = try db.clone();
    defer staging.deinit();
    const goals = try compileGoal(&staging, "node", input.atom("absent"));
    defer freeClauses(&staging, goals);
    var removed = try resolveRetraction(&staging, goals);
    defer removed.deinit();

    try testing.expectEqual(@as(usize, 0), removed.len());
    try testing.expect(staging.eval.scalars.values.items.len > scalars_before);
    try testing.expectEqual(scalars_before, db.eval.scalars.values.items.len);
    try testing.expectEqual(@as(usize, 1), db.facts.len());
}

test "a listing with names projects answers onto them, lists each once, and sorts by them" {
    var db: database.Database = .init(testing.allocator);
    defer db.deinit();
    for ([_][2][]const u8{ .{ "a", "one" }, .{ "b", "three" }, .{ "a", "two" } }) |pair| {
        const expression = try compile.compileRelation(&db, "p", &.{ input.atom(pair[0]), input.atom(pair[1]) }, false);
        defer syntax.freeExpr(db.allocator, expression);
        try addFactExpr(&db, expression, null);
    }
    const goals = try compile.compileGoals(&db, &.{
        input.relation("p", &.{ input.variable("X"), input.variable("Y") }),
    });
    defer freeClauses(&db, goals);
    const x = db.strings.get("X").?;
    const listing: Listing = .{ .variables = &.{x}, .names = &.{"Who"} };

    // `Y` is left out, so the two `a` answers are one, listed as `Who`.
    var projected = try queryClausesAs(&db, goals, listing, &.{});
    defer projected.deinit();
    try testing.expectEqual(@as(usize, 2), projected.answers.items.len);
    try testing.expectEqual(@as(usize, 1), projected.answers.items[0].bindings.items.len);
    try testing.expectEqualStrings("a", try projected.answers.items[0].getAtom("Who"));
    try testing.expectEqualStrings("b", try projected.answers.items[1].getAtom("Who"));

    // Keys name what the answers are called, not what the goals call it.
    var descending = try queryClausesAs(&db, goals, listing, &.{input.descending("Who")});
    defer descending.deinit();
    try testing.expectEqualStrings("b", try descending.answers.items[0].getAtom("Who"));
    try testing.expectError(
        errors.Error.UnknownVariable,
        queryClausesAs(&db, goals, listing, &.{input.ascending("X")}),
    );
}
