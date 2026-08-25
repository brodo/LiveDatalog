//! Whether growing the relations a query reads can only grow its answers.
//!
//! This is the restricted class of Section 6.4.1, and it exists to lift a
//! refusal rather than to describe queries for its own sake. A reconstruction
//! holds what the views prove existed, which can be less than the relation
//! held, so a plan runs the query over a *subset* of what it asked about. If
//! the query's answers only grow as its relations grow, running it over a
//! subset returns a subset of its answers, and that is containment. If they do
//! not — if the query asks for a collected set to be *empty*, or hands the set
//! itself back — then a subset can produce an answer the query does not have,
//! which is Example 6.4.1 exactly.
//!
//! The check is conservative by construction: it says yes only to shapes whose
//! monotonicity is visible in the rule that wrote them, and a shape it cannot
//! read is a no. Saying no costs a fold; saying yes wrongly costs containment,
//! which is the one thing a fold may not trade.
//!
//! Negation is not a separate case here, it is the first one refused. Chapter 6
//! assumes negated subgoals have been rewritten into `setof` subgoals with an
//! empty output, and that rewriting lands on precisely the shape this rejects:
//! adding a tuple to a relation deletes the answers that negated it. This
//! engine keeps negation and aggregation apart, so the refusal is stated
//! directly instead — but it is the same refusal, and it means the monotonic
//! class never discharges a negated read.

const std = @import("std");
const fold_ir = @import("fold_ir.zig");

/// Whether this query is monotonic: Definition 6.4.2 over Definition 6.4.1,
/// restricted to what this language can write.
///
/// The rules are the query's own — the `Q` of `Q ∪ V⁻¹` — and the goals are
/// what the caller asked for. Both are judged, because an answer the plan
/// returns can come through either.
pub fn ofQuery(goals: []const fold_ir.Goal, rules: []const fold_ir.Rule) bool {
    // A goal list has no head because everything in it is the head: its
    // variables are the bindings the caller is handed. A set reported back is
    // a set whose growing is visible, so an aggregate there is never free.
    if (!monotonicGoals(goals, .{ .head = null, .body = goals })) return false;
    for (rules) |rule| {
        if (!monotonicGoals(rule.body, .{ .head = rule.head.terms, .body = rule.body }))
            return false;
    }
    return true;
}

/// What an aggregate's output is judged against: what the rule reports, and
/// everything that could read the set besides the aggregate that collected it.
const Context = struct {
    /// The head's terms, or null for a goal list, which reports everything.
    head: ?[]const fold_ir.Term,
    body: []const fold_ir.Goal,

    /// Whether the rule neither reports this variable nor reads it anywhere
    /// but the one place it stands. Such a variable constrains nothing:
    /// whatever the set turns out to be, it fits, and it fits again when the
    /// set grows.
    ///
    /// Lemma 6.4.1 is the head half of this, and the second condition of
    /// Definition 6.4.1 is the body half: a goal that reads the set is
    /// permitted there only when it is monotone under `⊆`, which is a property
    /// of a stored relation that nothing here can check. Requiring the set to
    /// go unread is the conservative reading of it.
    fn free(self: Context, variable: fold_ir.Variable) bool {
        const head = self.head orelse return false;
        if (countTerms(head, variable) != 0) return false;
        return countGoals(self.body, variable) == 1;
    }
};

fn monotonicGoals(goals: []const fold_ir.Goal, context: Context) bool {
    for (goals) |goal| if (!monotonicGoal(goal, context)) return false;
    return true;
}

fn monotonicGoal(goal: fold_ir.Goal, context: Context) bool {
    return switch (goal) {
        // Growing a relation can only add tuples for a positive goal to read.
        // Negating it is the opposite and there is no weaker reading of it.
        .relation => |relation| !relation.negated,
        // A comparison reads values, not relations, so how much of a relation
        // the plan knows does not reach it.
        .builtin => true,
        // The body is judged whatever the output looks like. An output nothing
        // reads makes the aggregate's own result irrelevant, but not what its
        // body binds for the goals around it: a nested aggregate asking for an
        // empty set inside a free-output one still loses answers as its
        // relations grow, and still gains them as they shrink.
        .aggregate => |aggregate| monotonicGoals(aggregate.body, context) and
            survivesGrowth(aggregate.output, context),
    };
}

/// Whether an answer that matched this collected output still matches once the
/// collected set has grown.
///
/// Two patterns survive, and Section 6.4.1's contrast is exactly that pair. A
/// free variable asks for *whatever set there is*, and every set is one. `H!T`
/// with both halves free asks for *some non-empty set*, and a non-empty set
/// that grows is still non-empty. Everything else pins the set down — `[]` to
/// the empty one, a written-out list to its elements, `[a!T]` to a first
/// element, a reported variable to one particular set — and a plan running
/// over a subset can then match where the query does not.
fn survivesGrowth(output: fold_ir.Term, context: Context) bool {
    return switch (output) {
        .variable => |variable| context.free(variable),
        .cons => |pair| freeVariable(pair.head, context) and freeVariable(pair.tail, context),
        else => false,
    };
}

fn freeVariable(term: fold_ir.Term, context: Context) bool {
    return term == .variable and context.free(term.variable);
}

fn countGoals(goals: []const fold_ir.Goal, variable: fold_ir.Variable) usize {
    var total: usize = 0;
    for (goals) |goal| total += countGoal(goal, variable);
    return total;
}

fn countGoal(goal: fold_ir.Goal, variable: fold_ir.Variable) usize {
    return switch (goal) {
        .relation => |relation| countTerms(relation.terms, variable),
        .builtin => |builtin| countTerms(builtin.terms, variable),
        .aggregate => |aggregate| countTerm(aggregate.template, variable) +
            countTerm(aggregate.output, variable) +
            countGoals(aggregate.body, variable),
    };
}

fn countTerms(terms: []const fold_ir.Term, variable: fold_ir.Variable) usize {
    var total: usize = 0;
    for (terms) |term| total += countTerm(term, variable);
    return total;
}

fn countTerm(term: fold_ir.Term, variable: fold_ir.Variable) usize {
    return switch (term) {
        .variable => |value| if (value == variable) 1 else 0,
        .cons => |pair| countTerm(pair.head, variable) + countTerm(pair.tail, variable),
        .skolem => |call| countTerms(call.arguments, variable),
        else => 0,
    };
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
};

/// `q(...) :- setof(Y, r(X, Y), <output>).` — Section 6.4.1's pair of queries,
/// with the collected output and what the head reports as the two things that
/// vary.
fn collectingRule(
    fixture: *Fixture,
    allocator: std.mem.Allocator,
    output: syntax.Term,
    head: []syntax.Term,
) !fold_ir.Rule {
    const q = try fixture.strings.intern("q");
    const r = try fixture.strings.intern("r");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var body = [_]syntax.Clause{.{ .aggregate = .{
        .template = .{ .variable = y },
        .body = &inner,
        .output = output,
    } }};
    return fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = head },
        .body = &body,
    });
}

test "asking for an empty set is not monotonic and asking for a non-empty one is" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const x = try fixture.strings.intern("X");
    const s = try fixture.strings.intern("S");
    var head = [_]syntax.Term{.{ .variable = x }};

    // q(X) :- setof(Y, r(X, Y), []). Example 6.4.1: adding a tuple to `r`
    // deletes the answer, so a plan that knows less of `r` answers more.
    const empty = try collectingRule(&fixture, allocator, .nil, &head);
    defer fold_ir.freeRule(allocator, empty);
    try testing.expect(!ofQuery(&.{}, &.{empty}));

    // q(X) :- setof(Y, r(X, Y), H!T). Section 6.4.1's contrast: it asks for
    // some non-empty set, and a set that grows stays non-empty.
    var pair: syntax.Term.Cons = .{
        .head = .{ .variable = try fixture.strings.intern("H") },
        .tail = .{ .variable = try fixture.strings.intern("T") },
    };
    const nonempty = try collectingRule(&fixture, allocator, .{ .cons = &pair }, &head);
    defer fold_ir.freeRule(allocator, nonempty);
    try testing.expect(ofQuery(&.{}, &.{nonempty}));

    // q(X) :- setof(Y, r(X, Y), S). Nothing reads S, so nothing depends on
    // which set it was.
    const free_output = try collectingRule(&fixture, allocator, .{ .variable = s }, &head);
    defer fold_ir.freeRule(allocator, free_output);
    try testing.expect(ofQuery(&.{}, &.{free_output}));

    // q(X, S) :- setof(Y, r(X, Y), S). Lemma 6.4.1: the rule reports the set,
    // so growing `r` replaces the answer rather than leaving it alone.
    var reported = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    const in_head = try collectingRule(&fixture, allocator, .{ .variable = s }, &reported);
    defer fold_ir.freeRule(allocator, in_head);
    try testing.expect(!ofQuery(&.{}, &.{in_head}));

    // q(X) :- setof(Y, r(X, Y), [H]). One element exactly, which is a set that
    // stops matching as soon as a second value joins it — so it is the tail
    // being a variable, and not merely the pattern being a list, that decides.
    var single_cons: syntax.Term.Cons = .{
        .head = .{ .variable = try fixture.strings.intern("H") },
        .tail = .nil,
    };
    const single = try collectingRule(&fixture, allocator, .{ .cons = &single_cons }, &head);
    defer fold_ir.freeRule(allocator, single);
    try testing.expect(!ofQuery(&.{}, &.{single}));
}

test "a set another goal reads is a set whose growing is visible" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const q = try fixture.strings.intern("q");
    const r = try fixture.strings.intern("r");
    const t = try fixture.strings.intern("t");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const s = try fixture.strings.intern("S");

    // q(X) :- setof(Y, r(X, Y), S), t(X, S). The second condition of
    // Definition 6.4.1: the rule keeps the set out of its head and then reads
    // it anyway, and whether `t` survives the set growing is `t`'s business.
    var head = [_]syntax.Term{.{ .variable = x }};
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var read_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = s } };
    var body = [_]syntax.Clause{
        .{ .aggregate = .{
            .template = .{ .variable = y },
            .body = &inner,
            .output = .{ .variable = s },
        } },
        .{ .relational = .{ .predicate = t, .terms = &read_terms } },
    };
    const rule = try fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = &head },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, rule);
    try testing.expect(!ofQuery(&.{}, &.{rule}));
}

test "a query that reads a collected set with a list function is never monotonic" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    // q(X, T) :- p(X), setof(Y, r(X, Y), S), sum(S, T). Section 6.5's own
    // query shape, and it is the previous test's with a name on the second
    // goal: a list function *is* a goal that reads the collected set, so the
    // set occurs twice and is never free.
    //
    // That settles which half of Theorem 6.5.1 the list-function class can
    // reach. The theorem offers a monotonic query or canonical aggregate
    // views, and the first is closed to every query this phase exists for —
    // not by policy but by the shape of the question, since asking what a
    // collected set sums to is asking about which set it was.
    const q = try fixture.strings.intern("q");
    const p = try fixture.strings.intern("p");
    const r = try fixture.strings.intern("r");
    const sum = try fixture.strings.intern("sum");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const s = try fixture.strings.intern("S");
    const t = try fixture.strings.intern("T");

    var head = [_]syntax.Term{ .{ .variable = x }, .{ .variable = t } };
    var outer_terms = [_]syntax.Term{.{ .variable = x }};
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var summing = [_]syntax.Term{ .{ .variable = s }, .{ .variable = t } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = p, .terms = &outer_terms } },
        .{ .aggregate = .{
            .template = .{ .variable = y },
            .body = &inner,
            .output = .{ .variable = s },
        } },
        .{ .relational = .{ .predicate = sum, .terms = &summing } },
    };
    const rule = try fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = &head },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, rule);
    try testing.expect(!ofQuery(&.{}, &.{rule}));
}

test "a negated goal is the shape the class exists to exclude" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const q = try fixture.strings.intern("q");
    const r = try fixture.strings.intern("r");
    const t = try fixture.strings.intern("t");
    const x = try fixture.strings.intern("X");

    // q(X) :- t(X), not r(X). Rewritten the way Chapter 6 assumes, the negated
    // goal is a `setof` with an empty output, which is Example 6.4.1's shape.
    var head = [_]syntax.Term{.{ .variable = x }};
    var terms = [_]syntax.Term{.{ .variable = x }};
    var body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = t, .terms = &terms } },
        .{ .negated = .{ .predicate = r, .terms = &terms } },
    };
    const rule = try fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = &head },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, rule);
    try testing.expect(!ofQuery(&.{}, &.{rule}));

    // The same rule with the negation gone is monotonic, so it is the negation
    // and not the shape of the rule that this refuses.
    var positive_body = [_]syntax.Clause{
        .{ .relational = .{ .predicate = t, .terms = &terms } },
        .{ .relational = .{ .predicate = r, .terms = &terms } },
    };
    const positive = try fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = &head },
        .body = &positive_body,
    });
    defer fold_ir.freeRule(allocator, positive);
    try testing.expect(ofQuery(&.{}, &.{positive}));
}

test "an aggregate nested in one nothing reads is still an aggregate" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const q = try fixture.strings.intern("q");
    const r = try fixture.strings.intern("r");
    const t = try fixture.strings.intern("t");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const z = try fixture.strings.intern("Z");
    const s = try fixture.strings.intern("S");

    // q(X) :- setof(Y, (t(X, Y), setof(Z, r(Y, Z), [])), S).
    //
    // Nothing reads S, but the inner aggregate decides which Y are collected
    // at all, and it asks for an empty set: shrinking `r` lets more Y through,
    // so the outer group exists where the query has none.
    var head = [_]syntax.Term{.{ .variable = x }};
    var innermost_terms = [_]syntax.Term{ .{ .variable = y }, .{ .variable = z } };
    var innermost = [_]syntax.Clause{
        .{ .relational = .{ .predicate = r, .terms = &innermost_terms } },
    };
    var outer_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var middle = [_]syntax.Clause{
        .{ .relational = .{ .predicate = t, .terms = &outer_terms } },
        .{ .aggregate = .{
            .template = .{ .variable = z },
            .body = &innermost,
            .output = .nil,
        } },
    };
    var body = [_]syntax.Clause{.{ .aggregate = .{
        .template = .{ .variable = y },
        .body = &middle,
        .output = .{ .variable = s },
    } }};
    const rule = try fixture.rule(allocator, .{
        .head = .{ .predicate = q, .terms = &head },
        .body = &body,
    });
    defer fold_ir.freeRule(allocator, rule);
    try testing.expect(!ofQuery(&.{}, &.{rule}));
}

test "a set the caller is handed back is reported however the goals are written" {
    const allocator = testing.allocator;
    var fixture: Fixture = .init(allocator);
    defer fixture.deinit();

    const r = try fixture.strings.intern("r");
    const x = try fixture.strings.intern("X");
    const y = try fixture.strings.intern("Y");
    const s = try fixture.strings.intern("S");

    // setof(Y, r(X, Y), S)? asked directly. There is no head to keep S out of:
    // the answer *is* the binding of S, so growing `r` changes it.
    var inner_terms = [_]syntax.Term{ .{ .variable = x }, .{ .variable = y } };
    var inner = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    var clauses = [_]syntax.Clause{.{ .aggregate = .{
        .template = .{ .variable = y },
        .body = &inner,
        .output = .{ .variable = s },
    } }};
    const goals = try fold_ir.lowerClauses(
        allocator,
        &fixture.symbols,
        try fixture.symbols.openScope(.query),
        &clauses,
    );
    defer fold_ir.freeGoals(allocator, goals);
    try testing.expect(!ofQuery(goals, &.{}));

    // A goal list of ordinary relational goals is monotonic, which is the
    // usual case and the one that has to keep working.
    var plain = [_]syntax.Clause{.{ .relational = .{ .predicate = r, .terms = &inner_terms } }};
    const positive = try fold_ir.lowerClauses(
        allocator,
        &fixture.symbols,
        try fixture.symbols.openScope(.query),
        &plain,
    );
    defer fold_ir.freeGoals(allocator, positive);
    try testing.expect(ofQuery(positive, &.{}));
}
