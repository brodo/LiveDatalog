# LiveDatalog

LiveDatalog is an embeddable Datalog engine for Zig 0.16, modelled after
[Jatalog](https://github.com/wernsey/Jatalog). It also includes a small command-line interpreter.

## Features

- Facts, rules, and multi-clause queries
- Recursive rules and stratified negation
- Structural lists, deterministic `setof`, and nested aggregates
- Checked 64-bit integer addition and subtraction for recursive list functions
- Equality (`=`), inequality (`!=` or `<>`), and numeric comparisons (`<`, `<=`, `>`, `>=`)
- Bare and quoted values, including escaped quotes
- Line comments (`%` and `//`) and block comments (`/* ... */`)
- Fact retraction with `~`
- A REPL, file runner, standard-input mode, and an embeddable Zig API

Predicates, terms, variables, and values are interned. A `StringTable` ID is
the insertion index in its ordered `std.StringArrayHashMapUnmanaged(u64)`, so
the ID is stable and can also be resolved back to its string.

## Command line

Run a Datalog file:

```sh
zig build run -- program.dl
```

Start the interactive REPL:

```sh
zig build run
```

Enter one fact, rule, query, or retraction per line. Use `.help` for a
reminder and `.quit` or `.exit` to leave. The REPL supports line editing and
history through [linenoize](https://github.com/hazre/linenoize/tree/feat/port-zig-0.16).

You can also pipe a complete program through standard input:

```sh
printf 'parent(alice, bob). parent(alice, X)?' | zig build run
```

```text
X: bob
```

## Language tour

Save this as `family.dl` and run it with `zig build run -- family.dl`. The
final query is printed; earlier facts and rules populate the database.

```datalog
% A percent comment runs to the end of the line.
parent(alice, bob).
parent(bob, carol). // So does a C++-style comment.
person(alice).
person(bob).
person(carol).
employed(alice).

/* Values containing whitespace or punctuation can be quoted. Quotes may be
   escaped with a backslash. */
note(alice, "works from home").
note(bob, 'calls it \'the office\'').

% Rules may be recursive.
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- ancestor(X, Z), parent(Z, Y).

% Negation is allowed when it is stratified. Variables in a negated clause
% must already be bound by a positive clause.
idle(X) :- person(X), not employed(X).

% Built-ins can bind with = and compare bound values. != is an alias for <>.
age(alice, 36).
age(bob, 17).
adult(X) :- age(X, Years), Years >= 18.
different_people(X, Y) :- person(X), person(Y), X != Y.
same_person(X) :- person(X), X = alice.

% A query may contain multiple clauses. This returns carol.
ancestor(alice, Descendant), idle(Descendant)?
```

```text
Descendant: carol
```

All comparison operators work with bound values:

```datalog
age(X, Years), Years < 18?
age(X, Years), Years <= 17?
age(X, Years), Years > 17?
age(X, Years), Years >= 36?
age(X, Years), Years <> 36?
```

Numeric-looking values are compared numerically (`1` equals `1.0`); other
values are compared as strings. For every operator except `=`, both sides
must be bound. `=` may bind one side, but cannot have two unbound variables.

Retract matching base facts with `~`. Derived facts are recomputed from the
remaining facts and rules on each query.

```datalog
parent(bob, carol)~
ancestor(alice, carol)?
```

```text
Yes.
No.
```

Negation cannot participate in a recursive cycle. For example, this program
is rejected with `NotStratified`:

```datalog
p(X) :- q(X).
q(X) :- not p(X), seed(X).
```

### Aggregation and structural lists

The checked-in `examples/aggregation.dl` language tour runs verbatim with
`zig build run -- examples/aggregation.dl`:

```datalog
% Structural lists, set aggregation, and an ordinary recursive list function.
person(alice).
person(bob).
parent(alice, bob).

children(X, S) :- person(X), setof(Y, parent(X, Y), S).

length([], 0).
length(H!T, N) :- length(T, M), N = M + 1.

numchildren(X, N) :- children(X, S), length(S, N).
numchildren(X, N)?
```

```text
X: alice, N: 1
X: bob, N: 0
```

Terms support `[]`, `[a, b]`, nested lists, the head/tail pattern `H!T`, and
the equivalent `cons(H, T)` constructor. `setof(Template, Goal, Result)`
collects distinct ground template values into a deterministically ordered
proper list. It succeeds with `[]` when there are no matches. Parenthesize a
multi-goal body:

```datalog
setof([Score, Student], (score(Test, Student, Score), passed(Student)), S)
```

Aggregates may be nested, but their bodies may only depend on completed lower
strata. Correlated variables must be bound before the aggregate; variables
local to its template/body cannot escape. Recursive list rules must consume at
least one structural argument through a cons tail without growing another
tracked argument. This intentionally conservative check accepts `length`,
`member`, and `sum`, while rejecting rules such as `q([X]) :- q(X)`.

Integer expressions use signed 64-bit arithmetic: `N = A + B` and
`N = A - B`. Operands must already be bound integer atoms; overflow and
non-integer inputs are errors.

## Embed it in Zig

Use `execute` to parse Datalog source. For typed construction, `expr` and `not`
create caller-owned expressions, `clauseFromExpr` classifies one as a
relational, built-in, or negated clause, and `setof` creates a structural
aggregate goal. Term strings passed to `expr` and `setof` accept the structural
syntax described above.

`setof` takes ownership of its body clauses only on success. Likewise,
`addRule` and `addRuleClauses` take ownership of their head and body expressions
only on success. Release anything not transferred with `freeExpression` or
`freeClause`; freeing an aggregate clause recursively frees its template,
output, and body. `query` and `queryClauses` only borrow their goals. Every
`QueryResult` and `ExecutionResult` must be deinitialized.

```zig
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

pub fn main() !void {
    var database = LiveDatalog.Jatalog.init(std.heap.page_allocator);
    defer database.deinit();

    try database.addFact("parent", &.{ "alice", "bob" });

    const parent = try database.expr("parent", &.{ "X", "Y" });
    const ancestor = try database.expr("ancestor", &.{ "X", "Y" });
    try database.addRule(ancestor, &.{parent}); // Takes ownership on success.

    const goal = try database.expr("ancestor", &.{ "alice", "Who" });
    defer database.freeExpression(goal);
    var result = try database.query(&.{goal});
    defer result.deinit();

    const who = result.answers.items[0].get(&database, "Who").?;
    std.debug.print("{s}\\n", .{who}); // bob
}
```

For negated clauses, construct them with `database.not("employed", &.{ "X" })`.
Use `ExecutionResult.deinit` after `execute`; it is a tagged union of `none`,
`changed`, and `query`.

Aggregate rules use clauses so nested goals retain their ownership explicitly:

```zig
try database.addFact("person", &.{"alice"});

const parent = try database.expr("parent", &.{ "X", "Y" });
var parent_owned = true;
defer if (parent_owned) database.freeExpression(parent);
const set = try database.setof("Y", &.{database.clauseFromExpr(parent)}, "S");
parent_owned = false; // set owns parent after setof succeeds.
var set_owned = true;
defer if (set_owned) database.freeClause(set);

const person = try database.expr("person", &.{"X"});
var person_owned = true;
defer if (person_owned) database.freeExpression(person);
const children = try database.expr("children", &.{ "X", "S" });
var children_owned = true;
defer if (children_owned) database.freeExpression(children);

// On success, the database owns children, person, set, and set's parent goal.
try database.addRuleClauses(children, &.{ database.clauseFromExpr(person), set });
children_owned = false;
person_owned = false;
set_owned = false;

const goal = try database.expr("children", &.{ "alice", "S" });
const goal_clause = database.clauseFromExpr(goal);
defer database.freeClause(goal_clause); // queryClauses only borrows it.
var result = try database.queryClauses(&.{goal_clause});
defer result.deinit();

const value = result.answers.items[0].getValue(&database, "S").?;
const text = try database.formatValue(std.heap.page_allocator, value);
defer std.heap.page_allocator.free(text);
std.debug.print("{s}\\n", .{text}); // [bob]
```

If a fallible ownership-taking call fails, the caller still owns all inputs
and must release them. `Binding.get` returns scalar atoms; use
`Binding.getValue` with `formatValue` or `writeValue` for structural bindings.

### Errors

The public error names mark separate failure boundaries: `InvalidSyntax` for
parsing, `InvalidRule`/`InvalidQuery` for safety, `NotStratified` for recursion
through negation or aggregation, `UnboundVariable` for grounding, and
`NotAdmissible` for structural termination checks. Arithmetic additionally
reports `NumericType` and `NumericOverflow`.

## Development

```sh
zig build test
zig build fmt
zig build test-fmt
zig build lint
```

The test step runs unit tests, formatting verification, and Ziglint.

Run the reproducible aggregate workload with:

```sh
zig build benchmark-aggregation -Doptimize=ReleaseFast
```

Its workload and Phase 5 measurements are documented in
[`docs/aggregation-performance.md`](docs/aggregation-performance.md).
