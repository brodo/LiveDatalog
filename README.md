# LiveDatalog

LiveDatalog is an embeddable Datalog engine for Zig 0.16, modelled after
[Jatalog](https://github.com/wernsey/Jatalog). It also includes a small command-line interpreter.

## Features

- Facts, rules, and multi-clause queries
- Recursive rules and stratified negation
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

## Embed it in Zig

Use `execute` when you want to parse Datalog source, or use `expr`/`not` to
construct expressions directly. Expressions created with `expr` or `not` are
owned by the caller until they are passed successfully to `addRule`; free
other expressions with `freeExpression`. Query and execution results also
need to be deinitialized.

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

## Development

```sh
zig build test
zig build fmt
zig build test-fmt
zig build lint
```

The test step runs unit tests, formatting verification, and Ziglint.
