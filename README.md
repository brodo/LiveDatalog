# LiveDatalog

LiveDatalog is a small, embeddable Datalog engine for Zig 0.16. It is modeled
after [Jatalog](https://github.com/wernsey/Jatalog) and includes a command-line
interpreter for running files, piping programs, and exploring data in a REPL.

## Features

- Facts, rules, multi-goal queries, and recursive relations
- Stratified negation and fact retraction
- Equality, inequality, and numeric comparisons
- Structural lists, deterministic `setof`, and nested aggregates
- Checked 64-bit integer addition and subtraction
- Bare and quoted values with escaped quotes
- Line and block comments
- A command-line interpreter and an embeddable Zig API

## Requirements

LiveDatalog requires Zig 0.16 or newer.

## Quick start

Pipe a program into the interpreter:

```sh
printf 'parent(alice, bob). parent(alice, X)?' | zig build run
```

```text
X: bob
```

Statements ending in `.` add facts or rules. A statement ending in `?` runs a
query, and a statement ending in `~` retracts matching base facts.

### Command-line modes

Run a Datalog file:

```sh
zig build run -- program.dl
```

Start the interactive REPL:

```sh
zig build run
```

Enter one fact, rule, query, or retraction per line. Use `.help` for a reminder
and `.quit` or `.exit` to leave. The REPL provides line editing and history
through [linenoize](https://github.com/hazre/linenoize/tree/feat/port-zig-0.16).

For a guided introduction to facts, queries, rules, recursion, negation,
lists, and aggregation, read the [LiveDatalog language tutorial](docs/language-tutorial.md).

## Embed LiveDatalog in Zig

Import the `LiveDatalog` module and create a `Jatalog` database with an
allocator:

```zig
const std = @import("std");
const LiveDatalog = @import("LiveDatalog");

pub fn main() !void {
    var database = LiveDatalog.Jatalog.init(std.heap.page_allocator);
    defer database.deinit();

    try database.addFact("parent", &.{ "alice", "bob" });

    const parent = try database.expr("parent", &.{ "X", "Y" });
    const ancestor = try database.expr("ancestor", &.{ "X", "Y" });
    try database.addRule(ancestor, &.{parent});

    const goal = try database.expr("ancestor", &.{ "alice", "Who" });
    defer database.freeExpression(goal);
    var result = try database.query(&.{goal});
    defer result.deinit();

    const who = result.answers.items[0].get(&database, "Who").?;
    std.debug.print("{s}\\n", .{who}); // bob
}
```

Use `execute` to parse and run Datalog source directly. For typed construction:

- `expr` and `not` create caller-owned expressions
- `clauseFromExpr` classifies an expression as relational, built-in, or negated
- `setof` creates a structural aggregate goal
- `query` and `queryClauses` borrow their goals
- `addRule` and `addRuleClauses` take ownership of their inputs on success

Term strings passed to `expr` and `setof` accept the structural syntax described
in the language tutorial.

### Ownership

Every `QueryResult` and `ExecutionResult` must be deinitialized. Release an
expression or clause whose ownership was not transferred with `freeExpression`
or `freeClause`.

`setof` takes ownership of its body clauses only on success. Similarly,
`addRule` and `addRuleClauses` take ownership of their head and body values only
on success. If one of these calls fails, the caller still owns every input.

`Binding.get` returns scalar atoms. Use `Binding.getValue` with `formatValue`
or `writeValue` for structural values such as lists.

## Development

Run the complete test suite:

```sh
zig build test
```

The test step runs unit tests, formatting verification, Ziglint, and the
checked-in aggregation example. Individual maintenance steps are also
available:

```sh
zig build fmt
zig build test-fmt
zig build lint
```

Run the reproducible aggregation workload with:

```sh
zig build benchmark-aggregation -Doptimize=ReleaseFast
```

See [Aggregation performance](docs/aggregation-performance.md) for the workload
and recorded measurements.
