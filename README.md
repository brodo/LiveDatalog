# LiveDatalog

LiveDatalog is a small, embeddable Datalog engine for Zig 0.16. It is modeled
after [Jatalog](https://github.com/wernsey/Jatalog) and includes a command-line
interpreter for running files, piping programs, and exploring data in a REPL.

## Features

- Facts, rules, multi-goal queries, and recursive relations
- Stratified negation and fact retraction
- Exact signed 64-bit integers and finite `f64` floats with one canonical
  numeric identity (`1` and `1.0` are the same value)
- Structural lists, deterministic `setof`, and nested aggregates
- Checked integer arithmetic and mixed floating-point addition and subtraction
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

    const input = LiveDatalog.input;
    try database.addFact("parent", &.{ input.atom("alice"), input.atom("bob") });

    const x = input.variable("x");
    const y = input.variable("y");
    try database.addRule(
        input.relation("ancestor", &.{ x, y }),
        &.{input.relation("parent", &.{ x, y })},
    );

    var result = try database.query(&.{input.relation(
        "ancestor",
        &.{ input.atom("alice"), input.variable("who") },
    )});
    defer result.deinit();

    const who = try result.answers.items[0].getAtom("who");
    std.debug.print("{s}\\n", .{who}); // bob
}
```

Use `execute` to parse and run Datalog source directly. The `input` helpers
construct typed atoms, integers, floats, variables, proper lists, cons cells,
relations, negation, equality, comparisons, checked arithmetic, and `setof`.
They allocate nothing and cannot fail. Database operations synchronously
borrow and compile the descriptors, so stack values and temporary slices are
safe and remain caller-owned.

`applyChanges` applies one batch of ground fact insertions and deletions
atomically with set semantics, using `input.fact` descriptors:

```zig
const changed = try database.applyChanges(&.{
    input.fact("edge", &.{ input.atom("b"), input.atom("c") }),
}, &.{
    input.fact("edge", &.{ input.atom("a"), input.atom("b") }),
});
```

Insertions into a materialized database propagate incrementally through
positive rules, and deletions use delete-and-rederive, so facts with an
alternative proof survive while unsupported recursive consequences —
including cyclically self-supporting ones — disappear. A rule with a single
unnested `setof` maintains only the groups an update touched. When such a
rule's head projects an outer variable away, several groups can derive the
same tuple, so derivation counts decide when it appears and disappears.
Updates that reach negation, or an aggregate outside that class, recompute
the affected strata. Every path is checked against a full rebuild.
`maintenanceStats` reports closure size, incremental work, and how the
maintained views are classified.

Floats follow the finite-value policy from
[ADR 0001](docs/adr/0001-finite-f64-scalars.md): compiling `input.float`
reports `NumericType` for NaN and `NumericOverflow` for an infinity, and an
integral in-range value such as `input.float(1.0)` canonicalizes to the
integer scalar `1`. Non-integral floats format deterministically with
shortest round-trip digits, such as `0.5` and `5e-324`.

### Ownership

Every `QueryResult` and `ExecutionResult` must be deinitialized. Results own
their variable names, atoms, integers, floats, and reachable list structure,
and remain readable after the database is deinitialized. Use `getAtom`,
`getInteger`, `getFloat`, or `getValue`; generic values support list
inspection, `write`, and `formatAlloc`. The slice returned by `formatAlloc`
belongs to the supplied allocator and must be freed by the caller.
Unknown variables return `UnknownVariable`, while using a scalar getter on the
wrong kind returns `TypeMismatch`. Getters never coerce between numeric
kinds: a float that canonicalized to an integer when it was stored, such as
`1.0`, is retrieved with `getInteger`, and `getFloat` returns only values
that remained floats, such as `2.5`.

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

Run the reproducible benchmark workloads with:

```sh
zig build benchmark-aggregation -Doptimize=ReleaseFast
```

```sh
zig build benchmark-materialization -Doptimize=ReleaseFast
```

See [Aggregation performance](docs/aggregation-performance.md) for the workload
and recorded measurements.
