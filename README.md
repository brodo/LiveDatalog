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
- Query folding against declared views, with an explicit answer guarantee
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

### Editor support

[`tree-sitter-livedatalog`](tree-sitter-livedatalog) is a tree-sitter grammar
for `.dl` files. It includes highlighting, scope and folding queries for
editors that use tree-sitter. For diagnostics, navigation and completion,
connect the editor to the development server's language listener.

[`zed-livedatalog`](zed-livedatalog) is a [Zed](https://zed.dev) extension
built from both. It uses the grammar for highlighting and the outline, and
connects Zed to a running server's language listener.

### Development server

`zig build` installs a second binary, `LiveDatalogServer`, for local
development. It loads every `*.dl` file under a directory, reloads them as
they change, and serves the database on two TCP ports: the query listener
(`--port`, default 7070) and the language listener (`--lsp-port`, default
7071). The data comes only from the files: neither listener can change it.

```sh
zig build run-server -- --port 7070 --lsp-port 7071 examples/researchers
```

[`examples/researchers`](examples/researchers) holds 50 famous researchers
(`people.dl`) and quotes by them (`quotes.dl`).

#### Query listener

```sh
printf 'researcher(X, N), field(X, physics), quote(X, Q)?\n' | nc 127.0.0.1 7070
```

Send one request per line; every response ends with an empty line. A request
is a query (the trailing `?` is optional) or a command: `.explain goals`,
`.status` (counts and load errors), `.files`, `.reload`, `.help`, `.quit`.
Answers use the REPL's format. Facts, rules, retractions and schemas sent over
the connection are rejected, and queries inside the files are ignored.

#### Language listener

The language listener speaks the Language Server Protocol over TCP, so an
editor can connect to the running server instead of starting one of its own.
It offers:

- **Diagnostics.** Every file that failed to load is reported, whether or not
  it is open, and cleared once it loads. An open document is also parsed as
  you type, and its syntax errors replace those of the saved file.
- **Hover** on a predicate name: whether its facts are base, derived or both,
  how many of each the database holds, its schema, and the files defining it.
- **Go to definition**: the predicate's schema, or else the rules whose head
  it is, or else its facts, in every loaded file.
- **Find references**: every place a loaded file names the predicate, with or
  without its definitions. `edge/2` and `edge/3` are different predicates.
- **Document highlight**: the other places the open document names the
  predicate, with its definitions marked as writes and its uses as reads.
- **Workspace symbols**: every defined predicate, as `name/arity`, found by
  typing part of its name.
- **Completion** of predicate names wherever a goal can start — not inside a
  relation's arguments — inserting a placeholder per column, named after the
  schema's columns where they have names.

What you type is never loaded: everything the listener says about a predicate
describes the database the saved files built, and a draft that does not parse
is read at the positions of its last version that did. Files outside the
watched directory get these features too. Positions are counted in UTF-8 when the editor offers it, and
in UTF-16 otherwise.

An editor that can only launch a language server over stdio can bridge to the
port, for example with `nc 127.0.0.1 7071` as the server command.

#### How it works

The server runs on one `std.Io.Threaded`:

- The **engine** task owns the database. File changes, query requests and the
  language listener's lookups arrive on one `Io.Queue`, so no other thread
  touches the database. After each change it tells every editor connection,
  which then republishes its diagnostics.
- **Nightwatch**'s thread watches the directory and reports changed `.dl`
  paths. Hidden directories, `zig-out`, `node_modules` and `target` are
  ignored.
- Each listener has a task that accepts clients. Each connection runs as a
  small task that passes its requests to the engine; an editor connection has
  a second task that follows the engine's changes.

The engine waits 40 ms after a change so that bursts of saves become one
reload. Each file is a contributor to the database, named by its path, so a
fact stays as long as any file still asserts it. When only facts changed, the
file's new facts replace its contribution through `setContribution`. Any other
change rebuilds a fresh database from all files in path order and swaps it in. A change applies completely or not at all: if
a file fails to parse or load, the previous database stays and `.status`
shows the error with its location. A full `.reload` skips broken files and
loads the rest.

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

Use `execute` to parse and run Datalog source directly. The whole program is
parsed before any of it runs, so a syntax error leaves the database untouched;
a statement that fails when it runs keeps every statement before it. Pass a
`Diagnostic` to learn where a failure was:

```zig
var diagnostic: LiveDatalog.Diagnostic = .{};
var result = database.execute(source, &diagnostic) catch |err| {
    std.debug.print("{s} at {d}:{d}\n", .{ @errorName(err), diagnostic.line, diagnostic.column });
    return err;
};
defer result.deinit();
```

The parser is also available on its own, needing no database. `parseProgram`,
`parseRule` and `parseGoals` return the same `input` descriptors the helpers
below build, owned by the returned `Parsed` value:

```zig
const rule = try LiveDatalog.parseRule(allocator, "reach(X, Z) :- edge(X, Y), reach(Y, Z)", null);
defer rule.deinit();
try database.addRule(.{ .relation = rule.value.head }, rule.value.body);

const parsed = try LiveDatalog.parseProgram(allocator, "p(a). p(b). p(X)?", null);
defer parsed.deinit();
var answers = try database.executeStatements(parsed.value.statements, null, null);
defer answers.deinit();
```

The `input` helpers
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

### Maintenance

LiveDatalog keeps a materialized closure of all derived facts and updates it
incrementally.

**Eager versus lazy.** Materialization is lazy: an update marks the affected
strata and the next query repairs them. `materialize` forces that work to
happen now, and `rebuild` discards the closure and recomputes everything from
the base facts. A database with no rules never allocates derived state.

```zig
try database.materialize(); // bring the closure up to date now
try database.rebuild();     // recompute it from scratch
const stats = database.maintenanceStats();
```

**Update paths.** Every update takes one of three documented paths:

- insertions propagate through positive rules with semi-naive deltas;
- deletions use delete-and-rederive, so a fact with an alternative proof
  survives while unsupported recursive consequences — including cyclically
  self-supporting ones, and those of a structurally recursive rule whose base
  case is removed — disappear;
- updates reaching negation, or an aggregate outside the maintained class of
  one unnested `setof` per rule, recompute the affected strata.

Retraction takes the deletion path too. `retract` and the source `~`
statement resolve their goals against the closure and hand the matching base
facts to the same engine, so pattern retraction such as
`retract(edge(a, X))` — which deletes every matching fact and has no
batch-API equivalent — is maintained incrementally rather than triggering a
rebuild.

A maintained aggregate rule recomputes only the groups an update touched.
When its head projects an outer variable away, several groups can derive the
same tuple, so derivation counts decide when that tuple appears and
disappears. `maintenanceStats` reports closure size, facts added and removed
incrementally — with the over-deleted and rederived halves of that removal
count reported separately — groups recomputed, rebuild fallbacks, and how the
views are classified.

**Choosing between them.** Maintaining and recomputing produce the same
database, so which one runs is purely a cost decision. By default the engine
makes it automatically: it measures both paths in candidate facts examined,
learns their cost from this database's own history, and takes the cheaper
one. Pin the choice when you need a specific path:

```zig
database.setMaintenancePolicy(.incremental); // always maintain
database.setMaintenancePolicy(.recompute);   // always recompute
database.setMaintenancePolicy(.automatic);   // default
```

The measured cost model matters because neither path dominates. On a
recursive closure where one edge changes a small part of a large relation,
maintaining is several times faster; on a shallow program whose closure is
cheap to recompute, recomputing wins. `maintenanceStats` reports how many
updates went each way and the learned estimates.

**Batching and atomicity.** `applyChanges` applies one batch as a single
transition with set semantics. It runs on a staged copy and commits only on
success, so an allocation failure, an invalid descriptor, or a failed
verification leaves the database exactly as it was. `addFact`, `execute`,
and `retract` remain available and interoperate with the batch API.

**Ownership.** Input descriptors are borrowed for the duration of a call and
never retained. Query results own their data and outlive the database.

**Debugging.** `setShadowVerification(true)` makes every maintained closure
be compared against a fresh rebuild before the change commits, reporting a
disagreement as `MaintenanceMismatch`. It roughly doubles update cost and is
meant for tests. `internStats` reports what interning ground values has cost
this database, in searches made and table entries compared rather than in
time, so a workload can be checked against a machine-independent number.

**Value identity.** A ground value is interned once per database: equal values
share one identifier, and a copy of a database gives the same value the same
identifier. Loading many facts one at a time is much more expensive than
loading them in one `applyChanges` batch — each statement is its own
transaction and copies the database — so prefer the batch when you have one.

### Join planning

Goals are solved in the order the engine judges cheapest, not the order they
are written. A goal may only move to a position where the variables it
consumes are already bound — a negation, comparison, arithmetic goal, or
correlated `setof` never overtakes what binds it — and among the goals that
may run next the engine takes the one expected to examine the fewest facts,
using the relation sizes and index statistics the store already keeps.
Answers do not depend on the order: they name their variables as the query
does, and the same rows come back either way.

```zig
database.setPlanPolicy(.cost_based);   // default
database.setPlanPolicy(.source_order); // solve goals as written

const plan = try database.explainQuery(&.{
    input.relation("many", &.{input.variable("X")}),
    input.relation("few", &.{input.variable("X")}),
});
defer allocator.free(plan);
// few/1 join scan ~3
// many/1 join index {0} ~8
```

`explainQuery` renders the chosen order, the argument positions each goal is
looked up on, and the candidates the planner expected to examine. It answers
nothing; the caller owns the returned text.

### Query folding

A query asks about relations. Sometimes those relations are no longer there and
only *views* computed from them are — an extract, a summary, a table someone
else maintains. Folding rewrites the query into a plan over what is there, and
tells you what the rewrite is worth.

**This is not the join planner and it is not a query.** `query` answers the
question. `foldQuery` answers nothing: it hands back a plan and a guarantee,
and you decide whether the guarantee is enough before you run it. That
distinction is the whole design — the general case can produce a plan whose
answers are *not* the query's, so a fold can never be applied silently.

```zig
const x = input.variable("X");
const y = input.variable("Y");
const z = input.variable("Z");

// `v` holds the pairs two edges apart. The edges themselves are gone.
_ = try database.defineView(input.fact("v", &.{ x, z }), &.{
    input.relation("edge", &.{ x, y }),
    input.relation("edge", &.{ y, z }),
}, .materialized);

// Ask for the transitive closure of `edge` anyway.
const fold = try database.foldQuery(&.{input.relation("q", &.{ x, y })}, &.{
    input.rule(input.fact("q", &.{ x, y }), &.{input.relation("edge", &.{ x, y })}),
    input.rule(input.fact("q", &.{ x, z }), &.{
        input.relation("edge", &.{ x, y }),
        input.relation("q", &.{ y, z }),
    }),
});
switch (fold.guarantee) {
    .equivalent, .maximally_contained => {
        var answers = try database.answerFolded(fold);
        defer answers.deinit();
    },
    .contained, .unsupported => {
        const why = try database.explainFold(fold);
        defer allocator.free(why);
    },
}
```

**The four guarantees.**

- `equivalent` — the same answers as the query, over any database. Only when
  nothing had to be reconstructed, because everything the query reads was
  available already.
- `maximally_contained` — every answer it returns is one the query returns, and
  no plan over these views returns more. A view remembers less than the
  relations behind it, so this is the best a fold that reconstructed anything
  can promise.
- `contained` — every answer it returns is one the query returns, with nothing
  claimed about how many. Eliminating the terms a reconstruction could not name
  dropped rule instances.
- `unsupported` — there is no plan. Not an empty one, none: `answerFolded`
  reports `PlanNotExecutable` and `explainFold` lists the preconditions that
  were not met.

**Where the loss is.** `maximally_contained` says the plan answers no more than
the query; it does not say where an answer could have gone missing.
`foldReconstructions` names every relation the plan derives instead of reads,
and says of each whether the plan gets all of it — which it does when a
*canonical aggregate view* of that relation was read, because reading such a
view's lists back out returns the relation itself. A plan whose reconstructions
are all exact loses nothing.

**What a plan may read.** By default, only the stored extensions of views
declared `.materialized`. `setViewAvailability` withdraws or restores one, and
a fold that needed a withheld view says so instead of quietly answering less.
`declareBaseAvailable` says a base relation is still there and may be read as
it stands, which is how a caller that has some of its data asks for a hybrid
plan. `publishView` takes the definition from a rule this database already
maintains, so a materialized predicate can be folded against without writing
its definition out twice.

```zig
try database.declareBaseAvailable("label", 2);      // read this one directly
database.setViewAvailability(id, .withheld);        // and not this one
_ = try database.publishView("two", 2, .materialized);
```

**Where a plan runs.** `answerFolded` runs the plan against a copy of the
database holding exactly what the catalog admits, with everything else removed:
the other facts, the database's own rules, and the derived closure. A plan is
built to answer from what remains once the original relations are gone, and
running it somewhere that still holds them would let it read what it was built
to do without. The copy is discarded, so a plan's reconstructed relations never
join the database.

**Plans are cached.** Asking the same question again returns the same plan
without folding it; `fold.reused` says which happened. Any change to the views,
their availability, or the program's rules discards every cached plan, and a
`Fold` handle from before the change reports `StalePlan` rather than naming
whichever plan took its place. `foldStats` reports hits, misses, and discards.

Cost enters folding in exactly one place. When several views reconstruct one
relation *exactly*, they are interchangeable, and the plan reads the one with
the smallest stored extension — ties going to the first declared, so the same
catalog over the same data always reaches the same plan. Cost never chooses a
weaker guarantee to get a cheaper plan.

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
A `Fold` is a handle, not a value: the plan belongs to the database and lives
until the views or the rules change. What comes back from the calls taking one
is the caller's — `answerFolded` returns a `QueryResult` to deinitialize,
`explainFold` returns text to free, and `foldReconstructions` returns a
`Reconstructions` to deinitialize.

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
checked-in aggregation example. The test binary is built in `ReleaseSafe`
rather than following the executable's `Debug` default, because the suite
spends its time running the engine and every safety check still applies. Pass
`-Doptimize=Debug` for the failure that wants a Debug binary to step through.
Individual maintenance steps are also available:

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

```sh
zig build benchmark-projected-aggregate -Doptimize=ReleaseFast
```

```sh
zig build benchmark-maintenance -Doptimize=ReleaseFast
```

```sh
zig build benchmark-structural-deletion -Doptimize=ReleaseFast
```

```sh
zig build benchmark-folding -Doptimize=ReleaseFast
```

See [Aggregation performance](docs/aggregation-performance.md) for the workload
and recorded measurements.
