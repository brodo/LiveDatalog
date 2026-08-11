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
meant for tests.

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

## Query folding

*Not yet reachable from the embedding API.* Folding is built and tested but has
no public entry point, because there is no way for an embedder to declare a
view yet. This section describes what the engine can already do so that the
restrictions below are on record; see [CONTEXT.md](CONTEXT.md) for the
vocabulary and `docs/deferred-projects-plan.md` for the remaining phases.

Query folding answers a query against stored *view extensions* rather than the
relations the views were computed from — the case where the original data is
gone, or is too expensive to read. A view is a rule whose results were kept:
given `v(X, Z) :- edge(X, Y), edge(Y, Z)` and a stored `v`, a fold rewrites a
query over `edge` into one over `v`, by inverting the definition into rules
that reconstruct what its body must have read.

A fold returns a plan *and* a guarantee, because the rewrite can lose answers:

| Guarantee | Meaning |
| --- | --- |
| `equivalent` | The same answers as the query. Nothing was reconstructed. |
| `maximally_contained` | Every answer is the query's, and no plan over these views returns more. |
| `contained` | Every answer is the query's, with nothing claimed about how many. |
| `unsupported` | No plan at all — not an empty one. |

Answers are lost rather than invented because a view remembers less than the
relations behind it. `v` above records that *some* node sits between `X` and
`Z` without recording which, so the reconstructed fact names that node with an
internal term the plan can join on but never return. A query for paths of any
length, folded over `v`, gets the paths of even length.

### When a fold is refused

`unsupported` is the honest answer rather than a plan that is not contained in
the query. A fold is refused when:

- **a relation is not reachable at all** — nothing declares it available and no
  view's body mentions it;
- **the only views that mention it cannot be inverted** — a definition that
  reads what it defines is recursive, one containing `setof` or a negated goal
  is not conjunctive, and one mentioning a list needs the functional-dependency
  work; each is reported separately, naming the view;
- **a view's extension is withheld** by the availability policy;
- **two relations a plan may read share a name and arity**, which a lowered
  plan could not tell apart;
- **a relation the plan would know incompletely is read under negation or
  inside an aggregate.**

The last one is the subtle one, and it is the reason folding cannot be applied
silently. A reconstruction is *contained* in the relation it stands for: it
holds what the views prove existed, which can be less than what was there.
Reading such a relation positively is therefore safe — fewer facts, fewer
answers. Asking what is **not** in it inverts that: `not edge(X, Y)` succeeds
for every edge the views could not prove, so the plan would answer **more**
than the query, which is exactly the containment the guarantee promises. An
aggregate is the same failure counting instead of testing: `setof(Y, edge(X,
Y), S)` over a reconstruction binds a shorter list, and every downstream
comparison against it is then wrong in an unpredictable direction.

This is not something a plan can trade away, so there is no guarantee weak
enough to cover it and the fold refuses. It applies transitively: a predicate
the query derives from a reconstructed relation is no more exact than the
relation, so negating that predicate is refused too. Declaring the underlying
relation available with the catalog's availability policy removes the
objection, because what is there is then known exactly and nothing is
reconstructed.

By contrast, a goal that merely *compares* a reconstructed value — `X != Z`
where one of them is a node the view did not keep — costs answers rather than
soundness. Those rule instances are dropped, the fold still returns a plan, and
the guarantee falls from `maximally_contained` to `contained` with the drop
recorded in the plan's list of transformations.

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

See [Aggregation performance](docs/aggregation-performance.md) for the workload
and recorded measurements.
