# ADR 0002: Acyclic module layering

- Status: accepted
- Date: 2026-08-07

## Context

`root.zig` held the `Jatalog` type, the public re-exports, and most of the
engine's tests. Every layer below it — compilation, evaluation, validation,
materialization, maintenance, aggregate views, the parser — imported `root.zig`
to name `Jatalog`, `Error`, or `input`, and `root.zig` imported all of them
back. Eight modules pointed at the interface, and the interface pointed at all
eight.

Zig permits import cycles, so this compiled. It still cost: no module could be
read or changed without the whole engine in view, the public interface was
indistinguishable from the engine's internals, and there was no direction in
which a reader could work.

## Decision

The engine's imports form a DAG. Three rules produce it.

### The state is at the bottom, the interface at the top

`database.zig` defines `Database`: the interned program, the facts, the derived
closure, and the operations that need nothing but them — lifecycle, staging and
commit, single-fact insertion, result copying, and the materialization
tri-state with the predicates that read and set it.

`root.zig` defines `Jatalog`, which owns one `Database` and exposes the public
operations. Everything between the two — `compile`, `validation`,
`materialization`, `maintenance`, `aggregate_view`, `statement`, `parser` —
takes a `*Database` and never names `Jatalog`.

This is the only arrangement that keeps method syntax on the public API while
letting the layers below stay unaware of it. A module that finds itself needing
`Jatalog` is either misplaced or is reaching for an operation that belongs
lower down.

### Types live below the state that holds them

`Database` has fields whose types would otherwise sit above it, so those types
were moved down: `StringTable` into `string_table.zig`, `AuxiliaryView` into
`auxiliary_view.zig`, and `Materialization` into `database.zig` itself.
Building an auxiliary view is part of materializing, so that code lives in
`materialization.zig`, below the aggregate maintenance that consumes it.

### A layer that needs the database's numbers takes the numbers

Added 2026-08-25, when query folding first had to cost something. The six
folding modules sit at `planner.zig`'s level and none of them takes a
`*Database`, which is what let them be written and tested without the engine in
view. Choosing between two views on the size of their stored extensions is the
first thing folding does that needs a fact the database holds.

It does not take a database to get it. `view_catalog.Catalog` borrows a
`*RelationStore` — a type it already imported — and the interface above points
it at one for the length of a fold. The rule this states is the general one: a
layer that needs a number from below takes *that number*, or the smallest thing
that carries it, rather than the state it lives in. Taking the database would
have given folding access to the rules, the closure and the maintenance
machinery in order to read a length, and every later phase would have found a
use for one of them.

### Tests obey the layering too

A test lives in the module it covers whenever it can be written with imports at
or below that module's level, and moves up only when it cannot.

Two things make most tests stay put. `test_support.zig` takes a `*Database`
rather than the public `Jatalog` and reaches no higher than materialization, so
any module above it can assert with it. And a module whose tests only need to
*drive* the layer under test can do so directly: `parser.zig` builds a
`Database` and runs a `Parser` over it, which is what `Jatalog.execute` does one
layer up, so its tests never mention the interface.

What cannot be written that way is a test that builds its database from source
syntax, because parsing is the top of the engine. Those live in `root.zig`,
alongside the interface they go through — including the tests covering
evaluation, closure maintenance and aggregate views, which would otherwise make
`evaluator.zig`, `maintenance.zig` and `aggregate_view.zig` import the interface
built on top of them.

## Consequences

- The public interface is separable from the engine: `root.zig` is the only
  file an embedder reads, and nothing under `src/` imports it.
- `root.zig` carries most of the suite, because most tests start from source
  syntax. That is the cost of the rule; the alternative is modules importing
  the interface built on them.
- `Database` fields are reachable through `Jatalog.state`. Zig has no private
  fields, so this is a convention, not an enforcement — the same convention
  that already applied to `facts` and `eval`.
- **Zig contributes a file's tests only once something references the file.**
  `root.zig` no longer references every module in its own code, so it carries a
  `test` block naming the ones it does not. A module missing from that block
  still compiles and still passes — it just silently stops being tested. This
  is not hypothetical: during this change the whole suite dropped to zero tests
  while the build stayed green. Check the reported test count, not the exit
  code.
- The rule is mechanically checkable and needs no exemption for tests: no file
  under `src/` may import one at or above its own level, `root.zig` included.

## Addendum: parsing below the state

Added 2026-09-24, when the parser became public. Parsing used to intern into
the database it was pointed at, which put it at the top of the engine and
fused it with running what it parsed. It is now two modules. `parser.zig`
turns text into the borrowed `input` descriptors and imports nothing that
holds state — only `input` and the database-free literal classifier in
`scalar.zig` — so it sits at the bottom beside `input.zig`. `program.zig` runs
`input` statements against a `*Database` through `transaction.zig` (formerly
`statement.zig`) and sits where the parser used to. No new rule was needed:
this is the existing one applied to a layer that turned out not to need the
state at all.

It also retires the reason the tests section above gives for keeping
source-built tests in `root.zig`: parsing is no longer the top of the engine.
A module at or above `program.zig` can build its database from source with
`parser.parseProgram` and `program.execute`, as `program.zig`'s own tests do.
The tests still in `root.zig` for that reason can move down; moving them is a
separate change.

## Addendum: view selection above the program runner

Added 2026-09-24, when the fold code left `root.zig`. `view_selection.zig`
owns the view catalog, the plan cache and answering folded plans, takes a
`*Database` per call, and sits directly below `root.zig` — above
`program.zig` rather than beside it, so that its tests can build their
databases from source through `program.execute` without importing a module at
their own level. Nothing below it needs it. `Jatalog` owns one next to its
`Database` and passes its own state on every call, which is what keeps a
catalog paired with the database whose identifiers it holds.
