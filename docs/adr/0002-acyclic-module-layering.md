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
