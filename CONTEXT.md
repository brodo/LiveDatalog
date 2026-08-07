# LiveDatalog context

## Glossary

### Scalar

A ground, non-structural Datalog value. Scalars include atoms and supported
numeric values. LiveDatalog supports exact signed 64-bit integers and finite
`f64` floating-point values; NaN reports `NumericType` and infinities report
`NumericOverflow` (see `docs/adr/0001-finite-f64-scalars.md`).

Bare signed decimal integer literals denote canonical integer values. Quoted
numeric text remains an atom. Bare decimal or exponent-shaped literals denote
finite `f64` values rounded to nearest; literals beyond the finite range
return `NumericOverflow`, and malformed numeric-leading bare tokens return
`InvalidSyntax`. Bare integer-shaped literals outside the signed 64-bit range
return `NumericOverflow`.

Scalar identity is numeric across integer and floating-point representations.
A finite floating-point scalar that exactly represents an in-range integer
canonicalizes to that integer scalar at intern time, so facts, unification,
equality, and aggregation treat values such as `1` and `1.0` identically.
Floats format deterministically with shortest round-trip digits and reparse
to the same canonical scalar.

Mixed integer and floating-point comparisons are exact and do not first coerce
the integer to `f64`. Mixed arithmetic produces a floating-point result, then
canonicalizes an exact in-range integral result back to an integer scalar.

Canonical ground values have a deterministic total order: numbers in numeric
order, atoms in lexical byte order, `nil`, then cons values lexicographically
by head and tail. The total order reports equality exactly when scalar identity
is equal.

### Materialization

The persistent derived closure. A database with rules materializes lazily at
the first evaluation: the closure store holds base plus derived facts as one
read view, and a tri-state (`uninitialized`, `clean`, `dirty_from_stratum`)
tracks validity. Base updates dirty the first stratum that reads the changed
predicate; rule additions invalidate from the new head's stratum; rebuilds
reuse derived facts below the dirty stratum. Query-local literals and
structures never enter the persistent closure — statements evaluate on
staging clones, and novel ground structures expand a discardable closure
copy.

### Aggregate group

The maintained unit of a rule containing one unnested `setof`. Because
aggregates are evaluated during rule matching rather than stored as their
own relation, a group is identified by the binding of the rule's outer
goals — the variables occurring in the outer clauses or the head — and its
maintained value is the rule's head tuple for that binding. Group existence
therefore comes from the outer goals: a group whose last member disappears
still yields `[]`, while removing the group key removes the tuple.

### Update path

How a base-fact update reaches the derived closure (`update.zig`). Every
update takes exactly one of three paths, all of which yield the same database
a clean rebuild would: incremental insertion propagation through positive
rules, delete-and-rederive for deletions, or a stratum rebuild when the update
reaches negation or an aggregate outside the maintained class. Deletion takes
the rebuild in one further case: it runs a rule backwards from a deleted body
fact to the head it supported, which a seeded structural rule does not permit
because its head carries a variable only the value table binds. Because
maintaining and recomputing differ only in cost, a cost model chooses between
them per update, estimating both from measured work — counted in candidate
facts examined, and attributed so that each candidate moves exactly one of the
two estimates, with a fallback rebuild counting as recomputation rather than
as the maintenance that triggered it. The model is asked with the number of
base facts the caller named, because that is all that is known before applying
them, and taught with the number the update realized. `MaintenancePolicy` pins
the choice when a caller needs one path. Retraction — including pattern
retraction with variables, which the batch API cannot express — resolves its
goals to base facts and takes the deletion path. Aggregate group maintenance
runs on top of the first two. `maintenanceStats` makes the path taken
observable, and shadow verification checks the result against a rebuild before
committing.

One delta reaches the closure through three calls in a fixed order: the
removals, then staging the insertions, then propagating from the watermark
staging returned. Delete-and-rederive joins against a snapshot of the
pre-deletion closure, so a fact staged first would be over-deleted against a
closure it was never absent from. Each half reports whether it maintained or
fell back to a rebuild — a distinction the materialization tri-state cannot
make, because the fallback repairs the closure before returning and leaves it
`clean` either way. A rebuild retires the watermark and has already recomputed
every consequence, so it yields nothing for the aggregate phase to reconsider.

### Projected view

A maintained aggregate rule whose head omits some outer variable, so several
groups can derive the same head tuple. Each projected rule owns an auxiliary
view holding one tuple per derivation — the projected values followed by the
head values — and the number of such tuples is the head tuple's derivation
count. The tuple becomes visible on a zero-to-one transition and is deleted
on a one-to-zero transition. A rule retaining every outer variable needs no
auxiliary view and is self-maintainable. Group identity is the projected
values together with the head variables the outer goals bind; projected
values alone are ambiguous.

### Relation store

The indexed owner of ground facts (`relation_store.zig`). Its
insertion-ordered entry list is the source of truth; exact membership, per
predicate/arity buckets, and lazily created bound-position pattern indexes
are rebuildable caches over it. Pattern indexes are candidate prefilters:
evaluation unifies every candidate, so indexing can never change which facts
match, only how quickly candidates are found. Base and derived facts share
one store per evaluation but stay distinguishable through a per-entry flag.

### Database

The engine's state: the interned program, the base facts, the derived closure,
the auxiliary views, and the materialization tri-state (`database.zig`). Every
layer between the state and the public interface — compilation, validation,
materialization, maintenance, aggregate views, statements, parsing — operates
on a `Database` and does not name the interface above it.

`Jatalog` is what an embedder holds: it owns one `Database` and exposes the
operations that change it. The split is what makes the engine's imports
acyclic; see [ADR 0002](docs/adr/0002-acyclic-module-layering.md).
