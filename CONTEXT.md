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

Every base-fact update takes exactly one of three paths, all of which yield
the same database a clean rebuild would: incremental insertion propagation
through positive rules, delete-and-rederive for deletions, or a stratum
rebuild when the update reaches negation or an aggregate outside the
maintained class. Because maintaining and recomputing differ only in cost, a
cost model chooses between them per update, estimating both from measured
work; `MaintenancePolicy` pins the choice when a caller needs one path. Retraction — including pattern retraction with variables,
which the batch API cannot express — resolves its goals to base facts and
takes the deletion path. Aggregate group maintenance runs on top of the first two.
`maintenanceStats` makes the path taken observable, and shadow verification
checks the result against a rebuild before committing.

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
