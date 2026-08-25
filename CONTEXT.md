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
reaches negation or an aggregate outside the maintained class. Because
maintaining and recomputing differ only in cost, a cost model chooses between
them per update, estimating both from measured work — counted in candidate
facts examined, and attributed so that each candidate moves exactly one of the
two estimates, with a fallback rebuild counting as recomputation rather than
as the maintenance that triggered it. The model is asked with the number of
base facts the caller named, because that is all that is known before applying
them, and taught with the number the update realized. `MaintenancePolicy` pins
the choice when a caller needs one path. Retraction — including pattern
retraction with variables, which the batch API cannot express — resolves its
goals to base facts and takes the deletion path. It resolves them against a
copy of the database, because evaluating them interns whatever they name and a
retraction may name values the database has never held; only the facts it
resolved to cross back, and they can because a copy shares the original's value
identifiers. Aggregate group maintenance runs on top of the first two.
`maintenanceStats` makes the path taken observable, and shadow verification
checks the result against a rebuild before committing.

One delta reaches the closure through three calls in a fixed order: the
removals, then staging the insertions, then propagating from the watermark
staging returned. Delete-and-rederive joins against a snapshot of the
pre-deletion closure, so a fact staged first would be over-deleted against a
closure it was never absent from. Each half reports whether it maintained or
fell back to a rebuild — a distinction the materialization tri-state cannot
make, because the fallback repairs the closure before returning and leaves it
`clean` either way. A rebuild retires the watermark and has already recomputed
every consequence, so it yields nothing for the aggregate phase to reconsider.

Over-deletion runs a rule backwards, from a deleted body fact to the head that
derivation supported, and how it names that head depends on the rule. An
ordinary rule's body binding determines its head, so the head is built. A
seeded structural rule's does not — in `length(H!T, N) :- length(T, M),
N = M + 1` nothing in the body names `H` — so its head is instead looked up in
the closure and unified, which is sound because over-deletion only ever acts on
head tuples the closure holds. The candidate is unified into the binding before
the remaining goals are solved, because the seed argument's variables can
appear in the body as well, as `H` does in `sum(H!T, N) :- sum(T, M),
N = M + H`. The lookup is a candidate prefilter like any other, so a head it
cannot constrain costs candidates rather than correctness.

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

### Query fold

A rewrite of a query so that it runs against what is *available* — stored view
extensions, plus whichever base relations a policy declares — together with a
statement of what its answers are worth: `equivalent`, `maximally_contained`,
`contained`, or `unsupported` (`folding.zig`). Folding is not the join planner.
`planner.zig` reorders goals that will be run either way and cannot change
which answers come back, so it applies silently and cannot fail; a fold changes
what is asked, and Chapter 6 shows the unrestricted case producing a plan whose
answers are not the query's. A fold therefore returns a result the caller
inspects rather than a substitution it performs, and `unsupported` carries no
plan at all rather than an empty one, so a fold that found nothing cannot be
read as one that succeeded with nothing in it.

A fold's input is the query's goals *and* the rules it defines its own
predicates by, because the plan is the query's program together with the
inverse rules of the views it needs — Chapter 6's `Q ∪ V⁻¹`. A query already
inside the availability boundary is its own plan and the fold is `equivalent`;
one that needed a reconstruction is `maximally_contained`, or `contained` when
eliminating Skolem terms had to drop rule instances.

### Folding IR

The terms, goals and rules a fold reasons about (`fold_ir.zig`), deliberately
separate from `syntax`, which is what the evaluator runs. Inversion introduces
terms naming a value some fact must have had — Skolem terms — and equalities
nobody wrote, and neither has an executable meaning while the plan is unproved,
so `syntax` has no representation for them. The IR is lowered from `syntax`,
and the only way back out is `folding.lowerPlan`, which takes a plan rather
than arbitrary IR and refuses one still holding a Skolem term: eliminating them
is what earns the way back, and there is no general lifting function. Identity
here is an entry in a
`Symbols` table and the printed name is a lookup, so variables spelled alike in
different scopes stay distinct and a generated symbol cannot collide with a
user one. Generated symbols additionally print with characters no user
identifier can contain, so a rendered plan cannot be mistaken for a program
somebody wrote.

### View catalog

What a fold is allowed to read (`view_catalog.zig`): each view's definition in
the folding IR, the schema its stored extension holds — an aggregate output is
a list column whatever the head spells it — and its availability, which is
policy and can be withdrawn without the definition becoming unknown. A view is
identified by its catalog entry rather than its name, so a view and a base
relation spelled alike are never one predicate. The catalog owns the symbol
table its definitions share with the queries folded against it, and its
identifiers are the database's: a catalog outliving that database resolves
nothing.

### Inverse Method

How a fold gets a relation the catalog does not have (`inversion.zig`). A
view's definition is run backwards: each body goal must have had a fact behind
it, so each becomes a rule deriving one from the view's stored tuple. A
variable the head kept is still a value a plan can name, so it stays a
variable; a variable the head projected away becomes a Skolem term applied to
the head's values — one function per projected variable, shared by every rule
that view yields, because the reconstructed facts have to join back up.
Chapter 6's even-length paths only exist because the node between `X` and `Z`
is the same `f(X, Z)` in both halves.

A definition may also *collect*: `setof` gathers every value satisfying its
body into one list. Inverting that reads the list back — each value in it is a
fact the aggregate's body must have had — through `$member`, a relation the
fold defines itself with three rules rather than a builtin, because a list the
database holds already holds each of its own tails. What the head must keep is
the *list*, not a variable holding one: a definition that wrote it down fixes
it just as firmly. Aggregates nest by chaining, since collecting `Y!T` pairs
means binding one of them binds the inner list `T`; and two aggregates side by
side mean their own values by the names they share, so each gets its own
Skolem functions.

A value projected out of an aggregate's own body has one witness per collected
value rather than one per stored tuple, so its Skolem term is applied to the
collected value too. A value the definition binds outside its aggregates keeps
the per-tuple naming, which is what preserves the join between the two halves.

Only non-recursive conjunctions of positive base relations and such aggregates
are inverted. A list outside an aggregate is F5's, a collected list the head
does not keep is F4's, and a definition reading what it defines is recursion
inversion cannot bound; each is reported as the precondition it is.
Because a catalog holds one rule per view, self-reference is the only recursion
a definition can express — mutual recursion between views is not representable
rather than undetected. A relation read under negation or inside an aggregate
is refused outright rather than reconstructed: a reconstruction holds what the
views prove existed, which can be less than the relation held, and asking what
is *not* in it would answer more than the query does. The refusal is
transitive, because a rule is no more exact than what its body reads: a
predicate the query derives from a reconstruction is refused under negation
just as the reconstruction is.

### Skolem elimination

What makes an inverted plan runnable (`inversion.zig`). A Skolem term is not
substituted — there is no value to put in its place — but it is fully described
by its function and the arguments it was applied to, so the relation holding it
is *split*: one relation per assignment of a function to each column, with that
column spread across those arguments. Rules are instantiated once per
combination of splits they can read, and the query's answers are the tuples of
the split whose columns all stayed ordinary, which is exactly the answers a
Skolem term never reached. The split with no function in it keeps the original
predicate, so goals over relations that were available all along are unchanged.

The transformation is finite because Skolem terms never nest: one is built only
in an inverse rule's head, out of values read from a stored extension. A goal
that is not a positive relation must see ordinary values, and an instance where
it would not is dropped — which loses answers, keeps containment, and lowers
the guarantee from maximally contained to contained.
