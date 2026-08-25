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

Chapter 6's unsound case is a query that reads a reconstruction under negation
or inside an aggregate, and it is refused by default. Two proofs discharge that
refusal and nothing else does: a *canonical aggregate view* of the relation,
which makes the reconstruction equivalent rather than contained, or a
*monotonic query*, whose answers can only shrink when its relations do. Both
are below, and both are checked rather than assumed.

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

A head that projects its collected list away leaves a set with no stored value,
and the plan names it with a Skolem term applied to the head's values — the
same term wherever the definition mentioned that set. The goals *outside* the
aggregate are then reconstructed as any projection is, while the membership
goal that reads the set stands and reaches nothing, because nothing ever stored
what was inside it. Such a view remembers that its outer goals held, which is
worth having and is less than a view that kept the list.

Only non-recursive conjunctions of positive base relations and such aggregates
are inverted. A list outside an aggregate is F5's, and a definition reading
what it defines is recursion inversion cannot bound; each is reported as the
precondition it is. Because a catalog holds one rule per view, self-reference
is the only recursion a definition can express — mutual recursion between views
is not representable rather than undetected.

A relation read under negation or inside an aggregate is refused unless one of
two things is proved of it, because a reconstruction holds what the views prove
existed, which can be less than the relation held: asking what is *not* in it,
or counting what is, would answer more than the query does. The refusal is
transitive, because a rule is no more exact than what its body reads — a
predicate the query derives from a reconstruction is refused under negation
just as the reconstruction is — and what lifts it is a canonical aggregate view
or a monotonic query, both below.

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

Splitting is also what a Skolem *set* becomes. `$member(Y, f(X))` splits into a
two-column relation meaning "Y is in the set f(X)", which is the set reified —
so Chapter 6's `σs2`, the identity saying that collecting the members of a set
gives the set back, holds by construction rather than by rewriting. Nothing
derives that relation, because nothing stored what was in the set, so the goal
is a name the plan can join on and never read.

### Monotonic query

A query whose answers can only grow as the relations it reads grow
(`monotonicity.zig`): Section 6.4.1's restricted class. It matters because a
reconstruction is a *subset*, so a plan runs the query over less than it asked
about. A monotonic query then returns a subset of its answers, which is
containment. One that is not can return an answer the query does not have,
which is Example 6.4.1: `q(a) :- setof(Y, r(a, Y), [])` asks for a collected
set to be empty, and a plan that cannot see what is in the set answers yes.

The check is conservative and admits two collected outputs. A variable nothing
else in the rule reads asks for *whatever set there is*, and every set is one.
`H!T` with both halves likewise unread asks for *some non-empty set*, which is
Section 6.4.1's own contrast, and a set that grows stays non-empty. Anything
else pins the set down — a written-out list to its elements, a variable the
rule reports or reads again to one particular set. A negated goal is refused
first of all: Chapter 6 assumes negation has been rewritten into a `setof` with
an empty output, which is precisely the shape this rejects, so the monotonic
class never discharges a negated read.

### List function

A relation over a list — `sum(L, T)`, `length(L, C)`, Appendix B's whole
catalogue — which in this engine is an ordinary user relation defined by
*seeded structural rules*, not a language feature. Inverting a view that uses
one needs no special machinery: to `inversion.obstacle` a list function is a
positive relational goal over variables, so
`v1(X, T) :- p(X), setof(Y, r(X, Y), S), sum(S, T)` is inside the conjunctive
class and yields Definition 6.5.1's rules unchanged — the collected list
becomes a Skolem set, and the *same* Skolem set stands in the membership goal
and in the reconstructed `sum` fact. That is what Section 6.5's proof means by
saying the list functions in the views are treated no differently than base
relations.

A plan holds no list-function *definitions*. What derives `sum` is the inverse
of a view that stored a sum; the structural rules stay out, because applied to
a set the plan can only name they build a longer list at every step, which is
Example 6.5.1's non-termination. A query that defines its own list function is
therefore either identical to one the views expose, or a conjunction over ones
they do — `excess(L, E) :- sum(L, T), length(L, C), E = T - C` — in which case
the goal is *expanded* into that definition and the definition dropped
(`list_functions.zig`). A query defining one by structural recursion is refused
rather than expanded, wherever in its rules that definition is written.

### Auxiliary view and the chase

What lets two views speak about one set (`list_functions.zig`, driven from
`folding.zig`). A view that collects a set its head does not keep and then
reads it with list functions is two views wearing one head: an auxiliary view
`va(K̄, S) :- Φ(K̄), setof(Ȳ, Ψ, S)` that collects, and a layer
`v(X̄) :- va(K̄, S), λ(S, T)` that reads. Splitting is not tidying — two views
say nothing about each other while each keeps its own copy of the set, and
everything about each other once both are written against one `va`.

`va` is functional in its key, so two views written against one of them read
one set for one group. Inverting a layer names the set it read with a Skolem
term, and the dependency says that term *is* the auxiliary view's set — so the
term is replaced by the variable `va` binds and the goal binding it is joined
on, and the companion rule saying `va` holds that set is dropped as saying only
that it holds what it holds. The equalities are decided while the plan is being
built, by a union-find over set terms, rather than carried in it as Section
6.5's chase rules: `e(X, X)` ranges over every term there is, and a plan that
only answers correctly when something applies its equalities is not a plan.
The union-find terminates because set terms are finite and do not nest, and it
gives symmetry through canonical representatives, which the dissertation's rule
set — reflexivity and transitivity only — does not.

Three conditions decide whether a view has an auxiliary view at all. Its
collecting half has to be a rule, so the key must be bound by the goals that
half kept; and every value the aggregate takes from outside itself has to be
one the head kept, or two stored tuples with one key would have collected
different sets. A view failing either keeps its set nameless, the chase leaves
it alone, and a query reading that set with a list function is `unsupported`
rather than quietly answered from nothing.

The relations *inside* an auxiliary view's aggregate must be known exactly, and
this is the one place in folding where a reconstruction being a subset is not
merely a loss. The layer rule asserts that a view's stored value is what the
list function returns of the set `va` derived; derive a shorter set and the
plan holds a `sum` fact that never held — not less of `sum` but a different
one — and a query reading it answers wrongly however monotonic it is. Only a
canonical aggregate view will do, which is Theorem 6.5.1's second condition
read strictly. Its first condition, a monotonic query, is unreachable here:
reading a collected set with a list function *is* reading the set with a second
goal, which is what Definition 6.4.1's second condition forbids.

### Canonical aggregate view

A view that remembers a whole relation (`view_catalog.zig`), in the sense of
Definition 6.4.3: either the relation copied, `v(X̄) :- r(X̄)`, or the relation
grouped by some of its columns with every other column collected —
`v(Xi1, …, Xik, S) :- r(X1, …, Xn), setof(Ȳ, r(Z̄), S)`, of which there are
`2^n` for an n-ary relation. Inverting one returns the relation itself rather
than a subset of it (Lemma 6.4.2), so a relation such a view reconstructs is
*exact*: it never enters the set of relations the plan knows incompletely, and
there is nothing left for negation or an aggregate to ask about.

The condition is the whole condition. A view that merely mentions the relation
is not one that remembers it; a canonical view of a *different* relation says
nothing about this one; and a canonical view whose extension the policy
withholds discharges nothing, because the plan cannot read it. A fold records
which of the two proofs applied — the relation was reconstructed exactly, or
the query was monotonic — among the transformations it lists, so a plan says
why it was allowed to exist.
