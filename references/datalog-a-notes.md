# DatalogA implementation notes

## Source

Abhijeet Mohapatra, *Aggregates in Datalog*, Stanford University doctoral
dissertation, December 2019. The canonical Stanford record is
<https://purl.stanford.edu/rx626ty8196>. Page numbers below refer to the page
numbers printed in the dissertation.

These notes summarize implementation-relevant claims from the primary source.
They are not a replacement for the definitions and proofs in the dissertation.

## Core language model

DatalogA adds finite lists as first-class terms. The empty list is `nil` or
`[]`; `cons(H, T)`, `H!T`, and bracket notation construct non-empty lists.
Although `cons` can represent nonlinear structures, the dissertation presents
its results using linear, potentially nested lists. List relations such as
`length` and `member` are defined as ordinary recursive rules rather than fixed
aggregate primitives. (Section 3.1, pp. 10–11.)

Unrestricted structural recursion makes the language capable of producing
infinite answers. The dissertation therefore adopts admissibility: for every
recursive call involving `cons`, some non-empty set of bound arguments must
contain at least one argument whose size decreases while the other tracked
arguments do not increase. Admissible queries have finite answers. (Definition
3.1.1 and Lemma 3.1.1, p. 12.)

## `setof`

The general aggregation operator has the form `setof(Z, Goals, S)`. `Z` is the
projection or aggregation term, `Goals` is a conjunction that may itself
contain aggregate goals, and `S` is the output term. For fixed correlated
inputs, the output is a sorted list containing each successful projection
exactly once. The particular total order is immaterial, but uniqueness and a
stable order are semantic requirements. (Section 3.2, p. 12.)

An aggregate over no matching values produces the empty list. Consequently,
enumerating group keys outside `setof` produces a result for every key,
including keys whose group is empty. The dissertation's example derives both
`children(a, [b])` and `children(b, [])`. (Example 3.2.1, pp. 12–13.)

Count, sum, and similar operations are expressed by feeding the generated list
to user-defined list relations. Bag-like aggregation remains expressible under
set semantics by projecting a compound value that includes a distinguishing
identifier, then projecting the desired component from the resulting list.
(Examples 3.2.2 and 3.2.3, p. 13.)

## Safety and stratification

A rule containing `setof` is safe only when head variables are supplied by a
positive non-aggregate goal or by aggregate output, and variables correlated
into the aggregate body are supplied by a positive outer goal when they are not
part of the aggregate projection or output. (Definition 3.2.1, pp. 13–14.)

The dependency graph distinguishes ordinary positive edges from strict
aggregate edges. Every predicate used inside an aggregate body contributes a
strict edge from the rule's head predicate. A program is stratified exactly
when no dependency cycle contains such an edge. The stratum of a predicate is
determined by the maximum number of strict edges along a dependency path.
(Definitions 3.2.2–3.2.4, pp. 14–15.)

Thus positive recursion may compute a relation in one stratum and a later
stratum may aggregate its completed extension, but a predicate may not recurse
through its own `setof`. (Examples surrounding Figure 3.1, p. 15.)

## Bottom-up semantics

Within one stratum, rules are repeatedly applied until a fixpoint. Strata are
then evaluated in order. A ground `setof` instance succeeds when its output is
the set of projected values satisfying its body in the available lower-stratum
extension. New structural terms need not be pre-enumerated; they may be added to
the working universe as rules derive them. (Section 3.3, pp. 15–16.)

The worked example first computes a recursive transitive relation and only then
aggregates it, producing both a non-empty list and an empty list. (Example
3.3.1 and Figure 3.2, pp. 16–17.)

Rules with multiple or nested aggregate goals can be rewritten into rules with
at most one `setof` goal. Safe, stratified, admissible programs with finitely
many goals terminate with finite answers. (Lemma 3.3.1 and Theorem 3.3.1,
pp. 17–18.)

## Incremental maintenance is a later layer

Chapter 5 does not change the Chapter 3 meaning of aggregation. It derives
differential relations for insertions and deletions to maintain materialized
views. The approach isolates `setof` in an auxiliary view, updates the stored
set by list difference and union, and then reapplies list functions to the
updated tuple. (Sections 5.1–5.2, pp. 29–31.)

The maintenance rules distinguish views that retain all outer grouping
variables from views that project some of them away. Projection requires
tracking whether alternative derivations still support a view tuple. (Sections
5.2.1–5.2.2, pp. 31–34.)

LiveDatalog currently reconstructs derived facts at query time. Implementing
Chapter 5 therefore requires a separate persistent-view and delta-maintenance
design; it is not necessary for a correct first implementation of the Chapter
3 semantics.

## Query folding

Chapter 6 defines query folding as finding a query plan over supplied views
that is equivalent to a query, or otherwise maximally contained in it. The
ordinary Inverse Method reconstructs view-body relations with inverse rules;
variables omitted from a view head become Skolem terms parameterized by the
head. The resulting rules can feed recursive query definitions. (Sections
6.1–6.2, pp. 39–41.)

`InverseAgg` extends inversion to conjunctive `setof` views. It first rewrites
multiple or nested aggregates so generated rules contain a single unnested
aggregate, then inverts outer and inner relations and uses list membership to
recover facts represented by an aggregate output. Aggregate output omitted
from a view head is represented internally by a Skolem set. (Sections
6.3–6.3.2 and Algorithms 6.1–6.2, pp. 41–45.)

The unrestricted transformation is not sound: the dissertation gives a query
whose folded plan is not even contained in the original query. It proves
maximal containment only for restricted monotonic DatalogA queries, or when
canonical aggregate views are supplied for relations used inside aggregates
and negation. An implementation must therefore reject unsupported folding
problems rather than assume that every generated plan is valid. (Section 6.4,
Definitions 6.4.1–6.4.3 and Theorems 6.4.1–6.4.2, pp. 45–51.)

Arbitrary recursive list functions in view definitions can make inverse plans
non-terminating. The dissertation sketches a restricted extension when query
list functions are identical to, or conjunctive views over, functions exposed
by the supplied views. It uses auxiliary aggregate views and functional-
dependency chase rules to equate Skolem sets. (Section 6.5, pp. 51–57.)

## Consequences for LiveDatalog

- Flat interned scalar terms are insufficient; unification and bindings must
  support structural ground values and list patterns.
- Aggregate goals need their own syntax tree node because their body is a
  nested conjunction with local and correlated variables.
- Existing negation strata provide a useful basis, but aggregate bodies add
  dependencies for every predicate nested inside them.
- `setof` must bind `[]` rather than fail when its inner query has no answers.
- Exact deduplication and deterministic structural ordering are part of
  correctness, not optional presentation details.
- Direct built-ins for `count` and `sum` would be useful conveniences but would
  not implement the general DatalogA model.
- A practical release must state and enforce its admissibility subset before it
  allows recursive structural rules.
