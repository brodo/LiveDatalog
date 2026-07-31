# Deferred DatalogA projects implementation plan

## Goal

Continue from the completed five-phase DatalogA implementation with three
related projects:

1. an indexed evaluation foundation;
2. persistent and incremental view maintenance based on Chapter 5 of
   Mohapatra's dissertation;
3. query folding based on the `InverseAgg` work in Chapter 6.

The projects share storage and rule-analysis infrastructure, but they have
different correctness contracts. Incremental maintenance must produce exactly
the same database as a clean rebuild. Query folding may produce an equivalent
or a maximally contained plan only when its preconditions are proved.

Primary-source notes and the local dissertation are indexed in
[`references/README.md`](../references/README.md).

## Current implementation boundary

The plan assumes the implementation present after aggregation Phase 5:

- `Jatalog.facts` stores base facts and `Jatalog.rules` stores validated rules.
- Every query clones the base facts, calls `expand`, and discards all derived
  facts afterward.
- `expand` reaches a fixpoint one stratum at a time, but each iteration scans
  all rules and relational goals scan the entire fact slice.
- Facts have set semantics, but the engine does not retain rule provenance or
  derivation counts.
- Retraction deletes matching base facts; the next query obtains correct
  derived results by rebuilding them from scratch.
- Structural values are canonical inside `ValueTable`. Query evaluation uses a
  temporary value scope so query-only values do not permanently grow the
  database.
- The aggregate benchmark records the cost of this intentionally naive model
  in [`aggregation-performance.md`](aggregation-performance.md).

These properties make full rebuild the reference implementation and semantic
oracle throughout the deferred work.

## Project ordering

```text
P1 indexed relation store
 ├─> P2 semi-naive evaluation
 │    └─> M1 persistent materialization
 │         ├─> M2 insertion deltas
 │         ├─> M3 deletion and negation maintenance
 │         └─> M4–M6 aggregate maintenance
 └─> F1–F5 query folding
      └─> F6 planner/materialization integration
```

Query-folding transformations can be developed independently after P1, but
automatic reuse of LiveDatalog materialized views belongs after the maintenance
project is stable.

## Shared correctness rules

1. Full rebuild remains available as a public or test-only reference path.
2. Every incremental state transition is atomic: allocation or evaluation
   failure leaves base facts, derived facts, indexes, counts, and aggregate
   state unchanged.
3. Batch updates use set semantics. Repeated insertion of an existing base fact
   and deletion of an absent fact are no-ops.
4. Rule additions, future rule removals, and changes to validation semantics
   may invalidate materialization. The first implementation may rebuild all
   affected strata rather than trying to update rules incrementally.
5. Value IDs are database-local implementation details. Stored views and query
   plans must not assume that IDs are stable across serialization or databases.
6. An optimization may fall back to recomputing an affected stratum or the
   complete closure. It may not return a partial result without making that
   status explicit.
7. Differential tests compare optimized results with a fresh database rebuilt
   from the same base facts and rules after every update batch.

# Project P: indexed and semi-naive evaluation

This project provides the storage operations needed by both incremental
maintenance and practical query folding. It should land before persistent
materialization changes query behavior.

## P1: relation store and indexes

### Scope

- Introduce a `RelationStore` abstraction owning facts by predicate and arity.
- Preserve deterministic iteration where observable results currently depend
  on it.
- Provide exact membership and predicate/arity lookup.
- Add lookup by bound argument positions. Start with lazily created indexes for
  binding patterns actually used by validated rules and queries rather than an
  index for every possible partial atom.
- Route positive matching, negation probes, duplicate checks, deletion, and
  aggregate-body matching through one lookup interface.
- Keep base and derived partitions distinguishable even if they share indexes.

### Acceptance tests

- Existing language and allocation-failure tests pass unchanged.
- Indexed and legacy scan lookups return identical matches for every binding
  pattern over atoms, proper lists, nested lists, and improper lists.
- Predicate names reused at different arities never share an index.
- Insert, duplicate insert, delete, and clear keep every index consistent.
- Random operation sequences agree with a simple unordered reference set.
- The aggregate benchmark reports the new median using the existing protocol.

### Session boundary

Stop when evaluation still rebuilds per query but no semantic path depends on
directly scanning a raw fact slice.

## P2: semi-naive positive recursion

### Scope

- Assign stable internal IDs to rules and body occurrences.
- Track `all`, `delta`, and `next_delta` facts per recursive stratum.
- For each recursive rule application, require at least one recursive body
  occurrence to read from the current delta while the remaining occurrences
  read from the complete relation.
- Deduplicate `next_delta` against both existing closure and the current round.
- Preserve the current special seeding of admissible structural recursion.
- Keep aggregate and negated dependencies outside the recursive strongly
  connected component, as guaranteed by stratification.

### Acceptance tests

- Semi-naive and naive closures are identical for non-recursive, directly
  recursive, mutually recursive, structural-recursive, negated, and aggregate
  programs.
- Multiple recursive body occurrences do not miss derivations.
- Duplicate derivations do not create duplicate facts or endless delta rounds.
- The existing recursive-closure aggregate benchmark improves or records an
  explained regression before merge.

### Session boundary

Stop with query-time rebuilding intact. Persistent state begins in M1.

## P3: join planning and aggregate lookup

### Scope

- Describe each clause's required and produced bindings.
- Choose a safe clause order first, then prefer the most selective available
  index among safe choices.
- Record lightweight relation cardinality and indexed-prefix counts.
- Let `setof` collect projected values from indexed inner matches.
- Avoid sorting only when an index is proven to emit the canonical structural
  order; otherwise retain the current sort and deduplication path.

### Acceptance tests

- Planning never moves a negation, comparison, arithmetic expression, or
  correlated aggregate before its required bindings.
- Forced old and new plans return identical answers.
- Explain output in tests shows the selected clause order and indexes.
- Benchmarks include sparse joins, dense joins, recursive closure, empty
  aggregates, and large aggregate groups.

# Project M: persistent and incremental view maintenance

Chapter 5 defines differential relations and the CReaM optimization for
materialized DatalogA views. LiveDatalog also supports recursive rules and
stratified negation, so the implementation needs an explicit correctness
fallback beyond the dissertation's simplest non-recursive examples.

## M1: persistent closure with rebuild equivalence

### Scope

- Split storage into base facts and a persistent derived closure while exposing
  a unified read view to queries.
- Cache the dependency graph, strongly connected components, stratum mapping,
  and rule-to-predicate dependencies after validation.
- Add materialization state: `clean`, `dirty_from_stratum`, or `uninitialized`.
- Rebuild only when dirty, using the same evaluator as the explicit reference
  rebuild path.
- Make base updates mark the first dependent stratum dirty.
- Define rule-addition behavior: validate first, then invalidate from the new
  head's stratum and rebuild lazily or eagerly according to one documented
  policy.
- Keep query-created structural values separate from values required by the
  materialized closure.

### Acceptance tests

- Repeated queries without updates perform no rule expansion after the first
  materialization.
- Persistent results exactly match the old query-time rebuild for all current
  tests.
- Base updates, rule additions, failures, and deinitialization cannot expose a
  half-built closure.
- Retraction followed by a query remains correct using dirty-stratum rebuild.
- A database with no rules does not allocate derived-state machinery eagerly.

### Session boundary

Stop with persistent materialization but rebuild-based updates. This establishes
the state model before deltas make it more complicated.

## M2: insertion deltas for positive rules

### Scope

- Add a batch update API that records base insertions and deletions separately.
- Propagate base insertions through positive strata using the semi-naive delta
  engine.
- Store, per derived fact, whether it is present and enough support information
  for later deletion work. Do not expose support counts as Datalog values.
- If an update reaches negation or `setof`, mark that stratum dirty and use the
  M1 rebuild path until its specialized phase lands.
- Commit the new closure and indexes only after the entire batch succeeds.

### Acceptance tests

- Insert-only traces over positive recursive programs match full rebuild after
  every batch.
- Inserting a fact that creates many recursive consequences propagates each new
  fact once per delta round.
- Duplicate base insertions produce no derived delta.
- Failures during propagation roll back the complete batch.
- Instrumentation distinguishes incrementally added facts from rebuilt facts.

## M3: deletion, recursion, and stratified negation

### Scope

- Use delete-and-rederive or an equivalent proven algorithm for recursive
  positive components. Plain reference counts are insufficient because cyclic
  derivations can support one another after their base support disappears.
- Maintain derivation counts for acyclic projections where counts are sound and
  useful.
- On deletion, over-delete potentially unsupported recursive consequences,
  then rederive facts that retain an alternative proof.
- For negated dependencies, invalidate and recompute the affected higher
  stratum first. Optimize anti-join deltas only after rebuild equivalence is
  well tested.
- Treat a batch containing both insertions and deletions as one transition from
  the old base snapshot to the new base snapshot.

### Acceptance tests

- Deleting the only base support for a positive cycle removes the entire
  unsupported cycle.
- Alternative recursive and non-recursive derivations preserve a fact.
- Adding and removing a fact correctly toggles conclusions depending on its
  negation.
- Projection counts change without prematurely deleting a still-supported
  tuple.
- Random mixed update traces match a clean rebuild after every batch.

### Session boundary

Stop when ordinary Datalog and stratified negation are incrementally correct.
Aggregate strata may still rebuild.

## M4: materialized aggregate groups

### Scope

- Normalize each maintained aggregate occurrence into an internal auxiliary
  view containing:
  - the correlated group key;
  - the projected member value;
  - support for that member;
  - the canonical aggregate list for the group.
- Maintain member sets independently from downstream list functions.
- Apply inner insertions and deletions to affected groups only; rebuild the
  canonical list for each changed group.
- Represent group existence separately from membership so an enumerated key
  continues to produce `[]` when its last member is removed.
- Emit the old aggregate tuple as a deletion and the new tuple as an insertion
  when a group's canonical list changes.
- Support one unnested `setof` per internal rule first. Normalize multiple and
  nested aggregates into auxiliary rules using the Chapter 3 transformation.

### Acceptance tests

- Member insertion, duplicate derivation, support deletion, last-member
  deletion, and group-key deletion all match full rebuild.
- Empty groups survive exactly when their outer positive goals still derive
  the group.
- Canonical list ordering remains independent of update order.
- Bag emulation retains equal projected values with distinct discriminator
  terms.
- Nested and multiple source aggregates work through normalization.

## M5: projected aggregate views and CReaM counts

### Scope

- Detect outer variables omitted from a maintained view head.
- Materialize an auxiliary view that retains those variables, as in CReaM.
- Maintain a derivation count from auxiliary tuples to each projected view
  tuple.
- Insert the projected tuple on a zero-to-one transition and delete it on a
  one-to-zero transition.
- Keep counts transactional and verify that count overflow is reported rather
  than wrapped.
- Record which views are self-maintainable and which updates require base or
  auxiliary lookups.

### Acceptance tests

- Removing one of several projected derivations leaves the visible tuple.
- Removing the last derivation deletes it.
- A changed aggregate list transfers support from the old tuple to the new
  tuple atomically.
- Counts agree with explicit proof enumeration on bounded test databases.
- The Chapter 5 examples are executable regression tests.

## M6: downstream list functions and maintenance API

### Scope

- Propagate aggregate tuple changes through ordinary downstream strata,
  including admissible list functions and arithmetic.
- Recompute a downstream structural-recursive component when no proven delta
  strategy exists; keep the fallback scoped to the affected component.
- Expose explicit `materialize`, `applyChanges`, `rebuild`, and maintenance
  statistics APIs while preserving `addFact`, source execution, and retraction
  compatibility.
- Document eager versus lazy maintenance, batching, error atomicity, and memory
  ownership.
- Add an optional debug mode that performs an immediate shadow rebuild and
  asserts equality.

### Completion gate

- All existing tests and randomized rebuild-oracle tests pass.
- Insert, delete, and mixed-update benchmarks report time, touched groups,
  delta sizes, rebuild fallbacks, and memory use.
- The 25-node baseline gains a second workload that changes one edge between
  queries and compares incremental maintenance with full rebuild.
- No update category silently falls outside the documented incremental or
  rebuild path.

# Project F: query folding

Query folding is a planner feature, not a transparent evaluator optimization.
Its first API should return a plan and a stated guarantee rather than silently
substitute views. Chapter 6 explicitly shows that unrestricted `InverseAgg`
can produce a plan that is not contained in the original query.

## F1: folding IR, view catalog, and plan guarantees

### Scope

- Add a planner-owned IR separate from executable `Term` and `Clause` storage.
- Represent base predicates, view predicates, variables, constants, internal
  Skolem terms, list constructors, aggregates, and generated equality goals.
- Give variables and generated symbols hygienic identities independent of their
  printed spelling.
- Add a view catalog containing each definition, materialized schema, and
  availability policy.
- Define plan results with an explicit guarantee:
  `equivalent`, `maximally_contained`, `contained`, or `unsupported`.
- Provide deterministic rendering and an explanation of transformations and
  unmet preconditions.

### Acceptance tests

- IR cloning, substitution, variable renaming, and structural-term traversal
  preserve ownership and scope.
- Generated names cannot collide with user predicates or variables.
- Plans round-trip through a debug renderer or execute directly without
  requiring generated syntax to be valid user input.
- An unsupported fold cannot be mistaken for an empty successful plan.

## F2: ordinary conjunctive Inverse Method

### Scope

- Invert non-recursive conjunctive view definitions.
- Replace body-only variables with internal Skolem terms parameterized by view
  head values.
- Combine inverse rules with the supplied query program.
- Implement or port the Skolem-elimination transformation needed for executable
  plans.
- Execute plans against view extensions treated as available relations, not
  against hidden original base facts.

### Acceptance tests

- Reproduce the Chapter 6 even-length-path example.
- Head-preserved variables remain ordinary variables; projected variables use
  consistent Skolem terms across inverse atoms.
- Exhaustive small finite databases confirm containment of produced answers.
- Recursive query rules can consume reconstructed base relations even though
  view definitions themselves are not recursive.

## F3: conjunctive `setof` view inversion

### Scope

- Normalize supported views to one unnested `setof` per generated rule.
- Implement inversion when aggregate output appears in the view head.
- Generate membership goals that reconstruct inner relation facts from the
  stored aggregate list.
- Generate Skolem terms for projected outer and inner variables according to
  the view head and aggregate output.
- Implement the `setof` identities used by `InverseAgg` as explicit,
  terminating planner rewrites rather than runtime axioms.

### Acceptance tests

- Reproduce Chapter 6 examples for an aggregate output retained in the head.
- Ground, variable, structural, nested, and empty aggregate outputs transform
  correctly.
- Normalizing nested aggregates preserves source-level answers before
  inversion.
- Rewrite application terminates and produces deterministic plans.

## F4: projected aggregate output and soundness restrictions

### Scope

- Invert supported views whose `setof` output is projected out, using an
  internal Skolem set and the applicable `setof` identities.
- Implement a conservative monotonicity checker for the Chapter 6 restricted
  query class.
- Recognize canonical aggregate views for relations used inside `setof` or
  negation.
- Return a fold only when one proved condition applies:
  - the query is in the supported monotonic class; or
  - the necessary canonical aggregate views are available.
- Return `unsupported` for the general case demonstrated to be unsound in
  Section 6.4.

### Acceptance tests

- The Chapter 6 non-contained empty-set counterexample is rejected.
- Supported monotonic queries receive a `maximally_contained` guarantee.
- Queries with required canonical aggregate views fold even when non-monotonic.
- Removing one required canonical view changes the result to `unsupported`.
- Bounded exhaustive model tests search for counterexamples to every claimed
  containment guarantee.

## F5: list functions and functional-dependency chase

### Scope

- Initially reject recursive list functions in view definitions unless they
  satisfy the restricted Chapter 6 relationship: a query list function is
  identical to, or a conjunctive view over, list functions exposed by views.
- Split a view into an aggregate auxiliary view and a list-function layer.
- Derive functional dependencies for unique aggregate lists per group key.
- Encode required equalities in a terminating union-find or bounded chase
  implementation; do not materialize unrestricted recursive equality rules.
- Simplify plans by substituting proven-equal Skolem terms and eliminating
  satisfied list-function goals.

### Acceptance tests

- Reproduce the dissertation's average-from-sum-and-count example.
- Arbitrary recursive list-function inversion that would generate infinite
  terms is rejected.
- Equality closure is reflexive, symmetric through canonical representatives,
  and transitive without nontermination.
- Plans lacking the required functional dependency remain unsupported.

## F6: execution integration and view selection

### Scope

- Allow callers to fold against explicitly selected view extensions.
- Optionally expose M-project materialized predicates through the view catalog.
- Cost equivalent plans using relation cardinalities and index availability;
  never let cost override the semantic guarantee.
- Permit hybrid plans using declared available base relations only when the
  caller's policy allows them.
- Cache plans by normalized query, view definitions, availability policy, and
  rule/catalog generation.
- Invalidate cached plans when any dependency changes.

### Completion gate

- API documentation clearly distinguishes query answers from folded plans and
  explains every guarantee.
- End-to-end tests execute equivalent and maximally contained plans against
  view-only datasets.
- Planner tests cover stale-cache invalidation and deterministic plan choice.
- Benchmarks report planning time separately from execution time and compare
  folded execution with direct execution where equivalence is guaranteed.

## Suggested session sequence

Use one session and one commit per phase unless a phase proves too large:

1. P1 relation store and indexes
2. P2 semi-naive evaluation
3. M1 persistent rebuild-equivalent materialization
4. M2 insertion deltas
5. M3 deletion and negation maintenance
6. M4 aggregate group maintenance
7. M5 projected views and CReaM counts
8. M6 downstream propagation and public API
9. P3 join planning and aggregate lookup
10. F1 folding IR and view catalog
11. F2 ordinary Inverse Method
12. F3 conjunctive aggregate inversion
13. F4 soundness restrictions
14. F5 list functions and dependency chase
15. F6 execution and view selection

P3 may move earlier if profiling shows join scans dominate M-project test runs.
F1–F5 may run in parallel with M2–M6 in separate branches because they share
only the stable P1 storage interface.

## Cross-session completion checklist

Each phase ends with:

1. focused semantic and allocation-failure tests;
2. optimized-versus-reference equivalence checks where applicable;
3. `zig build test`, formatting, and lint passing;
4. benchmark results or an explicit note that the phase is not performance
   relevant;
5. public API and ownership documentation updated;
6. completed decisions and new invariants recorded in this document;
7. one phase-scoped commit.

## Open design questions

- Should persistent materialization be eager at update time or lazy at the next
  query? Batch atomicity is required either way.
- Which bound-position indexes justify their memory cost on typical embedded
  workloads?
- Should full rebuild remain public, test-only, or available through a debug
  policy after incremental maintenance is stable?
- Is delete-and-rederive sufficient for the expected recursive workloads, or
  should a later design adopt a differential-dataflow-style timestamp model?
- Should folded plans be returned only as an internal executable IR, or also as
  printable Datalog extended with internal function terms?
- Is `maximally_contained` useful to embedders without an accompanying
  explanation of which source relations could not be reconstructed?

