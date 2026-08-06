# Deferred DatalogA projects implementation plan

## Goal

Continue from the completed five-phase DatalogA implementation with four
related projects:

1. first-class finite `f64` scalars;
2. an indexed evaluation foundation;
3. persistent and incremental view maintenance based on Chapter 5 of
   Mohapatra's dissertation;
4. query folding based on the `InverseAgg` work in Chapter 6.

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
- Atoms and exact signed 64-bit integers are canonical scalars. Bare decimal
  and exponent-shaped literals are reserved with `NumericType` until the
  floating-point project below lands.
- Structural values are canonical inside `ValueTable`. Queries and retractions
  use transactional staging so query-only scalars, symbols, and structures do
  not permanently grow the database.
- Typed input uses borrowed `input.Term` and `input.Goal` descriptors. Query
  results own their names, scalars, and reachable structures independently of
  the originating database.
- The aggregate benchmark records the cost of this intentionally naive model
  in [`aggregation-performance.md`](aggregation-performance.md).

These properties make full rebuild the reference implementation and semantic
oracle throughout the deferred work.

## Project ordering

```text
S1 finite-f64 policy and syntax
 └─> S2 canonical numeric semantics
      └─> S3 embedding, results, and migration
           └─> P1 indexed relation store
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

# Project S: first-class finite `f64` scalars

This project extends the scalar policy established by first-class integers.
It must remain local to the scalar and input-compilation layers: structural
terms continue to contain one opaque scalar identity, and callers never observe
representation-specific scalar IDs.

## S1: finite-value policy, syntax, and formatting

### Scope

- Record an ADR fixing the public behavior for NaN, infinities, overflow, and
  underflow before implementation. The default policy is to accept finite
  values only; typed non-finite inputs fail during compilation, and arithmetic
  that produces a non-finite result reports a numeric error.
- Parse the already-reserved decimal and exponent forms as `f64` without
  changing quoted values: `'1.0'` remains an atom.
- Keep integer-shaped source literals on the checked `i64` path, including
  `NumericOverflow` immediately outside the integer limits.
- Define a deterministic, locale-independent, round-trippable spelling for
  non-integral floats. Values canonicalized to integers format as integers.
- Preserve the parser-extraction boundary: numeric recognition and
  canonicalization belong to the scalar module rather than introducing a
  parser dependency into it.

### Acceptance tests

- Decimal and exponent literals cover positive, negative, subnormal, minimum
  normal, and maximum finite values.
- Quoted decimal and exponent text remains atom data in facts, equality,
  structures, formatting, and `setof`.
- Malformed numeric-looking source remains an explicit syntax or numeric error
  according to the documented grammar; it is never silently reclassified.
- Every formatted float parses back to the same canonical scalar identity.
- The selected non-finite and arithmetic-overflow errors are stable public
  behavior and allocation safe.

### Completed decisions

S1 was completed on 2026-08-06 with these decisions, recorded in
[ADR 0001](adr/0001-finite-f64-scalars.md):

- Only finite `f64` values are scalars. NaN reports `NumericType`, infinities
  report `NumericOverflow`. Literals round to nearest; overflow beyond the
  finite range is `NumericOverflow`, and gradual underflow (including rounding
  to zero) is accepted.
- Canonicalization happens at intern time in `scalar.Store.internFloat`: an
  integral float exactly representable as `i64`, including both zero signs,
  interns as the equal integer scalar. Stored floats are therefore non-integral
  or have magnitude at least 2^63, which makes float equality plain value
  equality.
- Floats format with shortest round-trip digits: plain decimal for
  non-integral magnitudes in `[1e-3, 1e16)`, scientific notation otherwise.
  Every spelling reparses to the same canonical scalar identity.
- Malformed numeric-leading bare tokens (`1e`, `1.2.3`, `12abc`) now report
  `InvalidSyntax` instead of silently parsing as atoms, and digit-leading
  atoms always format quoted.
- Exact mixed integer/float ordering landed early (S2 scope) because the total
  ground order and `setof` sorting need it as soon as floats exist: the float
  is floored to an exact `i64` rather than rounding the integer through `f64`.
  Comparison builtins accept mixed numerics; `+` and `-` remain integer-only
  (`NumericType` on a float operand) until S2.

## S2: canonical mixed numeric semantics

### Scope

- Extend `scalar.Store` with canonical finite `f64` values while keeping
  `scalar.Id` opaque and leaving structural term/value variants unchanged.
- Canonicalize every exactly representable in-range integral float to the
  existing integer scalar. This includes both floating-point zero signs.
- Define scalar equality numerically rather than by representation: `1`,
  `1.0`, and `1e0` share one identity, while nearby values remain distinct.
- Compare mixed integers and floats exactly without first converting the
  integer to `f64`. Preserve the total ground-value order: all numbers in
  numeric order, atoms lexically, `nil`, then cons values recursively.
- Extend addition and subtraction so integer-only operations remain checked
  `i64`, while an operation involving a float produces `f64` and then
  canonicalizes an exact in-range integral result back to an integer.
- Route unification, explicit equality, fact deduplication, arithmetic output
  checking, structural equality, ordering, and `setof` deduplication through
  the same canonical scalar identity.

### Acceptance tests

- `1`, `1.0`, `01`, and `1e0` deduplicate in facts and aggregates; quoted
  equivalents remain distinct atoms.
- Mixed equality and ordering are exact around `2^53`, both `i64` limits, and
  adjacent representable floats. Total ordering reports equality exactly when
  scalar identity is equal.
- Numeric semantics remain correct recursively inside proper and improper
  lists and nested aggregate templates.
- Integer-only overflow behavior is unchanged. Mixed positive and negative
  addition/subtraction cover binding, bound-output success and mismatch,
  underflow, overflow, and canonical integral results.
- Source and typed programs produce identical answers for every supported
  mixed numeric operation.

### Completed decisions

S2 was completed on 2026-08-06. Canonicalization, numeric identity, and exact
mixed ordering had already landed with S1 (see the S1 decisions and
[ADR 0001](adr/0001-finite-f64-scalars.md)); S2 added mixed arithmetic:

- `scalar.Store.add` and `subtract` keep integer-only operands on the checked
  `i64` path. Any float operand promotes both operands to `f64` (the integer
  via round-to-nearest), computes in `f64`, and interns through `internFloat`,
  which reports `NumericOverflow` for a non-finite result and canonicalizes an
  exact in-range integral result back to an integer scalar.
- Consequently a mixed operation on an `i64` extreme can yield an
  out-of-range integral float that stays a float, for example
  `9223372036854775807 + 0.5 = 9.223372036854776e18`. This is accepted rounding
  behavior for mixed arithmetic, unlike comparisons, which never round.
- Gradual underflow in arithmetic results is accepted down to subnormals and
  exact zero, which canonicalizes to integer `0`.
- Unification, equality, fact deduplication, structural equality, ordering,
  and `setof` deduplication needed no changes: they already flow through
  canonical scalar identity, now verified by boundary, list, nested-aggregate,
  and typed-versus-source parity tests.

## S3: typed embedding, owned results, and migration

### Scope

- Add an allocation-free `input.float` descriptor helper without changing
  list, cons, relation, or goal descriptor shapes.
- Add `ResultValue.getFloat` and `Answer.getFloat`. Preserve distinct
  `UnknownVariable` and `TypeMismatch` errors; integer getters never coerce
  floats and float getters never coerce integers. An integral float
  canonicalized to an integer is consequently retrieved with `getInteger`.
- Copy float values into self-contained `QueryResult` storage so results remain
  readable after database destruction.
- Preserve strong per-operation rollback for typed input, each parsed
  statement, queries, result construction, and retractions. Novel float query
  literals and derived values must not grow persistent storage.
- Update the README, language tutorial, CLI help, examples, and benchmarks to
  describe mixed numeric identity, construction, access, formatting, and the
  chosen finite-value policy.

### Completion gate

- Public-interface tests cover source and typed construction, getters,
  structural inspection, result lifetime, query-local storage, and every
  numeric error boundary.
- Exhaustive allocation-failure tests prove rollback and cleanup across scalar
  interning, input compilation, evaluation, answer copying, and result
  construction.
- Existing integer, aggregation, recursive-list arithmetic, retraction, and
  CLI behavior remains green without representation-specific test access.
- `zig build test` and the ReleaseFast aggregation workload pass, with any
  performance change recorded.

### Completed decisions

S3 was completed on 2026-08-06, finishing Project S:

- `input.float` is an allocation-free descriptor like the other scalar
  helpers. Non-finite values fail during compilation inside `internFloat`
  (NaN as `NumericType`, infinities as `NumericOverflow`) under the existing
  per-operation staging, so failed typed input rolls back completely.
- `ResultValue.getFloat` and `Answer.getFloat` mirror the integer getters
  with distinct `UnknownVariable` and `TypeMismatch` errors and no numeric
  coercion. Because canonicalization happens at intern time, an integral
  float stored through any path is retrieved with `getInteger`; `getFloat`
  returns only values that remained floats. `ResultValue.Kind` gained a
  `float` case (already public since S1).
- Result nodes copy floats by value, so query results with floats stay
  readable after database deinitialization like atoms and integers.
- The CLI example now exercises mixed numeric identity (`limit(2.0)`
  compared against integer list lengths), and the build's expected-output
  drift test covers it. README, tutorial, and REPL help describe the policy,
  identity, construction, access, and formatting.

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

### Completed decisions

P1 was completed on 2026-08-06 with these decisions:

- `relation_store.zig` owns `Fact`, `PredicateKey`, and `RelationStore`. The
  insertion-ordered entry list is the source of truth and keeps answer order
  deterministic; exact membership, per-predicate/arity buckets, and
  bound-position pattern indexes are lazily built caches over it. A cache that
  cannot absorb an insert is destroyed and rebuilt on next use, so caches are
  always either consistent or absent; removal drops all caches.
- Pattern indexes are candidate prefilters keyed by a hash of the projected
  bound values. Evaluation always unifies every candidate, so hash collisions
  and positions past 64 can only add candidates, never hide matches.
  Bound positions are resolved through `termToValue` under the current
  bindings, so ground structural terms index by canonical value identity.
- Positive matching, negation probes, aggregate bodies (via recursion),
  duplicate checks in `addFact` and `expand`, retraction matching, and
  retraction commits all route through `insert`/`contains`/`lookup`. Query
  evaluation clones the base store and `expand` inserts derived facts marked
  with a per-entry `derived` flag, keeping the partitions distinguishable.
- The aggregation benchmark median improved from 6.117 ms to 1.995 ms per
  query (about 3.1x).

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

### Completed decisions

P2 was completed on 2026-08-06 with these decisions:

- Rules carry a stable database-local `id` assigned from a never-reused
  counter that survives cloning; body occurrences are identified by
  `(rule id, clause index)`.
- Deltas are store index ranges rather than separate relations: because the
  relation store appends in derivation order, `delta` is the range of
  entries added in the previous round and `next_delta` accrues past the
  range's end, with set-semantics insertion deduplicating against both the
  closure and the current round automatically.
- `expandLevel` runs round zero naively, then re-evaluates each rule once
  per *growing* body occurrence with that occurrence restricted to the delta
  range. A predicate is growing when it belongs to the current stratum or is
  the head of an active seed rule — the latter matters because seeded
  structural recursion (which keeps its naive evaluation over the value
  table) inserts lower-stratum facts during a higher stratum's rounds.
- Rounds continue while facts append or the value table grows, matching the
  naive fixpoint condition; stratification keeps negated and aggregate
  dependencies below the stratum, so they never need delta treatment.
- `expandNaive` remains as the in-tree semantic oracle, and differential
  tests compare both closures for joins, direct, mutual, and structural
  recursion, negation, aggregation, double-recursive rules, and
  multi-proof diamonds.
- The aggregation benchmark median improved from 1.995 ms to 0.910 ms per
  query.

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

### Completed decisions

M1 was completed on 2026-08-06 with these decisions:

- The committed database owns `closure` (a relation store holding the base
  facts plus every derived fact as one unified read view), a
  `materialization` state (`uninitialized`, `clean`, or
  `dirty_from_stratum`), and a cached `Analysis` (stratum mapping plus the
  first dependent stratum of every predicate read in a rule body). All three
  stay null/uninitialized until the first evaluation on a database with
  rules.
- Materialization is lazy at the next evaluation, and rebuilds are partial:
  `buildClosure(from)` clones the current base facts, retains derived facts
  of strata below `from` from the old closure, and re-expands the rest with
  the same semi-naive evaluator used by the reference rebuild. Base changes
  dirty the first dependent stratum of the changed predicate (or the level
  past the last stratum when no rule reads it, refreshing only the base
  partition). Rule additions validate first, then invalidate from the new
  head's stratum under the new analysis — lazy rebuild is the documented
  policy.
- Queries and retractions materialize the committed database *before*
  cloning statement staging, so the staged copy shares the closure's value
  identifiers and evaluation never expands. The parser classifies each
  statement by a terminator peek so bulk fact loads never trigger rebuilds;
  atomicity keeps the staging-and-commit pattern unchanged. On
  materialization failure the previous closure stays installed; values
  interned by the aborted expansion remain until deinit (documented, not
  observable through query results).
- Ground query structures that are new to the value table still join the
  seed set of admissible structural recursion: the staged database expands
  its own discardable closure copy for that query only, keeping query-local
  derivations out of persistent state.
- A new `benchmark-materialization` workload (20 repeated queries over 14
  rules) dropped from a 5.262 ms/query pre-M1 median to 23.3 us/query, and
  the aggregation workload median improved from 0.910 ms to 52.1 us.

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

### Completed decisions

M2 was completed on 2026-08-06 with these decisions:

- `applyChanges(insertions, deletions)` is the batch API, taking exact
  ground `input.Relation` descriptors (built with the new `input.fact`
  helper) with set semantics. The batch runs on staging and commits only
  when something changed, so failures roll back completely and a fully
  no-op batch leaves no trace.
- Insertions into a clean materialized closure append to both the base
  store and the closure, then propagate stratum by stratum with the
  semi-naive delta engine: no naive round zero, the initial delta is the
  batch's index range, and every relational body occurrence is delta-joined
  because a batch may grow predicates at any lower stratum. Statement-level
  `addFact` keeps the M1 dirty-marking path.
- A stratum blocks propagation only when one of its rules reads a
  *grown* predicate through negation or anywhere inside a `setof` body;
  negation over unchanged predicates propagates incrementally. A blocked
  stratum is marked dirty and rebuilt through the M1 path, keeping the
  incrementally updated strata below it.
- Deletions always take the dirty-stratum rebuild path in M2, and a batch
  containing an effective deletion disables propagation for its insertions.
- Relation-store entries now carry a `support` counter (first insertion
  plus one per duplicate attempt) as internal scaffolding for M3 deletion
  work; it is never exposed as a Datalog value. The `propagated_facts`
  counter distinguishes incrementally added facts from rebuilt facts, and a
  test pins that one edge insertion into a three-edge chain propagates
  exactly the four new derived paths.

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

### Completed decisions

M3 was completed on 2026-08-06 with these decisions:

- `applyChanges` treats a batch as one transition by running deletions as
  phase A (delete-and-rederive) and insertions as phase B (the M2 delta
  engine). Sequencing keeps phase B's append-only index-range deltas valid,
  and a fact deleted then re-inserted in one batch is simply rederived by
  phase B — the final state always equals a clean rebuild.
- Over-deletion pins each deleted fact at every matching body occurrence
  and joins the remaining clauses against a snapshot of the pre-deletion
  closure, so derivations that consumed several deleted facts are still
  found. Rederivation unifies each over-deleted fact with matching rule
  heads and evaluates bodies against the reduced closure, repeating until
  chains of rederivations settle. Reference counts are deliberately not
  used to skip over-deletion: support counters remain approximate
  bookkeeping, and cyclic derivations require the over-delete/rederive
  discipline anyway.
- Both phases are per-stratum with the same fallback: a stratum whose rules
  read a shrunk (or grown) predicate through negation or inside a `setof`
  body is invalidated and recomputed via the dirty-stratum rebuild, with
  maintained strata below it retained. Anti-join negation deltas remain
  future work as planned.
- The pinned-occurrence join needs no evaluator changes: matching uses the
  rule body with the pinned clause removed and its bindings pre-applied,
  which is safe because clause-order validation only requires binders to
  precede consumers. Numeric errors during pinned matching are swallowed
  exactly as in seeded rule application.
- A `removed_facts` counter mirrors `propagated_facts` for instrumentation,
  and a 40-batch random mixed-update trace over a program with recursion,
  negation, and aggregation matches a clean rebuild after every batch.

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

### Completed decisions

M4 was completed on 2026-08-06 with these decisions:

- Aggregates are evaluated inside rule matching rather than stored as
  separate relations, so the maintained unit is the *rule head tuple per
  group* rather than a standalone auxiliary aggregate view. Group identity
  is the binding of the rule's outer goals: variables that occur in the
  outer clauses or the head. This gives the auxiliary view's group key,
  member projection, and canonical list without a second storage format.
- `stratumImpact` replaced the earlier boolean block check. Negation over a
  changed predicate still forces the stratum rebuild; an aggregate over a
  changed predicate forces it only when the rule is outside the maintainable
  class (`maintainableAggregateIndex`): exactly one `setof`, not nested, and
  not a seed rule.
- `maintainAggregates` runs after the deletion and insertion phases over the
  batch's touched facts. For each maintainable rule whose inner relations
  changed it derives candidate groups by unifying each touched fact with the
  aggregate's inner clauses, restricting the binding to group scope, and
  solving the outer goals; only those groups are recomputed. A group's stale
  head tuples become deletions and its recomputed tuple an insertion, which
  cascade through the existing delete-and-rederive and delta engines, so
  downstream strata and structural list functions update without extra
  machinery. Rounds repeat while results keep changing, bounded by the
  stratum count with a documented full-rebuild fallback.
- Group existence is separate from membership for free: because groups come
  from the outer goals, a group whose last member disappears still yields
  `[]`, while deleting the group key removes the tuple. Both directions are
  tested, including restoring a deleted key.
- Multiple and nested aggregates per rule remain outside the maintained
  class in this phase and take the documented stratum-rebuild fallback;
  they are covered by rebuild-equivalence tests. The Chapter 3 normalization
  into auxiliary rules is deferred rather than implemented here.

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

### Completed decisions

M5 was completed on 2026-08-06 with these decisions:

- A maintained aggregate rule is *projected* when its head omits some outer
  variable, matching the Chapter 5 Case 2 / Section 5.2.2 distinction.
  `projectedVariables` computes that set; a rule keeping every outer
  variable is self-maintainable in the sense of Corollary 5.2.1 and keeps
  the M4 path, because each of its head tuples belongs to exactly one group.
- Each projected rule gets an `AuxiliaryView` holding one tuple per
  derivation: the projected values followed by the head values they derive.
  This is exactly the chapter's `v_c` counting view, with the count stored
  as tuple multiplicity rather than a separate number.
- The derivation count is *derived* from the auxiliary view by an indexed
  lookup rather than stored alongside it, so it cannot drift from the
  tuples it summarizes; it is transactional because the auxiliary views live
  in the staged database and are rolled back with it. `derivationCount`
  reports `NumericOverflow` rather than wrapping when a count exceeds the
  counter width.
- A projected head tuple becomes visible only on a zero-to-one transition
  and is deleted only on a one-to-zero transition, so a group whose
  canonical list changes transfers its whole support from the old tuple to
  the new one inside one batch.
- Group identity is the projected values *together with* the head variables
  the outer goals bind — projected values alone are ambiguous, since
  different groups can share them. Both the per-group tuple lookup and the
  vanished-group sweep therefore re-unify a stored tuple's head portion
  against the rule head before treating it as belonging to a group. The
  randomized count-versus-enumeration test caught this.
- Projected views also react to outer-goal changes, which create and destroy
  whole groups; a group with no remaining outer solution has its auxiliary
  tuples swept. Delete-and-rederive still backstops every path, so an
  imprecise transition cannot produce a wrong closure.
- `maintenanceStats` records the classification the phase asks for: closure
  size, propagated and removed facts, stratum expansions, and the counts of
  self-maintainable views, projected views, and auxiliary tuples.
- Chapter 5 Examples 5.2.1 and 5.3.1 are executable regression tests,
  including the `v_c` counts of 2 and 1 and the two-step deletion that keeps
  and then drops `v(a, [1, 2])`.
- A `benchmark-projected-aggregate` update workload compares M5 against the
  M3 rebuild path. Incremental aggregate maintenance is *not* uniformly
  faster: rebuild wins below roughly 100 groups and maintenance wins above
  it, because maintenance carries fixed per-batch overhead while rebuild
  cost scales with the group count. See
  [`aggregation-performance.md`](aggregation-performance.md) for the numbers
  and the two follow-ups it suggests, both deferred to M6: avoiding the
  whole-closure snapshot taken for over-deletion, and falling back to a
  stratum rebuild when the affected groups approach the total.

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

### Completed decisions

M6 was completed on 2026-08-06, finishing Project M:

- The public maintenance API is `materialize`, `rebuild`, `applyChanges`,
  `maintenanceStats`, and `setShadowVerification`. `addFact`, `execute`, and
  `retract` are unchanged and interoperate with the batch API. `retract` is
  not superseded by `applyChanges`: it deletes every base fact matching a
  goal, including goals with variables and joins, which exact-fact batch
  deletion cannot express.
- Retraction was subsequently routed through the incremental deletion
  engine. `commitRetraction` is the single choke point for both `retract`
  and the source `~` statement: it replays the removed base facts onto a
  fresh clone — so query-local values interned while evaluating the goals
  never reach the committed database — and then takes the same path a batch
  deletion takes, delete-and-rederive plus aggregate maintenance when the
  closure is clean and dirty-stratum rebuild otherwise. Retraction therefore
  leaves the closure clean, and shadow verification now covers it.
- Maintenance stays lazy by default — an update marks strata and the next
  query repairs them — with `materialize` as the eager trigger and `rebuild`
  as the always-available reference path. Both run on staging and commit
  atomically.
- Shadow verification compares the maintained closure against a fresh
  rebuild *before* the batch commits, so `MaintenanceMismatch` leaves the
  database untouched. It runs on a throwaway copy and never pollutes the
  database being verified.
- Aggregate changes reach downstream strata through the existing deletion
  and insertion cascades; no separate propagation layer was needed.
  Downstream structural recursion recomputes inside its own stratum, because
  seed rules are evaluated naively within the stratum they belong to, which
  is the scoped fallback the phase asks for.
- `MaintenanceStats` gained `rebuild_fallbacks` and `maintained_groups`, so
  every update category is observable: incremental insertion, incremental
  deletion, aggregate group maintenance, or rebuild fallback.
- Benchmarks: `benchmark-maintenance` reports time, delta sizes, groups
  touched, rebuild fallbacks, and memory for insert, delete, mixed, and
  negation-blocked workloads; the 25-node baseline gained edge-change
  workloads comparing incremental maintenance against full rebuild.
- Measured honestly, incremental maintenance is about 2x faster than rebuild
  on the 25-node closure workload, and *slower* than rebuild on small
  aggregate-heavy databases, where fixed per-batch overhead dominates. See
  [`aggregation-performance.md`](aggregation-performance.md).
- Deliberately not done: removing the whole-closure snapshot that
  `propagateDeletions` takes. Deferring removal so over-deletion can join
  against the live closure does not work, because over-deletion at stratum L
  needs the pre-deletion state of strata at or below L, and a derivation
  consuming two deleted facts is invisible from either pinning direction
  once both are gone. Eliminating the snapshot needs matching that can read
  the closure together with the pending deletions, which is an evaluator
  change rather than a local fix.
- A maintenance cost model was added after M6, resolving the open question
  the benchmarks raised. `MaintenancePolicy` selects `automatic` (default),
  `incremental`, or `recompute`. The automatic policy counts work in
  candidate facts examined — deterministic and machine-independent — and
  learns two estimates from the database's own history: the cost of a
  dirty-stratum rebuild and the cost of maintaining one changed base fact.
  Each path is measured once to bootstrap, and every sixteenth decision
  takes the rejected path so neither estimate goes stale.
  Design notes worth keeping:
  - Only rebuilds that *repair an update* are recorded. Seeding the estimate
    from the initial full build made recomputation look permanently
    expensive, so the model preferred maintenance everywhere.
  - Insertions and deletions must follow the same decision. They were
    initially wired separately, so insertions kept maintaining while the
    model believed it had chosen recomputation, and the closure never went
    dirty for the rebuild estimate to be learned from.
  - A decision is only counted when maintenance was possible at all; a dirty
    closure must be repaired regardless of cost.
  - Tests that assert a specific mechanism pin the policy, and a differential
    test runs one trace under all three policies to confirm they agree on
    base facts and closure. The choice is a cost decision only.

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

1. S1 finite-f64 policy, syntax, and formatting
2. S2 canonical mixed numeric semantics
3. S3 typed embedding, owned results, and migration
4. P1 relation store and indexes
5. P2 semi-naive evaluation
6. M1 persistent rebuild-equivalent materialization
7. M2 insertion deltas
8. M3 deletion and negation maintenance
9. M4 aggregate group maintenance
10. M5 projected views and CReaM counts
11. M6 downstream propagation and public API
12. P3 join planning and aggregate lookup
13. F1 folding IR and view catalog
14. F2 ordinary Inverse Method
15. F3 conjunctive aggregate inversion
16. F4 soundness restrictions
17. F5 list functions and dependency chase
18. F6 execution and view selection

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
