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

This describes the *starting* point, not the current engine — every property
below has since been replaced by Projects S, P, and M. It is kept because it is
what the phases were written against. For the engine as it stands, read the
completed decisions of the last finished phase in each project, plus
[`aggregation-performance.md`](aggregation-performance.md) for what it costs.

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
                │    ├─> M1 persistent materialization
                │    │    ├─> M2 insertion deltas
                │    │    ├─> M3 deletion and negation maintenance
                │    │    │    └─> M7 deletion through seeded structural rules
                │    │    └─> M4–M6 aggregate maintenance
                │    └─> P3 join planning
                │         └─> P4 measured constant-factor work
                └─> F1–F5 query folding
                     └─> F6 planner/materialization integration
                          └─> F7 folded execution that reuses its work
```

Query-folding transformations can be developed independently after P1, but
automatic reuse of LiveDatalog materialized views belongs after the maintenance
project is stable.

F7 sits on the diagram under F6 because that is where its contract is, but its
optional second half — maintaining a kept reconstruction rather than rebuilding
it — reads M2 and M3, so it belongs after the maintenance project for the same
reason. Its first half does not.

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

### Completed decisions

P3 was completed on 2026-08-07:

- Clause order is now decided twice, and the two decisions are deliberately
  kept apart. `validation.orderClauses` still fixes the stored order at
  admission time and is unchanged, so no program's admissibility moved. The
  new `planner.zig` reorders that already-safe body again at evaluation time,
  purely on cost. Keeping admission out of it is what makes the planner
  unable to fail: the stored order is a witness that a safe order exists.
- A clause is *ready* when the variables it consumes are bound, by exactly the
  condition `validation.validateClause` admits it under, so any order the
  planner produces is one admission would have accepted. Readiness is monotone
  in the bound set, so a greedy walk that always places some ready clause
  cannot strand the rest; if nothing is ready, no safe order of the remainder
  existed and the planner falls back to the order it was handed.
- Among ready clauses it takes the one expected to examine the fewest
  candidates. `RelationStore.selectivity` is the statistic: the relation's
  size and the number of groups an index on the bound positions splits it
  into. A `setof` is costed by its inner plan, and a built-in at zero, so
  neither needs a special case to land before the joins that would run it
  repeatedly — they do not multiply their input, and costing them by their own
  work puts them where that matters.
- A correlated `setof` is ready only once every variable it shares with the
  surrounding body is bound, which is the same condition that makes it
  correlated to one group. Its inner body is planned from the outer bindings,
  which is what lets it collect members through an index on the group key.
- Sorting was **not** avoided. A pattern index emits insertion order, never
  the canonical structural order, so the phase's precondition for skipping the
  sort is not met and `setof` keeps its sort-and-deduplicate path.
- `matchClauses` walks a `Plan` rather than a clause slice, because a step
  carries more than its clause: the stored body position a semi-naive delta
  restriction names — translated through `Plan.constrain`, so the restriction
  follows the occurrence rather than the slot — and the inner plan of a
  `setof`. Every body solve in the engine now goes through `Evaluator.solve`.
- An answer names its variables in the order the *query* writes them, not the
  order evaluation bound them. This had to change with the planner: binding
  order is join order, and join order now moves with the data, so what a
  caller reads would otherwise have moved with it too.
- `selectivity` never builds an index, and `RelationStore.lookup` builds one
  on the *second* request for a pattern rather than the first. A single probe
  cannot repay a pass over the relation plus a group per distinct key, and the
  whole relation is already a valid candidate set under P1's superset
  contract. Deciding this in the store rather than in the planner was the
  second attempt: a planner-side rule based on the estimated row count fed
  back on itself — a plan that declined to index left the index unbuilt, so
  the next plan saw no statistic and declined again, which cost 3x on
  structural deletion and gave back the whole recursive-closure win.
- The public interface gained `setPlanPolicy` (`.cost_based` by default,
  `.source_order` for the pre-P3 order) and `explainQuery`, which renders the
  chosen order, each goal's index positions, and the candidates the planner
  expected. Both policies are differentially tested to produce the same
  closure and the same answers.
- Measured on the existing benchmarks: recomputing an edge change on the
  25-node closure improved 1.41x, maintaining one 1.16x, and incremental
  structural leaf deletion 1.09x; repeated materialized queries and the
  aggregation query workload were unchanged. The new
  `benchmark-join-planning` compares the planned order against the stored
  order directly and finds 1.40x on a sparse join and 1.02–1.06x on the other
  four shapes. Numbers and the limitation they expose are in
  [`aggregation-performance.md`](aggregation-performance.md).
- The limitation P3 recorded — a statement runs on a clone, cloning dropped
  the store's caches, so query planning saw relation sizes but never an index
  statistic and any index a query used was built for that query alone — was
  taken as a follow-up rather than left. `RelationStore.clone` now carries the
  caches, with three decisions:
  - The buckets and the pattern indexes describe the entry list by *position*,
    and a group is keyed by a hash of interned value identifiers. Cloning
    preserves both order and identifiers, so every index and every hash means
    in the copy exactly what it meant in the original. Measured before the
    change: a join query over a 20,500-fact closure made three passes over it,
    one to clone the entries and one each to rebuild the buckets and the
    pattern index it used.
  - Membership stays lazy, and must. Its keys are facts rather than positions,
    so a copy has to re-key them against the copy's own terms, and a hash map
    cannot be copied without rehashing — copying one costs what building one
    costs, and a statement that never probes membership would pay it for
    nothing. Queries never probe it at all.
  - A pattern index is carried only when it is *dense*. A group is a list of
    its own, so copying an index costs an allocation per group while
    rebuilding it costs a hash per entry; a near-unique index is therefore
    slower to copy than to rebuild, and is paid whether or not the copy looks
    at it. Copying every index unconditionally was measured first and cost 19%
    on the repeated-query workload, whose 666-fact closure holds seven indexes
    over 360 groups. The density gate turned that into a 14% gain.
  - **This gate was retired by P4's third item on 2026-08-26.** Its premise —
    that a group is a list of its own — stopped being true when the index
    became one flat array. The experiment was re-run on both layouts: removing
    the gate costs 1.51x on that workload under the layout it was written for
    and nothing at all under the flat one. The reasoning above is exactly right
    about the layout it was measured on; it is the layout that went.
  - `requested` does not carry over either. It records that a pattern was asked
    for once *here*, and `lookup` defers building an index to the second ask
    precisely so a lookup happening once does not pay for one; a copy that
    inherited the record would build on its own first ask, which for a
    per-statement copy is every ask.
  - **This one survived P4's third item, re-measured.** Building on the first
    request costs `benchmark-join-planning`'s sparse join 1.30x and moves
    nothing else: that shape looks a goal up exactly once, on a staging copy
    the query discards. Two asks is a proxy for a third, because a goal inside
    a join is looked up once per binding the goal outside it produced.

## P4: measured constant-factor work

### Why this is deferred work

P3 and its follow-up were both diverted by costs that had nothing to do with
what they were optimizing, and measuring those diversions turned up work with a
better return than either. None of it changes semantics; all of it is recorded
here with the measurement that motivates it, so a later session can decide on
evidence rather than on suspicion.

**Interning is a linear scan.** `ValueTable.intern` walks the whole value table
comparing tagged unions, and `scalar.Store.internAtom` / `internInteger` /
`internFloat` walk the whole scalar table — the atom case comparing strings.
Counted directly:

| Workload | intern calls | table entries scanned |
| --- | --- | --- |
| load 2000 facts, 2001 distinct atoms | 4000 scalar, 4000 value | 4.0M, 4.0M |
| materialize a 120-element structural recursion | 7500 scalar, 22500 value | 0.9M, 5.4M |

Two things that measurement settles. Loading facts spends roughly four times
as much in interning as in the per-statement cloning that P3's follow-up went
after — half of it in string comparison. And the structural case scans 5.4M
times over a table of **242 entries**: the table is small, it is simply walked
22,500 times. That is the same program `benchmark-structural-deletion` runs.

**The first of those two is wrong, and the completed decisions below record
what replaced it.** It compares 4.0M *comparisons* against 1,999,000 *cloned
entries*, which are not the same unit of work: a cloned entry is an allocation
and a copy, a comparison is a length check and a few bytes. Interning is at
most a tenth of what that load costs and on the source path is not separable
from noise at all; the copying is nearly all of it. The structural figure held
up exactly.

**A run of assertions is quadratic.** Every statement clones the database, and
`RelationStore.clone` dupes every fact's terms, so 2000 `addFact` calls copy
1,999,000 entries between them. `applyChanges` already amortizes this over a
batch; a source file of 2000 facts does not, because the parser opens a
transaction per statement.

**This one held, and it was the largest constant factor on the list.** Measured
directly it is 248 ms against 0.6 ms for the same 2000 facts, which is 398x and
is all copying. The completed decisions below record what a run of consecutive
assertions sharing one transaction was worth: 268x, to within 1.51x of the
batch.

**The pattern index allocates one `ArrayList` per group.** This forced three
separate accommodations rather than one fix: index construction is expensive
enough that P3 made `lookup` defer building to the second request; copying is
expensive enough that the clone follow-up needed a density gate; and it is why
a near-unique index costs an allocation per fact either way.

**Planning allocates per body solve.** P3 introduced this. It is most of why
`benchmark-projected-aggregate` is about 5% slower and the test suite went from
3.8s to 4.9s, and it buys nothing on the one- and two-goal bodies where it
shows up.

The suite half of that evidence has since expired and should not be reached
for: it is about twelve seconds as of F6, and F2's exhaustive sweep over all
512 three-node graphs is roughly half of that on its own — hundreds of engine
runs over tiny databases. Suite wall clock is no longer a proxy for engine
speed in either direction. The benchmarks are.

### Scope

- **Done 2026-08-25.** Give `ValueTable` and `scalar.Store` a hash index beside
  their ordered tables, in the shape of `RelationStore.membership`: the ordered table stays
  the source of truth and IDs stay insertion-ordered indices, so identity,
  ordering, canonicalization, and `setof` are untouched and the map is a pure
  lookup accelerator. Both tables are cloned, so decide the same
  copy-versus-rebuild question the store's caches answered.
- **Done 2026-08-25.** Let a run of consecutive assertions share one statement
  transaction, without weakening the guarantee that a failure leaves every
  earlier statement and none of the failing one. This touches the transaction
  model and is the riskiest item here; it may reasonably be split out or
  declined.
- **Done 2026-08-26.** Reconsider the pattern index layout — a flat `[]u32`
  grouped by key plus a map to ranges is cheap to build and cheap to copy. The
  obstacle is `noteInserted`, which appends to a group in place; a layout that
  cannot absorb an insert needs either an overflow list or a rebuild policy,
  and the candidate slice a caller is iterating must stay valid across nested
  lookups. Retiring the deferred build and the density gate is the prize. Half
  the prize was won: the density gate is retired, the deferred build was
  re-measured and kept.
- Cache plans per rule and pre-bound variable set, invalidated with the
  analysis, so a body solved once per delta round is planned once.

### Acceptance tests

- Every existing test passes unchanged, including the allocation-failure
  sweeps: none of this has observable semantics.
- Interning through the hash index agrees with a linear scan over the same
  table for atoms, both integer limits, subnormal and adjacent floats,
  canonicalized integral floats, `nil`, and nested cons values.
- A cloned database interns to the same identifiers as the database it came
  from, which is what the retraction path already depends on.
- A source file whose statements are assertions, queries, and retractions
  interleaved commits and rolls back exactly as it does now, statement by
  statement.
- Random operation sequences over the pattern index agree with an unordered
  reference set, as P1 requires, under whatever layout lands.

### Measurement gate

Report the intern scan counts above alongside times, since the counts are
machine-independent and the times are not. `benchmark-structural-deletion` and
a fact-loading workload are the two that should move most; if they do not, the
item that was supposed to move them has not been understood and should be
recorded as such rather than kept.

### Session boundary

Each item is independently shippable and they are listed in expected-payoff
order. Stop after any one of them with its measurement recorded. Do not take
the transaction-batching item and the pattern-index item in the same session:
both change contracts other phases rest on, and a regression would be hard to
attribute.

### Completed decisions

**The first item — a hash index beside each value table — was completed on
2026-08-25, the second — one transaction per run of assertions — on the same
day, and the third — a flat pattern index — on 2026-08-26.** The fourth, plan
caching, has not been started. Each item's decisions follow under its own
heading, in the order the items landed.

- `intern_index.Index` is an open-addressed table of *positions*: a slot holds
  one more than an identifier so that zero means empty, and nothing else is
  stored. It holds no keys, so the comparison stays the caller's and is made
  against the ordered table, which stays the source of truth with identifiers
  still its insertion positions. Identity, ordering, canonicalization and
  `setof` are untouched, and `scalar.Store` — which owns the bytes of its
  atoms — needs no re-pointing when it is copied.
- The copy-versus-rebuild question the store's caches answered gets a third
  answer here: **copy, because this layout copies with `memcpy`.** A slot means
  the same in a copy as in the original, since cloning a table preserves both
  order and content, so there is nothing to rehash. `RelationStore.membership`
  is keyed by facts and must rehash, which is why it stays lazy; positions do
  not, which is why these are carried. Interning happens on staging copies, so
  it was the copy that had to be cheap.
- The index reserves room before the table appends, so a failure on either side
  leaves the two agreeing. No new allocation-failure sweep was added, and none
  was needed: the new allocation site is on paths the nineteen existing sweeps
  already walk, and they pass unchanged.
- `Database.internStats` and `Jatalog.internStats` report the searches made and
  the entries compared. The counts follow a statement's staging copy back on
  commit, so a rolled-back statement takes its own share of them with it. This
  is the measurement gate's instrument: a comparison count is the same number
  on every machine, and it is what says whether a workload's cost is in the
  value tables at all.
- The acceptance tests are `scalar.zig`'s and `evaluator.zig`'s agreement with
  a linear scan over the same table — atoms, both integer limits, subnormal and
  adjacent floats, canonicalized integral floats, `nil` and nested cons — and
  `root.zig`'s "a cloned database interns to the same identifiers as the
  database it came from", which now names its three dependents: the retraction
  path, the alignment between `Catalog.clone` and `Database.clone` that F1 and
  F6 created, and F6's cached folded plans. The fourth acceptance test —
  interleaved assertions, queries and retractions committing statement by
  statement — needed nothing new: "source persistent statements roll back every
  allocation failure point" and the retraction and parser tests cover it and
  pass unchanged.
- Hashing a float by its bits agrees with the `==` the scans used because the
  only two distinct bit patterns that compare equal are the two zeroes, and
  `internFloat` canonicalizes both to the integer zero before any float reaches
  the table. That is a property of the S2 numeric policy, so it is written down
  next to the hash rather than assumed.

**The measurement gate's verdict, in full.** Comparisons fell 378x on a fact
load and 119x on the structural workload.
`benchmark-structural-deletion` moved 1.7x on every rebuilding path and
materializing a 120-element structural recursion moved 1.92x. **The fact load
did not move**, and rather than being dropped the item was kept with the reason
measured: the same 2000 facts loaded in one `applyChanges` batch — the same
4000 interns without the per-statement copying — moved 11.9x, so interning was
about 92% of that and the per-statement load is 400x more expensive than the
batch for reasons that are entirely the second item's. P4's own inference is
what was wrong, and `docs/aggregation-performance.md` corrects it: it compared
4.0M comparisons against 1,999,000 cloned entries as though those were the same
unit of work.

- Two things noted for the items still to come. The transaction-batching item
  now has the measurement it was missing: 245 ms against 0.6 ms for the same
  2000 facts is what a statement-per-fact transaction costs, and the risks
  recorded above are unchanged. And the pattern-index item's prize — retiring
  the deferred build and the density gate — is untouched by this item: neither
  rule was consulted or altered, because a value table's index is not a
  relation's.

**The second item — one transaction per run of consecutive assertions — was
completed on 2026-08-25.** These are its decisions.

- **The acceptance test came first.** P4 named one acceptance test the suite
  did not already prove — a source file of interleaved assertions, queries and
  retractions committing and rolling back statement by statement — and the
  reason it did not was that the tests standing in for it passed because
  nothing had changed. So it was written against the unchanged engine, watched
  to pass, and only then was the transaction model touched. It is `root.zig`'s
  "a source program commits and rolls back one statement at a time", which
  interleaves the three statement kinds and then puts a failing statement in
  the middle of a run of assertions, and its companion "an allocation failure
  leaves a source program's statements as a prefix", which sweeps the failure
  point across a four-assertion program and requires that whatever reached the
  database is a *prefix* of the program — never a partial statement and never a
  later statement without an earlier one.
- A rolled-back statement's interning is observable, not merely untidy, and
  that is what ruled out the cheap implementation. A value the database does
  not hold still joins the seed set of admissible structural recursion — see
  `statement.evaluateClauses`, which expands when the value table grew — so a
  statement that failed after interning a novel ground structure could derive
  facts. The acceptance test asserts the exact `internStats` entry counts
  across a failing statement for that reason.
- **Rejected: replaying the prefix.** The obvious cheap design runs the whole
  run optimistically and, on failure, discards the copy and re-executes
  statements one at a time down the old path — deterministic, and by
  construction exactly today's behaviour. It fails on the one failure that can
  strike anywhere: `std.testing.FailingAllocator` does not advance its index
  when it denies an allocation, so once it starts failing it never stops, and a
  replay would lose the whole prefix rather than reproduce it. The nineteen
  sweeps would not have caught that — they check for leaks, not for what
  survived — which is precisely why the acceptance test asks for the prefix.
- **What is undone, and what is instead made atomic.** Interning is the one
  thing a statement cannot undo where it happens: it goes on across many calls
  while parsing, long before the statement knows whether it will succeed. So
  `Database.savepoint` records the three interning tables' lengths and
  `Database.rollback` truncates them back — identifiers are insertion
  positions, so truncating restores them exactly, and each table's hash index
  is rebuilt in place over what remains through `intern_index.retainBelow`.
  Neither half allocates, because the failure being undone is usually an
  allocation that failed. **P4's first item had to land before this one could**:
  the rollback is a rebuild of that index.
  Everything else a statement does it does in one operation that either lands
  or does not, and the two that did not are now atomic — `addFactExpr` takes
  its insertion back out if marking the closure dirty fails, and
  `addRuleClauses` takes its rule back out on every failure below the append
  rather than on two of the three, and spends the rule identifier only once the
  rule is certain to stay. `rollback` asserts the fact store and the rule set
  are where it left them, so the contract cannot be quietly broken later.
- A run whose *first* statement fails has staged nothing and is discarded
  rather than committed. Committing it would leave the database equal to itself
  but not identical, since the lazily built caches it came away with would be
  the copy's rather than its own. The existing "source persistent statements
  roll back every allocation failure point" test measures that in bytes and is
  what caught it — the one existing test this item had to be corrected by.
- The commits `foldQuery` and `defineView` make are untouched, deliberately. No
  commit anywhere became conditional, deferred or skippable: `Statement` gained
  `commitAssertions`, which is `commit(.none)` without the error union so that
  the failure path has neither an allocation to spend nor a second error to
  report. `foldQuery` still commits its staged copy on a cache miss because the
  plan it just cached holds identifiers interned on that copy, and still drops
  the copy on a hit so that asking the same question twice cannot grow the
  database. Both halves stand.
- The counts go back with the rollback, so a rolled-back statement still takes
  its own share of what interning cost with it — the property the first item's
  decisions recorded, kept meaning the same thing now that a statement no
  longer has a staging copy to itself.

**The measurement gate's verdict, in full.** Loading 2000 facts as source
statements went from 248 ms to 0.92 ms, **268x**, and now costs 1.51x the
`applyChanges` batch that is the floor for that work, against 398x before.
Every comparison count in `benchmark-interning` is identical before and after,
on all four workloads, which is what says the item changed how often the
database is copied and nothing about what is interned. The three rows that did
not move have no run of statements to share: `addFact` is the embedder's
one-fact call and clones per call by construction, `applyChanges` already was
one transaction, and the structural workload measures `materialize`. Extending
the same treatment to consecutive `addFact` calls would mean an
embedder-visible transaction, which is what `applyChanges` already is, so it
was declined. Every other benchmark landed inside its run-to-run band with all
derived-fact, closure, group and policy counts identical, and the suite is
unchanged at about twelve seconds. `docs/aggregation-performance.md` carries
the tables.

- One thing noted for the items still to come. The pattern-index item's prize —
  retiring the deferred build and the density gate — is still untouched: this
  item consulted neither rule, and `RelationStore` changed not at all. What did
  change under it is that a run of assertions now maintains one store's caches
  incrementally through `noteInserted` instead of rebuilding them from a fresh
  clone per statement, so a layout that cannot absorb an insert has one more
  caller to satisfy than it did.

**The third item — a flat pattern index — was completed on 2026-08-26.** These
are its decisions.

- **What replaced the group-per-`ArrayList` layout.** A `PatternIndex` is now
  three plain arrays: a flat `[]u32` with every group laid out end to end, an
  insertion-ordered `[]Group` giving each group its key and its range in that
  array, and an `intern_index.Index` of *positions* in the group list. That is
  the same answer P4's first item gave the value tables, for the same reason —
  see `intern_index`'s own header, which had already written down why. The
  point of it is that a copy is three `memcpy`s whatever the shape, where a
  `std.HashMap` of ranges would have to re-key every group and cost what
  building one costs.
- **A middle version was built and measured and is not what landed.** The
  first flat layout kept a `std.AutoHashMapUnmanaged(u64, Range)` beside the
  array. It made `benchmark-materialization` **2.6x worse** — the map clone was
  the whole cost, and it is exactly the cost the density gate had been avoiding
  all along. Replacing the map with the positional index is what turned that
  into a 1.03x gain. Recorded because the flat array was never the hard part;
  the group directory was.
- **The density gate is retired, on a controlled experiment rather than on the
  argument.** `min_group_size` was set to zero under *both* layouts and
  measured today: carrying every index costs 1.51x on the repeated-query
  workload under the layout the gate was written for, and nothing under the
  flat one. P3 measured the same thing at 19% when it installed the gate.
  `clonePatterns` now carries every index unconditionally, and P3's decision is
  corrected in place above rather than deleted — its reasoning is right about
  the layout it was measured on.
- **The deferred build survived, and the measurement that kept it is the
  sparse join.** Retiring it was the other half of the prize, so it was tried:
  `lookup` building on the first request cost `benchmark-join-planning`'s
  sparse join **1.30x** and moved nothing else. That shape is what the rule is
  about — one goal binds a single value, the goal after it is looked up exactly
  once, and the store it is looked up in is a staging copy the query discards.
  Two asks is a cheap proxy for a third, because a goal inside a join is looked
  up once per binding the goal outside it produced. The conclusion is about the
  behaviour as it actually runs, `requested` resetting on every clone included:
  it is the per-query clone that makes "asked once" the common case worth not
  paying for.
- **So F6's decision not to cost index availability stands, untouched.** It was
  binding only while the deferred build was, and the deferred build is still
  here. Plan choice is unchanged on every workload — every maintenance policy
  count, group count, derived-fact count and closure size in every benchmark is
  identical before and after, which is the direct evidence that no join order
  moved. P1's claim that the insertion-ordered entry list is what keeps answer
  order deterministic was checked rather than assumed and holds under this
  layout: a group holds entry indices in insertion order both when it is built
  and after it has been grown and moved, and the acceptance test below pins
  that against a scan of the entry list.
- **`noteInserted` needed neither an overflow list nor a rebuild policy.** A
  group reserves room past its end and takes an insert in place; when the room
  runs out the group is copied to the end of the array with twice as much,
  exactly as an `ArrayList` grows, and its old slots are abandoned. That bounds
  the array without compaction — a group at capacity `c` has ever occupied
  `2c - 1` slots and holds more than `c / 2`, so the array stays under four
  times what it holds however long it is grown, and equals it exactly when the
  index is built rather than grown. A candidate slice stays valid until the
  next insert into its own index, which is the promise the per-group lists made
  too. The batching item's `parsed, 2000 facts` row is 923083 ns against
  921042 before, so the path that got 268x faster did not give any of it back.
- **The acceptance test came first, again.** P4's acceptance test for this item
  — random operation sequences agreeing with an unordered reference set — was
  already in `relation_store.zig` and passed only because nothing had changed,
  and it says nothing about a clone. So `relation_store.zig`'s "a clone and its
  original answer every pattern lookup as each keeps inserting" was written
  against the unchanged engine, watched to pass, and only then was the layout
  touched: it spans a dense mask, a near-unique one and every combination, and
  requires that verified candidates are the entry list's own matches in the
  entry list's own order on both sides of a clone as each side takes inserts
  the other never sees.
- **The two tests that asserted the retired rule.** "A clone keeps the index
  caches worth copying and rebuilds the rest" became "a clone carries every
  pattern index whatever its density", which asserts the opposite of what the
  density gate made true — both indexes come across, the near-unique one
  answers on the copy's first ask, and the copy can report its selectivity
  without rediscovering it. "A pattern index is built on the second request,
  not the first" stayed, because the rule stayed; its comment now says that the
  flat layout made building cheap enough to reconsider and names what kept it.
  A third test was added for the layout's one moving part, "a group that
  outgrows its room moves without disturbing the others". Every other test
  passes untouched, all nineteen allocation-failure sweeps included, and the
  suite is 227 tests at about twelve seconds.
- No new allocation-failure sweep was added and none was needed: the new
  allocation sites are on paths the nineteen existing sweeps already walk.
  `PatternIndex.append` is the one that had to be got right — it reserves
  before it writes, so a failure leaves the index exactly as it was, which is
  what lets `noteInserted` go on treating a failure as a reason to drop the
  index rather than as a half-applied insert.
- **The measurement gate's verdict, in full.** The gate names
  `benchmark-structural-deletion` and a fact-loading workload as the two that
  should move most. **Neither moved**, and neither did any other time: every
  row of every benchmark is inside its run-to-run band, measured best-of-three
  in paired alternating runs. What moved is memory. `benchmark-maintenance`
  live bytes fall 4x on the delete-only and mixed rows — 12 KiB to 3, 14 to 5 —
  and 7 KiB on every other row that holds indexes; peak falls up to 6.8%. The
  direction is the point: under the old layout carrying every index *raised*
  peak on every row, and under the flat one it *lowers* it. The item is kept on
  that plus the retired rule, and the flat verdict on the gate's own two
  workloads is recorded here rather than dressed up.
  `docs/aggregation-performance.md` carries the tables.
- One thing noted for the item still to come. Plan caching is untouched by
  this: `Selectivity` reports the same numbers it did, planning still never
  builds an index, and the analysis a cache would be invalidated with is
  unchanged. The suite-timing evidence its entry rests on has expired — the
  suite is about twelve seconds and F2's sweep over all 512 three-node graphs
  is roughly half of it — so it should be measured on `benchmark-folding` as
  well as on the benchmarks P4 names: a folded plan installs its rules into a
  fresh copy on every `answerFolded` and re-plans everything, every time.
- And the standing observation, unchanged and still not on P4's list: folded
  execution is 7.4x slower than direct on `copied 200x5` and 65x on
  `grouped 50x40`, measured today. That is the largest constant factor anyone
  has measured here, F6 found it, and nothing in P4 targets it. **F7's first
  item took it on 2026-08-26** and it is now a property of the *first* call
  after a change rather than of every call; what P4's remaining item would
  speed up is what is left of that first call, and F7's completed decisions
  say where.

**The fourth item — caching plans per rule and pre-bound variable set — was
attempted and reverted on 2026-08-26.** Recorded here because the gate this
whole document runs on is "benchmarks must not regress," and this failed it
on two of them.

**What was built.** `Evaluator` gained a `PlanCache` keyed by `(rule.id,
pre-bound variable set)`, populated by `applyRule` and cleared wherever
`invalidateAnalysis` already is — the lifetime the scope asked for, since a
cached plan's clauses are borrowed from the rule it was planned from and that
is exactly what a rule-set change invalidates. Both of `applyRule`'s branches
were rewired to consult it: the seeded branch, which already planned once and
reused it for every value in one call, now reuses that plan across calls too;
the ordinary branch, which used to call `solve` (plan, then execute) on every
delta round, now looks up or builds once and executes many times. Every
existing test passed, including the allocation-failure sweeps — the design
around `PlanCache.insert` mirrors `ValueTable.intern`'s reserve-before-commit
shape precisely so a failure never leaves a plan belonging to neither the
caller nor the cache.

**It failed on the benchmarks it was supposed to help.**
`benchmark-folding`'s `grouped 50x40` first-call candidate count *rose* from
10646 (F7's second item's number) to 18143, a 70% increase, reproducible
across repeated clean rebuilds. `benchmark-aggregation`'s recomputation row
went from 446162 ns/change to 708700 ns/change, a 59% slowdown. Every other
benchmark was flat or slightly favorable — `benchmark-materialization`
improved from 25697 to 21891 ns/query, which is the win the scope predicted —
so this is not a story about the idea being wrong everywhere, only about where
it costs more than it saves.

**Why: a plan cached early can be worse than one planned late, and this cache
had no way to tell.** The planner costs a clause by asking the store's current
selectivity statistics, and those statistics are not static — P1's own rule is
that an index is built on a relation's *second* request, not its first, because
a single probe cannot repay a pass over it. A rule solved repeatedly over a
relation that is *itself growing during that repetition* — a seeded structural
rule deriving into its own head across `expandLevel`'s rounds, or any
recursive rule recomputed from scratch across several outer calls — gets
planned once, early, against a small or empty relation with no index yet
worth having, and every later call now reuses that choice instead of
re-asking with the benefit of what has since been learned. Before this item,
a redundant-looking replan on a later round or a later call was, by accident,
exactly what let the planner notice a relation had grown enough to index. The
cache removed the redundancy and the accidental benefit together. This is not
a defect in the `(rule.id, pre-bound set)` key or in the cache's lifetime — it
is a property of caching a cost-based decision made against a store that does
not stay still, which the scope's own phrasing ("invalidated with the
analysis") did not anticipate because the analysis is not what was going stale.

**Reverted rather than patched.** A narrower version — cache only within one
`expandLevel` call, or only for rules with no seed argument, or add a
staleness heuristic keyed on relation growth — might dodge this specific
regression, but each is a new, unmeasured design rather than the one the scope
named, and the session boundary this document has followed throughout is to
stop and record rather than iterate past a failed gate in the same session.
`src/evaluator.zig` was restored to its last-committed content (verified
byte-identical by diff) rather than built up with `git checkout`, per this
run's standing instruction not to use it. No commit was made for this item;
the attempt and its measurements live only here.

**What this leaves for a later attempt.** The measured shape of the problem —
a plan chosen when a relation is small getting reused once the relation is
large — suggests the cache would need to know when a relation it planned
against has grown by enough to be worth reconsidering, not just when the rule
set changed. That is a second kind of staleness beside the one this document
already has a name for (`Database.fact_generation`, added in F7 for a
different cache), and inventing it was out of scope for a session whose gate
had already failed.

**The fourth item was retried, with a staleness signal, and completed on
2026-08-26.** Same session boundary as the rest of this document: a design
was proposed, measured against the two benchmarks the first attempt broke,
and kept because it passed.

**What the staleness signal is.** Each `PlanCache` entry records, alongside
the plan, every distinct predicate the rule's body reads anywhere — including
inside a `setof`, via the existing `noteBodyDependencies` walk rather than a
new one — and the fact count `RelationStore.selectivity(key, 0).facts`
reported for each at the moment the plan was chosen. A lookup recomputes those
counts and compares; any difference discards the entry and replans, which
also refreshes the recorded counts. This is keyed by rule id alone rather than
by `(rule.id, pre-bound set)`: at `applyRule`'s two call sites the pre-bound
set is fixed by the rule's own shape — empty for an ordinary rule, exactly the
seed term's variables for a seeded one — so the pair the scope named collapses
to the rule id there, and tracking the pair would have added a key with
exactly one value ever observed for it.

**Why fact count, and not the planner's own cost model.** The failure the
first attempt measured was always a fact-count change: a seeded rule deriving
into its own head across `expandLevel`'s rounds, or a recursive rule
recomputed from scratch across outer calls, both grow some relation the body
reads between the calls that share a cached plan. Checking fact count catches
exactly that, cheaply — a bucket-length read per distinct predicate, no
allocation, no index lookup. What it does not catch is P1's own case, a
pattern index appearing between calls with no change in the relation's fact
count (crossing from a first to a second request on the same pattern) — the
gap the previous attempt's writeup named as the prerequisite. A fully rigorous
check would need, at every position a clause could have been placed, the
selectivity every other ready-but-unplaced clause was compared against there —
which is exactly what `chooseNext`'s own search computes, so checking it
costs what replanning costs and buys nothing. Rule bodies here are small
enough that the *rigorous* version would have been affordable too, but there
was no way to build only the affordable half of it: the moment a losing
candidate's selectivity is being tracked, the check has become the planner
walking its own search again. Fact count is the coarser thing that is still
cheap. It is an accepted approximation, not a proof, and it is being kept on
the measurement below rather than on the argument, matching how the
second-request indexing rule itself was decided.

**Never carried by `clone`.** A cached plan's `clauses` slice borrows from the
rule it was planned from, and `Evaluator.clone` deep-copies rules into new
allocations via `syntax.cloneRule` — an entry that crossed the clone would
borrow from memory the clone does not own. `plan_cache` is simply omitted from
`clone`'s result literal, so it takes its declared default of empty; a test
confirms a clone starts with `plan_cache.entries.count() == 0` after the
original has populated one.

**A pointer-identity pitfall the test caught before it shipped.** The first
version of the reuse test compared `&entry.plan`'s address across calls —
the address of the *slot in the hash map* — to prove reuse, and compared it
again after growing the tracked relation to prove a replan had happened. It
passed the reuse half and failed the replan half: `PlanCache`'s stale-entry
path removes the old entry and inserts a fresh one under the same key, and an
unmanaged hash map with one live entry reliably reuses the same slot for a
reinsertion under the same key, so the slot address is identical whether or
not the *contents* changed. The test was rewritten to check content instead:
`Plan.clauses.ptr` (a real heap allocation, never coincidentally reused
because nothing was freed on the no-replan path) proves reuse, and
`Plan.steps[0].estimate` — the candidate count `describe` measures fresh
every time it is not reused — proves a replan happened, since a stale reuse
would still carry the estimate the superseded plan recorded. Recorded because
the same pitfall would have looked identical either way if only the address
had been checked, and a green test proving nothing is worse than no test.

**The measurement gate's verdict, in full.** Median of two or three runs,
ReleaseFast, from a clean `.zig-cache` rebuild, arm64, macOS 26.5.2, Zig
0.16.0, against the same commit's benchmarks run without this item (via a
saved diff, not a second checkout). `benchmark-folding`'s `grouped 50x40`
first-call candidate count is **10646**, unchanged from F7's second item and
nowhere near the reverted attempt's 18143 — candidate counts are
machine-independent, so this alone settles that specific regression.
`benchmark-aggregation`'s recomputation row is 454241–466116 ns/change across
three runs without this item and 454241–459654 ns/change (after discarding one
visibly cold first run at 637854, the same kind of noise this document has
flagged before) across three runs with it — flat to a percent, not the 59%
regression the first attempt measured. `benchmark-materialization` improved to
20414 ns/query, in the same range as the first attempt's predicted win
(25697 to 21891). Every other benchmark named in this run's gate —
`benchmark-maintenance`, `benchmark-structural-deletion`, `benchmark-interning`,
`benchmark-join-planning`, `benchmark-projected-aggregate` — reported counts
and timings inside the ranges this document already has on record for them,
with `benchmark-interning`'s comparison counts identical to the digit, which
is what says this item touched planning and nothing about what is interned.
`zig build test` passed all 233 existing tests plus two new ones for this
item, with `zig fmt` and `ziglint` clean, from a clean `.zig-cache` rebuild.

**The fingerprint's own known gap — a pattern index appearing with no
fact-count change — was closed later the same day.** `PlanCache.Entry` no
longer records a fact count per distinct predicate; it records, per placed
step (recursing into a `setof`'s inner plan), the full
`RelationStore.selectivity` result — `facts` and `groups` — for that step's
own `(key, mask)`, which is the exact figure `planner.describe` measured to
cost it, at the mask the step actually runs with rather than a fixed `mask =
0`. A mismatch on either field invalidates the entry. This is strictly more
sensitive than the fact-count-only version, so it cannot reuse a plan the
coarser check would have wrongly kept, only replan in cases the coarser check
would have missed; the residual gap it does *not* close is recorded in
Follow-ups. Re-run against the same gate: `benchmark-folding`'s `grouped
50x40` candidate count stayed at 10646 across three runs,
`benchmark-aggregation`'s recomputation row stayed at 453475–465820 ns/change,
`benchmark-materialization` stayed improved at 21956 ns/query, and every other
named benchmark's maintain/recompute/fallback/group counts and
`benchmark-interning`'s comparison counts were identical to the prior run —
the refinement cost nothing measurable on this suite. `zig build test` stayed
green (235 tests) with `zig fmt` and `ziglint` clean from a clean
`.zig-cache` rebuild.

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

## M7: incremental deletion through seeded structural rules

### Why this is deferred work

Delete-and-rederive runs a rule *backwards*: `overdeleteOccurrence` unifies a
deleted fact against one body occurrence, solves the remaining goals, and
reconstructs the head tuple that derivation supported. A seeded structural
rule cannot be run backwards, because its head carries a variable no body goal
binds:

```datalog
length([], 0).
length(H!T, N) :- length(T, M), N = M + 1.
```

Pinning `length(T, M)` against a deleted fact binds `T`, `M`, and then `N`, but
never `H`. Forward evaluation binds it by enumerating the value table —
`applyRule` unifies every interned value against `head.terms[seed_argument]`
before solving the body — and `seed_argument` records exactly which head
argument that is. Backwards there is no value to enumerate against, so
`deriveFact` has nothing to bind `H` to.

Seeded rules are the *only* rules with this shape. `validateRuleSafety`
pre-binds the seed argument's variables and then requires every other head
variable to be bound by the body, so no other rule can reach over-deletion
with an unbound head variable. That bounds this project tightly.

Deleting a fact such a rule reads previously reported `UnboundVariable` to the
caller. As of the fix that closed that defect, `deletionBlocked` sends the
whole stratum to a dirty-stratum rebuild instead. Rederivation needs no
equivalent work and is already correct: `hasAlternativeDerivation` unifies a
complete candidate fact against the head, which binds the seed like any other
head variable.

This phase asks whether that rebuild can be replaced by incremental deletion.

### Scope

- Replace head *construction* with head *enumeration* for a pinned body match
  of a seeded rule: produce every head tuple consistent with the body binding
  rather than the single tuple `deriveFact` would build.
- Choose between two candidate sources and record why, since they differ in
  cost rather than in result:
  - **Closure lookup.** Over-deletion only ever acts on head tuples that are
    in the closure — `overdeleteOccurrence` already discards a constructed
    head that is absent — so look the candidates up through the existing
    pattern indexes on the head predicate, using the head arguments the body
    binding fixes, and unify each against the head term. This needs no new
    storage and narrows candidates to facts that exist.
  - **Value-table enumeration.** Mirror forward evaluation: unify interned
    values against `head.terms[seed_argument]` under the body binding, which
    constrains them to structures whose tail is the bound one. This scans a
    monotone table that never shrinks, so it needs a structural index on the
    value table to be affordable.
  Closure lookup is the expected answer; the value-table form is recorded
  because it is the direct inverse of forward evaluation and is the fallback
  if a head is found that closure lookup cannot constrain.
- Narrow or remove the seeded-rule guard in `deletionBlocked` once candidates
  can be enumerated, keeping the rest of that predicate intact.
- Leave rederivation, aggregate maintenance, and the insertion path untouched.
- Let the maintenance cost model choose as it does for every other update; do
  not force incrementality when the estimate prefers recomputation.
- Preserve per-batch atomicity: a failure during enumeration must leave base
  facts, closure, indexes, and auxiliary views unchanged.

### Acceptance tests

- Deleting the base case of a structural recursion removes every derived fact
  of the chain, matches a clean rebuild, and records no rebuild fallback.
- A chain fact with an alternative proof survives the deletion of one support,
  and one without it does not.
- A rule with several seeded body occurrences, and mutually recursive seeded
  rules, over-delete every affected head exactly once.
- A seeded rule consuming lists interned by a higher stratum — the existing
  aggregate-plus-`length` case — stays correct with the fallback assertion
  inverted to require incremental maintenance.
- Randomized mixed traces over a program combining structural recursion,
  negation, and aggregation match a clean rebuild after every batch under
  shadow verification.
- Allocation-failure tests cover candidate enumeration and rollback.

### Measurement gate

This phase may reasonably conclude that the rebuild fallback should stay, and
that outcome must be recorded rather than worked around.

Deleting the base case of a structural recursion invalidates the derived facts
of *every* interned structure, so the over-deletion set can approach the whole
relation while a stratum rebuild costs one expansion. The benchmark must
therefore compare incremental deletion against the fallback on both shapes:
deleting a leaf of a deep structure, where few facts are affected, and deleting
the base case, where nearly all are. Report over-deleted and rederived counts
alongside time, so a win can be attributed to the algorithm rather than to the
workload.

### Session boundary

Stop when deletion through seeded structural rules is either incremental and
rebuild-equivalent, or measured to be slower than the fallback with the numbers
and the decision recorded here. Do not extend the work into indexing the value
table unless closure lookup has been shown insufficient.

### Open questions for the phase

- Can the head arguments a body binding fixes always constrain the closure
  lookup enough, or are there seeded rules whose head shares no bound argument
  with the body?
- Does anything else want a structural index on the value table — forward seed
  application currently scans it once per rule per round — or would this be its
  only consumer?

### Completed decisions

M7 was completed on 2026-08-07:

- Over-deletion now names a pinned occurrence's head two ways, chosen by the
  rule rather than by the fact. `overdeleteConstructed` keeps the old path for
  an ordinary rule, whose head `validateRuleSafety` guarantees the body binds.
  `overdeleteEnumerated` handles a seeded structural rule by looking the head
  up in the closure through the existing pattern indexes and unifying each
  candidate against the head term. Closure lookup was the expected answer and
  is what landed; the value-table form was not built.
- Enumeration is exact rather than an over-approximation, in both directions.
  A candidate that unifies names a seed value that is interned — it is in a
  stored fact — so forward evaluation would have derived it. A head the
  forward direction derived is either in the closure, and is found, or is not,
  and the constructed path would have discarded it too.
- The candidate is unified into the binding *before* the remaining goals are
  solved. Solving first and narrowing the lookup with the result is the
  cheaper order and does not work: the seed argument's variables can occur in
  the body, as `H` does in `sum(H!T, N) :- sum(T, M), N = M + H`, and solving
  `N = M + H` without the candidate reports the same `UnboundVariable` the
  phase exists to remove. Unifying first also makes the guarantee simple —
  every head variable is bound, so any one solution of the remaining goals is
  a whole proof of that exact tuple.
- The seeded-rule guard is gone from `deletionBlocked`, which no longer
  differs from `insertionBlocked`; the two became one `levelBlocked`.
  Rederivation needed no change, as predicted.
- Answering the phase's first open question: **no**, and it does not matter
  for correctness. The canonical seeded rule shares no *ground* head argument
  with the body binding — the seed argument is only partially fixed (its tail)
  and the other head arguments are computed downstream of it — so the mask is
  usually empty and the lookup degenerates to the head predicate's whole
  relation. Unification filters it, so this is a cost, not a defect. The
  second open question was not reached: nothing else asked for a value-table
  index, and the session boundary reserved it for a case closure lookup could
  not handle.
- `MaintenanceStats` gained `overdeleted_facts` and `rederived_facts`, the two
  halves the existing `removed_facts` nets together, so a deletion's cost can
  be attributed.
- `benchmark-structural-deletion` compares the two shapes the measurement gate
  asks for. Incremental deletion is about **40x faster** than the rebuild when
  one element's support goes and one derived fact falls with it, and about
  **100x slower** when the recursion's base case goes and every derived fact
  falls at once — the latter because each over-deleted fact rescans the head
  relation, which is quadratic, while a rebuild after the base case is deleted
  derives nothing at all. Per delete-and-restore cycle the loss narrows to
  about 1.6x. The numbers are in
  [`aggregation-performance.md`](aggregation-performance.md).
- The rebuild fallback was therefore *not* kept: the incremental path is
  correct, rebuild-equivalent, and the large win on the local shape is the
  common one. The cost model arbitrates as it does everywhere else, and on
  the base-case shape it currently chooses wrong, because one learned rebuild
  estimate cannot separate a rebuild that recomputes everything from one that
  finds nothing. Making it shape-aware is cost-model work, not M7's.
- The follow-up this phase identified, and deliberately did not take: index
  the closure by the seed argument's *tail* rather than by whole values at
  bound positions. That is what would make the base-case shape linear, and it
  is a change to the P1 storage contract for one consumer, so it belongs to a
  phase that can weigh it against P3's planning work.

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

### Completed decisions

F1 was completed on 2026-08-11:

- Folding does **not** live beside `planner.zig`, and the name was the
  smaller reason. `planner` reorders the goals of a body that will be run
  either way: it cannot change which answers come back, so it applies
  silently, and the stored order is a standing witness that keeps it from
  failing. A fold changes what is asked and can return a plan whose answers
  are not the query's, so it must return a result the caller inspects. Two
  transformations with opposite contracts do not belong in one module. F1 is
  three: `fold_ir.zig` (the vocabulary), `view_catalog.zig` (what may be
  read), `folding.zig` (what a fold returns). All three import only
  `syntax`, `scalar`, `string_table` and `relation_store`, so they sit at
  `planner`'s level in the DAG and none of them takes a `*Database`.
- The IR is separate from `syntax` for a reason stronger than tidiness:
  everything expressible in `syntax` can be evaluated. A Skolem term and a
  generated equality have no executable meaning until a later phase proves the
  plan runnable, so giving `syntax` a representation for them is exactly what
  would let an unproved plan reach the evaluator. Lowering is therefore
  one-directional — `syntax` to IR, never back — and there is no lifting
  function to be tempted by. F6 defines the executable form when there is
  something proved to execute. Lowering does carry the seed argument of a
  structural rule across rather than dropping it, because a fold that inverted
  such a rule without knowing what it was would be inverting recursion, which
  is exactly what F5 has to reject.
- Identity is not spelling. A variable is an entry in a `Symbols` table and its
  printed name is a lookup, which makes collision impossible rather than
  unlikely: two variables spelled `X` in different scopes are different
  variables, and a generated variable has no user spelling at all. The same
  holds one level up — a view is identified by its catalog entry, so a view and
  a base relation spelled alike are never one predicate.
- Hygiene is enforced twice, because the two failures are different. Identities
  cannot collide, which is what protects the *reasoning*; and generated symbols
  print with `$`, `@` or `#`, none of which a user identifier can contain,
  which is what protects the *reading* — a rendered plan cannot be mistaken for
  a program somebody wrote. `isUserSpellable` states the second rule and the
  tests hold the renderer to it.
- The renderer prints a user variable as `X#3`, spelling *and* identity. A
  rendering that dropped the identity would print two different variables the
  same way, which is precisely the confusion the IR exists to prevent, and a
  plan combining a query with the inverse of a view has two such variables by
  construction. Generated goals are marked with a `% generated` comment, so a
  rendering reads as the program it stands for and still says which of its
  goals nobody wrote.
- The four-valued guarantee is one enum, but the fourth value is not shaped
  like the other three. `Outcome` is a union of `folded` and `unsupported`, and
  only the first carries a `Plan`; `Outcome.plan()` returns null for the
  second. An unsupported fold therefore cannot be mistaken for an empty
  successful plan by anybody who forgets to check a tag, because there is no
  plan there to read. A plan with zero goals stays representable and renders as
  a plan, guarantee and all.
- `foldQuery` folds nothing, which is the phase's boundary, but it is not a
  stub. It answers the availability question folding exists to answer: a plan
  may read a view's stored extension and whichever base relations the catalog
  declares, and nothing else. A query already inside that boundary is its own
  plan and the guarantee is `equivalent`, because nothing was done to it.
  Outside it the answer is `unsupported`, naming each relation it could not
  get — and distinguishing a relation nothing defines from one only a view's
  body mentions, which is the case F2 will reconstruct and this phase cannot.
  Removing an availability declaration is what turns the first answer into the
  second, which is the axis F4's tests need.
- A view carries its definition, its schema and its availability separately
  because later phases need them separately. The schema is not the head's
  shape: a column bound by an aggregate's output holds a list whatever the head
  spells it, which is the column F3 reconstructs member facts from. A withheld
  view still has a known definition, which is what lets a fold explain what it
  was missing.
- The catalog owns the `Symbols` table its definitions share with the queries
  folded against it and the plans that come back, so one identity means one
  thing everywhere. Its predicate names and constants are the *database's*
  identifiers: a catalog outliving the database it was built from resolves
  nothing. That is the standing rule about database-local value identifiers,
  and it is why nothing here is serializable.
- No public surface was added. Folding's own API is the catalog, and there is
  no way for an embedder to declare a view yet — that is F6's "fold against
  explicitly selected view extensions". Exporting a fold entry point now would
  document a feature that can only answer questions about an empty catalog.
- The allocation-failure sweep lives in `root.zig` rather than in the modules
  it covers, which is ADR 0002's rule rather than an exception to it:
  `test_support` sits above these modules, so a test needing it moves up. The
  scenario builds a catalog from a database's own rule, folds one query outside
  the availability boundary and one inside it, renders both, and standardizes a
  definition apart. The semantic tests stay in their own modules, where nothing
  above `string_table` is needed to write them.
- Not performance relevant: nothing in this phase runs during evaluation, and
  no benchmark changed. The suite goes from 142 tests to 152 in about the same
  wall clock.

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

### Completed decisions

F2 was completed on 2026-08-11:

- The lowering question F1 left open is answered, and the answer is the one
  F1's reasoning forces. There is a way from the IR back into `syntax`, and it
  is `folding.lowerPlan`: it takes a `Plan` rather than arbitrary IR, and it
  returns `error.PlanNotExecutable` for a plan still holding a Skolem term.
  That is not a weakened version of F1's rule but the same rule stated
  positively — a Skolem term has no executable meaning, so *removing every one
  of them* is what earns the way back, and a plan that has been through
  elimination needs no representation for what it no longer contains. `syntax`
  gained nothing: no Skolem term, no generated-relation identity, no marker of
  any kind. Anything that cannot be lowered is refused rather than represented,
  which is what keeps an unproved plan away from the evaluator.
- Skolem elimination is not a substitution, because there is nothing to
  substitute: a Skolem term names a value that exists and cannot be produced.
  What it *is* is fully described by its function and its arguments, so the
  relation holding it is split — one relation per assignment of a function to
  each column, that column spread across the arguments the function was applied
  to — and the query's rules are instantiated once per combination of splits
  they can read. The answers are then the tuples of the split whose columns all
  stayed ordinary, which is exactly the answers a Skolem term never reached.
  This is a plan transformation and not a runtime filter, which matters: a
  filter would mean the plan is only correct when executed by something that
  knows to apply it, and a plan is supposed to *be* the query.
- It terminates for a structural reason worth stating, because it is the reason
  this phase is bounded at all: a Skolem term is built only in the head of an
  inverse rule, out of values read from a stored extension, so Skolem terms
  never nest and the set of splits is finite. F5 rejects recursive list
  functions for the same reason from the other side — there the terms *would*
  nest.
- One Skolem function per projected variable, shared by every inverse rule of
  that view. The dissertation's notation suggests one per goal and per
  position; its own example refutes that reading, and so does correctness.
  `v(X, Z) :- edge(X, Y), edge(Y, Z)` reconstructs `edge(X, f(X, Z))` and
  `edge(f(X, Z), Z)`, and the even-length path only exists because the node in
  the middle is the same term in both halves. Different functions would
  reconstruct two dangling half-edges.
- `foldQuery` now takes the query's rules as well as its goals, because
  Chapter 6's plan is `Q ∪ V⁻¹` and a recursive `Q` is the case the Inverse
  Method exists for. Without them there is no `Q` to take the union with, and
  the phase's headline example — a transitive closure over a relation that only
  a non-recursive view remembers — cannot be stated.
- The split with no function in any column *is* the relation it came from,
  rather than a first split alongside the others. That is what lets a goal over
  an available relation, and the query's own goals, stay exactly as written:
  the answers a caller asked for are by definition the ones with no
  reconstructed value in them, so they are the tuples of the unsplit relation.
  The other splits get a hygienic identity in the IR — `Predicate.generated`,
  carrying the relation it came from for reading and a plan-local tag for
  identity — and a name only at lowering time, interned with a `$` no source
  program can produce. Naming them earlier would mean a fold writing into a
  database's string table for a plan that might never run.
- A relation read under negation or inside an aggregate is refused, and a rule
  instance whose comparison would see a reconstructed value is dropped. These
  look alike and are opposites. A reconstruction is *contained* in the relation
  it stands for, so reading what is not in it, or counting what is, answers
  **more** than the query — that breaks containment and cannot be traded for
  anything, so the fold is `unsupported`. Dropping an instance answers **less**,
  which is always sound, so it is allowed and reported: the guarantee falls
  from `maximally_contained` to `contained`, and the transformation list says
  which of the two happened. Chapter 6's Theorem 6.2.1 covers the undropped
  case exactly.
- The refusal has to be transitive, and checking it relation by relation left
  a hole worth recording because it was reachable and unsound. A predicate the
  *query* defines is not reconstructed, so the first version skipped it — but a
  rule is no more exact than what its body reads, so `reach(X, Y) :- edge(X, Y)`
  over a reconstructed `edge` knows less of `reach` than the query does, and
  `not reach(X, Y)` is therefore true of more. With edges `a→x`, `x→b` and
  `a→b`, the view stores only `(a, b)`, the query answers nothing, and the plan
  answered `(a, b)`. Exactness is now a fixpoint over the query's own rules
  rather than a property of one relation.
- `view_inversion_unimplemented` is gone, replaced by preconditions that name
  what is actually missing: a relation no view mentions, a relation only
  uninvertible views mention, and per view whether its definition recurses, is
  not a conjunction of positive relations, or mentions a list. The last three
  are F3's, F4's and F5's work stated as this phase's refusals, which is what
  makes an `unsupported` outcome a description of the problem rather than of
  the implementation.
- A lowered plan names a view by the name its extension is stored under, so two
  relations a plan may read cannot share a name and arity. `foldQuery` checks
  this over the views the plan touches and reports `predicate_name_ambiguous`
  rather than lowering an aliased plan, because the failure mode is a plan
  silently reading a relation the fold exists to avoid reading. F6's explicit
  view selection is where this stops being a check and becomes an argument.
- A plan's variable executes under the name it renders under — `X#4`, spelling
  and identity, from one function both paths call. Two distinct variables
  printing alike would be one variable to whoever reads the plan; two printing
  alike in a *lowered* plan would be one variable to the evaluator, which is
  the same confusion with teeth.
- Inverting a view produces rules for every goal of its body, including goals
  reading relations that were available anyway. That looks wasteful and is
  sound and occasionally useful: an inverse rule states that a fact existed, so
  adding reconstructed tuples to an available relation can only add derivations
  the original database supported. Views that reconstruct nothing the query
  needs are not inverted at all.
- The containment claim is checked by exhaustion over every graph on three
  nodes — all 512 — with the oracle computed by bit operations rather than by
  the engine, because a sweep that asked the engine for the answers and then
  asked it again through a plan would agree with itself whatever either did.
  This is the phase's one expensive test: the suite goes from about five
  seconds to about eleven. The cost is the method showing through, not the
  test being careless — the splits of a binary relation are quadratic in the
  view's extension, so a dense graph makes a plan with a few hundred derived
  facts, five hundred times over.
- Not performance relevant to the engine: nothing in this phase runs during
  evaluation and no benchmark changed. The suite goes from 152 tests to 159.
- Two limits worth writing down rather than discovering later. Splitting is
  exponential in principle — the number of splits of a relation is bounded by
  the number of functions raised to its arity — and nothing caps it; in
  practice the fixpoint only ever records splits some rule can actually derive,
  which is why the even-length-path plan has eight rules. And mutual recursion
  between views is invisible, because a catalog holds one rule per view and a
  mutually recursive view cannot be written down at all; the recursion check
  covers the self-reference that can be.

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

### Completed decisions

F3 was completed on 2026-08-11:

- The two normalization algorithms of Appendix A.1 are **not** implemented, and
  the cases they exist for are handled directly instead. Algorithm 1.1 splits a
  view with a nested aggregate into an auxiliary relation plus a rule, and
  Algorithm 1.2 chains a view with several aggregates through a sequence of
  them. Both introduce relations with *no stored extension*, so a plan would
  have to reconstruct an auxiliary and then invert it again — and Algorithm 1.2
  is printed in a form too garbled to follow faithfully. Reading the shapes
  directly is simpler and covers the same class:
  - a nested aggregate needs no rewriting because the enclosing template
    already binds its list. Collecting `Y!T` pairs means binding one of them
    binds `T`, so the inner relation is reconstructed by chaining a second
    membership goal after the first;
  - sibling aggregates need no chaining either, only their own identities. Each
    gets its own membership goal, and — this is what the rewriting was really
    buying — its own variables, so that two aggregates spelling a collected or
    projected value alike do not become one.
- `member` is three rules, not a language feature. Adding a builtin would have
  put a list-destructuring operation into the evaluator for the sake of the
  folder, and it is not needed: a list the database holds already holds each of
  its own tails as interned values, so `$member(H, H!T) :- T = []`, plus the
  first value of a longer list and everything its tail already had, derives
  exactly the membership facts over the lists that exist. They are seeded
  structural rules, which is a class the engine already admits.
- What the head must keep is the *list*, not a variable holding one. A
  definition that writes the collected list down — `[a, b]`, `[]`, or a partial
  `[a!T]` whose tail the head keeps — fixes it exactly as firmly as a variable
  does, and the plan reads members out of the literal. The condition is
  therefore "every variable in the output occurs in the head, or in an
  enclosing template", which makes the ground, empty, structural and nested
  cases one rule rather than four. An output the head genuinely projects away
  is the one refusal, and it is F4's Skolem set.
- Two soundness bugs were found by writing the tests, and both are places where
  the dissertation's Definition 6.3.1 is not enough to go on. A value projected
  out of an aggregate's *own body* has one witness per collected value, not one
  per stored tuple: Definition 6.3.1 names it `h(X̄, S)`, and naming every
  element's witness alike lets a query join two elements through a witness the
  database never had. The Skolem term is now applied to the collected value as
  well. A value the definition binds *outside* its aggregates keeps the
  per-tuple naming, because that is what preserves the join between the outer
  and inner halves — the `Z̄` of Definition 6.3.1 is exactly that case.
- The second bug is the sibling one, and it is about the language rather than
  the algorithm. A value the surrounding goals do not bind belongs to the
  aggregate that mentions it, so `setof(Y, r(X, Y, W), S1), setof(Y, t(X, Y,
  W), S2)` has two independent `Y`s and two independent `W`s, however the rule
  spells them. Skolem functions are therefore keyed by the aggregate as well as
  the variable, and a collected value's binding is withdrawn when its aggregate
  ends. Both tests fail with two answers and one answer respectively when the
  keying is removed.
- The `setof` identities `σs` are deferred to F4 rather than implemented here,
  and the reason is that they would have nothing to fire on. `σs1` and `σs2`
  rewrite an expansion containing a Skolem *set*, which only the projected
  output case produces — and F2 already refuses a query that reads a
  reconstructed relation inside an aggregate, which is the other way such an
  expansion could arise. Implementing them now would mean writing a rewrite
  system, proving it terminating, and testing it against no input. F4 inverts
  the projected case and needs them in the same breath.
- Membership is defined once per plan however many views turn out to need it,
  and it is the plan's own relation rather than a view's: `$member` is a
  `Predicate.auxiliary`, a fold-owned relation with a meaning of its own, as
  against a `Predicate.generated`, which stands for part of a relation the
  query named. The `$` keeps it out of reach of any program.
- Not performance relevant to the engine: nothing in this phase runs during
  evaluation and no benchmark changed. The suite goes from 159 tests to 168 in
  the same wall clock.
- One limit worth writing down. An aggregate whose template shares a variable
  with the goals surrounding it is refused rather than inverted. Such a
  variable would have to be read back out of the list *and* named by a Skolem
  term because the head lost it, and there is no reading of the definition
  under which those agree. It is a strange thing to write — the language admits
  it, and it means the aggregate collects a value that is already fixed — so
  the refusal costs nothing real.

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

### Completed decisions

F4 was completed on 2026-08-25:

- The `σs` identities are **not** implemented as rewrites, and the reason is
  that F2's Skolem elimination already does the work of the one that had
  anything to do. `σs2` says that collecting the members of a set gives the set
  back. Elimination splits a relation by which function each column carries and
  spreads that column across the function's arguments, so `$member(Y, f(X̄))`
  becomes a relation meaning "Y is in the set `f(X̄)`" — the Skolem set reified,
  with no separate list value left over for the identity to relate it to. It
  holds by construction. `σs1` drops a conjunct from inside a `setof` when the
  goals around it already established it, and it fires only on an *expansion* —
  a plan unfolded by substituting rule bodies into goals, which Chapter 6 builds
  to reason about containment and this engine never builds, because a plan here
  is a program rather than a formula. F3 deferred both for want of input; the
  honest finding is that one has permanent want of input and the other has been
  discharged by machinery that already existed. No rewrite system was written.
- Case 2 inversion is therefore a small change with a clearly bounded payoff,
  and stating the payoff exactly is the point. `v(X̄) :- Φ(X̄, Z̄), setof(Ȳ, Ψ, S)`
  with `S` projected away is now inverted: the collected list becomes a Skolem
  term applied to the head's values, the same term wherever the definition
  mentioned that set, so `p(X, f(X)) :- v(X)` and `member(Y, f(X))` agree about
  which set it was. What comes back is the `Φ` half, exactly as any projection
  comes back. The `Ψ` half comes back as nothing at all: after elimination the
  membership goal reads a split relation no rule derives, because nothing ever
  stored what was inside the set. That is the truthful reading of Section 6.3.2
  under bottom-up evaluation, and it is worth having — before this phase such a
  view was refused outright and took down every relation only it mentioned.
  `Obstacle.aggregate_output_projected` and its precondition are gone.
- Nothing is dropped by that reconstruction, which is worth recording because
  it looks as though something should be. The `$member` goal carrying a Skolem
  set never matches a split, so the rule is never instantiated; an instance that
  is never enumerated is not an instance that was refused, and the guarantee
  stays `maximally_contained` rather than falling to `contained`. That is the
  right answer: no plan over that view could have had those answers.
- The refusal F2 recorded stays the default and the two discharges are
  obligations that get checked, not a precondition that got deleted. A relation
  is exact only when a view that is canonical **for that relation** is readable
  and is one of the views the plan actually inverts — all three conditions
  settled in the same branch, so none of them can drift apart from the others.
  Breaking the recognizer into "some view mentions it" makes five tests fail,
  including the two acceptance tests and F2's own negation test.
- Canonical recognition is `view_catalog.View.isCanonicalFor`, and it lives
  there rather than in `inversion` because it is a question about what a view
  *stores*, which is the catalog's subject — the same reason the catalog
  already owns the schema. Definition 6.4.3 is read structurally: the relation
  copied, or the relation grouped by `k < n` of its columns with a variable of
  the aggregate's own in each of the others, collected in column order —
  bare when there is one and consed when there are several, which is how
  Example 6.4.2 writes the pair case. Narrower reads are refused: a repeated
  column, a constant, an outer goal over a different relation, a head whose
  kept columns are not the ones the aggregate held fixed.
- Monotonicity is its own module, `monotonicity.zig`, sitting beside the other
  four at `planner.zig`'s level and importing only `fold_ir`. It is a property
  of a query rather than of a fold, it allocates nothing, and it is the piece
  most likely to be wrong in a way that is invisible from `folding.zig`, so it
  is worth being able to test on its own. The class it admits is Definition
  6.4.1 with Lemma 6.4.1 folded in: a collected output is monotone when it is a
  variable nothing else in the rule reads, or `H!T` with both halves likewise
  unread. Everything else pins the set down, and the second condition of
  Definition 6.4.1 — a goal reading the set must be `⊆`-monotone — is a
  property of a stored relation nothing here can check, so requiring the set to
  go unread is the conservative reading of it.
- A query's *goal list* has no head, and that is not the same as a rule whose
  head keeps nothing. Its variables are the bindings handed back, so a set
  collected there is reported, and an aggregate at the top level is never
  monotonic. Modelling it as "a rule that reports everything" is what stops the
  top-level case from being read as the freest one.
- **F4 proves the aggregate half and only the aggregate half by monotonicity,
  and this is a decision rather than an omission.** Chapter 6 assumes negation
  has been rewritten into `setof` by Lemma 4.1.1; that rewriting produces an
  empty collected output, which is exactly the shape the monotonic class
  rejects. So a negated read of an inexact relation can never be discharged by
  monotonicity — not because this engine keeps the two separate, but because
  they agree. The checker states it directly by refusing a negated goal, and
  negation is discharged only by a canonical view, which is Theorem 6.4.2's
  reading of it. The engine still does not rewrite negation into aggregation
  and does not need to.
- Nested aggregates are checked even when the enclosing output is free. An
  output nothing reads makes that aggregate's own result irrelevant, but not
  what its body binds for the goals around it: an inner `setof` asking for an
  empty set decides which values the outer one collects at all, so shrinking a
  relation can *add* answers through it. The test that holds this down fails if
  the recursion into the body is made conditional on the output.
- Both discharges are recorded in the plan's transformations —
  `relation_reconstructed_exactly` naming the relation, and
  `monotonic_reads_admitted` once, and only when a read actually needed it — so
  a plan says which proof let it exist rather than merely that it does.
- Every containment claim was checked by breaking the fix and watching the test
  fail. Admitting `[]` as a monotone output fails four tests including the
  counterexample; treating "a view mentions the relation" as canonical fails
  five; dropping one of the three membership rules fails the bounded sweep.
- The counterexample test does more than assert a refusal, because Example
  6.4.1 is refused by F2's blanket rule and would pass this phase untouched.
  The inverse rules a plan is built from do not depend on which query is folded,
  so the test folds the *monotonic* query, installs that plan, and then asks it
  Example 6.4.1's question directly — the plan answers `q(a)`, which the query
  does not. The refusal is shown to be load-bearing rather than asserted to be.
- The bounded sweep is 64 databases for the monotonic discharge and 16 for the
  canonical one: two keys and two values, exhaustively. The bound is chosen for
  what it contains — a key whose collected set is empty and one whose is not, a
  key the outer goal admits and one it withholds, a value reachable only
  through a withheld key — and everything outside it is one of those with more
  names. Three of each would be sixty-four times the work, and the existing
  three-node graph sweep already costs more than half the suite's running time.
  The canonical half is held to *equality* rather than containment, because
  Lemma 6.4.2 claims equivalence and a containment check would pass a plan that
  had simply gone quiet.
- The README's "Query folding" section was removed at `dc20056` before this
  phase started, and it has not been restored. Folding still has no public
  entry point, so there is no public API or ownership documentation for F4 to
  update; the refusals and the two discharges are recorded in `CONTEXT.md`,
  which is where the folding vocabulary lives. F6 is when an embedder can
  declare a view, and that is when the README has a feature to describe.
- Not performance relevant to the engine: nothing in this phase runs during
  evaluation and no benchmark changed. The suite goes from 168 tests to 180 in
  the same eleven seconds.

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

### Completed decisions

F5 was completed on 2026-08-25:

- **F4 already produces Definition 6.5.1's inverse rules, verbatim, and the
  first thing this phase did was confirm it rather than rebuild it.** To
  `inversion.obstacle` a list function is an ordinary positive relational goal
  over variables, so `v1(X, T) :- p(X), setof(Y, r(X, Y), S), sum(S, T)` is
  inside the conjunctive class and inverts like any other definition: `p(X) :-
  v1(X, T)`, `r(X, Y) :- v1(X, T), $member(Y, $f0(X, T))`, `sum($f0(X, T), T)
  :- v1(X, T)` — the same Skolem set in the membership goal and in the
  reconstructed `sum` fact, which is the whole of what Definition 6.5.1 says.
  A rendering test in `inversion.zig` holds it to exactly that text. Treating
  the views' list functions as base relations is therefore not something this
  phase built; it is what the code already did, and it is also what Section
  6.5's proof relies on. What was left is three things: expanding a query list
  function defined as a conjunctive view over the views' list functions, the
  `va` auxiliary rewriting, and the equality chase. All three are in one new
  module, `list_functions.zig`, beside the other five at `planner.zig`'s level,
  importing only `fold_ir` and `relation_store` and taking no `*Database`.
- **Example 6.5.2 could not be written as printed, and was restated rather than
  approximated.** `avg(X, A) :- sum(X, S), length(X, C), A = S / C` needs
  division, and `syntax.GoalKind` has `add` and `subtract`. Adding division is a
  Project S decision — it touches S1's finite-`f64` policy, S2's canonical mixed
  numeric semantics, division by zero and integer/float canonicalization — and
  none of that is what a phase about the chase should be deciding. The headline
  test is therefore `excess(L, E) :- sum(L, T), length(L, C), E = T - C`: the
  same shape, a query list function defined as a conjunctive view over two the
  views expose, combined arithmetically, and the same folding in every respect
  that matters. The literal example becomes writable the day Project S adds
  division, and the test changes by one goal when it does.
- **F3's refusal of Appendix A.1 was right about its own case and does not
  cover this one, and the difference is which way the auxiliary is used.** F3
  declined Algorithms 1.1 and 1.2 because both introduce relations with no
  stored extension, so a plan would have to reconstruct an auxiliary and then
  *invert it again*. That is still true and nothing here does it: `va` is
  derived forward, from the relations the plan reconstructed, and it is never
  inverted. What it buys is a name for a set — the layer's Skolem set is proved
  equal to a set the plan can actually compute — and that is not something F3's
  cases needed, because there the enclosing template already bound the list.
  Section 6.5's step 2(a) is implemented, step 1 (Algorithm 1.2) and step 2(b)
  are not, and the shapes they exist for are refused with preconditions that
  name what was missing rather than silently mishandled.
- **The chase is a plan transformation and not a relation the plan carries**,
  which is F2's rule about Skolem elimination applied again: a plan that only
  answers correctly when something knows to apply its equalities is not a plan.
  `e(X, X)` ranges over every term there is and the transitive rule over an
  unbounded domain, so the dissertation's rules could not be materialized in
  any case. What is there instead is a union-find over set terms — an
  auxiliary view's set, or the Skolem set a layer's inverse names — decided
  while the plan is built, with the substituted rules as the output. It
  terminates for the reason splitting does: set terms are finite and do not
  nest. And it gives *symmetry through canonical representatives*, which is
  what the acceptance test asks for and what the dissertation's rule set, which
  lists reflexivity and transitivity only, does not — though its own dependency
  `e(S1, S2) :- va(X, S1), va(X, S2)` is symmetric by construction.
- **Example 6.5.1 is refused, not merely survived.** Skolem elimination does
  already prevent the nesting — a list holding a reconstructed value cannot be
  split, so the instance is dropped — and an accident that happens to terminate
  is not a rejection; it leaves a plan quietly answering less than it looks
  like it answers. The query-rule path was open besides, because a caller can
  hand `sum`'s definition over as one of the query's own rules, and
  `compiledRule` does not run admission so the rule arrives with no seed
  argument to notice. `list_functions.isStructuralRecursion` reads the shape
  instead — a head holding a list, and a body reading the head's own predicate
  — and any such rule in the query makes the fold `unsupported` whenever the
  fold reconstructs anything. A query already inside the availability boundary
  is untouched, because it is its own plan and no set was ever named.
- **The monotonic branch of Theorem 6.5.1 is unreachable for the list-function
  class, and this is stated rather than tested around.** A list function reads
  the collected set, so the set occurs in the aggregate's output and in the
  goal reading it — two occurrences, which is exactly the second condition of
  Definition 6.4.1 and exactly what `monotonicity.ofQuery` refuses. A test in
  `monotonicity.zig` holds Section 6.5's own query shape to that. Every F5 test
  therefore lives in the canonical-aggregate-view branch, and `monotonicity` is
  reused unchanged rather than relaxed.
- **One condition is stronger here than the two F4 proved, and it had to be.**
  Everywhere else in folding a reconstruction being a subset costs answers and
  keeps containment. The layer rule does not read the set, it *asserts* about
  it: `sum(S, T) :- v1(X, T), va(K̄, S)` says the stored `T` is the sum of
  whatever the auxiliary view collected. Collect a shorter set and the plan
  holds a `sum` fact that never held — not less of `sum` but a different `sum`
  — and a query reading a false fact answers wrongly however monotonic it is.
  So the relations inside an auxiliary view's aggregate must be *exact*, which
  is Theorem 6.5.1's canonical-aggregate-view condition read strictly, and
  `set_collected_from_inexact_relation` is the refusal when they are not. The
  test that holds it down is deliberately a monotonic query that never reads
  the relation at all — only the auxiliary view does — so nothing else in the
  fold would have objected.
- **A view has an auxiliary view only when its collecting half is a rule and
  its set is determined by what the head kept.** The key must be bound by the
  goals that half kept, or `va(K̄, S) :- setof(...)` has a head variable
  nothing binds; and every value the aggregate takes from outside itself must
  be a head variable, or two stored tuples sharing a key collected different
  sets and the dependency is simply false. A view failing either keeps its set
  nameless: the chase leaves it in a class of its own, and a query reading that
  set with a list function is `list_function_set_unidentified` rather than
  quietly answered from nothing. The first condition is also what keeps
  Section 6.3.2's shape — `v(X) :- p(X, S), setof(Y, r(X, Y), S)`, where the
  goal outside the aggregate *binds* the collected list rather than reading a
  function of it — inverted the ordinary way, which is what F4's test of it
  expects.
- The IR gained one thing: `fold_ir.Auxiliary` is a union rather than an enum,
  so a fold-owned relation can carry an identity. `$member` means the same
  thing in every plan; `$va0` means one particular group's set within one, and
  two views share a tag exactly when they collect the same set. It is compared
  by tag and printed as `$va{n}`, which no source program can spell.
- Two tightenings in `inversion.zig` that an auxiliary view makes reachable and
  nothing before it did, because `va` is the first head a fold derives into
  that is neither a base relation nor a split of one, and its body is the only
  place where an aggregate stands beside goals binding values for it. An
  instance whose auxiliary head would carry a Skolem shape is dropped — a
  relation the fold defines has no original to stand for part of, so a split of
  it would mean nothing, and without the drop `register` reaches its
  `unreachable`. And `admits` now requires every value an aggregate touches to
  be ordinary, not only what it collects and reports: a variable elimination
  spread across several columns outside would arrive inside the aggregate as
  itself and be bound nowhere. The first is held down by a test that crashes
  without it. The second is not: junk derived under a Skolem shape stays inside
  Skolem-shaped relations, so no answer changes, and it is kept as a
  well-formedness fix rather than a containment one. Recording that plainly is
  better than implying a test proves it.
- **A finding about the dissertation worth writing down.** Figure 6.2's plan
  does not derive its own example answer under bottom-up evaluation. `tq` still
  contains `setof(Y, r(X, Y), S)`, `r` is reconstructed only from
  `va(X, S), member(X, S)` over Skolem sets, so `S` is `[]`, and `sum([], T)`
  has no rule because the plan deliberately excludes the list functions'
  definitions. The derivation the chapter draws needs `va`'s *forward*
  definition in the plan, which step 5 does not put there. This implementation
  does put it there — `va` is derived, not inverted — and that is what makes
  the chase land on a set with a value in it rather than on two names.
- The containment claims were checked by breaking each and watching a test
  fail. Merging two set classes that were never one makes the containment test
  answer twice and fails the identity unit test; dropping the exactness
  requirement fails the monotonic-query test; dropping either separability
  condition fails the unidentified-set test or F4's projected-list test;
  making `isStructuralRecursion` blind fails the Example 6.5.1 test; dropping
  the identification requirement fails the unidentified-set test; dropping the
  auxiliary-head guard crashes the unnameable-group test.
- The bounded sweep is 64 databases — two keys and two values, exhaustively —
  held to *equality* rather than containment, because the canonical view makes
  the reconstruction exact and a containment check would pass a plan that had
  simply gone quiet. The bound contains a key whose collected set is empty and
  one whose is not, a key `r` relates that `p` withholds, two keys collecting
  different sets, and sets of size zero, one and two. The two values are 2 and
  5 so that all four reachable answers are distinct: a plan pairing one key's
  sum with another's length would have to answer a number the query never does,
  rather than coincidentally the right one. Three of either would be sixteen or
  sixty-four times the work for the same shapes.
- One wrinkle in the *oracle* rather than in the folding, recorded because it
  looks like a bug and is not. The source database needs the collected lists to
  exist as base structures — a `seed` relation naming them — before the seeded
  structural rules defining `sum` and `length` derive over them, since a list
  that only ever exists as an aggregate's output inside a higher stratum is not
  a list those rules are seeded from. The plan needs no such thing, because it
  holds no structural rules at all: it derives `sum` from the inverse of a view
  that stored one. So the folded side is, in this narrow sense, better behaved
  than the database it was folded from.
- Folding still has no public entry point, so there is no public API or
  ownership documentation to update; the README's "Query folding" section was
  cut at `dc20056` and stays cut. The vocabulary is in `CONTEXT.md`, which now
  has entries for list functions and for the auxiliary view and the chase. F6
  is when an embedder can declare a view.
- Not performance relevant to the engine: nothing in this phase runs during
  evaluation and no benchmark changed. The suite goes from 180 tests to 197 in
  about twelve seconds.

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

### Completed decisions

F6 was completed on 2026-08-25:

- **The catalog is owned by the `Jatalog`, and that decision settled every
  other one in the phase.** F1 recorded that a catalog's predicate names and
  constants are the *database's* identifiers, so a catalog outliving its
  database resolves nothing and none of it is serializable. A thing that can
  only be correct when paired with one particular database should not be
  something a caller can hold separately and pair wrongly; owning it makes the
  pairing the only one there is. It is also the only arrangement in which an
  embedder can declare a view at all, because `Catalog.define` takes a compiled
  `syntax.Rule` and compiling the borrowed `input` descriptors needs the
  database that will hold the interned names. So `defineView` compiles on a
  staged copy, defines into the catalog, and commits — the ids the catalog now
  holds are the committed database's, and a failure part-way leaves neither
  changed. `Jatalog.clone` carries the catalog, which needed
  `Symbols.clone` and `Catalog.clone`; it does not carry the plan cache,
  because a cache is not state.
- **The public surface hands back a result to inspect, never answers.**
  `foldQuery` returns a `Fold` — a guarantee and a handle — and `answerFolded`
  is a separate call. An API returning answers would erase exactly the
  distinction F1 built `Outcome` to protect, and Chapter 6 exists because the
  unrestricted case produces plans whose answers are not the query's. The two
  open design questions are closed together by this shape: **callers get
  both** forms, the rendering through `explainFold` and the executable form
  only ever indirectly, by asking the database to run it. Handing out
  `folding.Executable` itself was rejected — its `syntax.Rule`s are only
  meaningful against the database they were interned in, and a caller holding
  one could install it into a database where the plan's assumptions do not
  hold. Lowering happens eagerly at fold time, so a plan that cannot be
  lowered is still readable and reports `PlanNotExecutable` when run.
- **`answerFolded` enforces the availability boundary rather than trusting
  it**, and this is the decision most likely to look like belt-and-braces and
  is not. Every F-phase test so far constructed a database that happened to
  hold only view extensions. Through a public API that is not a property
  anybody can be relied on to arrange — the natural embedding has the views
  *beside* the data they were computed from, which is exactly the case
  `publishView` serves. So the plan runs against a copy holding what the
  catalog admits and nothing else: the other facts removed, the derived closure
  dropped, and **the database's own rules dropped too**, since a rule deriving
  a withheld relation would put it straight back. Extensions are taken from the
  closure rather than the base facts, because a maintained view's tuples live
  there. Both halves are load-bearing and the tests fail when either is
  removed — five answers instead of two without the fact filter, four instead
  of two without dropping the rules.
- **A finding from breaking that guard, recorded because it corrected a test
  comment that would have been wrong.** The first attempt to prove the boundary
  put a stray `edge` fact beside the even-length-path views and asserted it did
  not reach the answers. It never could have: `edge` there is reconstructed
  only with Skolem terms, so elimination gives the plan `edge$0` and `edge$1`
  and no rule reads the unsplit relation at all. The probe only bites where the
  plan names the relation under its own name, which is the *canonical* view
  case — `r(X1, Y2) :- narrow(X1, S), $member(Y2, S)` — so the probes live in
  the hybrid test, where a leftover fact and a rule manufacturing more of them
  are each blocked by a different half of the copy.
- **`predicate_name_ambiguous` becomes an argument error at selection time, and
  the precondition stays.** F2 checked it over the views a plan touches and
  refused after folding. Two readable extensions under one name and arity make
  a *selection* unusable, whatever is later asked of it — a lowered plan names
  what it reads by the name the extension is stored under, and no query makes
  that better — so the public path reports `AmbiguousViewName` before anything
  is folded, including for a query that would never have touched either view.
  The narrower per-fold precondition is kept because `folding.zig` does not get
  to assume its caller validated anything, and it stays tested there; the
  public path can no longer reach it.
- **"Equivalent plans" had to be defined before anything could be costed, and
  the honest answer is that folding has exactly one cost decision.** Reading a
  relation directly versus reconstructing it is not a cost choice: reading is
  exact and reconstructing is at best exact, so the guarantee settles it. Using
  some views rather than all of them is not one either: where nothing is exact,
  maximality requires inverting every view that mentions the relation. What
  *is* a cost choice is which of several **canonical** aggregate views of one
  relation to read. Lemma 6.4.2 makes each of them return the relation itself,
  so they are interchangeable by proof rather than by heuristic, and the others
  are then dropped — a view kept for no other relation contributes nothing to a
  relation already known whole. The plan reads the smallest stored extension,
  ties going to the lowest view id. `equivalent_view_preferred` records that a
  choice was made and which way, since nothing else in the rendering would show
  it.
- **Index availability is deliberately not costed, and the completion gate is
  what decides it.** The scope asks for cardinalities *and* index availability;
  P1 builds a pattern index on the second request for a pattern, so index
  availability is a function of query history. A plan costed on it would differ
  depending on when it was folded, which contradicts the gate's "deterministic
  plan choice" directly. Determinism wins. Cardinalities are used and are also
  not in the cache key, which is the same argument from the other side: cost
  only ever chooses between plans already proved to answer the same, so a stale
  choice is a slower plan and never a different answer — the licence
  `planner.zig` already runs on.
- **The four cache keys are two counters, and saying why is the point.** The
  scope asks for a cache keyed by normalized query, view definitions,
  availability policy, and rule/catalog generation. Definitions and
  availability are exactly what a catalog generation counts, so one counter
  covers both; `Catalog.generation` bumps on a definition, an availability
  change that changes something, and a base declaration. The rule generation
  already existed and was not recognized as one: `Evaluator.next_rule_id` is a
  monotone counter of rules added, cloned and committed with the database, and
  no new field was needed. It is in the key because `publishView` makes a
  catalog definition *be* a rule. Because both stamps are global, there is no
  such thing as invalidating one entry — either every plan was folded against
  what the database now holds or none was — so the cache is discarded whole,
  and a `Fold` carries the stamp it was made under so a handle that outlived a
  change reports `StalePlan` instead of naming its successor. The normalized
  query is taken of the *compiled* form rather than the IR, so that a cache hit
  costs no scopes: lowering opens one every time, and keying on the IR would
  mean growing the catalog's symbol table before the cache could say it had
  seen the question.
- **Folding did not cross the DAG line, and ADR 0002 gained the rule that kept
  it from having to.** Cardinalities live in the database and none of the six
  folding modules may take one. What `view_catalog.Catalog` borrows instead is
  a `*relation_store.RelationStore` — a type it already imported — pointed at
  the staged store for the length of a fold and cleared afterwards, so the
  catalog never holds a store that has gone. The general rule is now in the
  ADR: a layer that needs a number from below takes that number, not the state
  it lives in. Taking a `*Database` to read a length would have handed folding
  the rules, the closure and the maintenance machinery, and some later phase
  would have used one of them.
- **`maximally_contained` is not enough on its own, and the material F4 and F5
  recorded is what fixes it.** `foldReconstructions` reports every relation the
  plan derives instead of reads and whether it derives all of it, built from
  the `relation_reconstructed` and `relation_reconstructed_exactly`
  transformations those phases already produced. The guarantee says the plan
  answers no more than the query and no less than any other plan over these
  views; only the per-relation account says *where* an answer could have gone,
  and a plan whose reconstructions are all exact loses nothing. So the answer
  to the open question is yes, it belongs in the public surface, and it was
  already being computed.
- **Publishing a maintained predicate is one rule or none.** A catalog holds
  one rule per view, so a predicate several rules define has no definition to
  invert and `publishView` refuses it with `UndefinedView` rather than picking
  one. The definition is the rule's, which is the whole reason the rule
  generation is recorded and `StaleViewDefinition` exists — a definition that
  was true of the database when it was read is not a definition that stays
  true.
- **The benchmark says folded execution is five to fifty times slower than
  direct execution, and the reason is where the plan is kept.** A direct query
  reuses the materialized closure; a folded plan's rules are in the plan and
  not in the database, so `answerFolded` rebuilds a restricted copy and derives
  from nothing every call. That is a property of this implementation rather
  than of the method, and it is the obvious thing to fix if folded execution
  ever needs to be fast. Planning is reported apart and is cheap — 28–56µs to
  fold, 4–19µs to find the plan again. The workloads use canonical views so
  that both sides provably answer the same, and assert exactness rather than
  assuming it, because a view remembering less would make the folded side
  quicker by returning less. No list functions appear, so F5's seeding wrinkle
  does not apply to any of these numbers and none of them is a difference in
  what each side can answer. One measurement worth carrying forward: reading a
  40-element list back through `$member` costs sixteen times what the same 1000
  pairs cost in five-element lists, because membership is seeded structurally
  and a list contributes work in its tails — so the selection cost model counts
  stored tuples, and a tuple holding a long list is not the same unit of work
  as one holding a pair.
- Every guarantee introduced here was checked by breaking it and watching a
  test fail: keeping the withheld facts answers five where two are right;
  keeping the database's rules answers four; reading the first canonical view
  rather than the smallest fails the cost test; inverting every view of an
  exactly reconstructed relation fails both selection tests; never noticing two
  extensions of one name fails the ambiguity test and crashes its unit test;
  never noticing a stale published definition fails the publish test; and a
  cache that is not discarded answers a withheld-view question with the plan
  from before it was withheld.
- The suite goes from 197 tests to 212 in about twelve seconds. No existing
  test changed, and the exhaustive and bounded sweeps of F2, F4 and F5 are
  untouched: this phase adds no sweep of its own, because what it adds is an
  interface over machinery those sweeps already cover, and the containment
  claims are theirs.

## F7: folded execution that reuses its work

**Done 2026-08-26: first and second items implemented, third declined.**
Everything from here to "Completed decisions"
is the case as it stood before that, kept because the measurements it is built
from are still the ones the remaining items are aimed at. What changed, and
what the numbers are now, is at the end of the section.

### Why this is deferred work

F6 measured folded execution at five to fifty times slower than direct
execution and named the reason in one sentence: a direct query reuses the
materialized closure, a folded plan's rules live in the plan rather than in the
database, so `answerFolded` builds a restricted copy and derives the
reconstruction from nothing on every call. It recorded that as a property of
this implementation rather than of the method, and as the obvious thing to fix
if folded execution ever needs to be fast.

**It is still intact, and it is the largest constant factor still standing in
this engine.** Measured on 2026-08-26 at `ReleaseFast`, folded
against direct is 7.4x on `copied 200x5`, 5.6x on `grouped 200x5` and 65x on
`grouped 50x40`. Nothing in P4 targets it: P4's four items are about interning,
transactions, index layout and plan caching, and three of them have landed
without moving these rows at all.

Before proposing a fix, `answerFolded` was taken apart and each phase timed
separately, so that the item is aimed at a measurement rather than at the
sentence above. Mean of ten calls after a warm-up, arena allocator as the
benchmark uses, ns, arm64, macOS 26.5.2, Zig 0.16.0, `ReleaseFast`:

| Shape | copy | install rules | **derive** | solve goals | folded total | direct total |
| --- | --- | --- | --- | --- | --- | --- |
| `copied 200x5` | 175783 | 612 | **390700** | 50650 | 617745 | 74928 |
| `grouped 200x5` | 31383 | 1970 | **366637** | 45483 | 445473 | 89462 |
| `grouped 50x40` | 14733 | 4858 | **9347116** | 62400 | 9429107 | 98020 |

Four things that settles, and they are what the scope below is built from.

**Deriving the reconstruction is 63%, 82% and 99% of it.** Everything else is
noise by comparison. In particular *installing the plan's rules costs
nothing* — 612 to 4858 ns, under 0.1% — so caching the compiled or lowered
rules, the first thing the shape of the code suggests, would buy nothing.

**Solving the goals is not the problem and never was.** It is 45–62µs on the
folded side against 58–69µs on the direct side: the folded side is *faster*
at the part both sides do, because it solves against a small fresh store.
A folded plan that did not have to re-derive would beat direct execution on all
three shapes.

**The copy is the second lever, and only on one shape.** `viewOnlyCopy` clones
the database, walks the closure copying every readable fact into a list, clears
the store and copies them back — three passes over the extension — costing
176µs where the extension is 1000 flat facts and 15µs where it is 50 facts
holding lists. It is 28% of `copied 200x5` and 0.2% of `grouped 50x40`.

**The derivation also does much more work than the query it answers**, which
is a separate lever from doing it repeatedly. Candidate facts examined, the
machine-independent unit the cost model already counts: 3003 against 1001 on
`copied 200x5`, 6759 against 1001 on `grouped 200x5`, and 71706 against 2001
on `grouped 50x40`. The last is 36x. These three shapes differ in key count as
well as in list length, so they do not isolate the cause on their own — but F6
already did, on a comparison that holds the pairs fixed: reading a 40-element
list back through `$member` costs sixteen times what the same 1000 pairs cost
in five-element lists, because membership is seeded structurally and a list
contributes work in its tails.

### Scope

- Keep a folded plan's reconstruction between calls instead of rebuilding it,
  so that repeated `answerFolded` solves goals against a database that is
  already derived. This is the item; the phase table says it is 63–99% of the
  cost and the two floors below say what it can be worth.
- Decide what invalidates a kept reconstruction, and add whatever stamp that
  needs. **The two the plan cache already has are not enough**: `Catalog`
  generation and `Evaluator.next_rule_id` are unmoved by adding or retracting a
  fact, and a fact under a readable name changes the extension the plan reads.
  There is no monotone fact stamp on `Database` today — `Materialization` is a
  clean/dirty pivot rather than a counter — so one has to be introduced or the
  reconstruction has to be maintained rather than stamped.
- Preserve the availability boundary exactly. F6 made `answerFolded` run
  against a copy holding what the catalog admits and nothing else, with the
  database's own rules dropped, and recorded that both halves are load-bearing:
  five answers instead of two without the fact filter, four instead of two
  without dropping the rules. A kept reconstruction must not let a fact that
  was withheld when it was built become visible later, nor keep answering from
  one that has stopped being readable.
- Consider maintaining the kept reconstruction incrementally rather than
  rebuilding it when it goes stale. The staged database *is* a `Database`, so
  M2 and M3 already know how to maintain its closure; a change to the source
  database's readable extensions is a batch against the staged one. This may
  reasonably be split out or declined — it is the difference between "as fast
  as direct on a static database" and "as fast as direct on a changing one".
- Reduce the reconstruction's own work, which the candidate counts say is 3x
  to 36x what the query examines and which F6 traced to list length. The
  instrument already exists and the counts are machine-independent; this is a
  second item and is independent of the first.
- **Explicitly out of scope: installing a plan's rules into the source database
  as maintained views.** It would make folded execution ordinary execution and
  is the obvious third design, but it puts the question's rules into the
  program — which F6 deliberately refused, since a plan's rules are only
  meaningful against the database they were interned in — and it would defeat
  the availability boundary rather than preserve it.

### Acceptance tests

- Every existing test passes unchanged, including the nineteen
  allocation-failure sweeps and every F-phase containment sweep: none of this
  has observable semantics.
- **A kept reconstruction answers exactly what a rebuilt one answers**, after
  each kind of change taken separately: a fact added under a readable name, a
  fact added under a withheld name, a fact retracted, a view made readable,
  a view made unreadable, a definition added, a rule added, and a view
  published from a database rule. This is the shared correctness rule that a
  full rebuild stays available as a reference path, applied to this cache.
- F6's two boundary probes still fail when their guard is removed — five
  answers where two are right without the fact filter, four without dropping
  the database's rules — with the reconstruction kept rather than rebuilt.
- A `Fold` handle that outlived a change still reports `StalePlan` rather than
  answering from a kept reconstruction made under the old stamp.
- Asking the same question twice does not grow the database, which is what
  `foldQuery` already promises on a cache hit and what a kept staging copy is
  the natural way to break.
- An allocation failure while refreshing or discarding a kept reconstruction
  leaves the database and the plan cache exactly as they were, and a later call
  still answers correctly rather than from a half-built copy.

### Measurement gate

`benchmark-folding` is the instrument and it already reports the right four
numbers; it needs one split. **Report the first `answerFolded` after a change
separately from the repeated one**, because the first must still derive and the
item is entirely about the rest. Report candidate counts beside the times, as
the table above does, since they are the same on every machine and are what say
whether the reconstruction got smaller or merely got reused.

The bar, from the floors the phase table gives:

- Repeated folded execution should reach **copy + solve** — 226µs, 77µs and
  77µs on the three shapes, against direct's 75µs, 89µs and 98µs — if the
  reconstruction is kept and the copy is not. That is 3.0x, 0.86x and 0.79x.
- It should reach **solve alone** — 51µs, 45µs and 62µs — if the staged
  database is kept whole, which would make folded execution faster than direct
  on all three shapes.
- A result outside **2x of direct on the repeated call** means the item has not
  done what it claims, and should be recorded as such rather than kept.
- The first call must not get slower, and `benchmark-maintenance`,
  `benchmark-structural-deletion` and `benchmark-interning` must not move.

If only the copy is addressed and not the derivation, the ceiling is 1.40x on
`copied 200x5`, 1.08x on `grouped 200x5` and 1.00x on `grouped 50x40` — which
is why the derivation is the item and the copy is a follow-up.

### Session boundary

Stop when repeated folded execution reuses its reconstruction and the benchmark
reports the two calls apart. Incremental maintenance of a kept reconstruction,
and the reconstruction's own candidate count, are separate items and should not
be taken in the same session: one changes when the reconstruction is refreshed
and the other changes how it is derived, and three levers moving at once on a
65x gap would make a regression impossible to attribute.

### Open questions for the phase

- Where does a kept reconstruction live — in the plan cache entry, or in the
  `Fold`? The cache is discarded whole on a generation change, which is the
  natural place; but the cache is unbounded today, and this turns each entry
  from a plan into a full copy of the readable extensions plus their closure.
  That is a memory-for-time trade the plan cache has never made before and it
  probably needs a bound.
- Is a fact stamp the right answer, or should the staged database be maintained
  from the source database's own change stream? A stamp is simpler and
  rebuilds on any change; maintenance is the thing that would make a folded
  plan cheap on a database that is actually being updated.
- P4's fourth item — caching plans per rule and pre-bound variable set —
  lands inside the `derive` column above, since a folded plan re-plans
  every rule on every delta round of every call. It would make the first call
  cheaper; this project makes the later calls free. They do not conflict, and
  the measurement favours this one first: eliminating a phase dominates
  speeding it up.

### Completed decisions

**Done 2026-08-26**, first item only. Repeated folded execution now reuses its
reconstruction; the reconstruction's own candidate count and incremental
maintenance of it are untouched, as the session boundary asks.

**The reconstruction is kept in the plan cache entry, and what discards it is a
third stamp.** `answerFolded` used to build a `viewOnlyCopy`, install the
plan's rules, derive, solve, and throw the whole thing away. It now derives
into a `database.Database` held in the entry beside the plan, and a later call
finds the closure clean and only solves. `Fold` was never a candidate to hold
it: a handle is a value the caller copies around, and a database it owned would
have to be freed by a caller that has no way to know when the plan behind it
went.

The stamp is `Database.fact_generation`, a monotone counter moved by
`applyInsertion` and by the new `Database.applyRemoval` — which exists so that
removal has one place to move it, rather than leaving `facts.removeFact`
reachable from anywhere. It is deliberately **conservative in one direction
only**: it moves for a fact under a withheld name, and for an insertion a
statement then takes back out, because the database does not know the catalog
and a stamp that guessed would be a stamp that could guess wrong. A spurious
move costs a rebuild; a missed one costs an answer.

It is kept apart from the two the plan cache already had, and that separation
is the item's whole correctness argument. `Catalog.generation` and
`Evaluator.next_rule_id` discard the **plans**; `fact_generation` discards only
what the plans **ran against**. Conflating them would have re-folded on every
insertion — undoing F6's cache to fix a problem F6 does not have — and would
have broken the property the acceptance test below pins: a `Fold` handle stays
live across an insertion on purpose.

**The acceptance test was written against the unchanged engine and watched to
pass before anything was touched**, as the pattern-index and transaction
sessions did. It is "a kept reconstruction answers exactly what a rebuilt one
answers, after each kind of change": fold a query over a materialized `copied`
view, answer it, add a fact under the readable name, fold again — `reused`,
zero invalidations, the original handle still live — and answer 2 rows. Then
each remaining kind of change, each followed by a comparison against the
reference path, which is the same question asked again with the plan cache
cleared. **With the `fact_generation` check removed the test answers 1 and the
other 232 tests, including all twenty allocation-failure sweeps, pass.** That
was verified rather than assumed: the suite was run with the check deleted, and
exactly one test failed.

**The availability boundary is unchanged and was re-proved by breaking it.**
With the reconstruction kept rather than rebuilt, removing the fact filter in
`viewOnlyCopy` still answers five where two are right, and keeping the
database's own rules still answers four — F6's two numbers exactly. Nothing
about keeping the copy weakens either half, because the copy is still built by
`viewOnlyCopy` from what the catalog admits at the moment it is built, and any
change to what the catalog admits discards the plan and the copy together.

**Asking the same question twice still does not grow the database.** `foldQuery`
commits its staged copy on a miss and drops it on a hit, unchanged; the kept
reconstruction is a second database that the source database never sees.
A test asserts that five folded answers leave the source's fact count, closure
size and both interning tables exactly where one answer left them.

**The cache of reconstructions is bounded and the plans are not.** Four, with
least-recently-used eviction, and only the reconstruction is evicted — the
entry and its plan stay, so no cache index ever moves under a live `Fold`. The
asymmetry is the point: a plan is small and discarding one costs a fold, while
a reconstruction is a copy of every readable extension plus its closure. This
is the memory-for-time trade the open question flagged, and it makes
`clearPlanCache` the memory control of the interface rather than a
convenience, which its documentation now says. `Jatalog.clone` still does not
carry the cache, and now for a second reason as well as the first.

**An allocation failure leaves nothing half-built.** The reconstruction is
derived into a local and handed to the cache by a `keep` that cannot fail, so
there is no window where it belongs to neither. A failure while *solving*
against a kept one discards it, because solving interns the goals' structures
into it and can expand its closure, and a half-expanded closure is not
something a later answer may be read from. Two tests: a new sweep over the
whole fold-answer-change-answer path, and a test that forces a failure at each
of four hundred allocation sites of one `answerFolded` and checks that the
*next* call still answers correctly.

#### Measurement

`benchmark-folding` reports the two calls apart, with candidate counts beside
the times. The change it applies between first calls is one fact put in and
taken back out on alternate rounds rather than a fresh fact each round —
twenty new keys is a 40% larger extension on `grouped 50x40`, and a first-call
time taken over twenty of those reports the workload growing under it.

Median of five runs, ns per call, arm64, macOS 26.5.2, Zig 0.16.0,
`ReleaseFast`. Candidate facts examined are the same on every machine.

| Shape | first | repeated | direct | first cand. | repeated cand. | direct cand. |
| --- | --- | --- | --- | --- | --- | --- |
| `copied 200x5` | 587795 | **30714** | 81156 | 3003 | 201 | 1001 |
| `grouped 200x5` | 471276 | **31225** | 80906 | 6788 | 201 | 1001 |
| `grouped 50x40` | 6806016 | **7435** | 109595 | 71805 | 51 | 2001 |

**Repeated folded execution is 0.38x, 0.39x and 0.07x of direct**, against a
bar of 2x and floors of 3.0x/0.86x/0.79x (copy + solve) and 0.68x/0.50x/0.63x
(solve alone). It beats the lower floor, which the floor did not predict; the
reason is in the candidate counts and is worth stating because it is not a
property of folding — see below. Against the same call before this item, on the
same benchmark shape, repeated execution is **18.6x, 14.6x and 923x** cheaper.

**The candidate counts say the reconstruction was reused and not made
smaller**, which is what they are there for. The first call still examines
3003, 6788 and 71805 — F6's 3003, 6759 and 71706, plus the handful of
structural seeds the change fact's own value contributes. That is F7's second
item and it is still entirely intact.

**The first call did not get slower.** Measured like for like — the engine as
it stood before this item, running the same benchmark with the same change
interleaved — the medians of five runs are 571710, 456045 and 6860997 against
587795, 471276 and 6806016: +2.8%, +3.3% and −0.8%. The same binary's median
moved by 5%, 14% and 66% between two batches an hour apart on this machine, so
none of that is a signal. `benchmark-maintenance`,
`benchmark-structural-deletion` and `benchmark-interning` are unmoved and their
comparison counts are identical to the digit.

**A finding this measurement turned up, which belongs to P4 rather than here.**
The repeated folded call examines 201 candidates where the direct call examines
1001 — for the same question, over the same 1000 pairs. P1 builds a pattern
index on the *second* request for a pattern, and a folded plan now has a store
that lives long enough to make a second request; `Jatalog.query` clones the
database into a staging copy and drops it, so the request is never remembered
and **a direct query re-scans every time, however often it is asked**. That is
why repeated folded execution beats direct rather than merely matching it, and
it flatters this table. It is not something F7 should fix — the staging copy is
what keeps a query's interning out of the database — but it is a measured
reason to think the index-on-second-request rule is worth less than P4 assumed
on the read path, and it is the kind of thing P4's remaining item should be
weighed against.

#### Open questions this answered, and what it did not

- *Where does a kept reconstruction live?* In the cache entry, bounded at four
  with LRU eviction of the reconstruction only.
- *Is a fact stamp the right answer, or should the staged database be
  maintained from the source's change stream?* A stamp, here. Maintenance is
  the difference between "as fast as direct on a static database" and "as fast
  as direct on a changing one", and the first column of the table above is what
  it would attack: 588µs, 471µs and 6.8ms are still what a folded question
  costs on a database that changes between every call. That remains a separate
  item, along with the reconstruction's own candidate count.
- *P4's remaining item — caching plans per rule and pre-bound variable set —*
  now has a measured place to land: it is inside the `first` column and nowhere
  else, because the `repeated` column no longer plans anything. Eliminating a
  phase dominated speeding one up, as predicted; what is left of the phase is
  what P4 would speed up.

### F7's second item: the reconstruction's own candidate count

**Done 2026-08-26**, in its own session as the boundary above asks — this does
not touch what invalidates a kept reconstruction, only how much work deriving
one does the first time.

**The cause was generic, not particular to `$member`.** F6 traced the 3x–36x
overshoot to list length and to `$member` specifically, but the mechanism
lives in `Evaluator.applyRule`'s seed branch and applies to every seeded
structural rule the same way: `sum`, `length`, and any user-written rule of
the same shape were all paying it, `$member` just paid the most because a
fold's reconstruction defines it over every list the plan reads. The seed
branch tries each of the value table's entries against the rule's structural
head position and, on a match, solves the body — but it used to collect every
round's derivations into one `answers` list and commit them to `facts` only
after the whole `0..value_count` sweep finished. A value bound to a list's
tail is a fact the *next* round's sweep could use, not this one's, so deriving
one more list position needed one more full sweep of the value table —
`expandLevel`'s outer fixpoint loop already runs seeded rules once per round
with no delta restriction, exactly because their seed set is the value table
rather than a fact relation. For a list of length `L` that is `L` sweeps of a
table that itself grows with the list, which is the quadratic-in-length shape
F6 measured and did not yet explain down to the mechanism.

**The fix uses an invariant the value table already had.** `ValueTable.intern`
is append-only and a `.cons` value's `head` and `tail` are `ValueId`s that must
already exist to be interned into it, so a cons cell's components always have
a strictly smaller identifier than the cons cell itself — the table is stored
in a topological order for free, without anything having to compute one.
Walking `0..value_count` in that order and committing each value's derived
facts *before* moving to the next value means that by the time a longer list's
cons cell is tried, its tail's facts — derived from a smaller identifier
earlier in the very same sweep — are already visible to the body. One sweep
now does what used to take one sweep per list position.

**This could not have produced a wrong answer, only a slower right one.**
Committing a fact earlier within a sweep than the old code would have is still
committing it no earlier than a monotone Datalog fixpoint allows, since
nothing about *which* facts are eventually derivable depends on the order
seed values are tried in — `expandLevel`'s outer loop still runs until nothing
grows, so a fact this change makes visible mid-sweep is a fact the old code
would have derived on the next sweep regardless. That is also why this did
not need new tests: the shared correctness rule is that a full rebuild stays
right, and every existing test — including the seeded-rule tests for `sum`,
`length`, over-deletion through a seeded head, and mutual seeded recursion —
passed unchanged, which is what a change with no semantic content should do.

**Measured.** Median of five runs, ns per call, arm64, macOS 26.5.2, Zig
0.16.0, `ReleaseFast`. Only the `first` column and its candidate count are
this item's target; `repeated` and `direct` are reported to show they did not
move.

| Shape | first (before) | first (after) | first cand. (before → after) | repeated | direct |
| --- | --- | --- | --- | --- | --- |
| `copied 200x5` | 587795 | 571297 | 3003 → 3003 | 28814 (201) | 78937 (1001) |
| `grouped 200x5` | 471276 | 412764 | 6788 → 5013 | 28279 (201) | 80102 (1001) |
| `grouped 50x40` | 6806016 | 1285325 | 71805 → 10646 | 7735 (51) | 124627 (2001) |

**`copied 200x5` does not move, and that is consistent rather than a miss.**
Its shared structure across groups already kept the value table small (3003
candidates before this item, against 6788 and 71805 for the grouped shapes at
the same list lengths), so there was little quadratic overshoot there to
remove — the fix collapses a sweep-per-position cost, and a table that was
already close to its floor has no positions' worth of sweeps to collapse.

**`grouped 50x40` is 5.3x faster and still 5.3x direct's candidate count, not
1x.** The remaining gap is the `71706`-candidate finding F6 already recorded
as intact and out of this item's scope: the reconstruction still derives
`$member` (and any other list function) as a general relation over every list
position rather than answering only the query's own goal, which is a
different overshoot from the one this item removed. Closing it further would
mean deriving list functions lazily against what the query actually asks
rather than eagerly over the whole extension, which is a new design rather
than a fix to this mechanism and is left as a follow-up.

**Every other benchmark's fact and derivation counts are unchanged.**
`benchmark-maintenance`, `benchmark-structural-deletion` and
`benchmark-interning` report the same over-deleted, rederived, fallback,
expansion and closure-fact counts as before this item — only timings moved,
and by amounts the plan's own noise note already covers. `benchmark-join-planning`,
`benchmark-aggregation`, `benchmark-materialization` and
`benchmark-projected-aggregate` likewise report unchanged maintain/recompute/
fallback counts.

### F7's third item: incremental maintenance of a kept reconstruction — declined

**Declined 2026-08-26**, in its own session as the boundary above asks, rather
than implemented. The scope explicitly allowed this: "this may reasonably be
split out or declined." Recorded here with the alternative and why it loses,
since the hard rule for this run is to record a decision rather than skip it
silently.

**The alternative was maintaining the cache entry's staged database from the
source database's own change stream, instead of discarding it on any
`fact_generation` move.** The staged database already is a `database.Database`,
and M2/M3 already know how to run an insertion or removal batch against one —
the plan's own open question named this directly. What it does not have is a
*source* for such a batch: `fact_generation` is a single counter that moves on
any insertion or removal reachable from `applyInsertion`/`applyRemoval`, with
no record of which fact or which readable name, because F7's first item chose
that counter for exactly the reason a richer stamp was rejected — "the
database does not know the catalog and a stamp that guessed would be a stamp
that could guess wrong." Turning it into maintenance would mean threading an
actual per-change record (fact, readable name, insertion or removal) out of
every call site that can move the counter, then, for every live cache entry —
up to four, each keyed to a different plan and each admitting a different
subset of readable names — deciding whether that change is inside the
catalog it was built against and replaying it if so. That is a second
plumbed path through the update code for a feature only the cache uses,
maintained beside the first item's stamp rather than instead of it, since a
change to what the catalog itself admits (a view made readable or
unreadable, a rule added) still has to discard the entry outright.

**It loses on what it would buy against what F7's second item already
bought.** The case incremental maintenance targets is a folded question asked
repeatedly against a database that keeps changing between calls — the `first`
column of F7's own measurement table, which a fact-stamp cache cannot help
because every call sees a new stamp. The second item just cut that column's
worst case from 6.8ms to 1.3ms (5.3x) by removing the sweep-per-list-position
cost, which was the larger share of it on every shape measured. What
incremental maintenance would still recover on top of that is bounded by the
`copy` and `solve` floors from F7's own measurement gate — a few hundred
microseconds on these shapes — against a design that touches every fact-change
call site in the engine and adds a second variety of cache-entry invalidation
next to the one that already works. The plan's own words on the parallel
question in P4 apply here too: eliminating a phase dominates speeding it up,
and the phase left to eliminate is now small enough that the architecture cost
of eliminating it is not obviously worth paying.

**This is a decision to defer, not to close.** If a workload turns up where
folded questions are asked at a rate that makes even the reduced `first`
column dominate, the design sketched above — a per-change record threaded out
of `applyInsertion`/`applyRemoval`, replayed against a cache entry whose
catalog still admits it — is the one to build, and F7's first item already
put the pieces it would need (a `database.Database` kept per cache entry, a
monotone stamp that tells a caller when it is stale) in place for it.

## Suggested session sequence

Use one session and one commit per phase unless a phase proves too large:

1. S1 finite-f64 policy, syntax, and formatting — **done 2026-08-06**
2. S2 canonical mixed numeric semantics — **done 2026-08-06**
3. S3 typed embedding, owned results, and migration — **done 2026-08-06**
4. P1 relation store and indexes — **done 2026-08-06**
5. P2 semi-naive evaluation — **done 2026-08-06**
6. M1 persistent rebuild-equivalent materialization — **done 2026-08-06**
7. M2 insertion deltas — **done 2026-08-06**
8. M3 deletion and negation maintenance — **done 2026-08-06**
9. M4 aggregate group maintenance — **done 2026-08-06**
10. M5 projected views and CReaM counts — **done 2026-08-06**
11. M6 downstream propagation and public API — **done 2026-08-06**
12. M7 deletion through seeded structural rules — **done 2026-08-07**
13. P3 join planning and aggregate lookup — **done 2026-08-07**
14. F1 folding IR and view catalog — **done 2026-08-11**
15. F2 ordinary Inverse Method — **done 2026-08-11**
16. F3 conjunctive aggregate inversion — **done 2026-08-11**
17. F4 soundness restrictions — **done 2026-08-25**
18. F5 list functions and dependency chase — **done 2026-08-25**
19. F6 execution and view selection — **done 2026-08-25**
20. F7 folded execution that reuses its work — **done 2026-08-26**: first and
    second items implemented, third item (incremental maintenance of a kept
    reconstruction) explicitly declined per the phase's own scope note

P4 is not in this sequence. It is constant-factor work with no semantics, its
items are independently shippable, and it can be taken whenever the engine's
speed matters more than its features — including before F1. All four items
are now done: a hash index beside each value table and one transaction per
run of assertions on **2026-08-25**, a flat pattern index on **2026-08-26**,
and plan caching per rule on **2026-08-26** in a second session after a first
attempt the same day was reverted for regressing `benchmark-folding`'s worst
shape by 70% and `benchmark-aggregation`'s recomputation row by 59%. The
second attempt added the staleness signal the first one lacked — a
fact-count fingerprint over the predicates a rule's body reads — and passed
the same two benchmarks it had previously failed; both attempts and the
signal's own accepted limitations are recorded in P4's completed-decisions
section.

F7 is in the sequence rather than beside it because it is not constant-factor
work: it changes what `answerFolded` keeps between calls, which is a contract
other phases could come to rest on. It is also the largest measured constant
factor in the engine, so a session choosing between it and P4's remaining item
should take this one — the numbers are in F7's own section.

F1–F5 may run in parallel with the rest in separate branches because they share
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

- ~~Should persistent materialization be eager at update time or lazy at the
  next query?~~ **Answered by M1: lazy**, with `materialize` as the eager
  trigger. An update marks the affected strata and the next evaluation repairs
  them; both paths stage and commit atomically.
- ~~Which bound-position indexes justify their memory cost on typical embedded
  workloads?~~ **Answered empirically rather than by policy**, and re-answered
  once. An index is built on the *second* request for a pattern, not the first,
  because a single probe cannot repay a pass over the relation — re-measured
  under P4's flat layout and kept, at 1.30x on the sparse join. The second rule
  is gone: an index used to survive a clone only when its groups were dense
  enough to be worth an allocation apiece, and a flat index copies with three
  `memcpy`s, so every index is now carried. The surviving rule is in
  `relation_store.zig` with the measurement behind it.
- ~~Should full rebuild remain public, test-only, or available through a debug
  policy after incremental maintenance is stable?~~ **Answered 2026-08-26: no
  change.** It stays exactly as it is — a public/test-only reference path per
  shared correctness rule 1. Nothing measured in this project argues for
  restricting it: it costs nothing to keep (it is only ever called, never
  built eagerly), it is the differential-testing oracle every maintenance
  phase compares against, and it is an embedder's escape hatch when a policy
  decision (e.g. `plan_policy`, `MaintenancePolicy`) goes wrong for their
  workload. Restricting it would be a public-API change with no problem
  behind it to justify one.
- Is delete-and-rederive sufficient for the expected recursive workloads, or
  should a later design adopt a differential-dataflow-style timestamp model?
  **Left open 2026-08-26.** Unlike everything else resolved in this document,
  nothing has measured a workload where delete-and-rederive actually strains —
  this stays open pending one turning up, rather than speculatively designing
  a timestamp model against no measured deficiency.
- Should folded plans be returned only as an internal executable IR, or also as
  printable Datalog extended with internal function terms? **F1 answered half
  of it**: a plan renders as Datalog extended with generated function terms,
  deliberately spelled so that it is not valid user input, because while no
  executable form exists the rendering is the only way to read a plan at all.
  **F2 answered the other half**: an executable form exists, produced by
  `lowerPlan` and only for a plan proved free of Skolem terms. **F6 closed
  it: both, and neither is handed over.** A caller gets the rendering through
  `explainFold` and reaches the executable form only by asking the database to
  run the plan, because a lowered plan's rules are interned against one
  database and a caller holding them could install them somewhere the plan's
  assumptions do not hold.
- ~~Is `maximally_contained` useful to embedders without an accompanying
  explanation of which source relations could not be reconstructed?~~
  **Answered by F6: no, and the explanation was already being computed.**
  `foldReconstructions` reports every relation the plan derives instead of
  reads and whether it derives all of it, from the transformations F4 and F5
  record. The guarantee bounds the answers; only the per-relation account says
  where one could have gone.

## Follow-ups

Noticed while doing scoped work, deliberately not chased there:

- F7's second item removed the sweep-per-list-position cost from seeded
  structural evaluation but left intact the overshoot F6 already recorded: a
  folded reconstruction still derives a list function like `$member` as a
  general relation over every position of every list the plan reads, rather
  than answering only the positions the query's own goal asks about.
  `grouped 50x40`'s repeated-call candidate count (51) already matches direct
  well; it is the *first* call, at 10646 against direct's 2001, where this
  remains. Closing it wants the reconstruction to derive list functions lazily
  against the query rather than eagerly over the whole extension, which is a
  new design rather than a fix to `applyRule`'s seed branch.

  **Attempted and reverted on 2026-08-26.** `member(X, L)` with `L` already
  bound has an exact native equivalent — walk `L`'s own cons chain rather than
  consult the relation `$member`'s three generated rules derive — since
  `$member`'s only caller (`inversion.Builder.membership`) always supplies a
  `setof`-collected, hence always-bound-when-reachable, list. Built as
  `Evaluator.list_membership: ?relation_store.PredicateKey`, set only by
  `Jatalog.deriveReconstruction` from a new `folding.Executable.list_membership`
  field, so no database outside a fold reconstruction is affected. Fell
  through to the ordinary relational lookup whenever the list argument was
  unbound.

  A first version unconditionally skipped a call in which a semi-naive delta
  constraint named `$member`'s own clause, reasoning that `expandLevel`
  restricts one occurrence per call, so some *other* call always leaves
  `$member` unrestricted and already covers a binding no native walk missed.
  That reasoning assumes the clause order is fixed across rounds, and it is
  not: the planner's own cost model treats an empty relation as free
  (`estimate() = facts/(groups orelse 1)`, zero over one), so a rule reading
  both `$member` and a base relation plans `$member` *first* while it is
  still empty — before `$member`'s own seeded rules have run that round.
  P4's fourth item's plan cache then notices `$member` grow and replans,
  moving it second — and the only call that ever has `$member`'s argument
  bound thereafter is exactly the delta-restricted one the skip discarded,
  losing real answers. `root.zig`'s "cost picks between views that
  reconstruct one relation exactly" test caught it (2 expected, 0 found);
  traced with temporary debug instrumentation dumping each `matchClauses`
  step and each fold rule's resolved predicate names, which is how the
  planner's reordering was found at all.

  Falling through to the relational lookup whenever the constraint names
  `$member`'s own clause (matching what a stale-plan replan already does
  correctly) fixed the answer but not the performance: with that guard, the
  native walk *never fires for the external consumer's own read* in this
  shape — round zero always finds `$member` unbound (planned first, still
  empty) and falls through, and every later bound call is the one the guard
  also routes to relational. The only path the native walk ever actually
  exercises is `$member`'s *own* recursive reads (`first`/`rest`'s body,
  always unconstrained since seeded rules never receive a delta), and that
  measured as a wash or a net loss against the pattern-indexed lookup it
  replaced: `grouped 50x40`'s first-call candidate count dropped from 10646
  to 7240, but wall-clock time rose from a tight 1300–1333k ns (four baseline
  runs) to a tight, non-overlapping 1382–1416k ns (four runs with the fix) —
  about 8%, reproducible, not noise. `zig build test` stayed green (235
  tests) through every version tried.

  **What this leaves for a later attempt.** The actual blocker is the
  planner's "an empty relation is free" cost heuristic, which plans `$member`
  first precisely because it has not been given a chance to be bound yet —
  backwards for what this optimization needs. Fixing that heuristic is a
  general cost-model change with consequences well beyond folding (every
  query in the engine costs through the same `Selectivity.estimate`), and the
  alternative — deriving `$member` on demand from a specific bound value
  regardless of clause order, i.e. the demand-driven design this session's
  own scoping discussion already named and set aside as large — is not
  smaller. Neither is a follow-up-sized fix; both need their own session.
  `src/evaluator.zig`, `src/folding.zig`, and `src/root.zig` were restored to
  their last-committed content (verified byte-identical), and no commit was
  made for the attempt.
- P4's fourth item's fingerprint (done 2026-08-26) originally invalidated a
  cached plan only on a fact-count change in a predicate the rule's body
  reads, which missed a pattern index appearing between two calls with *no*
  change in fact count. **Closed the same day**: the fingerprint now records,
  per placed step (recursing into a `setof`'s inner plan), the exact
  `RelationStore.selectivity` result for that step's own `(key, mask)` —
  `facts` and `groups` both, at the mask the step actually runs with, not a
  fixed `mask = 0` per predicate — and invalidates on any change to either.
  Every benchmark's maintenance/recompute/fallback/group counts stayed
  identical, `benchmark-materialization` kept its improvement, and the two
  benchmarks the original attempt regressed stayed flat, so this closed the
  gap for free. What remains, unmeasured and left as the accepted
  approximation: a fingerprint records what each *placed* step's own
  `(key, mask)` reports, not what every clause the planner passed over in
  favor of it would report now, so a losing candidate that has since become
  cheaper than the winner still goes unnoticed. Closing that would mean the
  planner's own `chooseNext` search re-running at lookup time, which costs
  what replanning costs and defeats the cache.
