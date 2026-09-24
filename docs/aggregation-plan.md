# DatalogA aggregation implementation plan

## Goal

Extend LiveDatalog with the aggregation model described in Chapters 3.1–3.3 of
Abhijeet Mohapatra's 2019 dissertation, *Aggregates in Datalog*.

The first milestone covers the DatalogA language and its bottom-up semantics:

- finite, structural list terms;
- `setof(Template, Goals, Result)` under set semantics;
- user-defined list functions for aggregates such as count and sum;
- safety, aggregate stratification, and an enforceable termination boundary.

Incremental view maintenance from Chapter 5 and query folding from Chapter 6
are explicitly deferred. LiveDatalog may continue rebuilding derived facts for
each query during the first milestone.

Primary-source notes and a local copy of the dissertation are indexed in
[`references/README.md`](../references/README.md).

## Semantic decisions

These decisions should remain stable across implementation sessions.

1. `setof` produces a canonical list of distinct ground terms. Ordering must be
   deterministic, but no program may depend on a particular ordering beyond
   that guarantee.
2. An empty matching set succeeds and binds the result to `[]`.
3. Aggregate bodies may only depend on completed lower strata. Recursion
   through `setof` is rejected, just as recursion through negation is rejected.
4. Ordinary positive recursion remains supported within a stratum.
5. Nested `setof` is part of the target language. It may initially be lowered
   to generated auxiliary rules so the evaluator only handles one aggregate
   goal at a time.
6. Set semantics remain the engine default. Bag aggregation can be expressed
   by including a distinguishing value in the aggregate template and then
   projecting it with a list function.
7. Retraction correctness takes priority over incremental performance. The
   existing full recomputation strategy is acceptable until the core semantics
   are complete.
8. Existing scalar Datalog programs and the public embedding API must remain
   source-compatible where practical. Any unavoidable API break should be
   isolated and documented in its phase.

## Intended language shape

The motivating program should be accepted:

```datalog
person(alice).
person(bob).
parent(alice, bob).

children(X, S) :- person(X), setof(Y, parent(X, Y), S).
numchildren(X, N) :- children(X, S), length(S, N).

length([], 0).
length(H!T, N) :- length(T, M), N = M + 1.
```

It derives `children(alice, [bob])`, `children(bob, [])`,
`numchildren(alice, 1)`, and `numchildren(bob, 0)`.

The exact concrete syntax for a multi-goal aggregate body must be decided before
Phase 2 is merged. Parenthesized bodies are the provisional choice:

```datalog
setof([Score, Student], (score(Test, Student, Score), passed(Student)), S)
```

## Phase 1: structural terms and list unification

### Scope

- Replace the flat `Term { id, variable }` representation with a structural
  term model capable of variables, atomic values, `nil`, and `cons`.
- Parse `[]`, `[a, b]`, nested lists, `H!T`, and `cons(H, T)`.
- Implement recursive structural equality, hashing or canonicalization, and
  unification.
- Permit structural terms in facts, rules, queries, and bindings.
- Define a deterministic total order for ground terms for later `setof` use.
- Preserve the existing string interning benefits for atom names and scalar
  values.

### Acceptance tests

- Existing tests remain green without source changes.
- Lists round-trip through parsing and query output.
- Nested-list facts unify structurally.
- Head/tail patterns such as `H!T` bind correctly.
- Repeated variables inside structures enforce equality.
- Ground facts containing variables or improper unbound tails are rejected.
- Allocation-failure and deinitialization tests cover the new owned structures.

### Session boundary

Stop after structural terms work everywhere ordinary scalar terms work. Do not
add `setof` in this phase.

### Completed decisions

Phase 1 was completed on 2026-07-30 with these decisions:

- Expression terms are recursive variable/atom/nil/cons patterns. Ground terms
  are canonicalized in a database-owned value table; atom leaves continue to
  use the existing string table. Facts and bindings therefore store compact
  canonical value IDs rather than owning duplicate trees.
- Proper lists print canonically as `[a, b]`. Ground improper lists are valid
  data and print with the unambiguous constructor form `cons(Head, Tail)`.
  Variables anywhere in facts, including improper tails, remain invalid.
- `H!T` is a right-associative cons pattern. `cons(H, T)` is the equivalent
  structural constructor, and bracket syntax supports empty, flat, and nested
  proper lists.
- The total ground-term order is atoms first (ordered bytewise by interned
  spelling), then `nil`, then cons cells ordered lexicographically by head and
  tail. It is independent of insertion order.
- The scalar embedding API remains source-compatible: `expr` and `not` still
  accept string slices, now parsing each string as a structural term, and
  `Binding.get` still returns scalar atoms. Structural bindings use
  `Binding.getValue` with `Jatalog.writeValue` or `Jatalog.formatValue`.
- Recursive expression trees are caller-owned under the existing expression
  ownership rules. Canonical ground values live for the database lifetime.
  Exhaustive allocation-failure tests cover structural parsing, rule/query
  evaluation, formatting, and teardown.

These embedding and scalar decisions were superseded on 2026-08-06 by the
first-class integer scalar implementation: typed borrowed descriptors replaced
caller-owned expression trees, results became self-contained, and integers no
longer use atom spellings.

## Phase 2: aggregate syntax, safety, and stratification

### Scope

- Introduce distinct clause variants for relational goals, built-ins, negation,
  and aggregate goals.
- Parse `setof(Template, Goals, Result)`, including nested terms and conjunctions.
- Record every predicate referenced by an aggregate body in the dependency
  graph as a strict dependency.
- Extend stratum computation to reject every cycle containing a negated or
  aggregate edge.
- Implement DatalogA aggregate safety checks:
  - head variables must be bound by positive goals or aggregate output;
  - variables correlated into an aggregate body must be bound outside it;
  - local variables may occur only inside the aggregate template/body;
  - aggregate output must be bindable at its evaluation point.
- Decide whether nested aggregates are represented directly or lowered to
  generated auxiliary predicates.

### Acceptance tests

- Valid correlated aggregates parse and validate.
- Unbound correlation variables are rejected.
- Direct and indirect recursion through `setof` returns `NotStratified`.
- Positive recursion below an aggregate remains valid.
- Negation and aggregation edges interact correctly in the same dependency
  graph.
- Parser errors inside an aggregate release all partially built structures.

### Session boundary

Stop with aggregates represented and validated but not necessarily evaluated.

### Completed decisions

Phase 2 was completed on 2026-07-30 with these decisions:

- Rule bodies use a tagged clause union with distinct relational, built-in,
  negated, and aggregate variants. `Aggregate` owns a template term, a clause
  body, and an output term.
- `setof(Template, Goal, Result)` accepts a single goal directly. Multi-goal
  bodies use the parenthesized conjunction syntax
  `setof(Template, (Goal1, Goal2), Result)`. Structural terms are accepted in
  both the template and output positions.
- Nested aggregates are represented directly as recursive clause trees rather
  than lowered to generated predicates. This keeps source-level variable scope
  explicit for safety checking and leaves lowering as an optional future
  optimization.
- A variable used inside an aggregate and elsewhere in its enclosing scope is
  correlated and must be bound before that aggregate is scheduled. Variables
  confined to the aggregate template/body are local; they cannot escape through
  the result, another outer clause, or the rule head. Aggregate output terms
  bind their variables after the aggregate safety check.
- Safety scheduling retains the engine's existing conjunction behavior:
  positive relational goals and binding equality run first, aggregates run
  next in source order, and negation/comparison checks run last. The same rules
  apply recursively inside nested aggregates and to parsed aggregate queries.
- Every relational predicate anywhere in an aggregate body, including inside a
  nested aggregate, creates a strict dependency. Negated dependencies are also
  strict, and a single stratum computation rejects cycles containing either
  kind of edge while preserving ordinary positive recursion below aggregates.
  Dependency identity includes predicate arity, so relations that share a name
  but have different arities remain distinct.
- Phase 2 intentionally did not evaluate `setof`. Reaching an aggregate during
  expansion or querying returned `AggregateEvaluationNotImplemented`; Phase 3
  replaced that temporary boundary with the set semantics described below.

## Phase 3: `setof` evaluation

### Scope

- Evaluate each lower stratum to a fixpoint before evaluating dependent
  aggregate goals.
- Evaluate an aggregate body using its correlated outer binding.
- Project the template from every successful inner binding.
- Require projected terms to be ground.
- Deduplicate projected values, sort them deterministically, construct the
  canonical list, and unify it with the output term.
- Return `[]` when the body has no solutions.
- Ensure multiple aggregate goals in a rule observe only completed lower
  strata.

### Acceptance tests

- Grouped `setof` returns one canonical list per outer binding.
- Duplicate derivations and duplicate base facts do not duplicate list values.
- Empty groups produce `[]`, including for explicitly enumerated group keys.
- A recursively derived lower relation is complete before aggregation begins.
- Structural templates such as `[Score, Student]` preserve logically distinct
  bag entries under the engine's set semantics.
- Retraction changes aggregate results correctly after recomputation.
- Results are deterministic across insertion and rule order.

### Session boundary

Stop when `setof` itself is semantically complete. Built-in aggregate shortcuts
are not a substitute for these tests.

### Completed decisions

Phase 3 was completed on 2026-07-30 with these decisions:

- Expansion evaluates strata in ascending order and reaches a fixpoint within
  each stratum before rules in the next stratum run. Aggregate bodies therefore
  see completed lower-stratum relations, including recursive ones.
- Aggregate evaluation begins with a clone of the current outer binding. Every
  successful inner binding grounds the template through the canonical value
  table; an unground projection returns `UnboundVariable` rather than creating
  a partial value.
- Projected canonical values are deduplicated, ordered with the structural total
  order from Phase 1, and folded into a canonical proper list. No solutions
  produce the canonical `[]` value.
- Nested and multiple aggregate goals execute directly through the recursive
  clause evaluator. Each aggregate independently reads the completed fact set
  and can correlate variables already bound by preceding outer clauses.
- Queries may contain aggregate clauses directly. Retraction still triggers
  full recomputation on the next query, so aggregate results reflect the
  current base facts without incremental maintenance.

## Phase 4: list functions, arithmetic, and admissibility

### Scope

- Add arithmetic expressions needed by recursive list functions, initially
  integer addition and subtraction with an explicit numeric error policy.
- Support relations such as `length`, `member`, `sum`, and `collectfirst` as
  ordinary user-defined rules over lists.
- Define and implement the supported admissibility check for recursive calls
  involving `cons`: at least one bound structural argument must decrease while
  the other tracked bound arguments do not increase.
- Reject programs outside the provable termination subset instead of silently
  accepting potentially infinite materialization.
- Document any intentionally conservative false rejections.

### Acceptance tests

- `length`, `member`, `sum`, and bag-emulation examples work as user rules.
- Arithmetic binds an output variable and checks an already-bound output.
- Numeric type and overflow behavior are deterministic and tested.
- A recursive list function consuming its tail is accepted.
- A rule that grows a list recursively, such as `q([X]) :- q(X)`, is rejected.
- Existing numeric comparisons retain their behavior or have a documented,
  tested migration.

### Session boundary

Stop when the Chapter 3 examples supported by LiveDatalog's chosen arithmetic
subset work and the termination boundary is enforced.

### Completed decisions

Phase 4 was completed on 2026-07-30 with these decisions:

- Arithmetic uses signed 64-bit integers and the infix forms `N = A + B` and
  `N = A - B`. Both operands must be bound integer atoms. The result may bind
  an output term or check an already-bound output. Invalid operands return
  `NumericType`; values and operations outside the `i64` range return
  `NumericOverflow`.
- Existing comparisons retain their `f64` parsing and compatibility behavior.
  Arithmetic does not change numeric equality or ordering in this milestone.
- Recursive list relations are evaluated from a structural input pattern.
  Canonical list values introduced by later strata, including `setof` results,
  reseed admissible rules, so `length`, `member`, `sum`, and `collectfirst` can
  remain ordinary user-defined relations.
- Structural input seeding is used only when ordinary body evaluation cannot
  bind a constructor-bearing head. Non-recursive rules may therefore construct
  new list values in their heads without requiring those values to exist first.

The comparison decision above is historical. Comparisons now use exact `i64`
scalars; floating-point parsing and comparison remain deferred.
- A recursive call involving `cons` is admissible only when at least one call
  argument is reached through one or more cons tails of its head argument and
  every other statically structural argument is unchanged or likewise a tail.
  This accepts tail-consuming list recursion and rejects element recursion such
  as `q([X]) :- q(X)`.
- The checker intentionally rejects rules whose decreasing input position is
  inconsistent across recursive calls, and it does not attempt a mutual-
  recursion or semantic-size proof. These are conservative false rejections at
  the enforceable termination boundary.

  *Corrected 2026-09-24:* the checker only ever compared a head with its own
  calls, so mutual recursion was not rejected — it was never examined. A cycle
  through two predicates was admitted whatever it did, and one that built a
  list (`p(a!L) :- q(L). q(L) :- p(L).`, or the same growth through
  `X = a!L`) loaded cleanly and then never finished a query. The same was true
  of a direct self-call that built its list in an equality rather than its
  head. See the open design question below for the rule that replaced it.
- A recursive dependency cycle containing value-producing arithmetic is
  rejected unless it is a direct recursive list call covered by the structural
  decrease proof. This prevents unbounded generators such as
  `number(N) :- number(M), N = M + 1` from entering materialization.
- While admissible rules are probed against canonical structural inputs,
  numeric type and overflow failures make an unrelated candidate inapplicable.
  Arithmetic goals evaluated directly still report the explicit numeric error.

## Phase 5: integration and public documentation

### Scope

- Add a complete language-tour example to the README.
- Document the embedding API for constructing structural and aggregate goals.
- Add end-to-end CLI, query, retraction, and memory-safety coverage.
- Review error names and ensure syntax, safety, stratification, grounding, and
  admissibility failures are distinguishable.
- Measure naive evaluation on representative aggregate programs and record a
  baseline for later optimization.

### Acceptance tests

- All formatting, lint, unit, and executable tests pass.
- README examples run verbatim.
- The public API has ownership documentation for every structural term and
  aggregate expression.
- No derived aggregate state survives a base-fact retraction incorrectly.

### Completed decisions

Phase 5 was completed on 2026-07-30 with these decisions:

- The README language tour now covers structural lists, empty-group `setof`,
  recursive list functions, arithmetic, termination rules, error boundaries,
  and retraction behavior. Its checked-in aggregate program is also exercised
  through the command-line executable by the default test step.
- The typed embedding API uses `clauseFromExpr`, `setof`, `addRuleClauses`, and
  `queryClauses`. Aggregate clauses recursively own their template, output,
  and body; ownership transfers only after a successful ownership-taking call,
  while query clauses remain caller-owned.
- `InvalidSyntax`, `InvalidRule`/`InvalidQuery`, `NotStratified`,
  `UnboundVariable`, and `NotAdmissible` remain the distinct syntax, safety,
  stratification, grounding, and termination errors. Numeric failures retain
  the separate `NumericType` and `NumericOverflow` errors.
- End-to-end tests cover the public aggregate API, CLI output, complete
  query/retraction recomputation, and exhaustive allocation failures through
  typed aggregate construction and evaluation.

The current typed API uses allocation-free borrowed `input.Term` and
`input.Goal` descriptors with `addFact`, `addRule`, `query`, and `retract`.
- `zig build benchmark-aggregation -Doptimize=ReleaseFast` is the reproducible
  naive-evaluation workload. The initial 25-node recursive-closure aggregate
  baseline is recorded in `docs/aggregation-performance.md` for later work.

## Deferred projects

The implementation roadmap for all deferred work is now maintained in
[`deferred-projects-plan.md`](deferred-projects-plan.md). The summaries below
explain why each item was separated from the completed Chapter 3 milestone.

### Incremental view maintenance

Chapter 5 requires persistent materialized derived relations, delta rules,
support or derivation counts, and careful handling of insertion and deletion.
That does not match the current query-time reconstruction model and should be a
separate design project after Phase 5.

### Query folding

Chapter 6 concerns rewriting queries using materialized views. It is an
optimizer and data-integration feature rather than a prerequisite for DatalogA
semantics. It should remain independent of the core implementation.

### Performance work

Indexes, semi-naive evaluation, group-keyed aggregate caches, and incremental
aggregate accumulators should be driven by measured workloads after semantic
tests exist.

## Cross-phase completion checklist

Each implementation session should end with:

1. focused tests for its new semantic boundary;
2. the full `zig build test` suite passing;
3. formatting and lint clean;
4. documentation updated for decisions made during the session;
5. a commit whose message names the completed phase;
6. unresolved design questions recorded in this document before handoff.

## Open design questions

- ~~Whether admissibility should eventually prove mutual recursion or support
  multiple decreasing input modes instead of conservatively rejecting them.~~
  **Answered 2026-09-24: reject mutual recursion.** A recursive cycle is
  rejected with `NotAdmissible` if any rule on it builds a list — in its head
  or in an equality — exactly as a cycle with value-producing arithmetic
  already was; `validateRecursiveGeneration` in `validation.zig` checks both.
  The one cycle admitted is a rule's direct call to itself that the structural
  decrease proof covers. This refuses tail-consuming mutual recursion such as
  `even(H!T) :- odd(T). odd(H!T) :- even(T).`, which terminates: a false
  rejection accepted on purpose, since proving a decrease across predicates is
  the proof this question declines to build. A cons matched in a relational
  body clause only takes a list apart and does not count, and mutual recursion
  that builds nothing is unaffected. Multiple decreasing input modes stay
  rejected for the same reason.
