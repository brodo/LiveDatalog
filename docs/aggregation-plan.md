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

## Deferred projects

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

- Should atom and list ground terms be hash-consed into one canonical value
  table, or should only scalar leaves remain interned?
- Should improper lists be permitted as ground data, or only as intermediate
  unification patterns?
- What is the total ordering across atoms, numbers, and nested lists?
- Should arithmetic initially use integers, preserve the current `f64`
  behavior, or introduce tagged numeric values?
- How conservative may the admissibility checker be?
- Should `setof` bodies use explicit parentheses, braces, or another syntax to
  delimit conjunctions unambiguously?

