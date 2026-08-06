# First-Class Integer Scalars

Status: ready-for-agent

## Problem Statement

LiveDatalog does not currently represent integers as values. Every numeric
literal is stored as an atom spelling, then interpreted differently depending
on where it is used: arithmetic reparses atoms as signed 64-bit integers,
explicit equality and comparison reparse them as `f64`, while relational
unification, fact identity, and `setof` use exact atom IDs. These competing
interpretations produce incorrect and surprising behavior. Large adjacent
integers can compare equal through `f64` precision loss, nonnumeric comparisons
silently treat operands as zero, explicit equality can disagree with fact
matching, and aggregation can retain two values that equality considers equal.

The public Zig embedding interface reinforces this problem by constructing all
terms from strings and returning scalar results as borrowed strings. Callers
cannot state or retrieve integer intent without textual round-tripping. Its
caller-owned parsed expression trees also require intricate allocation,
ownership-transfer, and cleanup rules.

LiveDatalog needs exact first-class signed 64-bit integers, one canonical notion
of scalar identity, a typed embedding interface, strong failure atomicity, and
self-contained query results. The design must leave a clean path for future
`f64` support and a future parser-file extraction without implementing either
one now.

## Solution

Introduce a deep, in-process scalar module that owns atoms and numeric values.
It will parse and canonicalize source literals, own scalar identity and total
ordering, perform checked arithmetic and numeric comparison, and format scalar
values. The initial numeric domain is exact signed 64-bit integers. Internal
terms and ground values refer to opaque canonical scalar identities rather than
atom spellings.

Replace the string-based Zig term-construction interface with borrowed typed
descriptors. Pure helper constructors describe atoms, integers, variables,
proper and improper lists, relations, negation, equality, comparisons,
arithmetic, and `setof` without allocating or parsing term text. `Jatalog`
operations synchronously compile those descriptors into persistent or
query-local representations. Callers no longer free expressions or clauses and
never transfer descriptor ownership.

Add a transactional input compiler. Each fact, rule, retraction, or query is
validated and compiled in staging storage. Persistent operations commit their
symbols, scalars, and logical changes only after all validation and allocation
succeeds. The source parser continues to exist in its current module for this
work but lowers through the same semantic machinery as typed descriptors.

Make query results self-contained. A result owns its returned variable names,
scalars, and reachable structures, can outlive the originating database, and
provides typed atom, integer, and generic value access with distinct unknown-
variable and type-mismatch errors. Query-only terms and derived values do not
grow persistent database storage.

## User Stories

1. As a Datalog author, I want integer literals to denote exact integer values, so that large integers do not lose precision.
2. As a Datalog author, I want `1`, `01`, and `+1` to denote the same integer, so that alternate spellings do not create duplicate logical values.
3. As a Datalog author, I want `-0` to canonicalize to integer zero, so that zero has one identity.
4. As a Datalog author, I want quoted numeric text to remain an atom, so that I can deliberately store identifiers such as `'1'`.
5. As a Datalog author, I want an out-of-range bare integer to return `NumericOverflow`, so that invalid integer data is rejected explicitly.
6. As a Datalog author, I want float-shaped bare literals to return `NumericType` until floats are supported, so that future numeric syntax is reserved without being misclassified as an atom.
7. As a Datalog author, I want nonnumeric comparison operands to return `NumericType`, so that atoms and structures are never silently treated as zero.
8. As a Datalog author, I want integer equality to be reflexive and exact, so that every integer equals itself and distinct integers stay distinct.
9. As a Datalog author, I want explicit equality and relational unification to share scalar identity, so that substituting an equal value does not change query answers.
10. As a Datalog author, I want fact deduplication to use canonical scalar identity, so that alternate integer spellings do not create duplicate facts.
11. As a Datalog author, I want arithmetic result checks to use canonical scalar identity, so that equality-shaped arithmetic behaves like equality.
12. As a Datalog author, I want `setof` to deduplicate canonical integers, so that it cannot retain multiple spellings of one number.
13. As a Datalog author, I want integers in `setof` output to sort numerically, so that `2` appears before `10`.
14. As a Datalog author, I want a deterministic mixed ground-value order, so that aggregate output remains reproducible.
15. As a Datalog author, I want integer semantics to work recursively inside lists, so that nested values obey the same identity and ordering rules.
16. As a Datalog author, I want addition and subtraction to remain checked `i64` operations, so that overflow never wraps silently.
17. As a Datalog author, I want arithmetic to require bound integer operands, so that evaluation remains safe and terminating under the existing rules.
18. As a Datalog author, I want source-text programs and typed embedding programs to produce identical semantics, so that interface choice does not change answers.
19. As a Zig embedder, I want to construct atoms explicitly, so that numeric-looking atom text is unambiguous.
20. As a Zig embedder, I want to construct integers from `i64` values, so that I never format and reparse numeric strings.
21. As a Zig embedder, I want variables to be explicit typed descriptors, so that source-level uppercase naming rules do not control typed construction.
22. As a Zig embedder, I want to construct proper lists without parsing list syntax, so that structural inputs are typed.
23. As a Zig embedder, I want to construct improper lists and head-tail patterns, so that typed construction covers the full supported term language.
24. As a Zig embedder, I want typed goal constructors for equality, comparison, arithmetic, negation, and aggregation, so that operator arity and role are not encoded as magic predicate strings.
25. As a Zig embedder, I want construction descriptors to allocate nothing, so that simple facts and queries are cheap and failure-free to describe.
26. As a Zig embedder, I want database operations to borrow descriptors only for the call, so that stack values and temporary slices are safe.
27. As a Zig embedder, I want facts and rules copied only after successful validation, so that caller ownership never transfers conditionally.
28. As a Zig embedder, I want failed operations to leave all database state unchanged, so that retries are predictable.
29. As a Zig embedder, I want query-only terms not to accumulate in the database, so that repeated ad hoc queries do not create permanent growth.
30. As a Zig embedder, I want query results to own their values, so that results can outlive the database that produced them.
31. As a Zig embedder, I want `getAtom` and `getInteger`, so that result access never reparses or formats the wrong scalar kind.
32. As a Zig embedder, I want lookup errors to distinguish an unknown variable from a type mismatch, so that failures are diagnosable.
33. As a Zig embedder, I want generic structural value inspection and formatting to remain available, so that list results are usable without scalar assumptions.
34. As a maintainer, I want one scalar module to own parsing, identity, ordering, arithmetic, and formatting, so that numeric policy has locality.
35. As a maintainer, I want callers to depend on opaque scalar identities, so that adding `f64` later does not change structural term and value variants.
36. As a maintainer, I want source parsing and typed descriptors to share one semantic compiler, so that the two entry paths cannot drift.
37. As a maintainer, I want the parser to be movable into its own file later through one-way dependencies, so that this refactor does not create an import cycle.
38. As a maintainer, I want strong per-operation allocation rollback, so that allocation-failure testing proves both memory safety and logical atomicity.
39. As a maintainer, I want tests at the public `Jatalog` interface, so that implementation refactors do not require behavioral test rewrites.
40. As a future maintainer, I want float-shaped syntax reserved today, so that introducing `f64` does not reinterpret previously valid atom data.
41. As a future maintainer, I want integer/float identity policy already defined, so that future float support remains local to the scalar module.

## Implementation Decisions

- The current numeric domain is signed 64-bit integers only. Integer parsing
  uses checked signed decimal conversion.
- A scalar is a ground, non-structural value. The scalar module owns atom bytes
  and supported numeric values; predicate and variable symbols remain in a
  separate symbol store.
- Scalar identities are canonical and opaque outside the implementation.
  Internal structural terms and values contain one scalar variant referring to
  that identity, rather than separate atom and integer variants.
- Bare signed decimal integers are recognized by syntax, range-checked, and
  canonicalized by numeric value. Alternate spellings including leading zeroes,
  a leading plus, and negative zero do not survive as distinct values.
- Quoting forces atom construction. A quoted value whose bytes look numeric is
  distinct from an integer.
- Bare decimal and exponent-shaped literals are reserved and return
  `NumericType` until floating-point support is implemented. Integer-shaped
  literals outside the `i64` range return `NumericOverflow`.
- Explicit equality, relational unification, fact identity, arithmetic output
  checking, structural equality, and aggregate deduplication use the same
  canonical scalar identity.
- Numeric comparisons accept supported numeric scalars only. Nonnumeric atoms,
  lists, and other structures return `NumericType`; there is no zero fallback.
- Addition and subtraction remain checked `i64` operations. Their operands must
  be bound integers, and overflow returns `NumericOverflow`.
- Canonical ground-value total order is: numbers in numeric order, atoms in
  lexical byte order, `nil`, then cons values lexicographically by head and
  tail. Total ordering reports equality exactly when canonical identity is
  equal.
- The future float identity policy is numeric rather than representation-
  sensitive. A future finite `f64` that exactly represents an in-range integer
  canonicalizes to that integer. Future mixed integer/float comparison must be
  exact without first coercing the integer to `f64`. Future mixed arithmetic
  produces `f64`, then canonicalizes an exact in-range integral result back to
  an integer.
- NaN and infinity policy is deliberately deferred until float implementation;
  no non-finite branches are added by this work.
- The scalar module is a concrete in-process dependency. It has no injected
  interface or adapter because no implementation varies.
- A separate typed-input compiler module lowers borrowed descriptors into the
  engine's internal representation and owns validation, staging, and commit.
- Textual parsing remains where it currently lives for this work. It must use
  the same scalar semantics and input compiler as typed construction. The
  dependency direction must allow a later parser extraction without the scalar
  module importing parser code.
- The public Zig embedding interface intentionally breaks compatibility. String
  term interpretation is removed from fact, expression, rule, query,
  retraction, and aggregate construction. The source-oriented `execute`
  operation remains textual.
- Typed input uses borrowed, allocation-free term and goal descriptors with
  pure helper constructors. Terms cover scalar atoms, integers, variables,
  proper lists, and improper cons structures. Goals cover positive relations,
  negation, equality, inequality, numeric comparison, arithmetic, and `setof`.
- Future `f64` construction adds a scalar helper and result getter without
  changing structural term descriptors.
- Descriptor constructors cannot fail and retain no database-owned identity.
  Database calls borrow descriptor strings, slices, and recursive references
  only for the duration of the synchronous call.
- Typed descriptor compilation must validate recursive borrowed structures and
  reject malformed or cyclic input with a dedicated invalid-term failure rather
  than recursing indefinitely.
- Database operations no longer take ownership of caller expressions or
  clauses. The public cleanup operations for those caller-owned parse trees are
  removed with the string-construction interface.
- Facts and rules compile into persistent database-owned storage. Queries and
  retractions compile into temporary workspaces.
- Strong atomicity applies per typed database operation and per parsed
  statement. Validation and allocation use staging storage; failure leaves
  facts, rules, symbols, and scalars unchanged. A multi-statement `execute` call
  is not one transaction: statements committed before a later statement fails
  remain committed.
- Query evaluation uses a temporary overlay rather than inserting query-only
  scalars and values into persistent storage.
- `QueryResult` is self-contained. It owns returned variable names, scalar
  bytes and numbers, bindings, and all answer-reachable structural values.
  Destroying the originating database does not invalidate the result.
- Results expose answer views with explicit atom, integer, and generic value
  access. Typed getters return distinct unknown-variable and type-mismatch
  errors. A future float getter is additive.
- Generic result values support deterministic formatting and structural/list
  inspection. Typed atom access never formats integers, and typed integer access
  never reparses atom bytes.
- Result views and borrowed atom slices remain valid until their owning result
  is deinitialized. Formatting operations that allocate make ownership explicit
  in their names and return caller-owned memory.
- Built-in identity, arity, binding requirements, scheduling role, and
  evaluation behavior should be represented by typed goal kinds rather than
  repeated operator-string checks. The input compiler and evaluator share that
  classification.
- Existing termination and admissibility behavior remains: unrestricted
  arithmetic generators are rejected, while structurally decreasing list
  recursion may use checked arithmetic.
- Implementation-specific interning structures and algorithms remain hidden.
  This spec does not require a particular hash table, ID width, or storage
  layout as long as canonical identity and observable semantics hold.

## Testing Decisions

- The primary test seam is the public `Jatalog` interface. Tests exercise both
  source-text execution and typed descriptors, then assert observable query
  results, public errors, rollback behavior, and result lifetimes.
- Do not test private scalar-store representation, ID allocation, hash-table
  layout, or compiler staging details. Add focused lower-level tests only if an
  invariant cannot be observed through `Jatalog`.
- Existing end-to-end query, recursive-list arithmetic, aggregation,
  retraction, CLI, and exhaustive allocation-failure tests are prior art. Migrate
  their typed construction portions to the new interface while preserving their
  externally visible intent.
- Add paired source/typed tests for atoms, integers, variables, proper lists,
  improper lists, comparisons, arithmetic, negation, rules, retraction, and
  nested `setof`.
- Test integer canonicalization for zero, negative zero, leading plus, leading
  zeroes, `i64` minimum, and `i64` maximum.
- Test source parsing failures immediately outside both `i64` limits.
- Test that decimal and exponent-shaped bare source literals return
  `NumericType`, while quoted equivalents remain atoms.
- Test that quoted numeric atoms and integer values remain distinct in facts,
  equality, unification, lists, formatting, ordering, and `setof`.
- Test exact equality for adjacent integers above `2^53`, including recursively
  inside lists.
- Test nonnumeric comparison operands including atoms, `nil`, proper lists, and
  cons values; every case must return `NumericType` rather than compare as zero.
- Test positive and negative addition/subtraction, both overflow directions,
  noninteger operands, bound-output success, bound-output mismatch, and variable
  output binding.
- Test that fact insertion and matching, explicit equality, arithmetic output
  checking, and `setof` all agree on canonical integer identity.
- Test total ordering with negative integers, multi-digit integers, atoms,
  empty lists, and nested cons values. Confirm numeric rather than lexical
  integer order.
- Test typed descriptor construction for explicit lowercase variable names,
  numeric-looking atoms, empty lists, nested lists, head-tail patterns, and
  improper lists.
- Test malformed or cyclic borrowed term descriptors return the specified
  invalid-term error without leaking memory or overflowing the call stack.
- Test that typed constructors allocate nothing and cannot fail.
- Test typed getters for successful atom/integer access, unknown variables,
  type mismatches, generic structural access, and formatting.
- Test that a query result remains readable after the originating database has
  been deinitialized.
- Test repeated queries with novel literals and derived structures through a
  bounded allocator or equivalent public behavior so persistent query growth
  would fail the test.
- Use exhaustive allocation-failure testing at public persistent operations to
  prove that facts, rules, symbols, and scalars are unchanged after every failed
  allocation point.
- Use exhaustive allocation-failure testing for query compilation, evaluation,
  answer copying, and result construction. Every failure must release staging
  and query-local storage.
- Test statement-level source atomicity: a failing statement changes nothing,
  while successfully completed earlier statements in the same `execute` input
  remain committed.
- Run the full build test, formatting verification, lint, CLI examples, and
  aggregation workload tests after migration.

## Out of Scope

- Implementing `f64`, decimal arithmetic, NaN, infinity, or signed-zero float
  policy.
- Multiplication, division, modulo, exponentiation, casts, or aggregate-native
  arithmetic operators.
- Arbitrary-precision integers.
- Extracting the textual parser into its own file during this work.
- Preserving deprecated string-based embedding constructors or providing a
  compatibility adapter for them.
- Whole-batch transaction semantics for multi-statement `execute` calls.
- Prepared or reusable compiled queries.
- Exposing scalar IDs or private scalar representation to embedding callers.
- Performance-driven changes to indexing, semi-naive evaluation, value hashing,
  or aggregate caches unless required to avoid a correctness regression.
- Changing recursive arithmetic admissibility or structural termination proofs.
- Adding a second scalar-store adapter or an abstract seam around an in-process
  implementation.

## Further Notes

- The repository domain glossary records the agreed scalar semantics and should
  remain the source of vocabulary for implementation and documentation.
- The existing aggregation plan explicitly identifies migration from atom-
  backed integer arithmetic and legacy `f64` comparison as open work; this spec
  resolves that question in favor of first-class integer scalars.
- Existing unrelated working-tree changes must be preserved.
- A sensible implementation sequence is: establish the scalar module and
  canonical semantics; migrate internal structural values; add typed borrowed
  descriptors and the transactional compiler; route source parsing through the
  same semantics; replace query-result ownership and access; migrate public
  documentation and examples; then complete behavioral and allocation-failure
  coverage.
- Completion requires all behavior in this PRD, removal of the obsolete
  string-construction and caller-owned expression cleanup interface, updated
  language and embedding documentation, and a passing full test suite.
