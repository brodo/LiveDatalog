# Predicate Schemas

Status: done

## Problem Statement

Every predicate is untyped. Nothing stops `age(alice, "thirty")`, `age(bob)`
alongside `age/2`, or a rule that derives atoms into a column every other
producer fills with numbers. Such mistakes don't raise an error. They show up
as missing answers, as `NumericType` failures that rule evaluation skips
silently, or as a new relation with a different arity. An embedder has no way
to state a relation's shape and have the engine hold the program to it.

## Solution

Add an optional **schema** per predicate name, declaring the predicate's arity
and one column type per position (see "Schema" in `CONTEXT.md`). A declared
schema is enforced:

- Base facts are checked when they are asserted.
- Rules, queries, retractions and fold inputs are checked statically when they
  are added or run.
- Derived facts are never checked at runtime (ADR 0004).

A value whose type can't be proven (`any`) may enter a typed column only
through a type test `X : T`, which filters and narrows. Predicates without a
schema behave exactly as today.

```datalog
schema person(Name: atom).
schema age(Person: atom, Years: int).
schema scores(atom, list(number)).

age(alice, 36).
age(bob, old).          % SchemaViolation: Years is int
age(carol).             % SchemaViolation: age has arity 2

adult(X) :- age(X, Y), Y >= 18.                 % X: atom, fine
schema adult(atom).
tagged(X) :- raw(X), X : atom.                  % raw untyped; the test proves atom
schema tagged(atom).
bad(X) :- raw(X).                               % IllTyped once bad has a schema
```

## User Stories

1. As a program author, I can declare a predicate's arity and column types,
   and asserting a fact that doesn't fit fails with `SchemaViolation`.
2. As a program author, using a typed predicate with the wrong arity anywhere
   (rule, query, retraction) fails with `IllTyped` and doesn't create a
   separate relation.
3. As a program author, a rule whose head can receive a value of the wrong
   type is rejected when it is added, not discovered later through missing
   answers.
4. As a program author, a goal that can never match because of a schema (for
   example `age(X, foo)` with `Years: int`) is an error, not an empty answer.
5. As a program author, I can feed values from an untyped predicate into a
   typed one by filtering them with a type test `X : T`.
6. As a program author, I can add a schema to a predicate that already has
   facts and rules. The declaration succeeds if they all fit and otherwise
   fails without changing anything.
7. As a program author, re-running a file whose schema declarations are
   identical does nothing, and a conflicting declaration fails with
   `SchemaConflict`.
8. As an embedder, I can declare schemas through `input` descriptors and
   `Jatalog.declareSchema`, with the same meaning as the source syntax.
9. As an embedder, one fact in an `applyChanges` batch that violates a schema
   rejects the whole batch and leaves the database unchanged.
10. As an embedder, maintenance cost and behaviour are unchanged by schemas.

## Implementation Decisions

### Type language

- Column types: `atom`, `int`, `number`, `list`, `list(T)`, `any`. `list` is
  `list(any)`. Nesting is allowed (`list(list(int))`).
- There is no `float` type, because integral floats canonicalize to integers.
- Subtyping: `int ⊂ number ⊂ any`, `atom ⊂ any`, `list(T) ⊂ list(U)` iff
  `T ⊂ U`, `list(T) ⊂ any`.
- Membership of a ground value:
  - an integer scalar is `int` and `number`
  - a float scalar is `number`
  - an atom scalar is `atom`
  - `[]` is every `list(T)`
  - a cons cell is `list(T)` when its head is `T` and its tail is `list(T)`
  - improper structures are only `any`
- Intersection (meet) is the operation that combines constraints on one
  variable. An empty meet (for example `int` ∩ `atom`, or `list` ∩ `number`)
  makes the goal impossible.

### Syntax

- Statement: `schema <name>(<column>, ...).` where
  `<column> ::= [<Name> ':'] <type>`.
  - Column names are optional, capitalised like variables, and distinct
    within one schema.
  - A 0-arity schema is `schema flag().`
- `schema` is a keyword only when an identifier follows it, so
  `schema(x).` is still a fact.
- Type test goal: `<term> : <type>`, allowed wherever a built-in test is
  (rule bodies, queries, retractions, `setof` bodies). `not X : T` is
  allowed.
- Type names are recognized only after `:` inside a schema or a type test.
  Elsewhere they remain ordinary atoms.

### `input` additions

- `ColumnType = union(enum) { atom, int, number, any, list: ?*const ColumnType }`
  (`list = null` means `list(any)`).
- `Column = struct { name: ?[]const u8 = null, type: ColumnType }`.
- `Schema = struct { predicate: []const u8, columns: []const Column }`.
- `Statement.schema: Schema`.
- `Goal.type_test: struct { term: Term, type: ColumnType }`, plus a matching
  `NegatedBuiltin.type_test`.
- Helper constructors in the existing style: `schema`, `column`,
  `typeTest`.

### Public interface (`root.zig`)

- `Jatalog.declareSchema(schema: input.Schema) !void`.
  - It runs in a transaction and validates every existing fact and rule of
    that name.
  - Returns `SchemaViolation` if an existing fact doesn't fit, `IllTyped` if
    an existing rule doesn't check, and `SchemaConflict` if a different schema
    is already declared.
  - An identical redeclaration does nothing. Column names count toward
    "identical".
- `executeStatements` / `execute` run `.schema` statements through the same
  path.
- `clone` copies schemas.
- No removal or replacement API in this version.

### Errors (`errors.zig`)

- `SchemaViolation`: an asserted base fact has the wrong arity or a value
  outside its column type.
- `IllTyped`: a rule, query, retraction or fold input fails the static check.
  This covers wrong arity, an impossible goal, and `any` or a too-wide type
  flowing into a narrower head column.
- `SchemaConflict`: a declaration differs from the existing schema for that
  name.
- `TypeMismatch` keeps its current meaning (the wrong answer-value getter).

### Static checking

- **Per rule:** infer a type for each variable as the meet of every
  constraint on it.
  - Typed relation positions, positive or negated, constrain their variable
    to the column type.
  - Untyped predicates give `any`.
  - `H!T` / `cons` / list literals against `list(T)` give the element type
    and list type.
  - `=` meets both sides.
  - `<` `<=` `>` `>=` `+` `-` constrain their operands to `number`, and
    arithmetic output is `number`.
  - `setof(Tmpl, G, R)` gives `R: list(type(Tmpl))`, typed in its own scope.
  - A positive type test `X : T` meets `X` with `T`. A negated one adds no
    constraint.
  - Constants have their literal's type.
- **Rejections:**
  - Any variable with an empty meet makes the rule `IllTyped`.
  - A head column whose inferred type isn't a subtype of the schema's column
    type makes the rule `IllTyped`.
  - A goal whose literals are outside their column types makes the rule
    `IllTyped`.
- Queries and retractions get the same body check; they have no head.
- Fold inputs (`foldQuery`'s rules and goals) are checked as rules and
  queries.
- Untyped predicates are always `any`. No inference across rules (ADR 0004).
- Comparisons on `any` operands keep today's runtime behaviour (the candidate
  is skipped on `NumericType`). Only an operand proven non-numeric is
  `IllTyped`.
- Checking runs after parsing, when the statement runs, next to the existing
  admission checks (safety, admissibility, stratification). The parser still
  decides only shape.

### Enforcement of facts

- Every base-fact entry point (`addFact`, fact statements, `applyChanges`
  insertions) checks against the schema before staging.
- One violation fails the whole statement or batch through the existing
  transaction rollback.
- Retractions never add facts, so they need only the static goal check.

### Evaluation

- The type test is a new built-in test clause. It needs no bindings beyond
  its operand (the operand must be bound, otherwise `UnboundVariable`, like
  other tests). A `list(T)` test walks the list, which is O(length).
- Planner and maintenance treat it like the other filtering built-ins.
- Folding carries it through as an ordinary test.

### Modules (ADR 0002)

- `schema.zig` (new, below `database.zig`):
  - `ColumnType`, the subtype and meet operations, and value membership over
    the interned tables.
  - The per-name schema registry that `Database` holds.
  - Types live below the state that holds them.
- `typing.zig` (new, at `validation.zig`'s level): the static checker. It
  takes a `*Database` and never names `Jatalog`.
- `syntax.zig` / `compile.zig` / `input_compiler.zig`: compile `type_test`
  and `.schema`.
- `evaluator.zig`: evaluate `type_test`.
- `parser.zig`: the `schema` statement and `:` type tests. It stays pure and
  needs no database.

### Docs

- `docs/language-tutorial.md`: a new "Schemas" section and syntax-reference
  entries. Fix the stale sentence claiming numeric comparisons accept only
  integers; mixed int/float comparison is exact.
- `CONTEXT.md` "Schema" entry and ADR 0004 are already written.

## Testing Decisions

- `schema.zig` needs no parser:
  - a membership table over scalars, `[]`, nested and improper lists
  - subtype and meet laws: reflexive, `list` ≡ `list(any)`, and an empty meet
    for disjoint types
- `typing.zig`, over hand-built descriptors:
  - each inference rule
  - `any` into a typed head rejected, and accepted after `X : T`
  - `not X : T` not narrowing
  - `setof` output typing
  - impossible goals in bodies, queries and retractions
  - wrong arity
- Parser:
  - `schema` with and without names
  - 0-arity schemas
  - `schema(x).` stays a fact
  - `X : list(int)` and `not X : atom`
  - malformed type names give `InvalidSyntax` with a diagnostic
- Integration (source-built, `root.zig`):
  - every user story
  - declaring over existing conforming or violating facts and rules, and that
    the database is unchanged on failure
  - identical redeclaration does nothing, conflict errors
  - batch atomicity in `applyChanges`
  - a `1.0` literal fits `int`
  - `clone` preserves schemas
- Maintenance: the existing benchmarks and shadow-verification tests run
  unchanged. A typed program's `maintenanceStats` match its untyped
  equivalent.
- Allocation-failure scenarios for `declareSchema` and the checker.
- Per ADR 0002: add the new modules to the `root.zig` test block and check the
  reported test count.

## Out of Scope

- Dropping, replacing or loosening a schema.
- Union types, user-defined named types, a strict `float`, string or other
  new scalar kinds.
- Inferring types for untyped predicates.
- Runtime checks on derived facts.
- Using column names in error messages or diagnostics, or exposing them in
  answers.
- Schemas on views or view-specific typing in folding, beyond checking fold
  inputs.

## Further Notes

- Glossary: "Schema" (including type tests) in `CONTEXT.md`.
- Decision record: `docs/adr/0004-static-schema-enforcement.md`.

- Implemented 2026-09-24. Deviations from the text above:
  - Goals that read no typed predicate are not checked at all (and neither
    is a rule whose head is untyped as well). Without this, an untyped
    program would change behaviour: `'a' < 1` would become `IllTyped`
    instead of the runtime `NumericType` it has always been.
  - Internally a column type is a `(lists, element)` pair
    (`schema.ColumnType`) rather than a tree, because every type in the
    language is some number of `list(...)` around a base type. It has
    `never` as a bottom element; `list(never)` is the type of `[]`.
  - Arithmetic infers `int` when both operands are `int`, so
    `N = M + 1` can fill an `int` column. Otherwise the result is `number`.
  - The copy a folded plan runs on (`viewOnlyCopy`) drops the schemas. The
    plan was checked when it was folded, and its inverse rules were never
    written by the caller.
  - The claim above that a comparison on an `any` operand "is skipped on
    `NumericType`" is only true for seeded structural rules. Ordinary rules
    and queries raise `NumericType`, as they did before schemas.
  - `schema Age(...)` (an uppercase name) isn't taken as a schema
    declaration; it parses as a clause and fails there.
- The view catalog used "schema" internally for a view's column kinds. It
  is now `view_catalog.ColumnKinds` (field `View.column_kinds`), so "schema"
  means only a predicate schema.
