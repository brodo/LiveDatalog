# ADR 0004: Schemas are enforced statically, and `any` must be proven

- Status: accepted
- Date: 2026-09-24

A predicate may declare a schema, and a declared schema is enforced. We
enforce it in two places. Base facts are checked when they are asserted. Rules
are checked when they are added, by inferring the types their variables take.
Derived facts are never checked at runtime. A value from an untyped predicate
has type `any`, and a rule that sends it into a narrower column is rejected
unless the rule proves the type. It proves it either through a typed goal or
through a type test (`X : int`), which filters. An untyped predicate stays
`any` even when every rule defining it happens to produce, say, integers.

## Considered options

- **Check each derived tuple at runtime.** This would accept every rule. The
  cost is a check on every derivation, and a violation would fail an update
  midway through maintenance, a failure that depends on the data rather than
  on the program.
- **Silently drop derived tuples that don't fit.** This would accept every rule
  with no failures. Rejected because the schema would change what a rule
  means, and nothing in the rule text would show it.
- **Infer types for untyped predicates.** This would need fewer annotations.
  Rejected because it is unsound: a later untyped fact can break the inferred
  type, unless the inferred type is quietly enforced as a schema nobody
  declared.

## Consequences

- Maintenance, rebuilds and the cost model are unaffected by schemas, because
  nothing about derivation changes.
- Adding a schema to one predicate can require type tests or further schemas
  in the rules that feed it. We accept this, and the type test is the local
  fix.
- A goal the schema proves impossible is an error in rules, queries and
  retractions, not an empty answer.
- Dropping or loosening a schema can only admit more programs, so it can be
  added later without breaking anything. Tightening an existing schema is not
  offered.
