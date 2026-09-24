# ADR 0005: A non-numeric operand in a rule fails the goal instead of raising an error

- Status: accepted
- Date: 2026-09-24

When a rule compares or adds a value that is not a number — `A >= 18` with
`A = old` — the goal fails for that binding and evaluation continues, the same
as any test that doesn't hold. It does not raise `NumericType`. Before this,
ordinary rules raised the error while seeded structural rules and parts of
maintenance skipped the binding. The error surfaced at whatever evaluation came
next, so one bad fact failed every later query, including unrelated ones, and
the lazy path accepted a fact the incremental path rejected.

A query's own goals still raise `NumericType`. There the error points at what
the caller wrote and fails only that query.

## Considered options

- **Raise the error, but when the fact is asserted.** This keeps typos loud.
  Rejected because asserting a fact would then have to evaluate every rule
  that reads it, including on the lazy path, which exists so that asserting
  costs nothing.

## Consequences

- A non-number in a rule's comparison or arithmetic now silently produces no
  answers from that binding. Predicate schemas (ADR 0004) are how to make that
  loud: a typed column proves its operands numeric or rejects the rule.
- Every update path — rebuild, lazy materialization, incremental insertion,
  delete-and-rederive and seeded rules — gives the same result on the same
  input, as the Update path glossary entry requires.
- Evaluation stays monotone: a fact can make a rule derive less only through
  negation, never by breaking it.
