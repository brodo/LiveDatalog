# A non-numeric value in a rule's comparison fails every query

Status: ready-for-agent

## Problem

When an ordinary (non-seeded) rule compares or adds a value that isn't a
number, deriving that rule raises `NumericType`, and the whole evaluation
fails with it. Because a query materializes every stratum first, one such
fact breaks *every* query, including queries about unrelated predicates:

```datalog
other(x).
age(alice, 36).
adult(P) :- age(P, A), A >= 18.
age(bob, old).
other(X)?          % Error: NumericType
```

The fact itself is accepted: `age(bob, old).` succeeds, because asserting a
fact dirties the closure and evaluates nothing. The failure only shows up at
the next evaluation, and it keeps showing up until the fact is retracted.

The same situation is handled differently depending on the path it takes:

| Path | Behaviour |
| --- | --- |
| Seeded structural rule (`evaluator.zig`, `applyRule`, seed loop) | skips the candidate: `len([1, a], N)?` answers `No.` |
| Ordinary rule, rebuild or lazy materialization | fails the evaluation with `NumericType` |
| `applyChanges` against a clean closure | rejects the batch with `NumericType` |
| `maintenance.zig` (around lines 414 and 494), `materialization.zig` (around lines 182 and 209) | catch `NumericType`/`NumericOverflow` and skip or return early |

So whether a non-number in a comparison is an error or means "no match"
depends on the rule's shape and the update path, and the lazy path accepts a
fact the incremental path rejects. The Update path glossary entry says every
path yields the database a clean rebuild would.

Found while implementing predicate schemas: the PRD claimed that comparisons
on `any` operands keep the runtime behaviour where "the candidate is skipped
on `NumericType`", which is only true for seeded rules. Schemas catch this
case statically for typed predicates. This issue is about untyped programs,
which schemas deliberately leave unchanged.

## Decision needed

Pick one meaning and apply it on every path:

- **(a) Skip.** A comparison or arithmetic goal on a non-number fails for that
  binding, like any other test that doesn't hold, and evaluation continues.
  This matches seeded rules, is monotone, and can't poison the database. The
  cost: typos become silently missing answers, which is what schemas are for.
- **(b) Error.** Keep `NumericType`, but raise it when the offending fact is
  asserted rather than at some later, unrelated query. The cost: asserting a
  fact then has to evaluate the rules that read it, even on the lazy path.

(a) looks like the smaller and more consistent change. Queries could keep
raising `NumericType` for their own goals, since there the error points at
what the caller wrote.

## Acceptance

- The program above answers `other(X)?` (under (a)), or rejects
  `age(bob, old).` when it is asserted (under (b)).
- Rebuild, lazy materialization, incremental insertion, delete-and-rederive and
  seeded rules all agree on the same input, and shadow verification passes.
- The tutorial's "Equality and comparisons" section states the chosen meaning.

## Comments

Decided (2026-09-24): **(a) Skip**, recorded in
`docs/adr/0005-non-numeric-operands-fail-in-rules.md`. In a rule, a comparison
or arithmetic goal on a non-number fails for that binding and evaluation
continues, on every path. A query's own goals keep raising `NumericType`.
Acceptance is the (a) case above.

What is left to do:

- Make a non-numeric operand fail the goal for that binding inside rule
  evaluation (`evaluator.zig`: `evalBuiltin` and its caller in
  `matchClauses`), and keep raising it for a query's own goals. A query
  still materializes through the rules first, so the distinction is whether
  the evaluation derives a rule's head or answers a query's goals.
- The seeded path in `applyRule` catches the error around the whole seed
  value, not the binding, so one bad element skips every derivation from that
  seed. Once the error no longer reaches it, that catch is dead code; remove
  it.
- The catches in `maintenance.zig` (around 414 and 494) and
  `materialization.zig` (around 182 and 209) exist only because the error used
  to reach them. Remove the ones that become dead, and check that every path
  still agrees with a rebuild.
- Tests: the program above, `applyChanges` with the bad fact against a clean
  closure (accepted, and no answer from it), shadow verification on, and a
  query whose own goal compares an atom (still `NumericType`).
- Update the tutorial's "Equality and comparisons" section and the "Update
  path" glossary entry if it needs it.
