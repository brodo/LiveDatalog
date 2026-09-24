# A non-numeric value in a rule's comparison fails every query

Status: needs-triage

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
