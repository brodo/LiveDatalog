# Folded answers should list the caller's variable names

Status: done

## Problem

`Jatalog.answerFolded` lists each answer under the plan's variable names as the
fold IR spells them (`X#3`, `Y#4`), not the names the caller wrote. So
`answer.getValue("X")` on a folded answer returns `UnknownVariable`.

The plan cache makes it worse. Its key normalizes variables by first
occurrence, so a cached plan keeps the spelling of whichever query folded it
first. If `q(X, Y)` is folded first, a later `q(A, B)` gets answers named `X#3`
and `Y#4`.

Found while adding answer order (ADR 0003). `answerFolded` could not take sort
keys, because a key could not name the answers' variables, so it currently
lists folded answers in the default order only.

## Proposed direction

The `Fold` handle records the caller's answer variables in first-mention order.
The handle belongs to one call, even when the plan it points at is shared.
`answerFolded` renames the answer bindings to those names by position. The
cost: `Fold` becomes an owning handle with a `deinit`, which is a breaking API
change.

Once this lands, add an `order: []const input.SortKey` parameter to
`answerFolded` and pass it to `transaction.queryClauses`, just as
`Jatalog.query` does.

## Acceptance

- `getValue("X")` works on a folded answer to a query that wrote `X`.
- A reused plan lists the reusing caller's names.
- `answerFolded(fold, &.{input.descending("X")})` orders by the caller's `X`.

## Comments

Done. `Fold` owns the caller's answer-variable names and has a `deinit`. Each
cached plan records where the query's answer variables ended up in the plan.
`answerFolded(fold, order)` projects the plan's answers onto those variables,
renames them to the caller's names, lists each projected answer once, and
sorts them by the caller's keys.
