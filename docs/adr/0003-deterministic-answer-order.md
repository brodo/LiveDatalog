# ADR 0003: Answers are always deterministically ordered

- Status: accepted
- Date: 2026-09-24

A query's answers used to come back in whatever order evaluation produced
them. That order depended on the join order the planner chose and on the order
facts were inserted, so the same question over the same facts could list its
answers differently after a planner change or a reload. When we added
requested orderings (`order by`), we chose to sort *every* query's answers: by
the canonical total order over the answer tuple, variables in first-mention
order, when no ordering is requested, and as the tie-break under one that is.
The only other option was leaving the default order unspecified.

## Considered options

- **Unspecified default order.** No sort unless one is requested, so an
  unsorted query costs nothing extra. Rejected: results would stay
  irreproducible, tests would keep depending on the planner, and a requested
  ordering would still need a tie-break to be deterministic, which would need
  exactly this default anyway.

## Consequences

- Every query pays an O(n log n) sort over its answers, including queries that
  never cared about order. That cost is presentation, not evaluation: it is
  not counted in `evaluationWork` and does not affect the maintenance cost
  model.
- Callers and tests will come to depend on the order. Going back to
  unspecified order later would be a breaking change, even though it would
  never change which answers a query returns.
- Ordering stays outside the query's meaning. The planner, folding, the plan
  cache and maintenance never see it, and `answerFolded` sorts a plan's
  answers in the default order the same way `query` does. `answerFolded`
  doesn't take a requested order yet, because folded answers list the plan's
  variable names (`X#3`) instead of the caller's
  (`.scratch/folded-answer-names/`).
