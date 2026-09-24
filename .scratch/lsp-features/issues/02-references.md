# Find references

Status: done

Answer `textDocument/references` with every reference (CONTEXT.md) to the
predicate/arity at the position across the loaded files, in sorted path order.
When `context.includeDeclaration` is false, leave out exactly the locations
`definitions` returns. Generalize `Heads` into a walk over all names of a
predicate so definitions and references share it. Advertise
`referencesProvider`.

## Acceptance

- References include body goals, queries, retractions, schemas, and goals
  under `not` and inside `setof`, across files.
- Without the declaration, a predicate with rules keeps its fact heads but
  drops its rule heads; one with a schema drops only the schemas.
- Other arities are excluded.
