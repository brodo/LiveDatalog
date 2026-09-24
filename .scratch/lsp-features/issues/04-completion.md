# Completion of predicate names

Status: done

Answer `textDocument/completion` where a goal can start, as the PRD's lexical
scan decides, with every predicate/arity defined in the loaded files and the
keywords `not` and `setof`. A predicate item is labelled `name/arity`, filters
on `name`, and inserts the snippet `name(${1:Col}, …)` with its schema's column
names or `$1…$n`; after `schema` it inserts the bare name. Elsewhere return an
empty list. Advertise `completionProvider`.

## Acceptance

- Offered at statement start, after `:-`, after `,` between goals, after
  `not`, in a bare `(`, and in `setof`'s second argument.
- Not offered inside a relation's arguments, `setof`'s template or result, a
  comment, or a quoted atom.
- `schema age(Person: atom, Years: int).` makes `age` insert
  `age(${1:Person}, ${2:Years})`.
