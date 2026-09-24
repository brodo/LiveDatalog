# Signature help

Status: done

Answer `textDocument/signatureHelp` while the cursor is among a relation's
or `setof`'s arguments, found by the same lexical scan completion uses, which
also counts the argument being typed. Lists and quoted atoms inside the
arguments do not end them; a schema statement's own columns get no help.

- A predicate with a schema has one signature, `name(Col: type, ...)`, since
  the schema fixes its arity.
- One without has a signature per arity it is defined with, `name(_, _)`, and
  the first with room for the current argument is active.
- `setof` has `setof(Template, Goal, Result)`.
- Unknown names get none.

Trigger characters are `(` and `,`.
