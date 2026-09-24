# Variables

Status: done

A parsed `Program` records every variable occurrence (name, span,
statement, innermost `setof`) and every `setof` with its parent. A schema's
column names are not variables. The listener derives each occurrence's scope
as CONTEXT.md's "Variable scope" defines it: the outermost level, out from
where it is written, that writes the name itself.

- Document highlight (`Text`) and find references on a variable: its
  occurrences in its scope, in the current document.
- Rename: within the scope, in the current document only, as a versioned
  edit; the draft must parse; the new name must be `[A-Z][A-Za-z0-9_]*` and
  not already occur anywhere in the statement (which would merge variables or
  capture a `setof`-local one).
- Completion: the variable names in the current statement's text, lexically,
  where the typed word is empty or uppercase, outside comments, quoted atoms
  and schemas — relation arguments included, after the predicates in goals.

Not done: go to definition and hover for variables; singleton warnings (see
`.scratch/anonymous-variables`).
