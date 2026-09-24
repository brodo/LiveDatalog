# Rename

Status: done

Answer `textDocument/prepareRename` and `textDocument/rename` for
predicates. Rename reads the working text (CONTEXT.md, ADR 0007): each
watched `.dl` file's open draft, else the file on disk, plus open documents
outside the directory, parsed in the listener without the database.

- prepareRename works only on a predicate name in a draft that parses now;
  the placeholder is the name as written.
- Every occurrence of the predicate/arity is renamed; a name with a schema is
  renamed at every arity.
- Refused, with a `window/showMessage` giving the reason, when any working
  text does not parse, the new name at a renamed arity already occurs, the
  new name has a schema, or the new name starts in uppercase.
- The new name is inserted bare when it can be and quoted otherwise; a quoted
  name typed in is unquoted first. The same name changes nothing.
- Edits are versioned document changes: drafts carry their version, files on
  disk none.
