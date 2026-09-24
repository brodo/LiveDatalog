# ADR 0007: Rename reads the working text, not the loaded files

- Status: accepted
- Date: 2026-09-24

Every other language-listener feature that looks across files reads the
files as the engine loaded them, so what it says matches the database. Rename
does not. It reads each file's working text — the editor's draft if the file
is open, else the file on disk now — and parses it in the listener, without
the database.

A rename answers with text edits at positions, and the editor applies each
one to the buffer it holds for an open file or to the file on disk. Positions
from the loaded files are wrong for any file edited since it last loaded, and
a file that failed to load is not in the loaded files at all, so its
occurrences would be missed. Only the working text lines up with what the
edits are applied to.

## Considered options

- **The loaded files, like references.** Consistent with every other
  cross-file answer. Rejected: it edits at stale positions and silently skips
  broken files, which are exactly the files one is most likely to be fixing.

## Consequences

- Rename and find references can disagree about the same predicate while a
  file is unsaved or does not load.
- The listener reads the directory's files itself, on the connection task.
