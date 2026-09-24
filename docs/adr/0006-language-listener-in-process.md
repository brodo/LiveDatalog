# ADR 0006: The language listener runs inside the development server

- Status: accepted
- Date: 2026-09-24

The development server gained a Language Server Protocol endpoint for editors.
It was first asked for as its own process on its own port. We kept the own
port but run it as a task inside `LiveDatalogServer`, beside the query
listener, on the same `Io.Threaded`. It reads the database through the
engine's queue like every other client, so the engine still owns the database
alone.

## Considered options

- **A separate binary.** Isolates an LSP crash from the query listener.
  Rejected: everything the LSP reports — load errors, a predicate's facts,
  rules and schema, where each is defined — lives in the engine. A second
  process would either load the directory again, keeping a second database
  that can disagree with the first, or query the engine over some new IPC
  protocol that would carry exactly what the queue already carries.
- **A child process spawned by the server.** Has the IPC cost of a separate
  binary, and adds lifecycle coupling on top.

## Consequences

- A fault in the language listener can take down the query listener. Both
  are development tools for one person's directory, so we accept that.
- LSP requests queue behind reloads and queries on the one engine task. A slow
  reload delays a hover.
- The language listener never changes the database: an editor's unsaved text
  is a draft, not a contributor, so what one editor types cannot change what
  another client sees.
- Only TCP is offered. An editor that can only launch a command over stdio
  needs a bridge such as `nc`.
