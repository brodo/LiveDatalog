# ADR 0008: The query listener speaks a counted, tab-separated protocol

- Status: accepted
- Date: 2026-09-24

The query listener used to answer in the REPL's format (`X: a, Y: b`,
`Yes.`, `No.`), with each response ended by a blank line. The browser needs to
read answers reliably, and that format could not guarantee it. Values such as
`[a, b]` and quoted atoms contain `, `, so a line cannot be split without a
Datalog parser. A quoted atom could also contain a raw newline, and `.help`
contained a blank line, and either one ended a response early. We made the
listener's only format a machine protocol:

- Every response starts with a status line. `ok table <rows>` is followed by
  a tab-separated header line and exactly that many tab-separated rows.
  `ok text <lines>` is followed by that many lines. `error <Name> <message>`
  is a single line.
- The line counts frame each response, not a blank line. That is how a ground
  query can be a table with no columns, whose header line is empty.
- Every cell holds a value in canonical Datalog syntax. Quoted atoms escape
  newline and tab, so a value never spans lines or cells, and every cell
  parses back to the same value.

The REPL keeps its human format, so the two no longer match.

## Considered options

- **Keep `X: a, Y: b` and document it as a grammar.** This was the least
  change. Rejected because every client would need a Datalog term parser just
  to find where a cell ends, and the blank-line terminator would still collide
  with free text.
- **JSON Lines.** This is the most robust to parse, with typed values.
  Rejected because it makes `nc` sessions hard for a person to read. The
  typing it adds is already in the canonical syntax, because a cell reparses
  to exactly one value.
- **A second, machine-only listener beside the human one.** Rejected because
  it would mean two protocols to keep in step for a single-user development
  tool.

## Consequences

- Scripts written against the old format break. There are no known clients
  besides `nc`.
- Changing what a quoted atom can contain now changes the wire format. The
  new escapes (`\n`, `\t`) are part of the language, not just the protocol.
- A human with `nc` sees status lines and tabs. We accept this as the price
  of a protocol that programs can parse.
