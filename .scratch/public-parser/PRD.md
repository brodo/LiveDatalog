# Public Parser API

Status: done

## Problem Statement

The parser is private and fused with execution: `Parser.executeAll` parses one
statement, runs it in a transaction, and moves on, interning into the database
as it goes. No parsed program ever exists as a value. An embedder who wants a
rule, a query program for `foldQuery`, or a view definition from text has to
build `input` descriptors by hand, and a program cannot be parsed once and run
later. Parse failures are bare error codes with no source location.

## Solution

Split parsing from running. A pure parser turns text into the existing
borrowed `input` descriptors, needing no database. A program runner executes
`input` statements against a database through transactions, keeping the
assertion-run batching. `Jatalog.execute(source)` becomes parse-then-run. An
optional `Diagnostic` reports where parsing failed, and which statement failed
at run time.

## User Stories

1. As an embedder, I can parse a rule from text and pass it to `addRule`,
   `defineView`, or `foldQuery` without building descriptors by hand.
2. As an embedder, I can parse a query body from text and pass it to `query`,
   `retract`, or `explainQuery`.
3. As an embedder, I can parse a whole program once and run it later, or
   against several databases.
4. As an embedder, I can run hand-built statements with the same batching
   `execute` gets.
5. As an embedder or REPL user, a syntax error tells me the line, column, and
   what was expected.
6. As an embedder or REPL user, a semantic error tells me which statement
   caused it.
7. As an embedder, anything the source language can say — including negated
   built-ins such as `not X < Y` — is representable in `input`.

## Implementation Decisions

### Public interface (`root.zig`)

- `parseProgram(allocator, source, ?*Diagnostic) !Parsed(Program)`, where
  `Program = struct { statements: []const input.Statement, spans: []const Span }`.
- `parseRule(allocator, source, ?*Diagnostic) !Parsed(input.Rule)`.
- `parseGoals(allocator, source, ?*Diagnostic) !Parsed([]const input.Goal)`.
- `Parsed(T) = struct { arena, value: T, deinit() }`, modelled on
  `std.json.Parsed`. The arena owns every slice the borrowed descriptors name.
- `Jatalog.executeStatements(statements, ?*Diagnostic) !ExecutionResult`.
- `Jatalog.execute(source)` gains the optional diagnostic and is implemented as
  `parseProgram` + `executeStatements`.
- Both return the last statement's result, as `execute` does today.
- No `parseTerm` until something needs it.

### `input` additions

- `input.Statement = union(enum) { fact: Relation, rule: Rule, query: []const Goal, retraction: []const Goal }`.
- Negation extends to built-ins so `not X < Y` and `not X = Y` survive a parse
  unchanged. The parser never normalizes (`not X < Y` is not rewritten to
  `X >= Y`). `input_compiler.zig` compiles the new variants.

### Diagnostic

```zig
pub const Diagnostic = struct {
    statement: ?usize,
    span: ?Span,
    line: u32,
    column: u32,
    expected: ?[]const u8,
};
```

- `line` and `column` are 1-based. `column` counts bytes.
- `expected` is a static string (e.g. `"')'"`, `"'.' or ':-'"`) and is set
  only for parse errors. Filling a diagnostic never allocates.
- Semantic errors from `executeStatements` set `statement`. When the program
  came from text, `span`/`line`/`column` come from the program's per-statement
  spans.

### What the parser decides vs. the run

- The parser rejects malformed text and wrong shapes: a fact that is not a
  relation, a rule head that is not a relation, a negated `setof`, unknown
  operators, and numeric literals that overflow their type (`NumericOverflow`,
  with location).
- Everything that needs the program's meaning waits for the run: fact
  groundness, `UnboundVariable`, `NotStratified`, `NotAdmissible`, etc.

### Execution semantics (behaviour change)

- A program is parsed whole before any statement runs. A syntax error anywhere
  means nothing ran. Today the statements before the error are committed.
- Semantic failures keep today's rule: earlier statements stay, the failing
  statement leaves nothing (savepoint rollback within the assertion run).

### Modules (ADR 0002 addendum)

- `parser.zig`: pure text → `input`. Imports only `input`, `errors`, and a
  database-free literal classifier in `scalar.zig`. Sits beside `input.zig`.
- `program.zig` (new): runs `input.Statement`s against a `*Database`, owning
  the assertion-run batching now in `Parser.executeAll`. Sits where
  `parser.zig` sits today.
- `statement.zig` → `transaction.zig`; `statement.Statement` → `Transaction`.
  The public `root.Statement` export is renamed to `Transaction` (breaking).
- `scalar.zig`: split `parseBare`'s classification (integer / float / atom /
  `InvalidSyntax` / `NumericOverflow`) from interning so the parser can use it.

### REPL

- `main.zig` prints the diagnostic with the offending source line and a caret.

## Testing Decisions

- Parser tests live in `parser.zig` and need no database: every construct in
  `docs/language-tutorial.md` parses to the expected descriptors.
- Round-trip property: for existing source-built tests, `execute(source)` and
  `executeStatements(parseProgram(source))` yield identical databases.
- Negated built-ins parse to the new descriptors and evaluate as they do today.
- Diagnostics: position and `expected` for a table of malformed inputs;
  statement index and span for semantic failures; overflow literals located.
- Behaviour change: a program with a syntax error in its last statement leaves
  the database unchanged.
- Allocation-failure scenarios (as `parser.zig` has today) for the parser and
  for `Parsed(T).deinit`.
- Per ADR 0002: check the reported test count, and add `program.zig` /
  `transaction.zig` to the `root.zig` test block.

## Out of Scope

- Formatting `input` back to source.
- Preserving comments or trivia; any lossless/concrete syntax tree for tooling.
- Returning every statement's result from a program run.
- `parseTerm`.
- Moving source-built tests out of `root.zig` (now possible; separate change).

## Further Notes

- Implemented 2026-09-24. Deviations from the text above:
  - Negated built-ins are a new `input.Goal.negated_builtin` variant (with an
    `input.notBuiltin` helper) rather than widening `.negation`, so existing
    `.negation` users are unaffected.
  - `!` binds within a list element, as it did in the old parser: `[a, b!T]`
    is a two-element list whose second element is `b!T`. The old parser's
    improper-list branch was unreachable and was dropped.
  - `program.zig` is imported in `root.zig` as `program_runner`, because
    `program` is a common local name in the tests.

- ADR 0002's addendum records that source-built tests no longer need to live
  in `root.zig`; moving them is left for a separate change.
- `parser.zig` ended up not needing `errors`: it imports only `input` and
  `scalar`.
- Glossary: `CONTEXT.md` **Statement** and **Transaction** entries.
