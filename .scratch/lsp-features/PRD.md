# More language listener features

Status: done

## Problem Statement

The language listener offers diagnostics, hover and go to definition. Zed
can do much more with a language server: highlight a name's occurrences, list
its references, jump to any predicate by name, and complete names. Without
those, navigating a directory of `.dl` files means grepping.

## Solution

Four read-only LSP features, each built on what the listener already has: the
parsed drafts, the loaded files' parsed programs, and `Engine.Call` to read
them on the engine task. None of them changes the database or any file.

## User Stories

1. With the cursor on a predicate, the other places this draft names it are
   highlighted, and definitions look different from uses.
2. I can list every reference to a predicate across the directory, with or
   without its definitions.
3. I can open the project symbol picker, type part of a predicate's name, and
   jump to where it is defined.
4. Typing a goal offers the predicates the directory defines, inserting a
   snippet with a placeholder per column.

## Implementation Decisions

Vocabulary: see "Draft", "Definition" and "Reference" in CONTEXT.md.

- A predicate is its name and arity throughout.
- **Cross-file answers read the loaded files only**, never drafts, as hover and
  definition already do. Features about the current document (document
  highlight, and deciding where completion applies) read the draft's last good
  parse or its text.
- **Document highlight**: occurrences in the current draft of the predicate at
  the cursor. The head of a fact, rule or schema is `Write`; every other name
  (body, query, retraction goals) is `Read`.
- **References**: every reference in the loaded files. With
  `includeDeclaration: false`, drop exactly the locations go to definition
  returns.
- **Workspace symbols**: one symbol per predicate/arity with a definition,
  named `name/arity`, at its first definition in sorted path order. Kind:
  `Interface` if defined by a schema, `Function` by rules, `Constant` by facts.
  Filtered by case-insensitive subsequence match on the query.
- **Completion**: candidates are each defined predicate/arity plus the
  keywords `not` and `setof`. A predicate inserts a snippet
  `name(${1:Col}, …)` using its schema's column names where it has them and
  `$1…$n` otherwise. Completion applies only where a goal can start, decided
  by a lexical scan of the draft text back to the statement's start that skips
  comments and quoted atoms and keeps a stack of open parentheses:
  - inside a relation's arguments: no;
  - inside `setof(`: only in its second argument;
  - inside a bare `(` (a parenthesized conjunction): yes;
  - at statement start, after `:-`, after a `,` between goals, after `not`: yes;
  - after `schema`: predicate names without snippets.
  Elsewhere the result is an empty list.
- Each feature advertises its capability in `initialize`.

## Testing Decisions

Each feature is tested in `src/server/LanguageSession.zig` with the same
fixture as hover and definition: files in a temporary directory, a session
over an engine, drafts opened through `didOpen`.

## Out of Scope

Rename, inlay hints, document symbols (the Zed outline comes from
tree-sitter), formatting, references from drafts, variable names.
