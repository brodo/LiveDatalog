# Workspace symbols

Status: done

Answer `workspace/symbol`: one `SymbolInformation` per predicate/arity that has
a definition in the loaded files, named `name/arity`, located at its first
definition in sorted path order. Kind `Interface` for a schema definition,
`Function` for rules, `Constant` for facts. Keep those whose name matches the
query as a case-insensitive subsequence; an empty query matches all.
Advertise `workspaceSymbolProvider`.

## Acceptance

- A predicate defined by a thousand facts is one symbol.
- `edge/2` and `edge/3` are two symbols.
- Query `ED` matches `edge/2`; query `xz` does not.
