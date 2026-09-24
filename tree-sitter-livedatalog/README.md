# tree-sitter-livedatalog

A [tree-sitter](https://tree-sitter.github.io/) grammar for LiveDatalog source
files (`.dl`), for syntax highlighting, folding and navigation in editors.

The engine's own parser, `src/parser.zig`, is the reference. This grammar
accepts the same statements: facts, rules, queries with `order by`,
retractions, schemas, negation, comparisons, arithmetic, type tests, lists,
`H!T`, `cons` and nested `setof`. Keywords are contextual, as in the engine,
so `schema(x).`, `order(a).` and `p(cons)` still use `schema`, `order` and
`cons` as atoms.

The grammar checks only syntax. The engine reports groundness, rule safety,
stratification, typing and numeric range when a statement runs, so a file can
parse here and still fail to load.

## Layout

| Path | Contents |
| --- | --- |
| `grammar.js` | The grammar |
| `src/` | The generated C parser. Commit it again after every change to `grammar.js` |
| `queries/highlights.scm` | Highlighting captures |
| `queries/locals.scm` | Variable scopes. Each statement is one scope |
| `queries/folds.scm` | Foldable regions |
| `test/corpus/` | Parse tree tests |
| `test/highlight/` | Highlighting tests |

## Development

You need Node.js and a C compiler:

```sh
cd tree-sitter-livedatalog
npm install
npx tree-sitter generate   # regenerate src/ after editing grammar.js
npm test                   # corpus and highlight tests, then parse examples/
```

Inspect how a file parses with `npx tree-sitter parse ../examples/aggregation.dl`.

## Known differences from the engine

- The engine reads a bare word that starts with a sign and a letter, such as
  `-foo`, as an atom. This grammar reports it as a syntax error.
- The engine lets a `+` or `-` after an `e` continue a bare word, so it reads
  `Xe-1` as one variable. This grammar reads it as `Xe`, `-` and `1`.
- The engine ignores everything after a block comment that never closes. This
  grammar reports that comment as an error.
