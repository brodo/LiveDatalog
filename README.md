# LiveDatalog

LiveDatalog is a Zig 0.16 port of [Jatalog](https://github.com/wernsey/Jatalog). It provides an embeddable Datalog engine and a small command-line interpreter.

Implemented language features include recursive rules, stratified negation, `=`, `!=`, `<>`, `<`, `<=`, `>`, and `>=` built-ins, quoted values, multi-clause queries, `%`/`//`/`/* */` comments, and `~` fact retraction.

All predicates, terms, variables, and values are interned. `StringTable.strings` is a `std.StringArrayHashMapUnmanaged(u64)` whose value is the key's insertion index; that index is the ID and also provides the reverse ID-to-string lookup through the map's ordered keys.

## Use

Run a Datalog file:

```sh
zig build run -- program.dl
```

Or pipe a program through standard input:

```sh
printf 'parent(alice, bob). parent(alice, X)?' | zig build run
```

As a library, initialize `Jatalog`, add facts or build expressions with `expr`/`not`, and call `query` or `execute`. Returned expressions and query results have explicit deinitializers.

## Development

```sh
zig build test
zig build fmt
zig build test-fmt
zig build lint
```

The test step runs unit tests, formatting verification, and Ziglint.
