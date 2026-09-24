# LiveDatalog for Zed

A [Zed](https://zed.dev) extension for LiveDatalog source files (`.dl`). It
brings two parts of this repository into the editor:

- the [tree-sitter grammar](../tree-sitter-livedatalog), for highlighting,
  bracket matching, the outline, indentation, comment toggling and Vim text
  objects;
- the development server's [language listener](../README.md#language-listener),
  for diagnostics, hover, go to definition, find references, document
  highlights, project symbols and completion.

## Install

The extension is not published to the Zed extension registry. Install it as a
dev extension:

1. Install Rust with [rustup](https://rustup.rs). Zed adds the
   `wasm32-wasip2` target and downloads the wasi-sdk that compiles the grammar
   on its own.
2. In Zed, open the extensions page and click **Install Dev Extension**, or run
   `zed: install dev extension`, and pick this `zed-livedatalog` directory.

Zed builds the extension, fetches the grammar from GitHub at the commit
pinned in `extension.toml`, and opens `.dl` files as LiveDatalog.

## Connect to the language listener

The language listener runs inside `LiveDatalogServer` and speaks the Language
Server Protocol over TCP. Zed launches language servers over stdio, so the
extension does not start the server. It runs `nc 127.0.0.1 7071`, or `ncat`
if there is no `nc`, to bridge Zed to a server that is already running.

Start the server on the directory you open in Zed:

```sh
zig build run-server -- examples/researchers
```

Then open a `.dl` file. If the server is not running, the bridge exits at
once, and Zed shows the language server as failed. Once the server is up, run
`editor: restart language server`. Run it again after restarting the server,
because the connection closes when the server stops.

### Settings

To use another host or port, pass it under `lsp.livedatalog.settings` in
Zed's `settings.json`:

```json
{
  "lsp": {
    "livedatalog": {
      "settings": { "host": "127.0.0.1", "port": 7071 }
    }
  }
}
```

To use a bridge other than `nc`, for example `socat` or on Windows, where
there is no `nc`, set the whole command. It then replaces the bridge, host and
port:

```json
{
  "lsp": {
    "livedatalog": {
      "binary": { "path": "socat", "arguments": ["STDIO", "TCP:127.0.0.1:7071"] }
    }
  }
}
```

## Layout

| Path | Contents |
| --- | --- |
| `extension.toml` | The manifest: the grammar to fetch and the language server |
| `src/lib.rs` | Builds the command Zed runs for the language server |
| `languages/livedatalog/config.toml` | File suffix, comments and auto-closed brackets |
| `languages/livedatalog/*.scm` | Tree-sitter queries in Zed's capture names |

## Development

```sh
cd zed-livedatalog
cargo test                                      # the settings parsing
cargo build --release --target wasm32-wasip2    # what Zed builds
```

The queries are written against the grammar in `tree-sitter-livedatalog`.
`highlights.scm` starts as a copy of the grammar's own. Check that every query
still compiles against the grammar:

```sh
cd tree-sitter-livedatalog
for query in ../zed-livedatalog/languages/livedatalog/*.scm; do
  npx tree-sitter query --quiet "$query" ../examples/*.dl
done
```

Zed fetches the grammar from GitHub, not from your checkout. After you change
`grammar.js`, push the change, then set `rev` in `extension.toml` to a commit
that contains it.
