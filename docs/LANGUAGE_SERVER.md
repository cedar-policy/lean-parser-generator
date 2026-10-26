# `.lig` Language Server

`lig-language-server` is a small [Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
server that provides live diagnostics for `.lig` grammar files. It reuses the
untrusted frontend parser and the Pager construction, so the problems it reports
are exactly the ones the code generator itself would reject.

## Building

```sh
lake build lig-language-server
```

The executable is produced at `.lake/build/bin/lig-language-server`. It speaks
LSP over **stdio** (standard `Content-Length`-framed JSON-RPC).

## What it checks

The analysis lives in `LeanParserGenerator/Frontend/Diagnostics.lean`
(`Frontend.collectDiagnostics : String → Array LigDiagnostic`) and is a pure
function of the document text. It reports:

| Severity | Diagnostic |
|---|---|
| error | scanner / parser errors (placed at the `at byte N` offset) |
| error | a symbol in a production that is neither a declared token nor a nonterminal |
| error | the start symbol is not a rule head |
| error | the `%eof` token used inside a production |
| warning | a `%token` declared more than once |
| warning | a nonterminal given two different result types |
| warning | LR(1) (Pager) conflicts in the constructed automaton |
| information | a nonterminal that is defined but never used |

Each diagnostic carries a precise source range: byte offsets from the `Surface`
spans the frontend already threads through, converted to LSP line/character
positions (UTF-16 code units) by `Frontend.byteToLineCol`.

## Protocol support

Document synchronization is **full** (`TextDocumentSyncKind.Full`).

| Message | Behavior |
|---|---|
| `initialize` | advertises full text sync + open/close, returns `serverInfo` |
| `initialized` | ignored |
| `textDocument/didOpen` | stores the document and publishes diagnostics |
| `textDocument/didChange` | updates the document and re-publishes diagnostics |
| `textDocument/didClose` | drops the document and clears its diagnostics |
| `shutdown` / `exit` | orderly shutdown (exit code 0 after a `shutdown`) |
| any other request | replies `methodNotFound` so clients never hang |

## Editor configuration (example)

Any LSP client can launch the server. For a Neovim client you might register a
server whose command is the built binary and whose `filetypes` include `lig`.
For VS Code, point a generic LSP extension's server command at the binary and
associate the `.lig` extension with a `lig` language id.

## Tests

- `lake build LspDiagnosticsTest` — compiles `test/lsp/DiagnosticsTest.lean`,
  whose `#guard`s exercise the engine (position conversion, offset extraction,
  and every diagnostic category).
- `python3 test/lsp_driver.py` — an end-to-end stdio session that runs
  `initialize`, `didOpen` (bad grammar), `didChange` (fixed grammar),
  `shutdown`, and `exit`, printing the framed responses and published
  diagnostics.
