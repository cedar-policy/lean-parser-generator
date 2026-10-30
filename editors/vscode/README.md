# LIG Grammar — VS Code extension

A VS Code extension for `.lig` grammar files: TextMate syntax highlighting plus
a client that runs the `lig-language-server` executable and shows its
diagnostics inline (squiggles + Problems panel).

## Syntax highlighting

`syntaxes/lig.tmLanguage.json` (scope `source.lig`) colors:

- directives `%header`, `%tokentype`, `%token`, `%eof`, `%start` and the `%%`
  separator;
- `%option` and its known names — the flags `compress_tables` and `roundtrip_lexer`, and
  the value-carrying `module_prefix <path>`, `roundtrip_parser <function>`,
  `roundtrip_format <function>`, `gen_rust <file>`, `rust_ctx <type>` and `rust_list <path>`; an unrecognized option name is
  colored as invalid (the server also reports it as an error);
- terminals (UPPERCASE names) vs nonterminals (lowercase names) in rule bodies;
- carried token types `<T>` and rule head types after `::`;
- `x=SYMBOL` value bindings and the `|` alternative separator;
- embedded Lean inside `%header { … }` and `{ … }` semantic actions, and embedded Rust
  inside `!!rust{ … }` (the Rust counterpart of an action, or the Rust type after a rule's
  Lean type);
- `--` line and `/- … -/` block comments.

Highlighting needs no build step — it works as soon as the extension is loaded.
The diagnostics feature below additionally needs the server binary.

## Prerequisites

1. Build the server once from the repository root:

   ```sh
   lake build lig-language-server
   ```

   This produces `.lake/build/bin/lig-language-server`.

2. Install the extension's one dependency:

   ```sh
   cd editors/vscode
   npm install
   ```

   > On an Amazon dev host, npm points at CodeArtifact. If `npm install` fails
   > with `E401`, authenticate first (e.g. `ada credentials update` / the
   > `aws codeartifact login --tool npm ...` your team uses), or temporarily use
   > the public registry:
   > `npm install --registry=https://registry.npmjs.org`.

## Run it (development / local use)

The simplest way to use it without packaging:

1. Open the `editors/vscode` folder in VS Code.
2. Press `F5` ("Run Extension"). A second VS Code window ("Extension
   Development Host") opens with the extension loaded.
3. In that window, open the repository and any `.lig` file
   (e.g. `test/calc/calc.lig`). Diagnostics appear as you type.

## Install it permanently

The convenience script builds the server, packages the extension, and installs it:

```sh
editors/vscode/build-and-install.sh
```

It takes `--no-server` (skip the `lake build`) and `--package-only` (build and
package but do not install). It needs the `code` CLI on PATH for the install step;
without it the script prints the `.vsix` path to install by hand.

Or do the steps directly — package into a `.vsix` and install:

```sh
cd editors/vscode
npx @vscode/vsce package        # produces lig-language-server-0.1.0.vsix
code --install-extension lig-language-server-0.1.0.vsix
```

## Settings

- `lig.serverPath` — absolute path to the `lig-language-server` binary. Leave
  empty to use `<workspaceFolder>/.lake/build/bin/lig-language-server`.
- `lig.trace.server` — `off` | `messages` | `verbose`, to log LSP traffic in the
  "LIG Language Server" output channel.

## How it works

`extension.js` starts the binary over **stdio** with `Content-Length` framing
(`TransportKind.stdio`) and registers it for the `lig` language. The
`vscode-languageclient` library drives the LSP handshake
(`initialize` → `didOpen`/`didChange` → `publishDiagnostics` → `shutdown`);
the server side is implemented in `LeanParserGenerator/LSP/Server.lean`. See
`docs/LANGUAGE_SERVER.md` in the repository for the full protocol and diagnostic
list.
