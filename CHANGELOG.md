# Changelog

All notable changes to this project are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). Until 1.0, minor
versions may change the CLI, the `.lig` syntax, and the generated module API.

## [Unreleased]

First release, planned as 0.1.0. Requires Lean 4.36.0 and Lake 5.0.0
(`lean-toolchain`). Generated modules use Lean's module system, so a project
that imports them must use the same Lean version.

### Added

- `leanparsergenerator`, which turns a `.lig` grammar with Lean semantic actions
  into an executable parser (`<Base>Parser`), a dependent specification module
  (`<Base>Verified`) with the proofs `parser_sound`, `parser_complete`,
  `parser_err_free`, `parser_ne_err`, `parser_unambiguous` and
  `parse_eq_dependent`, and, with a `%lexer` block, a lexer (`<Base>Lexer`).
- `LeanParserGeneratorRuntime`, a library holding only the runtime and lexer
  code that generated parsers import and link against.
- Source spans on tokens, `x_span` binders in actions, and generated error
  messages (`errorMessage`, `diagnose`).
- A command line of the form `leanparsergenerator [options] <input.lig>` with
  `--out-dir`, `--module-prefix`, `--rust-out`, `--only`, `--help` and `--version`.
  Exit code 0 means success, 1 an error, and 2 LR(1) conflicts (output is still
  written). `.lig` syntax errors are reported as `file:line:col`.
- `--print-grammar bnf|markdown` to render the grammar checked by the proofs.
- A language server (`lig-language-server`) and a VS Code extension for `.lig`.
- `%option compress_tables`, which shrinks the emitted executable tables.
- One table of `%option`s (`optionSpecs`) that both `.lig` parsers, the error
  messages, and a test (`lig-option-test`) share. The generated `.lig` parser now
  accepts a dotted `%option module_prefix`, and the hand-written one reports a
  missing `%option gen_rust` value instead of reading the next directive as the path.
- `cli-test`, which checks the exit codes, messages and written files of the CLI.

### Experimental

- Roundtrip proofs (`docs/ROUNDTRIP.md`): `%option roundtrip_lexer`, `roundtrip_parser` and
  `roundtrip_format`. Their output and options may change between releases.
- Rust backend (`%option gen_rust`, `--rust-out`, `--rust-report`). It has no proofs.
