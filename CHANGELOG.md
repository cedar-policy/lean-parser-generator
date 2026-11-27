# Changelog

All notable changes to this project are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). Until 1.0, minor
versions may change the CLI, the `.lig` syntax, and the generated module API.

## [0.1.0-alpha.1] - 2026-11-27

First alpha release. Requires Lean 4.36.0 and Lake 5.0.0
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
- A check that the `.lig` file name and the module prefix give valid Lean module names.
- Grammar checks in the generator, shared with the language server: errors for a
  duplicate binder, the EOF token inside a production, a lexer rule that matches
  nothing, a reversed character range and an unknown escape; warnings for a lexer
  rule that matches the empty string and for one that can never win. Messages carry
  `file:line:col`.
- `%option compress_tables`, which shrinks the emitted executable tables.

### Experimental

- Roundtrip proofs (`docs/ROUNDTRIP.md`): `%option roundtrip_lexer`, `roundtrip_parser` and
  `roundtrip_format`. Their output and options may change between releases.
- Rust backend (`%option gen_rust`, `--rust-out`, `--rust-report`). It has no proofs.
- A language server (`lig-language-server`) and a VS Code extension for `.lig` files.
