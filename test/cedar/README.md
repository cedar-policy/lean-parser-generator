# Cedar policies

`cedar.lig` is the grammar of Cedar policies. It mirrors `cedar-policy-core`'s
`parser/grammar.lalrpop` (see `test/README.md`). The Lean outputs are `CedarLexer.lean`,
`CedarParser.lean`, `CedarVerified.lean` and the roundtrip modules; `CedarBench.lean` is the
Lean throughput benchmark.

## Rust

`%option gen_rust rust/src/generated.rs` makes the generator write a Rust lexer and parser, and
the `!!rust{…}` actions build the CST of `rust/src/cst.rs`. `rust/` is a Cargo crate
(docs/RUST_PARSER.md describes the backend, docs/USING_RUST_GENERATOR.md how to use it):

    cd test/cedar/rust && cargo build --release
    ./target/release/check policy.cedar            # ok, lex, or parse <token> <state> <lookahead>
    ./target/release/cedar-rust-parser a.cedar     # benchmark over files

`%option gen_rust_verif rust_bridge` also writes `rust_bridge/`, the Lean package that proves
the Rust lexer and parser equal to the Lean ones (docs/RUST_VERIFICATION.md).

## Comparison with cedar-policy-core

`compare/` is a crate that parses the same files with this parser and with
`cedar-policy-core` 4.14.0 (from crates.io) and prints the time per file. It also parses
schemas, with `test/cedarschema/rust` (see `test/cedarschema/README.md` for those results).

    cd test/cedar/compare && cargo build --release
    ./target/release/cedar-parser-compare --policies-from policies.txt --schemas-from schemas.txt

The `*-from` files list one path per line (`--policies a.cedar b.cedar` also works).
`BENCH_ITERS` sets the number of passes (default 500). A file is timed only if both parsers
accept it; the others are listed.

Both sides go from text to a concrete syntax tree and drop it: `lex + parse_values` of
`cedar.lig` against `cedar_policy_core::parser::text_to_cst::parse_policies`. Neither does the
next step (CST to AST).

Corpus A: the 20 `.cedar` files of `cedar-examples` (36 KB). Corpus B: every `.cedar` under
`cedar-examples`, `cedar-spec` and `cedar-integration-tests` on the development machine (8046
files, 1.4 MB, mostly small generated files). Per file, release build with LTO:

| | core | generated `lex + parse_values` | lex only | trace parse only |
|---|---|---|---|---|
| A | 124 µs | 28.5 µs (4.4x) | 2.7 µs | 12.1 µs |
| B | 37.4 µs | 4.5 µs (8.3x) | 0.5 µs | 2.1 µs |

The ratios are not LALR(1) tables against LALRPOP. What the two sides do differs:

- core's CST carries a `Loc` (a range and an `Arc<str>` of the source) on every node, and
  `parse_collect_errors` copies the source into an `Arc` on each call and recovers from
  errors to report several. The generated parser has no locations in this CST, stops at the
  first error, and does not copy the source.
- the CSTs are different types. Ours follows `CedarAst.lean` (`rust/src/cst.rs`): owned
  `String`s and `VecDeque` lists. Core uses `SmolStr`.
- core's `text_to_cst` accepts missing nodes (`Node<Option<..>>`) that `cst_to_ast` rejects
  later, for example `when { }`; the generated parser requires the expression.

Acceptance check (it compares accept or reject, not the trees): all 8046 files of corpus B are
accepted by both. After mutating files (a character deleted, a span deleted, a token
inserted, truncation), 3998 mutated policies agree except for 12 that core accepts and the
generated parser rejects, all of the empty-condition kind above.
