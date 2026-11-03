# Cedar schemas

`CedarSchema.lig` is the grammar of the Cedar schema language. It mirrors
`cedar-policy-core`'s `validator/cedar_schema/grammar.lalrpop` (see `test/README.md`), except
that it has no `external` declarations (below). The Lean outputs are `CedarSchemaLexer.lean`,
`CedarSchemaParser.lean`, `CedarSchemaVerified.lean` and the roundtrip modules.

## Rust

`%option gen_rust rust/src/generated.rs` makes the generator write a Rust lexer and parser,
and the `!!rust{…}` actions build the CST of `rust/src/cst.rs` (it follows
`CedarSchemaAst.lean`). `rust/` is a Cargo crate:

    cd test/cedarschema/rust && cargo build --release
    ./target/release/check schema.cedarschema     # ok, lex, parse, or check <error>

`cedar-policy-core` rejects some inputs in the actions of its grammar (`=>?`), and the Lean
CST does not show them. The Rust actions do the same checks, with `%option rust_ctx
crate::cst::Checks`: a Rust action cannot fail, so it records the first error in the context
and `parse` returns it as `Error::Check`:

- reserved identifiers (`true false if then else in is like has`);
- repeated annotation keys on a declaration, a namespace or an attribute;
- string literals with a bad escape sequence. This uses `rustc-literal-escaper`, the unescaper
  core uses, and the CST holds the unescaped string.

The Lean side does none of these (its CST keeps raw strings), and the Lean outputs do not
change with the Rust actions.

## Comparison with cedar-policy-core

`test/cedar/compare` parses the same files with this parser and with `cedar-policy-core`
4.14.0 and prints the time per file (how to run it, and the policy results, are in
`test/cedar/README.md`). Both sides go from text to a concrete syntax tree and drop it:
`lex + parse_values` of `CedarSchema.lig` against
`cedar_policy_core::validator::cedar_schema::parser::parse_schema`. Neither does the next step
(CST to the JSON schema).

Corpus A: the 14 `.cedarschema` files of `cedar-examples` (13 KB). Corpus B: every
`.cedarschema` under `cedar-examples`, `cedar-spec` and `cedar-integration-tests` on the
development machine (7928 files, 5.0 MB). Per file, release build with LTO:

| | core | generated `lex + parse_values` + checks | lex only |
|---|---|---|---|
| A | 342 µs | 9.3 µs (37x) | 1.6 µs |
| B | 284 µs | 9.7 µs (29x) | 1.8 µs |

The ratios are not LALR(1) tables against LALRPOP:

- core's CST carries a `Loc` on every node, copies the source into an `Arc` on each call and
  recovers from errors; the generated parser does none of these.
- core's schema grammar reparses every identifier: `Ident` calls `Id::from_str`, which runs
  the policy parser (`parse_ident`), and `IDENTIFIER` goes through `AnyId::from_str`. One
  `parse_ident("principal")` takes 4.4 µs on this machine and corpus A averages 67
  identifier-like words per schema, which accounts for most of the 342 µs. I did not profile
  it. That is a cost of core's implementation, not of LALRPOP.
- the CSTs are different types: ours has owned `String`s and `VecDeque` lists, core uses
  `SmolStr`.

Acceptance check (accept or reject, not the trees): all 7928 files of corpus B are accepted
by both. After mutating files (a character deleted, a span deleted, a token inserted,
truncation), 3998 mutated schemas agree in every case (1141 accepted and 2857 rejected by
both).

Not replicated: the `external entity` and `external action` declarations of core's grammar
(4.14.0). `CedarSchema.lig` has no `external` keyword, so core accepts `external entity E;`
and the generated parser rejects it. Adding it changes the Lean AST and the Lean outputs.
