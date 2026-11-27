# Roundtrip proofs (experimental)

These options generate extra modules for printer inverses. They are experimental and are not needed to use the parser.

- `%option roundtrip_lexer` generates `<Base>LexerRoundtrip.lean`. A handwritten `<Base>LexerRoundtripSupport.lean` supplies `renderTok : Tok → String`. The generated `render_roundtrip` theorem is universal over arbitrary lists whose elements satisfy the decidable `RoundtrippableTok` predicate. The predicate checks that the rendered lexeme wins maximal munch, emits the same token, and is separated by a skipped space. The current generator accepts only single-mode lexers whose actions all stay in that mode. See [`LEXER.md`](LEXER.md).
- `%option roundtrip_parser <unparse>` generates source-order token/production tree helpers in `<Base>Verified.lean` and a generic `Certificate`/`parse_certificate` theorem in `<Base>ParserRoundtrip.lean`. The user writes `<Base>Unparse.lean` and a separate proof that builds certificates for the intended printable domain. After a grammar change, regenerate first, then update that proof if production helpers changed.
- `%option roundtrip_format <renderTok>` adds the corpus-independent `format`, `relex`, and `fullRoundtrip` definitions to the parser roundtrip module. A handwritten theorem can combine the universal lexer result with a parser inverse theorem.

The generated modules contain no sample corpus, coverage summary, `guarantees` string, or `#eval` output.
