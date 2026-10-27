# Parser regression tests

Each `.lig` fixture generates a verified module and an executable module in one
CLI invocation. Generated modules are committed; do not edit them directly.

| Grammar | Verified | Executable | Lexer (generated) |
|---|---|---|---|
| `calc/calc.lig` | `calc/CalcVerified.lean` | `calc/CalcParser.lean` | `calc/CalcLexer.lean` |
| `imp/imp.lig` | `imp/ImpVerified.lean` | `imp/ImpParser.lean` | — (hand-written) |
| `cedar/cedar.lig` | `cedar/CedarVerified.lean` | `cedar/CedarParser.lean` | `cedar/CedarLexer.lean` |
| `cedarschema/CedarSchema.lig` | `cedarschema/CedarSchemaVerified.lean` | `cedarschema/CedarSchemaParser.lean` | `cedarschema/CedarSchemaLexer.lean` |
| `cedarentities/CedarEntities.lig` | `cedarentities/CedarEntitiesVerified.lean` | `cedarentities/CedarEntitiesParser.lean` | `cedarentities/CedarEntitiesLexer.lean` |
| `c99/c99.lig` | `c99/C99Verified.lean` | `c99/C99Parser.lean` | — (hand-written) |

```sh
lake build parsers         # regenerate parser + lexer modules for stale non-heavy fixtures
lake build heavyParsers    # regenerate the heavy fixtures (c99)
lake build Generated       # compile executable artifacts
lake build VerifiedSmoke   # compile verified smoke tests (calc; default)
lake build VerifiedMid     # compile + CACHE non-heavy verified + roundtrip proofs
lake build VerifiedHeavy   # compile + CACHE the heavy *Verified module (c99)
lake build ParserTests     # calc/imp end-to-end + span/error-message/x_span tests
```

## Roundtrip fixtures

With `%option roundtrip_parser`, the generator writes production-tree helpers to
`*Verified.lean` and the generic certificate theorem to `*ParserRoundtrip.lean`.
Handwritten files define the printable domain and build certificates:

| Fixture | Handwritten domain/printer | Handwritten proof |
|---|---|---|
| calc | `calc/CalcUnparse.lean` | `calc/CalcParserRoundtripProof.lean` |
| IMP | `imp/ImpUnparse.lean` | `imp/ImpParserRoundtripProof.lean` |
| Cedar | `cedar/CedarPrintable.lean` | `cedar/CedarParserRoundtripProof.lean` |

After changing a grammar, run `lake build parsers` first. Then compile the
handwritten proof and update uses of `parseTreeProductionN` if production indices
or RHS shapes changed. Do not edit the generated helpers.

Lake 5.0.0 has no `-j`; bound parallelism with `LAKE_NUM_JOBS` (e.g.
`LAKE_NUM_JOBS=4 lake build VerifiedMid`).

The `parsers` target regenerates a fixture's modules when its grammar, the
generator, or any output is newer/missing. Grammars with a `%lexer` block
(`calc`, `cedar`, `cedarschema`, `cedarentities`) generate a lexer
module too, in the same invocation.

To proof-check the dependent specification (`*Verified`) modules, prefer the
caching `lean_lib`s over `lake env lean test/<g>/<G>Verified.lean`. The six
non-heavy specs are rooted in `VerifiedMid`, and the heavy one (c99) in
`VerifiedHeavy` (reached through the `heavyParsers` regeneration target); both
cache each `native_decide` certificate to `.olean`, so a rebuild after an unrelated
change is a Lake trace no-op (~0.9 s for Cedar) instead of the full re-check the
per-file `lake env lean` invocation pays every time (~230 s for Cedar). Neither is
a default target — plain `lake build` stays cheap. `VerifiedHeavy` is memory-heavy:
build it alone, one worker at a time (`LAKE_NUM_JOBS=1`). The `ParserTestFoo` and position/error-message tests
are rooted in the `ParserTests` `lean_lib`, separate `#guard`-based behavior tests,
not the proof modules.

## Lexers

A grammar is in one of two regimes. Grammars with a `%lexer { … }` block
(`calc`, `cedar`, `cedarschema`, `cedarentities`) are in the
**generated** regime: the
CLI emits the token type and the tokenizer into the lexer module (e.g.
`calc/CalcLexer.lean`), with the DFA tables validated offline by `native_decide`.
The validator conditions are interval arithmetic over character classes (DESIGN
§9.3), so Cedar's Unicode-wide classes are handled by testing one representative per
boundary cell, not per code point — there is no code-point budget gate. The
emitted `tokenize` runs the fast flat `state × class` scanner
(`Lexer.tokenizeFlatStr`), whose flat tables are checked against the DFA by
`FooLexer.flatValidated⟨m⟩` (`native_decide`). The parser modules import the lexer
module for the token type.

Grammars without a `%lexer` block (`imp`, `c99`) are in the **hand-written**
regime: the token type and the lexer are ordinary hand-written Lean. IMP's lexer is
a small recursive function in `imp/ParserTestImp.lean`.

The Cedar fixture is a structural port of
`cedar-policy-core/src/parser/grammar.lalrpop`: its Lean types mirror the Cedar
CST and its tokenizer mirrors the LALRPOP lexical rules. Source positions,
recoverable `Option` nodes, tolerant error variants, and explicit error-recovery
productions are intentionally omitted.

The cedarentities fixture is the Cedar entity-data syntax from
[RFC 0104](https://github.com/cedar-policy/rfcs/blob/main/text/0104-entity-data-syntax.md).
`cedarentities/CedarEntitiesAst.lean` restates the RFC grammar's tree
(`Entities`, `EntitiesDecl`, `EntitiesNamespace`, `EntityInstance`,
`EntityReference`, `EntityValue`). RFC 0104 leaves `Value` as a TODO ("scoped
down from policy grammar"); this fixture pins it to the value subset the JSON
entity format uses — strings, longs (with an optional leading `-`), booleans,
entity references (`Path::"id"`), sets, records, and extension calls
(`datetime("…")`, `ip("…")`). Entity references and extension calls share the
`Path` prefix, so they are left-factored through one ident spine
(`entity_ref_tail`, `path_value_tail`) to stay LR(1). Records, sets, extension
args, and parent lists allow an optional trailing comma, matching the RFC's
`[',' | ',' KeyValues]`. Annotations are not in RFC 0104 (a listed future
addition), so the `Annotated` wrapper always carries an empty list. Pager
construction is conflict-free; `cedarentities/CedarEntitiesParser.lean` and
`CedarEntitiesVerified.lean` both build, and the verified module proof-checks
(~7 s).

`test/cedarentities/corpus/` holds a positive/negative corpus:
`corpus/positive/*.cedarentities` must parse and `corpus/negative/*.cedarentities`
must be rejected. `test/cedarentities/CorpusTest.lean` (`lean_exe
cedarentities-corpus-test`) walks both subfolders and fails if any file lands in
the wrong bucket. An empty file is a valid empty entity set, so empty inputs go
under `positive/`.

```sh
lake build cedarentities-corpus-test
lake exe cedarentities-corpus-test
```

### Lex+parse performance

The numbers below come from `test/cedar/CedarBench.lean` (`lean_exe cedar-bench`) on the
`cedar-spec/cedar-benchmarking` corpus. They are per-policy averages for
before/after comparison, not absolute figures; DESIGN §9.6 has the full account.

**Flat `state × class` scanner.** The generated lexers' `tokenize` runs the fast
flat scanner (`Lexer.tokenizeFlatStr`: a flat `state × classId → target` table over
a `String.Pos` cursor, `DFA.flatScanStr`, plus `String.extract` lexemes, no
`List Char`). It is built in two steps, both proved sound with the standard axiom
budget:

- `Lexer/StringScan.lean` removes the `List Char` scan (walk the `String` by
  `String.Pos`, `tokenizeStr_eq_tokenize`) — a sound ~1.3x on its own.
- `Lexer/FlatValidator.lean`/`FlatScan.lean`/`FlatTokenize.lean` replace the
  per-character `DState.stepChar` interval search (which was ~87% of lex-only time)
  with two array reads (`classOf` binary search + flat table lookup). The flat
  tables' agreement with the DFA is checked per lexer by `native_decide`
  (`FooLexer.flatValidated⟨m⟩`), and `tokenizeFlatStr_eq_tokenize` proves the emitted
  `tokenize` equals the spec `tokenize`, so `tokenize_sound` transfers unchanged.

Token output is byte-identical (the `cedar-bench` lex-only checksums are unchanged).
Measured over 2000 iterations, per policy:

| Corpus | lex-only `List Char` | `String.Pos` | flat scanner | speedup |
|---|---|---|---|---|
| Cedar `generated/` (22) | 185.3 µs | 143 µs | 66.8 µs/policy | ~2.2x vs `List Char` |

This is the honest ceiling for the scan-representation lever: a profiler
decomposition attributes the remaining lex-only time to the flat scan (~72%), the
`String.extract` lexeme (~11%), and per-token semantic actions (~18%, user code the
generator cannot speed up). The flat table is `DFA.flatOfDFA` (untrusted); the
derivative-vector `DFA.scan` remains the specification.

**Inline (closure-free) parser engine.** The generated parser's `run` uses
`Runtime.Exec.runInline` over a `FlatTable` (the raw action/goto/default/lhs/len
arrays read inline) instead of the closure-wrapped `ExecTable`. Profiling the
parse-only path attributed a measurable share of the time to `ExecTable`'s six `fun`-field indirect
calls per step; reading the arrays inline removes them. The `ExecTable` `Exec.run`
stays the specification: `Runtime.Exec.runInline_eq_run` proves the inline engine
equals it (axioms `propext`/`Quot.sound`, no `native_decide`), so `parse_eq_dependent`
and the parser corollaries transfer with the same axiom budget (DESIGN §13).

Token/AST output is identical. A direct A/B on the Cedar `generated/` corpus (22
policies, `cedar-spec/cedar-benchmarking`, same tables, 0 mismatches) measured
closure 146.9 → inline 130.0 µs/policy (~11.5%).

An `Array` LR stack and input cursor were measured and were not faster than `List`
(the lexer's `List Char` lever does not transfer to the parser), so the stack stays
`List`; the remaining parse-only cost is `popN` allocation and per-token semantic
actions (user code).
