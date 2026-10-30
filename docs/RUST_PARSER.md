# Rust backend (prototype)

`leanparsergenerator --backend rust <grammar.lig> <out.rs>` writes one Rust file with a
lexer and an LR(1) parser. A grammar without a `%lexer` block (the C99 fixture) gets
only the parser and the terminal constants; the caller supplies the tokens by
implementing `Terminal` (`Kind` is a ready-made token that is only a terminal index).
The emitters are `LeanParserGenerator/Emit/CodegenRust.lean` (parser and assembly)
and `Emit/Rust/Lexer.lean` (lexer). It reuses the Lean side's table
construction: the Pager `Tables` for the parser and `DFA.build?WithVecs`,
`DFA.flatOfDFA` and `ByteDFA.byteOfFlat` for the lexer. Nothing is recomputed in Rust.

This is a prototype. It has no proofs, and verification is not designed yet.

## Where the files are

The `.lig` names the Rust output:

    %option gen_rust rust/src/generated.rs

The path is relative to the directory of the `.lig` and starts with a name, not with
`.` or `/`. `leanparsergenerator cedar.lig` (what `lake build parsers` runs) then writes
it next to the Lean modules, and the first lines of the generated file say which `.lig`
it came from. `--backend rust` writes a single file without the option. The Rust
functions that lexer actions call are named in the `%lexer` block with
`rust f => crate::module::fn`, so the module is visible there too; the file itself
(`test/cedar/rust/src/hooks.rs` for `crate::hooks`) is handwritten. In `cedar.lig`:

| File | Where it is named |
|---|---|
| `CedarVerified.lean`, `CedarParser.lean`, `CedarLexer.lean`, `CedarLexerRoundtrip.lean`, `CedarParserRoundtrip.lean` | from the `.lig` file name and its `%option`s, next to the `.lig` |
| `rust/src/generated.rs` | `%option gen_rust` |
| `rust/src/hooks.rs` | `rust … => crate::hooks::…` in the `%lexer` block |

## What is generated

Lexer. See "Lexers" below.

Parser. `ACTION[state * NUM_TERMINALS + t]` is 0 for error, `(target << 1) | 1` for
shift and `(prod + 1) << 1` for reduce. `GOTO`, `DEFAULT_REDUCE`, `LHS` and `RHS_LEN`
are the Lean tables. The loop follows `Runtime.Exec.step`: use the default reduction
if the state has one, otherwise look up the action. A reduction with no goto is
accepted if it is the augmented production, and an internal error otherwise. The
`%eof` token is the augmented `$`, as in `Emit.emitDecoder`.

`parse` fills a postorder `Vec<Node>`: one node per shifted token and one per reduction,
each with a source span. The last node is the augmented start production. This is a
reduction trace, not an AST, so it does less work per reduction than the Lean parsers,
which build the AST. The trace is what a correspondence proof with the Lean parser talks
about. With Rust actions in the `.lig` (next section) the generated file also has
`parse_values`, which is the same LR loop (a separate copy generated from its own template,
checked against `parse` by a test) and computes the user's values.

## Rust actions

The semantic actions of a `.lig` are Lean terms. The Rust backend does not translate them.
Instead the grammar author writes a Rust action next to each Lean one, with the marker
`!!rust{ … }`, and the generator pastes it, unchanged, into the reduction of that
production. A rule's Rust type goes after its Lean type:

    expr :: Expr !!rust{crate::ast::Expr<'a>}
      | e=expr PLUS t=term { Expr.add e t }
                           !!rust{ crate::ast::Expr::Add(Box::new(e), Box::new(t)) }
      | t=term             { t }
                           !!rust{ t }

The Lean side is unchanged, so a user's Lean AST is used as before and the Rust side is
free to use another representation: `Box`, an arena, borrowed strings, a `VecDeque` for a
right-recursive list. The generator never reads the Rust text. It uses the Rust type of
each rule only to decide which stack the rule's values live on. If the text does not
compile, the user changes it; the rustc error is in `generated.rs`, and each arm carries a
comment with the rule name and alternative number. How a user writes and calls them is in
`docs/USING_RUST_GENERATOR.md`.

The motivation is that the parsing theorems are stated on parse trees, so the proof that
the Rust parser corresponds to the Lean one needs the two parsers to agree on the trace,
and does not need their semantic values to agree. The values are the user's: the Lean and
the Rust action of a production are separate pieces of code, and nothing checks that they
build the same thing. A user who wants that can compare them on their own inputs.

The driver, `parse_values`, keeps one `Vec` per distinct Rust type (`Stacks`) and an entry
stack of states and spans. A reduction pops the values of its right-hand side, each from the
stack of its type, binds them to the names the `.lig` gave them, evaluates the Rust body and
pushes the result on the stack of the rule's type. A token's payload (`&'a str`, `u64`, `i64`)
is pushed when the token is shifted. `x_span`, for a binder `x`, is a `Span { start, end }`.

## Lexers

Tables. The byte DFA from `ByteDFA.byteOfFlat` has 256 columns per state. The emitter
merges bytes whose columns agree in every state into classes (Cedar: 53 classes, 71
states) and writes, per mode, `M<i>_CLASS`, `M<i>_TRANS` and `M<i>_ACCEPT`. The states
are renumbered with the accepting ones last; a state is the offset `(k + 1) * classes` of
its row, row 0 is the dead row, and `trans[row + class]` is the offset of the next row
(0 for dead). So a step is one load and an accepting row is `row >= accept_from`;
`accept[row]` is the rule plus one. Before writing the tables the generator checks
them against the byte DFA for every state and byte (D16). `tokenize(&str, &mut Vec<Spanned<Tok>>)` is the
usual longest-match loop: run until the dead state, remember the last accept, fail if
no rule matched or the match is empty. A state that steps to itself starts a separate
inner loop over the run (identifier characters, spaces): its loads do not depend on
each other, which a loop that carries the state does. It appends the `%eof` token last. Modes work as
in `Lexer.tokenizeByteAux`: a stack of modes starting with the first, `enter m` pushes,
`leave` pops, and end of input is an error unless exactly one mode is on the stack.

Actions. The Rust backend accepts a lexer rule only if its action has one of five
forms, with `s` the `as` binder:

| Action | Rust |
|---|---|
| `skip` | no token |
| `Tok.IDENT` | `Tok::IDENT` |
| `Tok.NAME s` | `Tok::NAME(text)`, `NAME` carrying `String`, which is `&'a str` |
| `Tok.NAME (f s)` or `Tok.NAME s.f` | `Tok::NAME(v)` for `Some(v) = f(text)` |
| `g s` | the token `t` for `Some(t) = g(text)` |

`f` and `g` are Lean functions. Their Rust counterparts return `Option`: `None` means
the Lean result does not fit the Rust type, and the lexer then fails at the start of the
lexeme with `LexErrorReason::Unrepresentable`. `String.toNat!`, `String.toInt!` and
`String.length` have Rust counterparts in the generated `lexrt` module. Any other function needs a line
in the `%lexer` block that names its Rust counterpart, which the user writes:

    rust keywordOrIdentifier => crate::hooks::keyword_or_identifier
    rust stripStringQuotes => crate::hooks::strip_string_quotes

The Lean function stays the specification. For `cedar.lig`, `keywordOrIdentifier` has
the dependent type `String → Tok` with `IDENTIFIER : {s // s ∉ keywords} → Tok`, and
the Rust one (`test/cedar/rust/src/hooks.rs`) returns `Some(Tok::IDENTIFIER(String))`. A
composition such as `(s.replace "_" "").toNat!` is rejected with a message asking for
a single function. So is any action outside the five forms; the message names the mode
and the rule. The Lean lexer generator does not read the `rust` lines or restrict
actions.

Token type. `Tok` has one variant per `%token`, with the Rust type of the declared
Lean type as payload: `String` is `&'a str`, `Nat` is `u64`, `Int` is `i64`, `Bool` is
`bool`, `Char` is `char`, and a subtype is its base type. Any other type is an error.
`Tok` implements `Terminal`, which gives the parser the terminal index.

Numbers. `Nat` is `u64` and `Int` is `i64` (decision D7). A numeral beyond the range
is not saturated: `lexrt::to_nat` and `lexrt::to_int` return `None`, so the Rust lexer
reports an error where the Lean lexer succeeds with a larger `Nat`, and never produces a
wrong value. In Cedar numerals are assumed to fit `u64`. `to_nat` also returns `None`
on anything but decimal digits, where `String.toNat!` panics and gives 0.

Errors. `LexError` has `pos`, a character offset as in Lean, `byte_pos`, `ch`, the
offending character (none at end of input), and `reason`: `NoMatch`, `Unrepresentable`
or `EndInMode`.

Differences from the Lean lexer that remain:
- A numeral beyond `u64` (`i64` for `Int`) is a lexer error in Rust; Lean accepts it.
  `18446744073709551615` lexes identically; `99999999999999999999999` fails at its first
  character.
- Lean's `toNat!` on a string that is not decimal digits gives 0 after a panic; Rust
  fails the lexer. A transform that decodes hex or binary digits has to say so in its
  own definition.
- The Rust lexer always appends the `%eof` token. Without an `eof` clause, Lean's
  token list has none (the parser supplies it).

## Cedar crate

`test/cedar/rust` is a Cargo crate (no dependencies):

- `src/generated.rs`: the generated file, committed like the Lean outputs.
  Regenerate with `lake build parsers` (the `.lig` names the file, `%option gen_rust`).
- `src/hooks.rs`: the Rust counterparts of `keywordOrIdentifier` and `stripStringQuotes`.
- `src/bin/check.rs`: prints `ok`, `lex`, or `parse <token> <state> <lookahead>` per
  file; with `--tokens` or `--values`, the token stream.
- `src/cst.rs`: the Rust CST built by the Rust actions of `cedar.lig`, hand-maintained.
  It follows `CedarAst.lean` (the layered Cedar CST) with lists as `VecDeque`s and owned
  strings.
- `src/main.rs`: benchmark, same corpus and unit as `CedarBench.lean` (one file per
  "policy").

## Measurements

Cedar corpus, 28 files, 49,670 bytes, `cargo build --release` with LTO. Lean numbers
are `cedar-bench` on the same machine and include building the AST.

| | Rust | Lean |
|---|---|---|
| lex + parse | 14.8 µs | 88 µs |
| lex only | 3.4 µs | 44 µs |
| parse only | 11.2 µs | 43 µs |

Rust lex + parse is about 120 MB/s and the lexer alone about 520 MB/s. Allocating the
token and node buffers on every call costs about 1.8 µs. Replacing every table index in
the hot loops with `get_unchecked` made no measurable difference, so bounds checks are
not a cost here.

### Lexer optimization

Lex only on Cedar, per file, each step measured on top of the previous one (the token
streams were compared with the Lean lexer after each):

| Step | Lex only |
|---|---|
| first version: class-compressed table, state number times classes, accept array | 7.4 µs |
| states renumbered, a state is the offset of its row, accepting rows last (D16) | 6.0 µs |
| inner loop over self-loops (identifier characters, spaces) | 4.8 µs |
| `String` payloads are slices of the source, not owned (D13) | 3.4 µs |

Tried and dropped: a separate "accepting and final" state range that stops the scan
without another load (no change). Measurements that guided the work: scanning without
building tokens takes 4.0 µs of the 4.8, so token construction was not the bottleneck
until the allocations went; with the allocations gone the loop is bound by the latency of
the dependent table load (4.2 instructions per cycle, 0.3% branch misses on this corpus).
Going further would need a different scanner, for example two bytes per step.

## C99

The C99 fixture has no lexer, so I tokenized three C programs with a throwaway Python
lexer (it tracks `typedef` names, so `TYPEDEF_NAME` is produced as the grammar
expects). The fixture grammar has no brace initializers and no declarations in `for`
headers, so the programs avoid them. 14,611 tokens in total, the largest file 13.6k.

Parse only, 3 files, built from the same tokens: Rust 192 µs per file against 634 µs
for the Lean parser (3.3x, about 76 million tokens/s against 23). The Lean parser
builds the C99 CST and the Rust one a reduction trace. The C99 tables have 305 states
and 184 productions.

## The action classifier

Before Rust actions were written by hand (previous section), the plan was to translate the
Lean actions. The classifier from that plan stays as a read-only report: for every parser
alternative and lexer rule it says whether the action is built only from constructors,
variables, lists, tuples and a few library functions. It does not emit anything, and the
lexer uses the same rules (D14). For a grammar author it answers "how much of this
grammar's Lean actions is plain data construction", which is also how much a Rust
action is a transcription:

    lake env .lake/build/bin/leanparsergenerator --rust-report [-v] grammar.lig

`lake env` is needed because the classifier imports the modules the `.lig` header
imports (here `cedar.CedarAst`), which must be built. The report lists, per grammar,
how many actions are emittable, each action that is not and why, how many actions use
each emission rule, which actions use a variable more than once, and the result of the
domain checks below.

Code, all under `LeanParserGenerator/Emit/Rust/`:

| File | Contents |
|---|---|
| `Action.lean` | `AExpr`, the subset of Lean terms that can be emitted, and its parser |
| `Ty.lean` | `Ty`, the subset of Lean types: applications, products, subtypes |
| `Resolve.lean` | `Resolver`: what a global name is (constructor, function, projection), from the Lean environment |
| `Rules.lean` | `knownFns`: library functions with a Rust counterpart; `builtinAliases` |
| `Classify.lean` | `Blocker` (why not), `Used` (which rule), `analyze` |
| `Domain.lean` | domain checks for partial known functions on lexer rules |
| `Report.lean` | the report |

An action is emittable if it is built from variables, literals, `()`, tuples, list
literals, `::`, `++`, `.1`/`.2`, constructors (including `some`/`none` and `.c`
shorthand), structure instances `{ f := e }`, structure projections and the functions
in `Rules.knownFns`, with every constructor fully applied. The whole list of rules is
`Used` plus `knownFns`, and the whole list of reasons for refusing is `Blocker`.

Result on the public grammars (emittable / total):

| Grammar | Parser | Lexer |
|---|---|---|
| Cedar policies | 135 / 143 | 31 / 33 |
| Cedar schema | 93 / 102 | 16 / 18 |
| Cedar entities | 42 / 53 | 13 / 15 |
| C99 | 180 / 183 | no lexer |
| IMP | 22 / 22 | no lexer |
| Calc | 4 / 7 | 6 / 6 |

What blocks the rest, in Cedar: four lambdas and two applications of a bound variable
(the grammar builds paths in continuation-passing style, `fun path => … tail (path ++
[next])`), two calls of helper functions defined in the AST module
(`Cedar.Add.fromIdent`, `Cedar.Expr.fromIdent`). The two lexer rules are calls of
functions defined in the `.lig` header (`keywordOrIdentifier`, `stripStringQuotes`).
Arithmetic (`e + t` in Calc), `if`, `match`, type ascriptions and `.getD` are not in
the subset. A next tier would translate helper functions whose bodies are themselves
in the subset; that would cover the helper calls but not the lambdas.

### Domain checks

`String.toNat!` panics, and returns 0, on a string that is not all digits. The type of
the action is fine; the regex of the lexer rule allows lexemes the function is not
defined on. `Rules.knownFns` records the domain of each partial function as a regex,
and `Domain.lean` checks that the language of the lexer rule, after the string
operations the action applies, is inside it. It understands the lexeme itself and
`s.replace "c" ""` for a single character `c` (deleting a character is a homomorphism
on regexes). The inclusion test explores the derivatives of both regexes together with
`DFA.build?WithVecs`. Every other expression is reported as not checked. The check is
not trusted, only informative.

On the public grammars all the `toNat!`/`toInt!` calls are proved. A grammar with
`0x` hex literals going through `toNat!` is reported `NOT SATISFIED` for that rule.

### Decisions

Each decision is recorded here so it can be changed. "Implemented" means the
classifier or report does it today.

| ID | Decision | Status |
|---|---|---|
| D1 | Actions are parsed by our own parser for a subset of Lean (`Action.lean`), not by Lean's parser, which does not know the notation a header declares. Text outside the subset is a blocker. | Implemented |
| D2 | Names are resolved against the Lean environment built from the header's `import`s, under its `open`s. Names defined in the header text itself are not visible and are reported as such. | Implemented |
| D3 | `.c` and `⟨…⟩` get their type from the expected type: the nonterminal's declared type, then constructor field types, tuple, list and `Option` components. A polymorphic constructor field loses the expected type. | Implemented |
| D4 | An action is emitted only if it uses the rules above and `knownFns`. Lambdas are never emitted. | Applies to lexer actions and the classifier; for parser actions superseded by D17 |
| D5 | A variable used more than once is a note ("copy needed"), not a blocker. | Reported by the classifier; with D17 it is the user's concern |
| D6 | `List T` as a Rust cons-list rather than `Vec<T>`, because `x :: rest` on a `Vec` is a front insert. | Superseded by D17: the user picks the type (a `VecDeque` with `push_front` does it in O(1)) |
| D7 | `Nat` becomes `u64` and `Int` becomes `i64`. A value out of range is an error in the Rust code (D15), so the correspondence theorem reads: if the Rust lexer succeeds, so does Lean's, with the same tokens. | Implemented for lexer token values |
| D8 | The Rust AST types are generated from the Lean environment. | Tried and dropped, see D17 |
| D9 | Unemittable actions become methods of a generated trait the user implements. | Not done; D17 puts the Rust text in the `.lig` instead |
| D10 | A partial known function carries its domain as a regex, and the generator checks lexer-rule languages against it. | Implemented for lexer actions |
| D11 | A structure instance must name exactly the structure's fields. | Implemented |
| D12 | In a parser action a binder has the type declared for its symbol, `x_span` has type `Runtime.Span`, and in a lexer action the lexeme is a `String`. | Implemented |
| D13 | A `String` token payload is a slice of the source, `&'a str`, and `Tok<'a>` has a lifetime parameter (only if some token has such a payload). Owned `String`s cost 1.4 µs of 6.0 on Cedar lexing in allocation and more in copying the larger token. | Implemented |
| D16 | The lexer tables are a re-encoding of the byte DFA: states renumbered with the accepting ones last, a state is the offset of its row, a step is one load. The generator checks the re-encoding against the byte DFA before it writes it. Proving it is part of the Rust-to-Lean bridge. | Implemented |
| D14 | A lexer action has one of five forms (`skip`, `Tok.T`, `Tok.T s`, `Tok.T (f s)`, `g s`); a Lean function used in one has a Rust counterpart, built in or declared with `rust f => path` in the `%lexer` block. | Implemented |
| D17 | A parser action has a Rust counterpart written by the grammar author, `!!rust{ … }` after the Lean action, pasted verbatim into the reduction. The Rust type of a rule is `!!rust{type}` after its Lean type. The generator does not parse, translate or check the Rust. The parse-tree correspondence is independent of the values. | Implemented |
| D18 | Values live on one `Vec` per distinct Rust type; the production being reduced pops from the stacks of its right-hand side symbols. Rejected: one enum of all value types, which has the size of the largest AST node and was copied on every shift and reduction. With an AST whose nodes were up to 500 bytes, two thirds of the time went to `memmove`; per-type stacks and nodes of at most 64 bytes (larger fields behind a `Box`) cut the cost of building the AST per token by more than half. The trace parser, which builds nothing, is several times faster still. | Implemented |
| D19 | Rust actions are all or nothing: every rule needs a type and every alternative an action, or none has any. | Implemented |
| D21 | Macro-generated rules get Rust text from the expansion when the grammar has Rust actions: lists are `VecDeque<T>` (the expansion is right-recursive, so `push_front` keeps it O(1)), options `Option<T>`, `T` the Rust type of the element, the payload type for a token (`&'a str` for a `String`). A user who wants another representation writes the list rule by hand. | Implemented |
| D22 | A reduction whose action is just the name of its only binder, with the symbol and the rule of the same Rust type, generates no code. | Implemented |
| D20 | The `.lig` frontend reads `!!rust{…}` without a change to `lig.lig`: the bootstrap lexer keeps the Rust text inside the type or action token, and `assembleSurface` splits it off. The committed bootstrap parser is unchanged. | Implemented |
| D15 | A numeral that does not fit `u64`/`i64`, or a string `toNat!` is not defined on, makes the Rust lexer fail (`Unrepresentable`) instead of saturating or returning 0. Rust counterparts of lexer functions return `Option`. | Implemented |

## Not done

- A check that a Rust action and its Lean action build the same thing.
- A pull-based lexer (no token vector) and collapsing unit-production chains, which
  dominate the 1600 nodes per Cedar file.
- Verification.
