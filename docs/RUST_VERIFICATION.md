# Proving the generated Rust lexer and parser

With `%option gen_rust_verif <dir>`, the generator also writes a Lean package that proves the
generated Rust lexer and parser equal to the generated Lean ones. This page says what is
generated, what it needs, and what the theorems say. How the proofs work, what they assume and
what is not done are further down.

## Asking for it

In the `.lig`, next to `gen_rust`:

    %option gen_rust rust/src/generated.rs
    %option gen_rust_verif rust_bridge

The directory is relative to the `.lig`, like the Rust path. `gen_rust_verif` needs
`gen_rust`. Then

    leanparsergenerator cedar.lig

writes the Lean modules, the Rust file, and the package. `lake build parsers` in this
repository runs `leanparsergenerator --skip-rust-verif`, which writes everything else and leaves
the package as it is, so that the build does not need Charon and Aeneas.

The proofs cover grammars whose lexer has one mode and whose lexer rules stay in it (or that
have no `%lexer` block). For another grammar the generator fails; with
`%option rust_verif_optional` it warns and writes no package, so that a grammar can have the
Rust code without the proof.

## What it needs

- `charon` and `aeneas`, on `PATH` or in `$AENEAS_DIR/charon/bin` and `$AENEAS_DIR/bin`, at
  the revisions `rust/verif/lakefile.lean` pins (Charon builds the crate with its own pinned
  nightly toolchain).
- `cargo`. The Rust crate is the nearest directory above the generated file with a
  `Cargo.toml`, which the user writes. It must depend on `lpg_kernel` (for now by path:
  `lpg_kernel = { path = ".../rust/lpg-kernel" }`), and the generated file must be a module
  of the crate (`src/generated.rs` is `crate::generated`). The crate may be a library or a
  binary.
- The generator's `rust/verif` package next to the kernel crate (`<kernel>/../verif`), which
  holds the proofs that do not depend on the grammar. The generated package requires it.

## What is generated

For `cedar.lig` with `gen_rust_verif rust_bridge`, in `test/cedar/rust_bridge`:

| File | What it is |
|---|---|
| `CedarRustBridge/Types.lean`, `Funs.lean` | The Charon and Aeneas translation of the crate, from `crate::generated::parse` and `crate::generated::lex` |
| `CedarRustBridge/TypesExternal.lean`, `FunsExternal.lean` | The kernel the translation calls: `Kernel.Types` and `Kernel.Funs` of `rust/verif` |
| `CedarRustBridge/LexCert.lean` | The certificate of the lexer check: the Rust lexer tables packed into numbers, the Rust state of each state of the Lean DFA, the intervals of code points the check walks |
| `CedarRustBridge/Proof.lean` | The parser theorem |
| `CedarRustBridge/LexProof.lean` | The lexer theorems |
| `CedarRustBridge.lean` | Imports both |
| `lakefile.lean`, `lean-toolchain` | Written once, if absent; edit them freely |

Every other file is rewritten by each run. The generated files are checked by Lean: their
checks run in the kernel (`decide +kernel`), so a wrong size or certificate makes the package
fail to build, it does not make a wrong theorem.

The lakefile requires `rust/verif` and shares its package directory, so Aeneas and Mathlib are
built once. The generated Lean modules of the grammar (`cedar.CedarParser`, `cedar.CedarLexer`)
must be reachable: in this repository they come from the generator's package, which `rust/verif`
requires. For a grammar in another package, add a `require` of that package to the lakefile.

Building:

    cd test/cedar/rust_bridge && lake build

(Cedar: about 30 s for the translation of the tables and 40 s of checks once `rust/verif` is built.)

## Before the translation: the kernel

The proofs about `lpg_kernel::parse` and `lpg_kernel::lex` are in `rust/verif`, about the
translation in `rust/verif/Kernel/{Types,Funs}.lean`. Each run translates the kernel the crate
depends on and fails if the translation is not that one. After a change to the kernel,

    leanparsergenerator --rust-extract-kernel rust/lpg-kernel rust/verif/Kernel

rewrites the translation (and checks that every function Aeneas has no model for is in
`rust/verif/Kernel/FunsExternal.lean`), and the proofs in `rust/verif` have to be updated.

## The theorems

In namespace `<crate>.Proof` (for Cedar `cedar_rust_parser.Proof`):

- `parse_lean`: for tokens whose terminals are those of a Lean parser input, the Rust `parse`
  ends as the kernel's machine, whose run corresponds to `Runtime.Exec` on the Lean parser's
  table (`CedarParser.table`), with the node vector the postorder trace of the parse tree, with
  spans.
- `lex_agrees`: on the UTF-8 bytes of a string, the Rust `lex` and
  `Lexer.tokenize CedarLexer.lexer` report the same run of the Lean DFA (`Spec.ruleRun`).
- `tokens_agree`: for a run without error, the Rust tokens and the Lean tokens are in
  one-to-one order with the same terminals, except for the rules in `hooks`, whose terminal a
  Rust function computes.

They use the axioms `propext`, `Classical.choice` and `Quot.sound` only. What they assume, and
what is not proved, is listed under "Conventions and what is assumed" and "Not done" below: among others, the 64-bit platform, the models of `Vec::clear` and `Vec::truncate`, the
terminals of the hook rules, and the code `tokenize` runs after `lex`.

## How the proofs work

The aim is a proof, in Lean, that the Rust lexer behaves as the Lean lexer and that the Rust
parser produces the parse tree of the Lean parser. It is built on Aeneas (Charon translates
the Rust to LLBC, Aeneas to Lean) and lives in `rust/verif/`, a separate Lake package, because it
needs Aeneas and Mathlib and the generator needs neither.

Aeneas translates a subset of Rust, so the code to prove is written for it:

- The loops that are the same for every grammar are in `rust/lpg-kernel` and take the
  grammar's tables as arguments. The kernel is translated and proved once. A grammar's crate
  is translated with the kernel as an external dependency (`--opaque lpg_kernel`), so the
  call `lpg_kernel::parse(tokens, stack, nodes, &ACTION, …)` in `generated.rs` is checked
  too, and the Lean statement for a grammar is the kernel theorem applied to its tables.
- Tables are `[[u16; N]; S]` with one `const` per row. Aeneas writes an array as one Lean
  list literal, which Lean cannot elaborate beyond a few hundred elements; rows of
  `NUM_TERMINALS` elements it can, at about 1 ms per entry (Cedar's 442 rows: 24 s).
- Tokens are plain data (`Token`), with no lifetime and no value. Values are not part of
  what is proved: the correspondence is on the trace and on the tokens' terminals and spans.
- Only the operations of `Vec` and slices that Aeneas models are used. `Vec::clear` and
  `Vec::truncate` have a model in `rust/verif/Kernel/FunsExternal.lean` that the proofs trust.

`%option gen_rust_verif` writes a grammar's proof package, with the translation of its crate
(docs/RUST_VERIFICATION.md); `leanparsergenerator --rust-extract-kernel` rewrites the
translation of the kernel in `rust/verif/Kernel/`.

What is proved (axioms `propext`, `Classical.choice` and `Quot.sound` only):

- `Spec.run_eq_eval`: `Exec.run` on any table and any semantic actions is the evaluation of
  the tree that the same table builds with the action "make a node". The Rust trace only has
  to be compared with that tree.
- `Spec/Machine.lean` is a pure Lean transcription of one iteration of the kernel loop
  (`mstep`), and `Spec/MachineSim.lean` proves that it refines `Exec.step` on the tree table
  (`sim_run_init`).
- `Kernel/ParseBody.lean` proves that the Aeneas translation of `reduce`, `first_start`,
  `lookahead` and the body of `parse` equal the pure machine, and the loop theorem follows by
  induction on the fuel. `lpg_kernel.Proof.parse_correct` states the result: for tables
  that satisfy `KWf` and `Spec.MWf`, the final stack and node vector of `parse` are those of
  `Spec.mrunN`, and `Spec.RunSim` relates the end of that run to `Exec`: out of fuel, the
  same rejection, the same internal error, or acceptance of a tree whose postorder trace,
  with spans, is the node vector.
- `Spec/TableAgree.lean`: two tables that agree on the states, terminals, nonterminals and
  productions in range, and that stay in range (`TblWf`), take the same steps
  (`stepN_sim`). `Spec/TableCheck.lean` turns equalities of lists between the Rust rows and
  the arrays of a Lean `FlatTable` into that agreement, also for the compressed Lean tables
  (`mergeEq`, `buildDense_toList`). `Kernel/Tables.lean` (`parse_lean`) adds to
  `parse_correct` that the run is the run of the Lean tree table on the Lean input, with each
  token index replaced by the token's value.
- The generated `CedarRustBridge/Proof.lean` (`test/cedar/rust_bridge`) checks the Cedar tables by `decide +kernel` (about 12 s) and proves
  `cedar_rust_parser.Proof.parse_lean`: `generated.parse` runs `CedarParser.table`. With
  `Spec.run_eq_eval` and `Spec.run_of_stepN` this is a statement about
  `Exec.run CedarParser.table`. The hypotheses are on the tokens: their terminals are those of
  the Lean input and are in range.
- `Kernel/LexBody.lean` (`lex_spec`): the Aeneas translation of `lpg_kernel::lex` is
  `Spec.llex` (`Spec/Lex.lean`), the longest-match loop over the Rust lexer tables, one byte
  per step. The inner loop over runs of one state is proved to skip what the byte-by-byte
  scan does (`Spec.lscan_run`).
- `Spec/LexSim.lean`: if the Rust DFA simulates a Lean character DFA on UTF-8 (`LexSim`: a map
  from Lean states to Rust states that keeps the accepted rule, and the bytes of every
  character go where the Lean step goes, through non-accepting states), the Rust scan from a
  byte position is `DFA.scan` on the characters from there (`lscanFrom_sim`). Both
  `Spec.llex` (`llex_rules`) and `Lexer.tokenizeAuxDFA` in one mode (`tokenize_rules`) are
  then reports of one rule-level run, `Spec.ruleRun`: every match with its rule, byte span and
  text, and the position of the error if there is one.
- `Spec/Utf8.lean` and `Spec/LexCheck.lean` decide `LexSim`. `String.utf8EncodeChar` is
  written in base 64 (`encN_eq_bytesOf`), and `walk` follows the Rust DFA over the encodings
  of all the code points of an interval at once, splitting on each digit (`walk_sound`). The
  check is given the map of states and the intervals between the endpoints of the edge
  classes (on which each Lean step is constant, `stepChar_congr_interval`), and compares
  every walk with the Lean step at the first valid code point of the interval.
  The generator writes these, and the Rust tables packed into numbers (the kernel reads a
  packed number in one shift; the transitions are one number per row, because a shift
  allocates a number the size of its result), into the package's `LexCert.lean`;
  `Kernel/LexTables.lean` checks that the packed numbers are the Aeneas arrays (`packCheck`)
  and proves `lex_run`. The generated proof runs `lexSimCheck` in blocks of 32 Lean states,
  one theorem each (`lexSimCheck_of_parts`). The kernel keeps its reductions until the end of
  a declaration, so a single check over the 387 states of a 93-rule lexer peaked above 30 GB.
  In blocks, that lexer's `LexProof.lean` takes 175 s, and the cold build of its package
  (with `verif` built) 352 s with a peak of 11.6 GB.
- The generated `CedarRustBridge/LexProof.lean` (about 16 s of kernel checks) proves `lex_agrees`: `generated.lex`
  and `Lexer.tokenize CedarLexer.lexer` report the same run of `CedarLexer.dfa0`, and
  `tokens_agree`: for a run without error the Rust tokens and the Lean tokens are in
  one-to-one order with the same terminals, except for rule 5, whose terminal the Rust
  `keyword_or_identifier` computes.

Conventions and what is assumed:

- Fuel. `parse` takes `fuel: usize`; the generated wrapper passes `lpg_kernel::FUEL`
  (2^62). Running out gives `Err` with `term = TERM_OUT_OF_FUEL`. Termination is not proved
  from the tables. `Exec.run` takes `2 ^ logN` steps; `run_of_stepN` relates the two when
  `Exec.run` does not time out.
- Spans. `Exec` has no spans, so the span convention is a specification of its own
  (`Spec/Spans.lean`, `Tree.ann`): a leaf has the span of its lexer token; the `$` leaf has
  `(prev, prev)`; a reduction ends at the end of the previous token and starts at its first
  child, or at `prev` if it has no children. The Lean parsers give `0..0` to an empty
  production; the Rust parser does not.
- `reduce` returns the `Reduced` enum (`Next`, `Accept`, `Inconsistent`). `Reduced` and
  `LexFail` have no derives, to keep the Lean extraction small.
- The theorems assume `System.Platform.numBits = 64`.
- `Vec::clear` and `Vec::truncate` are trusted models.
- On acceptance the theorem reports `rest`, the forest below the accepted tree. That
  `rest = []` and that the root is the augmented production follow from the Lean side's
  properties of `Exec`; neither is proved here.
- The lexer is related to `Lexer.tokenize` (the specification, over `List Char`), whose
  equality with the `tokenizeFlatStrPos` the Lean parsers run is the Lean side's
  (`tokenizeFlatStr_eq_tokenize`, which uses the `native_decide` flat-table check). The Rust
  spans are the byte lengths of the characters before and through each match
  (`Spec.ruleRun`); they are not compared with `tokenizeFlatStrPos`'s `String.Pos` spans.
- The input bytes are the UTF-8 encoding of the characters (`bytesOf src = encChars cs`), as
  Rust guarantees for `&str`, and there are at most `u32::MAX` of them (else `TooLong`).
- What runs after `lex` in `tokenize` (the terminals of `g s` rules, and the values that do
  not fit their Rust type) is not translated; the terminal of a `g s` rule is trusted.

## Not done

- A check that a Rust action and its Lean action build the same thing.
- A pull-based lexer (no token vector) and collapsing unit-production chains, which
  dominate the 1600 nodes per Cedar file.
- A theorem that composes the lexer and the parser: from `tokens_agree`, the Lean tokens
  decoded are the parser input of `parse_lean`, given the terminals of `g s` rules; and the
  link from `Lexer.tokenize` to the `String.Pos` spans of `tokenizeFlatStrPos`.
- Lexers with several modes: the kernel and the proofs are for one mode.
