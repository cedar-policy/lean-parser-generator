# LEXER

A `%lexer { … }` block in a `.lig` file defines a generated lexer. The block contains named regular expressions, ordered rules, optional mode transitions, `skip` actions, and an optional `eof` action. The lexer uses longest-match semantics; an equal-length tie goes to the earlier rule.

The CLI builds the DFAs and validation certificates at generation time and writes them as data in `FooLexer.lean`. The generated module exports:

- `Tok`, from `%tokentype` and `%token`;
- `FooLexer.tokenize : String → Except Lexer.LexError (List (Runtime.Positioned Tok))`;
- `FooLexer.tokenizeBare : String → Except Lexer.LexError (List Tok)`;
- one `validatedN` and `scanSoundN` theorem per lexer mode;
- the flat runtime tables and `flatValidatedN` agreement theorems.

`tokenize` returns byte spans. `tokenizeBare` runs the same flat scanner without positions and is used by the byte runtime and roundtrip proofs. `Lexer.tokenizeFlatStrPos_val` proves that erasing positions from `tokenize` gives the `tokenizeBare` result.

The generated tables are untrusted output. Lean checks the emitted validator certificates. `Lexer.scan_sound` connects each validated DFA to the regular-expression specification, and `Lexer.tokenizeFlatStr_eq_tokenize` connects the flat string runtime to the specification tokenizer for eligible single-mode lexers.

## Syntax

A rule has the form:

```text
| regex => action
| regex as text => action
```

An action is either `skip` or a Lean expression producing a token. A regex can use quoted strings, character classes, sequencing, alternation, grouping, `*`, and `+`. For example:

```text
%tokentype Tok
%token <Nat> NUM
%token PLUS EOF
%eof EOF
%lexer {
  let digit = ['0'-'9']
  | digit+ as s          => { Tok.NUM s.toNat! }
  | "+"                  => { Tok.PLUS }
  | (' ' | '\t' | '\n')+ => skip
  eof => { Tok.EOF }
}
```

`%lexerheader { … }` contains helpers used only by lexer actions. It is copied into `FooLexer.lean` after the token type is declared.

## Universal lexer roundtrip

`%option roundtrip_lexer` generates `FooLexerRoundtrip.lean`. The user supplies `FooLexerRoundtripSupport.lean` beside the generated lexer. That module imports `FooLexer` and defines:

```lean
namespace FooLexerRoundtripSupport

def renderTok : Tok → String := ...

end FooLexerRoundtripSupport
```

The generator imports this module by convention. A lexer imported as `MyProject.FooLexer` uses `MyProject.FooLexerRoundtripSupport`.

The generated module exports a renderer and one theorem:

```lean
abbrev RoundtrippableTok : Tok → Prop :=
  Lexer.RoundtrippableTok FooLexer.lexer
    FooLexerRoundtripSupport.renderTok ' '

def render (ts : List Tok) : String :=
  Lexer.render FooLexerRoundtripSupport.renderTok " " ts

theorem render_roundtrip (ts : List Tok)
    (h : Lexer.Forall RoundtrippableTok ts) :
    FooLexer.tokenizeBare (render ts) = .ok (ts ++ [Tok.EOF])
```

This is quantified over arbitrary token lists. It is not a theorem about a finite corpus or one generated list of tokens.

### `RoundtrippableTok`

`RoundtrippableTok t` is the local, decidable condition needed by the list theorem. It checks the following facts about `renderTok t`:

1. The rendered string is nonempty.
2. The start-mode DFA consumes the whole rendered string as one winning match.
3. The winning action emits exactly `t` and stays in the start mode.
4. A space stops the token scan, and the first character of the token stops the space skip scan.

The generated proof combines these facts with `Lexer.peel_emit`, `Lexer.peel_skip`, and a position-aware induction over the list. The flat-runtime premises (`flatValidated`, a nonempty start DFA, action mode stability, and text-independent action equality) are discharged in private generated lemmas.

For a fixed token, the condition is normally a finite check:

```lean
example : FooLexerRoundtrip.RoundtrippableTok Tok.PLUS := by
  native_decide
```

Value-carrying tokens may need a user lemma. For example, a numeric action must show that parsing the decimal rendering returns the original number. A string renderer must show that quoting and escaping produce a lexeme accepted by the string rule and that the action recovers the original payload. These proofs belong in the support module or another handwritten module, not in generated output.

The predicate excludes values that the token type admits but the renderer cannot reproduce. For example, a keyword-folding lexer must not treat an identifier payload containing a reserved word as roundtrippable. It also excludes `EOF`, whose renderer is normally empty; the theorem appends EOF itself.

### Current restrictions

Roundtrip generation currently rejects a lexer unless:

- it has exactly one mode;
- every action uses `.stay`;
- the winning rule on the separator `" "` consumes one character, skips it, and stays;
- the `eof` action is a token constructor such as `Tok.EOF`.

The fixed separator is one space. Push/pop mode roundtrips need a list predicate that tracks the mode stack and are not generated yet.

The generated module does not state constructor coverage or synthesize reachability witnesses. Those are separate lexer properties. It also emits no `#eval` summaries or generated examples.

## Byte runtime

`FooLexer.tokenizeByte` is the byte-oriented path. Its tables are derived from the validated flat character tables, and `byteValidatedN` checks their agreement. This path is separate from the current roundtrip theorem, which is stated about `tokenizeBare`.
