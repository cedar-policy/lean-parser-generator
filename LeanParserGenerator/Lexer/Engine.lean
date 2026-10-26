/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module
/-
The (unverified) lexer runtime, a mode-stack machine.

Given a `Tokenizer` (one or more named *modes*, each an ordered rule list) it
tokenizes by maximal munch. A rule's action is an `Act`: it optionally emits a
token and (orthogonally) moves the mode stack (`stay` / `push` / `pop`). Emitting
plus a push/pop covers ocamllex-style delimiter tokens; a plain push/pop with no
emit covers comment/whitespace modes.

The mode stack gives ocamllex-style *recursive rules*: nested comments are handled
by pushing on `(*` (in both the main and comment modes) and popping on `*)`. A
single-mode lexer is just a `Tokenizer` with one mode.

Eager and total (no `partial def`); the result is exposed as a `TokenStream`.
-/
public import LeanParserGenerator.Lexer.Regex
public import LeanParserGenerator.Lexer.DFA
public import LeanParserGenerator.Runtime.Buffer


@[expose] public section

namespace Lexer

open Runtime

/-- How a matched rule moves the mode stack. -/
inductive Trans where
  /-- Stay in the current mode. -/
  | stay : Trans
  /-- Push a mode (by index). -/
  | push : Nat → Trans
  /-- Pop the current mode. -/
  | pop : Trans
  deriving DecidableEq

/-- What a matched rule does: optionally emit a token, and (orthogonally) move the
    mode stack. `emit = none` is "skip"; `trans = .stay` is the common case. This
    orthogonality gives `enterEmit`/`leaveEmit` for free (emit + push/pop). -/
structure Act (Tok : Type) where
  /-- The token to emit, if any. -/
  emit : Option Tok := none
  /-- The mode-stack transition. -/
  trans : Trans := .stay

/-- A lexer rule: a regex and an action over the matched text. -/
structure Rule (Tok : Type) where
  /-- The pattern this rule matches. -/
  regex : Regex
  /-- What to do with the matched text. -/
  act : String → Act Tok

/-- An error describing why tokenization stopped. -/
structure LexError where
  /-- Character offset into the input where tokenization failed. -/
  pos : Nat
  /-- The offending character, if any (`none` at end of input, e.g. an
      unterminated comment). -/
  char : Option Char
  deriving Repr, DecidableEq, BEq

/-- A tokenizer: an array of modes (each an ordered rule list) and the start mode
    index. Single-mode lexers use exactly one mode. -/
structure Tokenizer (Tok : Type) where
  /-- The modes, indexed by position. -/
  modes : Array (List (Rule Tok))
  /-- The index of the mode the tokenizer starts in. -/
  start : Nat := 0
  /-- A token to emit once the input is exhausted (mirrors ocamllex's
      `| eof { … }`). `none` means the lexer emits nothing at end of input. -/
  eofToken : Option Tok := none

/-! ### Tokenization

A mode's rule set is compiled to a `DFA` and the input is scanned by array-indexed
state transitions (docs/DESIGN.md §9.2). Generated lexers build the tables offline
(the CLI, `Emit/CodegenLexer.lean`) and store them as data, so `Lexer.tokenize`
constructs nothing at run time. `Compiled.ofTokenizer` builds them at run time and
is used only for testing/benchmark comparison. -/

/-- A tokenizer with its modes compiled to DFAs. The action arrays parallel the
    DFAs: `acts[m][i]` is the action of rule `i` in mode `m`, indexed by the rule
    id that `DFA.scan` returns. -/
structure Compiled (Tok : Type) where
  /-- One DFA per mode. -/
  dfas : Array DFA
  /-- Per-mode rule actions, indexed by the scan's returned rule id. -/
  acts : Array (Array (String → Act Tok))
  /-- The start mode index. -/
  start : Nat
  /-- The end-of-input token, if any. -/
  eofToken : Option Tok

/-- Compile every mode of a tokenizer to a DFA. Untrusted construction. -/
def Compiled.ofTokenizer (t : Tokenizer Tok) : Compiled Tok :=
  { dfas := t.modes.map (fun rules => DFA.build! (rules.map (·.regex)).toArray)
  , acts := t.modes.map (fun rules => (rules.map (·.act)).toArray)
  , start := t.start
  , eofToken := t.eofToken }

/-- The tokenization loop. `stack` is the mode stack (head = current mode); `fuel`
    is the input length (each step consumes ≥1 character). A zero-length longest
    match is treated as no match, so the loop always advances or errors. Ends
    successfully only when the input is exhausted back in the start mode; a
    leftover pushed mode (an unterminated comment) is an error. -/
def tokenizeAuxDFA (c : Compiled Tok) :
    Nat → List Char → Nat → List Nat → List Tok → Except LexError (List Tok)
  | 0, _, pos, _, _ => .error { pos := pos, char := none }
  | _, [], pos, stack, acc =>
      match stack with
      | [_] =>
          match c.eofToken with
          | some tok => .ok (tok :: acc).reverse
          | none => .ok acc.reverse
      | _ => .error { pos := pos, char := none }
  | fuel + 1, cs, pos, stack, acc =>
      let mode := stack.headD c.start
      let dfa := c.dfas.getD mode default
      match DFA.scan dfa cs with
      | some (rule, len) =>
          if len = 0 then .error { pos := pos, char := cs.head? }
          else
            let matched := String.ofList (cs.take len)
            let rest := cs.drop len
            let act := (c.acts.getD mode #[]).getD rule (fun _ => {})
            let a := act matched
            let acc := match a.emit with | some tok => tok :: acc | none => acc
            let stack := match a.trans with
              | .stay => stack
              | .push m => m :: stack
              | .pop => stack.tail
            tokenizeAuxDFA c fuel rest (pos + len) stack acc
      | none => .error { pos := pos, char := cs.head? }

/-- Tokenize an input string into a token list (or a lexing error), scanning with
    the compiled DFA tables (docs/DESIGN.md §9.2).

    A lexer defined by the `lexer` DSL command is a `Compiled` whose tables are
    already data, so this constructs nothing. -/
def tokenize (c : Compiled Tok) (input : String) : Except LexError (List Tok) :=
  let cs := input.toList
  tokenizeAuxDFA c (cs.length + 1) cs 0 [c.start] []

/-! ### String byte-index tokenizer (the runtime path)

`tokenizeAuxDFA` above walks a `List Char` and, per token, does
`String.ofList (cs.take len)` + `cs.drop len` (and the whole input first goes
through `input.toList`). `tokenizeStrAux`/`tokenizeStr` do the same tokenization
over the `String` directly, using `DFA.scanStr` (a byte-index walk, no `List Char`)
and `String.Pos.Raw.extract` for the lexeme (a byte-range copy, no list rebuild).

This is the runtime the generated lexers call. It is proved equal to `tokenize`
(`Lexer.tokenizeStr_eq_tokenize`, `Lexer/StringScan.lean`), so `tokenize_sound`
transfers unchanged: the derivative-level `DFA.scan`/`tokenizeAuxDFA` remain the
specification and the byte-index tokenizer is a verified-equal implementation. This
removes docs/DESIGN.md §9.1 cause 4 (the `List Char` scan with per-token
`take`/`drop`/`ofList`). -/

/-- Byte-index tokenization loop over a `String`. Mirrors `tokenizeAuxDFA` but
    carries a `String.Pos` cursor into `input` instead of a `List Char`, scanning
    with `DFA.scanStr` and slicing the lexeme with `String.extract`. `fuel` is the
    remaining character count (each step consumes ≥1 character), so the structure
    matches `tokenizeAuxDFA` step for step, which is what makes the equivalence
    proof (`Lexer/StringScan.lean`) go through. -/
def tokenizeStrAux (c : Compiled Tok) (input : String) :
    Nat → input.Pos → Nat → List Nat → List Tok → Except LexError (List Tok)
  | 0, _, cpos, _, _ => .error { pos := cpos, char := none }
  | fuel + 1, p, cpos, stack, acc =>
      if hend : p = input.endPos then
        match stack with
        | [_] =>
            match c.eofToken with
            | some tok => .ok (tok :: acc).reverse
            | none => .ok acc.reverse
        | _ => .error { pos := cpos, char := none }
      else
        let mode := stack.headD c.start
        let dfa := c.dfas.getD mode default
        match DFA.scanStr dfa p with
        | some (rule, len, endPos) =>
            if len = 0 then .error { pos := cpos, char := some (p.get hend) }
            else
              let matched := input.extract p endPos
              let act := (c.acts.getD mode #[]).getD rule (fun _ => {})
              let a := act matched
              let acc := match a.emit with | some tok => tok :: acc | none => acc
              let stack := match a.trans with
                | .stay => stack
                | .push m => m :: stack
                | .pop => stack.tail
              tokenizeStrAux c input fuel endPos (cpos + len) stack acc
        | none => .error { pos := cpos, char := some (p.get hend) }

/-- Tokenize a `String` by the position-cursor runtime path (`DFA.scanStr` +
    `String.extract`, no `List Char`). Proved equal to `tokenize` in
    `Lexer/StringScan.lean`. -/
def tokenizeStr (c : Compiled Tok) (input : String) : Except LexError (List Tok) :=
  tokenizeStrAux c input (input.utf8ByteSize + 1) input.startPos 0 [c.start] []

/-- Present a finite token list as an infinite `TokenStream`, padded with `eof`. -/
def streamOfList (eof : Tok) (toks : List Tok) : NatStream Tok :=
  fun n => toks.getD n eof

/-- Full pipeline: tokenize, then expose the tokens as an infinite stream. -/
def lex (c : Compiled Tok) (eof : Tok) (input : String) :
    Except LexError (NatStream Tok) :=
  (tokenize c input).map (streamOfList eof)

end Lexer
