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
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Frontend.LigParse
/-
`test/lig/BootstrapAgreementTest.lean` — checks that the bootstrapped `.lig`
frontend agrees with the hand-written one (DESIGN §15.4).

For every `.lig` file in the repository (the fixtures plus the `.lig`
grammar's own `lig.lig`), the hand-written `Frontend.parseLig` and the generated
`Frontend.parseLigGen` must produce the same `Surface` up to source spans. Spans
differ by design: the hand parser records byte offsets (used by the LSP
diagnostics engine), while the generated parser produces `Span.dummy` because the
token stream carries no positions. Code generation does not read spans, so
agreement-up-to-spans is exactly the property the generator needs.

Run with `lake exe lig-bootstrap-test`.
-/


public section

open Frontend

private def stripElem (e : Elem) : Elem := { e with span := Span.dummy }
private def stripAlt (a : Alt) : Alt :=
  { a with actionSpan := Span.dummy, elems := a.elems.map stripElem }
private def stripRule (r : Rule) : Rule :=
  { r with span := Span.dummy, alts := r.alts.map stripAlt }
private def stripLexRule (lr : LexerRule) : LexerRule := { lr with span := Span.dummy }
private def stripMode (m : LexerMode) : LexerMode :=
  { m with span := Span.dummy, rules := m.rules.map stripLexRule }
private def stripLexer (l : LexerSpec) : LexerSpec :=
  { l with span := Span.dummy, modes := l.modes.map stripMode }
private def stripTok (t : TokenDecl) : TokenDecl := { t with span := Span.dummy }

/-- All spans reset to dummy, so two `Surface`s compare by structure only. -/
def stripSpans (s : Surface) : Surface :=
  { s with
    tokens := s.tokens.map stripTok,
    rules := s.rules.map stripRule,
    lexer := s.lexer.map stripLexer }

private def norm : Except String Surface → String
  | .ok s => toString (repr (stripSpans s))
  | .error e => s!"ERROR {e}"

def ligFiles : List String := [
  "test/calc/calc.lig", "test/imp/imp.lig", "test/cedar/cedar.lig",
  "test/cedarschema/CedarSchema.lig", "test/c99/c99.lig",
  "test/rustactions/rustactions.lig", "test/rustactions/rustarena.lig",
  "LeanParserGenerator/Frontend/lig.lig" ]

/-- A grammar around one rule, for the shapes of `!!rust{…}` that the fixtures do not cover. -/
private def withRule (rule : String) : String :=
  "%header {\n}\n%tokentype Tok\n%token A B\n%token <Nat> N\n%token EOF\n%eof EOF\n%start s\n%%\n" ++ rule

/-- Inline cases: the hand-written frontend and the generated one must agree on them. -/
def edgeCases : List (String × String) := [
  ("rust type and action on the next lines",
    withRule "s :: Nat !!rust{u64}\n  | n=N { n }\n    !!rust{ n }\n"),
  ("comment between the Lean and the Rust action",
    withRule "s :: Nat !!rust{u64}\n  | n=N { n }\n    -- the Rust counterpart\n    !!rust{ n }\n"),
  ("nested braces and a string in the Rust text",
    withRule "s :: Nat !!rust{u64}\n  | n=N { n } !!rust{ if n > 0 { match n { _ => { n } } } else { \"x\".len() as u64 } }\n"),
  ("an empty alternative with a Rust action",
    withRule "s :: Nat !!rust{u64}\n  | { 0 } !!rust{ 0 }\n  | n=N { n } !!rust{ n }\n"),
  ("a Rust type with generics and a lifetime",
    withRule "s :: List Nat !!rust{std::collections::VecDeque<&'a u64>}\n  | { [] } !!rust{ Default::default() }\n"),
  ("rust_ctx and rust_list options (Rust paths as values)",
    "%header {\n}\n%option rust_ctx crate::ast::Arena\n%option rust_list crate::ast::lists\n%tokentype Tok\n%token A\n%token EOF\n%eof EOF\n%start s\n%%\ns :: Nat !!rust{u64}\n  | A { 0 } !!rust{ 0 }\n"),
  ("no Rust text at all",
    withRule "s :: Nat\n  | n=N { n }\n"),
  ("Rust action on one alternative only",
    withRule "s :: Nat\n  | n=N { n } !!rust{ n }\n  | A { 0 }\n") ]

def main : IO UInt32 := do
  let mut failed := 0
  for (name, src) in edgeCases do
    let hand := norm (parseLig src)
    let gen := norm (parseLigGen src)
    -- Two errors would also compare equal, so the case must parse.
    if hand == gen && !hand.startsWith "ERROR" then
      IO.println s!"OK   {name}"
    else
      failed := failed + 1
      IO.println s!"DIFF {name}\n  hand: {hand.take 300}\n  gen:  {gen.take 300}"
  for f in ligFiles do
    let src ← IO.FS.readFile f
    let hand := norm (parseLig src)
    let gen := norm (parseLigGen src)
    if hand == gen then
      IO.println s!"OK   {f}"
    else
      failed := failed + 1
      IO.println s!"DIFF {f}"
  if failed == 0 then
    IO.println s!"bootstrap agreement: {ligFiles.length} grammars agree (modulo spans)"
    return 0
  else
    IO.eprintln s!"bootstrap agreement FAILED: {failed} grammar(s) differ"
    return 1
