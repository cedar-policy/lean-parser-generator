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
public import imp.ImpParser
-- `native_decide`/`#eval` reduce the generated parser & lexer, so they are meta-imported.
meta import imp.ImpParser

public section

open Imp ImpParser

/-! End-to-end IMP parser tests. IMP is in the *hand-written* lexer regime: its
`.lig` has no `%lexer` block, so the token type (`Imp.Tok`) and the lexer are
written by hand and the parser is generated over them. This lexer is an ordinary
recursive Lean function — no generator, no DSL. -/

namespace ImpLex

/-- Is `c` an identifier-continuation character? -/
private def isIdentCont (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Classify an identifier as a keyword token or a plain `ID`. -/
private def kw (s : String) : Tok :=
  match s with
  | "skip"  => .SKIP
  | "if"    => .IF
  | "then"  => .THEN
  | "else"  => .ELSE
  | "while" => .WHILE
  | "do"    => .DO
  | "true"  => .TRUE
  | "false" => .FALSE
  | _       => .ID s

/-- Tokenize IMP source by a direct left-to-right scan (maximal munch on
    identifiers and numbers). Emits a trailing `EOF`. -/
partial def tokenize (input : String) : Option (List Tok) :=
  go input.toList []
where
  go : List Char → List Tok → Option (List Tok)
  | [], acc => some (acc.reverse ++ [.EOF])
  | c :: rest, acc =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then go rest acc
    else if c.isAlpha then
      let (name, rest') := (c :: rest).span isIdentCont
      go rest' (kw (String.ofList name) :: acc)
    else if c.isDigit then
      let (digits, rest') := (c :: rest).span Char.isDigit
      go rest' (.NUM (Int.ofNat (String.ofList digits).toNat!) :: acc)
    else
      match c :: rest with
      | ':' :: '=' :: r => go r (.ASSIGN :: acc)
      | '<' :: '=' :: r => go r (.LE :: acc)
      | '&' :: '&' :: r => go r (.AND :: acc)
      | '=' :: r => go r (.EQ :: acc)
      | '!' :: r => go r (.NOT :: acc)
      | ';' :: r => go r (.SEMI :: acc)
      | '+' :: r => go r (.PLUS :: acc)
      | '-' :: r => go r (.MINUS :: acc)
      | '*' :: r => go r (.TIMES :: acc)
      | '(' :: r => go r (.LPAR :: acc)
      | ')' :: r => go r (.RPAR :: acc)
      | _ => none

end ImpLex

/-- Full evaluator: lex to tokens (with a trailing `EOF`), parse to a `Com`.
    IMP is hand-lexed, so tokens carry no real positions: wrap each with a dummy
    span to feed the positioned parser API. -/
def parseImp (input : String) : Option Com := do
  let toks ← ImpLex.tokenize input
  ImpParser.parse (toks.map Runtime.Positioned.dummy)

#guard parseImp "x := 1" = some (.assign "x" (.num 1))
#guard parseImp "y := 1 + 2 * 3" = some (.assign "y" (.add (.num 1) (.mul (.num 2) (.num 3))))
#guard parseImp "skip ; skip ; x := 0"
  = some (.seq .skip (.seq .skip (.assign "x" (.num 0))))
#guard parseImp "while x <= 10 do ( x := x + 1 )"
  = some (.while (.le (.var "x") (.num 10)) (.assign "x" (.add (.var "x") (.num 1))))
#guard parseImp "if true then ( x := 1 ) else ( x := 2 )"
  = some (.ite .tru (.assign "x" (.num 1)) (.assign "x" (.num 2)))
#guard parseImp "if !false && true then ( skip ) else ( skip )"
  = some (.ite (.and (.not .fls) .tru) .skip .skip)
#guard parseImp "x := 1 +" = none
