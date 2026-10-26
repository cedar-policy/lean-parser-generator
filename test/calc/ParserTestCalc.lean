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
public import calc.CalcLexer
public import calc.CalcParser
-- `native_decide`/`#eval` reduce the generated parser & lexer, so they are meta-imported.
meta import calc.CalcLexer
meta import calc.CalcParser

public section

open CalcParser

/-! End-to-end calculator parser tests. The token type and lexer are generated
into `CalcLexer` from `calc.lig`'s `%token`/`%lexer` (docs/DESIGN.md §9); this test
uses that generated API. Generated artifact instructions are in `test/README.md`. -/

/-- Full evaluator: lex the string to tokens (the lexer emits `EOF`), then parse. -/
def eval (input : String) : Option Int := do
  let toks ← (CalcLexer.tokenize input).toOption
  CalcParser.parse toks

/-- Wrap bare tokens with dummy spans to call the positioned parser directly. -/
private def parseBare (toks : List Tok) : Option Int :=
  CalcParser.parse (toks.map Runtime.Positioned.dummy)

/-- `(bare token list, expected result)`. Positions are irrelevant here. -/
private def tokenCases : List (List Tok × Option Int) :=
  [ ([.NUM 2, .PLUS, .NUM 3, .TIMES, .NUM 4, .EOF], some 14),
    ([.LPAR, .NUM 2, .PLUS, .NUM 3, .RPAR, .TIMES, .NUM 4, .EOF], some 20),
    ([.NUM 7, .EOF], some 7),
    ([.NUM 2, .PLUS, .EOF], none) ]

#guard tokenCases.all (fun (toks, expected) => parseBare toks == expected)

#guard eval "2 + 3 * 4"       = some 14
#guard eval "(2 + 3) * 4"     = some 20
#guard eval "2 * (3 + 4) * 5" = some 70
#guard eval "1 + 2 + 3 + 4"   = some 10
#guard eval "7"               = some 7
#guard eval "2 +"             = none

/-- The generated calc lexer's tables were validated offline (`native_decide`),
    and its scanner is proved to compute the derivative-defined maximal munch. -/
example : Lexer.validate CalcLexer.rules0 CalcLexer.dfa0 CalcLexer.cert0 = true :=
  CalcLexer.validated0

example (cs : List Char) :
    Lexer.DFA.scan CalcLexer.dfa0 cs = Lexer.fusedScan CalcLexer.rules0 cs 0 none :=
  CalcLexer.scanSound0 cs
