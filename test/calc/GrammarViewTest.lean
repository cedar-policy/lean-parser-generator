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
public import calc.CalcVerified
meta import calc.CalcVerified
meta import LeanParserGenerator.Runtime.GrammarView


public section

open Runtime
open CalcVerified

/-! The inspectable view pins the exact augmented calculator grammar users audit. -/

#guard verifiedGrammarView.terminals.map (fun terminal =>
    (terminal.index, terminal.name, terminal.semanticType)) == [
  (0, "PLUS", "Unit"),
  (1, "TIMES", "Unit"),
  (2, "LPAR", "Unit"),
  (3, "RPAR", "Unit"),
  (4, "DIV", "Unit"),
  (5, "NUM", "Int"),
  (6, "EOF", "Unit"),
  (7, "$", "Unit")]

#guard verifiedGrammarView.nonterminals.map (fun nonterminal =>
    (nonterminal.index, nonterminal.name, nonterminal.semanticType)) == [
  (0, "expr", "Int"),
  (1, "term", "Int"),
  (2, "factor", "Int"),
  (3, "S'", "Int")]

#guard verifiedGrammarView.productions.map (fun production =>
    (production.index, production.lhs, production.rhs, production.rhsBinders,
      production.actionSource, production.semanticAction)) == [
  (0, 0, [.nonterminal 0, .terminal 0, .nonterminal 1],
    [some "e", none, some "t"], "e + t", "semanticAction0"),
  (1, 0, [.nonterminal 1], [some "t"], "t", "semanticAction1"),
  (2, 1, [.nonterminal 1, .terminal 1, .nonterminal 2],
    [some "t", none, some "f"], "t * f", "semanticAction2"),
  (3, 1, [.nonterminal 1, .terminal 4, .nonterminal 2],
    [some "t", none, some "f"], "t / f", "semanticAction3"),
  (4, 1, [.nonterminal 2], [some "f"], "f", "semanticAction4"),
  (5, 2, [.terminal 2, .nonterminal 0, .terminal 3],
    [none, some "e", none], "e", "semanticAction5"),
  (6, 2, [.terminal 5], [some "n"], "n", "semanticAction6"),
  (7, 3, [.nonterminal 0, .terminal 7],
    [some "x", none], "x", "semanticAction7")]

#guard verifiedGrammarView.tokenMappings.map (fun mapping =>
    (mapping.token, mapping.terminal)) == [
  ("PLUS", 0), ("TIMES", 1), ("LPAR", 2), ("RPAR", 3),
  ("DIV", 4), ("NUM", 5), ("EOF", 7)]

#guard verifiedGrammarView.userStartNonterminal == 0 &&
  verifiedGrammarView.startNonterminal == 3 &&
  verifiedGrammarView.eofToken == "EOF" &&
  verifiedGrammarView.eofTerminal == 7 &&
  verifiedGrammarView.augmentedTerminal == 7 &&
  verifiedGrammarView.augmentedNonterminal == 3 &&
  verifiedGrammarView.augmentedProduction == 7

example : verifiedGrammarViewStructuralCheck verifiedGrammarView = true :=
  verifiedGrammarView_agrees.1

example : ∀ token : Tok,
    verifiedGrammarView.tokenTerminal (tokenName' token) = some (tokenTerm' token).val :=
  verifiedGrammarView_agrees.2.2

/-- Dropping a production makes a readable view disagree with the emitted signature. -/
def corruptedGrammarView : Runtime.VerifiedGrammarView :=
  { verifiedGrammarView with productions := verifiedGrammarView.productions.drop 1 }

#guard verifiedGrammarViewStructuralCheck corruptedGrammarView = false

#guard verifiedGrammarView.renderBNF ==
  "%terminal [0] PLUS : Unit\n" ++
  "%terminal [1] TIMES : Unit\n" ++
  "%terminal [2] LPAR : Unit\n" ++
  "%terminal [3] RPAR : Unit\n" ++
  "%terminal [4] DIV : Unit\n" ++
  "%terminal [5] NUM : Int\n" ++
  "%terminal [6] EOF : Unit\n" ++
  "%terminal [7] $ : Unit\n" ++
  "%nonterminal [0] expr : Int\n" ++
  "%nonterminal [1] term : Int\n" ++
  "%nonterminal [2] factor : Int\n" ++
  "%nonterminal [3] S' : Int\n" ++
  "%start [3] S'\n" ++
  "%user-start [0] expr\n" ++
  "%eof-token EOF -> [7] $\n\n" ++
  "[0] expr ::= e:expr PLUS t:term    { e + t }  -- semanticAction0\n" ++
  "[1] expr ::= t:term    { t }  -- semanticAction1\n" ++
  "[2] term ::= t:term TIMES f:factor    { t * f }  -- semanticAction2\n" ++
  "[3] term ::= t:term DIV f:factor    { t / f }  -- semanticAction3\n" ++
  "[4] term ::= f:factor    { f }  -- semanticAction4\n" ++
  "[5] factor ::= LPAR e:expr RPAR    { e }  -- semanticAction5\n" ++
  "[6] factor ::= n:NUM    { n }  -- semanticAction6\n" ++
  "[7] S' ::= x:expr $    { x }  -- semanticAction7"

#guard (verifiedGrammarView.renderMarkdown.splitOn "\n").contains
  "| 7 | S' | expr $ | semanticAction7 |"
