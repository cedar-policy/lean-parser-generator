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
import all calc.CalcParser


public section

open Calc CalcVerified Runtime

/-! Regression checks for the generated parser refinement witness.

    The executable parser runs over `Runtime.Positioned Tok`; the verified
    corollaries relate it to the dependent spec on dummy-spanned input (spans are
    diagnostic metadata and do not affect the dependent value). `pos` wraps a bare
    token list with dummy spans. -/

private def pos (ts : List Tok) : List (Runtime.Positioned Tok) :=
  ts.map (fun t => ⟨t, Runtime.Span.dummy⟩)

example (input : List Tok) (logNSteps : Nat) :
    CalcParser.parse (pos input) logNSteps = CalcVerified.parse input logNSteps :=
  parse_eq_dependent input logNSteps

example : CalcParser.parse (pos [.NUM 7]) 20 = CalcVerified.parse [.NUM 7] 20 := by
  simpa [pos] using parse_eq_dependent [.NUM 7] 20


/-! Parser-facing guarantees require no manual refinement/safety/completeness arguments. -/

example (input : List Tok) (logNSteps : Nat) (semantic : Int)
    (accepted : CalcParser.parse (pos input) logNSteps = some semantic) :
    ∃ (word : List Tok) (tree : CalcVerified.ParserStartTree word)
      (rest : Runtime.NatStream Tok),
      CalcVerified.toStream input = Runtime.NatStream.appList word rest ∧
      Runtime.Grammar.ptSem tree = semantic :=
  CalcVerified.parser_sound input logNSteps semantic accepted

example (input : List Tok) (logNSteps : Nat) :
    Runtime.Exec.ResultErrFree (CalcParser.run (pos input) logNSteps) :=
  CalcVerified.parser_err_free input logNSteps

example (input : List Tok) (logNSteps : Nat) (message : String) :
    CalcParser.run (pos input) logNSteps ≠ .err message :=
  CalcVerified.parser_ne_err input logNSteps message

example {word : List Tok} (tree : CalcVerified.ParserStartTree word)
    (logNSteps : Nat) (fuel : Runtime.Grammar.ptSize tree ≤ 2 ^ logNSteps) :
    CalcParser.parse (pos word) logNSteps = some (Runtime.Grammar.ptSem tree) :=
  CalcVerified.parser_complete tree logNSteps fuel

example {word : List Tok} (tree1 tree2 : CalcVerified.ParserStartTree word) :
    Runtime.Grammar.ptSem tree1 = Runtime.Grammar.ptSem tree2 :=
  CalcVerified.parser_unambiguous tree1 tree2
namespace CalcRefinementNegative

/-- A parser whose action table rejects every lookahead cannot refine the verified calculator. -/
def badActionTable : Runtime.Exec.ExecTable CalcParser.VP :=
  { CalcParser.table with action := fun _ _ => .error }

example : CalcVerified.refinementStructuralCheck badActionTable = false := by
  native_decide

/-- A wrong semantic dispatcher cannot reuse the generated refinement proof. -/
def badSemanticTable : Runtime.Exec.ExecTable CalcParser.VP :=
  { CalcParser.table with sem := fun _ _ => (Runtime.Span.dummy, .unit ()) }

/--
error: Type mismatch
  __src✝.semantic_agrees
has type
  ∀ (production : GrammarSig.Production) (values : Refinement.Values (GrammarSig.prodRhsRev production)),
    __src✝.table.sem (__src✝.productionIndex production) (Refinement.Values.encode __src✝.encodeValue values).reverse =
      __src✝.encodeValue (Symbol.NT (GrammarSig.prodLhs production)) (values.apply (Grammar.prodAction production))
but is expected to have type
  ∀ (production : GrammarSig.Production) (values : Refinement.Values (GrammarSig.prodRhsRev production)),
    badSemanticTable.sem (__src✝.productionIndex production)
        (Refinement.Values.encode __src✝.encodeValue values).reverse =
      __src✝.encodeValue (Symbol.NT (GrammarSig.prodLhs production)) (values.apply (Grammar.prodAction production))
-/
#guard_msgs in
def badSemanticRefinement : Runtime.Refinement.ExecRefinement
    (G := CalcVerified.grammarInst) (A := CalcVerified.automatonInst) CalcParser.VP :=
  { CalcVerified.executableRefinement with table := badSemanticTable }

end CalcRefinementNegative
