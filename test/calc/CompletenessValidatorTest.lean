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


public section

open Calc CalcVerified Runtime Runtime.Grammar

/-!
Regression checks for the generated verified calculator.

Importing `CalcVerified` elaborates both generated validation proofs:
`CalcVerified.safetyValidation` and `CalcVerified.completenessValidation`, then
derives `safety : Safe` and `completeness : Complete`. The examples below also
exercise the explicit-EOF augmented production and its semantic action by kernel
reduction.
-/

example : parse [.NUM 2, .PLUS, .NUM 3, .TIMES, .NUM 4, .EOF] = some 14 := by
  decide

example : parse [.NUM 2, .PLUS, .EOF] = none := by
  decide

/-!
Operational completeness and unambiguity specialize to the generated calculator.
These are compile-time checks that `Runtime.parseComplete` / `Runtime.unambiguity`
apply with the generated `completeness` certificate; they need no hand
constructed parse trees.
-/

/-- Unambiguity of the calculator: any two parse trees of one token list agree on
    their semantic value. Instantiates `Runtime.unambiguity` with the generated
    `completeness` proof. -/
theorem calc_unambiguity (init : automatonInst.InitState)
    {word : List Tok}
    (t1 t2 : ParseTree (G := grammarInst) (.NT (automatonInst.startNt init)) word) :
    ptSem t1 = ptSem t2 := by
  haveI : Inhabited grammarInst.Token := inferInstanceAs (Inhabited Tok)
  exact unambiguity (G := grammarInst) (A := automatonInst) completeness init t1 t2

/-- Operational completeness of the calculator: `Runtime.parseComplete` applies
    with the generated `completeness` proof. The result type (Parsed ⇒ exact
    sem/rest with `ptSize ≤ 2^logN`; Timeout ⇒ `2^logN < ptSize`; Fail/Err
    impossible) is inferred from `parseComplete`. -/
example (init : automatonInst.InitState) (logN : Nat)
    {word : List Tok} (bufEnd : NatStream Tok)
    (tree : ParseTree (G := grammarInst) (.NT (automatonInst.startNt init)) word) :=
  parseComplete (G := grammarInst) (A := automatonInst) completeness init logN bufEnd tree
