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

import LeanParserGenerator.Runtime.Exec

/-!
`Exec.run` counts its fuel in a logarithmic way (`parseFix`). The Rust kernel counts steps.
`stepN n` is `n` steps of `Exec.step`, and `parseFix_eq_stepN` says `parseFix logN` is
`2 ^ logN` steps, so a statement about step counts is a statement about `Exec.run`.
-/

namespace Spec

open Runtime.Exec

variable {V : Type}

/-- At most `n` steps of `Exec.step`: the result if a step produces one, otherwise the stack
    and the input after `n` steps. -/
def stepN (tbl : ExecTable V) :
    Nat → Stack V → List (Nat × V) → Result V ⊕ (Stack V × List (Nat × V))
  | 0, stk, input => .inr (stk, input)
  | n + 1, stk, input =>
    match step tbl stk input with
    | .inl r => .inl r
    | .inr (stk', input') => stepN tbl n stk' input'

theorem stepN_add (tbl : ExecTable V) (a b : Nat) (stk : Stack V) (input : List (Nat × V)) :
    stepN tbl (a + b) stk input =
      match stepN tbl a stk input with
      | .inl r => .inl r
      | .inr (stk', input') => stepN tbl b stk' input' := by
  induction a generalizing stk input with
  | zero => simp [stepN]
  | succ n ih =>
    rw [show n + 1 + b = (n + b) + 1 by omega]
    simp only [stepN]
    cases step tbl stk input with
    | inl r => rfl
    | inr si => exact ih _ _

/-- `parseFix logN` is `2 ^ logN` steps. -/
theorem parseFix_eq_stepN (tbl : ExecTable V) (logN : Nat) (stk : Stack V)
    (input : List (Nat × V)) :
    parseFix tbl stk input logN = stepN tbl (2 ^ logN) stk input := by
  induction logN generalizing stk input with
  | zero => simp [parseFix, stepN]; cases step tbl stk input <;> rfl
  | succ n ih =>
    simp only [parseFix, ih]
    rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by omega, stepN_add]
    cases stepN tbl (2 ^ n) stk input with
    | inl r => rfl
    | inr si => obtain ⟨s, i⟩ := si; rfl

/-- `Exec.run` in terms of step counts: the result of the first `2 ^ logN` steps, or
    `timeout`. -/
theorem run_eq_stepN (tbl : ExecTable V) (input : List (Nat × V)) (logN : Nat) :
    run tbl input logN =
      match stepN tbl (2 ^ logN) [] input with
      | .inl r => r
      | .inr _ => .timeout := by
  simp only [run, parseFix_eq_stepN]
  cases stepN tbl (2 ^ logN) [] input <;> rfl

end Spec
