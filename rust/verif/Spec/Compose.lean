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

import Spec.MachineSim
import Spec.TableCheck

/-!
The run of the machine on the Rust tables, related to the run of a Lean table.

`traceTable c` is the tree table of the Rust tables, whose leaves hold token indices. If the
Rust rows are the Lean `FlatTable` (`sameAutomaton_flat`) and the Lean input has the
terminals of the Rust tokens, then `n` steps of the Lean tree table are `n` steps of
`traceTable c` with each index replaced by the value of its token (`leafVal`). With
`run_eq_eval`, this is a statement about `Exec.run` of the Lean table with any semantic
actions.
-/

namespace Spec

open Runtime.Exec

variable {W : Type}

/-- The value of the token at index `k` of `input`, or the end-of-input value past the end. -/
def leafVal (L : ExecTable W) (input : List (Nat × W)) (k : Nat) : W :=
  ((input[k]?).map (·.2)).getD L.eof.2

theorem input_map (L : ExecTable W) :
    ∀ (toks : List MTok) (input : List (Nat × W)) (k : Nat) (g : Nat → W),
      input.map (·.1) = toks.map (·.term) → (∀ i (h : i < input.length), g (k + i) = input[i].2) →
      mapInput (Tree.map g) (traceInputFrom k toks) = treeInput input := by
  intro toks
  induction toks with
  | nil =>
    intro input k g h _
    cases input with
    | nil => rfl
    | cons _ _ => simp at h
  | cons t ts ih =>
    intro input k g h hg
    cases input with
    | nil => simp at h
    | cons x xs =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hx := hg 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hx
      simp only [traceInputFrom, mapInput, treeInput, List.map_cons, Tree.map, hx, h1] at ih ⊢
      congr 1
      exact ih xs (k + 1) g h2 (fun i hi => by
        have := hg (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)

theorem terms_lt {toks : List MTok} {NT : Nat} (h : ∀ t ∈ toks, t.term < NT) :
    ∀ k, ∀ e ∈ traceInputFrom k toks, e.1 < NT := by
  induction toks with
  | nil => intro k e he; simp [traceInputFrom] at he
  | cons t ts ih =>
    intro k e he
    simp only [traceInputFrom, List.mem_cons] at he
    rcases he with rfl | he
    · exact h t (List.mem_cons_self ..)
    · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) (k + 1) e he

/-- **The Rust tables run as the Lean table.** If the Rust rows `r` are well-formed and are
    the Lean `FlatTable` `f`, and `input` has the terminals of the tokens, then `n` steps of
    the Lean tree table on `input` are `n` steps of `traceTable` on the tokens, with each
    token index replaced by the token's value. -/
theorem lean_stepN (r : RustRows) (f : FlatTable W) {S NT NN P : Nat}
    (toks : List MTok) (input : List (Nat × W))
    (hwf : r.Wf S NT NN P)
    (hsame : ∀ (e : Nat) (sem : Nat → List Nat → Nat),
      SameAutomaton (r.tables.exec e sem) f.toExecTable S NT NN P)
    (hterms : ∀ t ∈ toks, t.term < NT) (hin : input.map (·.1) = toks.map (·.term)) (n : Nat) :
    stepN (treeTable f.toExecTable) n [] (treeInput input) =
      mapStep (Tree.map (leafVal f.toExecTable input))
        (stepN (traceTable ⟨r.tables, NT, toks⟩) n [] (traceInputFrom 0 toks)) := by
  have hlen : input.length = toks.length := by
    have := congrArg List.length hin; simpa using this
  have hA := agree_tree (hsame toks.length (fun _ _ => 0)) (leafVal f.toExecTable input)
    (by simp [leafVal, RustTables.exec, hlen])
  have hT := tblWf_tree (RustRows.tblWf hwf toks.length (fun _ _ => 0))
  have := stepN_sim hT hA n [] (traceInputFrom 0 toks) (by simp) (terms_lt hterms 0)
  have hi : mapInput (Tree.map (leafVal f.toExecTable input)) (traceInputFrom 0 toks) =
      treeInput input := by
    apply input_map f.toExecTable toks input 0 _ hin
    intro i hi
    simp [leafVal, List.getElem?_eq_getElem hi]
  rw [hi] at this
  simpa [mapStack, traceTable] using this

end Spec
