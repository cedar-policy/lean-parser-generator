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

import Kernel.ParseBody
import Spec.Compose

/-!
The kernel's `parse`, called with tables that are a Lean `FlatTable`, runs that table.

`rowsOf` reads the Aeneas arrays as `Spec.RustRows`. If `RustRows.wfCheck` holds (the
grammar's instance decides it), the conditions `KWf` of `parse_correct` hold, and
`parse_lean` adds to `parse_correct` that the run of the machine is the run of the Lean tree
table on the Lean input, with the token indices replaced by the token values.
-/

open Aeneas Aeneas.Std Result
open lpg_kernel

namespace lpg_kernel.Proof

/-- The Aeneas tables as lists of numbers. -/
def rowsOf {NT NN S P : Usize} (action : Array (Array U16 NT) S)
    (goto : Array (Array U16 NN) S) (default_reduce : Array U16 S)
    (lhs rhs_len : Array U16 P) (eof : U16) : Spec.RustRows where
  action := action.val.map fun r => r.val.map (·.val)
  goto := goto.val.map fun r => r.val.map (·.val)
  defRed := default_reduce.val.map (·.val)
  lhs := lhs.val.map (·.val)
  rhs := rhs_len.val.map (·.val)
  eof := eof.val
  nn := NN.val

theorem cell2_eq {m n : Usize} (a : Array (Array U16 n) m) (i j d : Nat) :
    cell2 a i j d = Spec.rowCell (a.val.map fun r => r.val.map (·.val)) i j d := by
  unfold cell2 Spec.rowCell
  cases h : a.val[i]? with
  | none => simp [h]
  | some r => simp [h]

theorem cell1_eq {n : Usize} (a : Array U16 n) (i d : Nat) :
    cell1 a i d = ((a.val.map (·.val))[i]?).getD d := by
  unfold cell1
  cases h : a.val[i]? with
  | none => simp [h]
  | some r => simp [h]

theorem tablesOf_eq {NT NN S P : Usize} (action : Array (Array U16 NT) S)
    (goto : Array (Array U16 NN) S) (default_reduce : Array U16 S)
    (lhs rhs_len : Array U16 P) (eof : U16) :
    tablesOf action goto default_reduce lhs rhs_len eof =
      (rowsOf action goto default_reduce lhs rhs_len eof).tables := by
  have hS : action.val.length = S.val := Array.property action
  simp only [tablesOf, Spec.RustRows.tables, rowsOf, List.length_map, hS]
  congr 1
  · funext s t; exact cell2_eq _ _ _ _
  · funext s n; exact cell2_eq _ _ _ _
  · funext s; exact cell1_eq _ _ _
  · funext p; exact cell1_eq _ _ _
  · funext p; exact cell1_eq _ _ _

/-- The well-formedness check of the rows gives the kernel's conditions. -/
theorem kwf_of_check {NT NN S P : Usize} (action : Array (Array U16 NT) S)
    (goto : Array (Array U16 NN) S) (default_reduce : Array U16 S)
    (lhs rhs_len : Array U16 P) (eof : U16)
    (hwf : (rowsOf action goto default_reduce lhs rhs_len eof).Wf S.val NT.val NN.val P.val)
    (hflag : NT.val ≤ Spec.prodFlag ∧ P.val ≤ Spec.prodFlag) :
    KWf action goto default_reduce lhs rhs_len where
  hasStart := hwf.start
  prods := hflag.2
  terms := hflag.1
  action := by
    intro s t r x hr hx
    have hrm : r.val.map (·.val) ∈ (rowsOf action goto default_reduce lhs rhs_len eof).action :=
      List.mem_map.mpr ⟨r, List.mem_of_getElem? hr, rfl⟩
    have hxm : x.val ∈ r.val.map (·.val) := List.mem_map.mpr ⟨x, List.mem_of_getElem? hx, rfl⟩
    have hok := (hwf.actRows _ hrm).2 _ hxm
    simp only [Spec.actOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq, beq_iff_eq] at hok
    omega
  goto := by
    intro s n r x hr hx
    have hrm : r.val.map (·.val) ∈ (rowsOf action goto default_reduce lhs rhs_len eof).goto :=
      List.mem_map.mpr ⟨r, List.mem_of_getElem? hr, rfl⟩
    have hxm : x.val ∈ r.val.map (·.val) := List.mem_map.mpr ⟨x, List.mem_of_getElem? hx, rfl⟩
    exact (hwf.gotoRows _ hrm).2 _ hxm
  defaultReduce := by
    intro s x hx
    exact hwf.defRed _ (List.mem_map.mpr ⟨x, List.mem_of_getElem? hx, rfl⟩)
  lhs := by
    intro p x hx
    have := hwf.lhs _ (List.mem_map.mpr ⟨x, List.mem_of_getElem? hx, rfl⟩)
    rw [← hwf.nn] at this
    exact this

theorem fuel_spec (hplat : System.Platform.numBits = 64) : FUEL ⦃ x => x.val = 2 ^ 62 ⦄ := by
  unfold FUEL
  have : Usize.numBits = 64 := by simp [Usize.numBits, hplat]
  step*

/-- **The kernel's `parse` runs the Lean table.** For Rust tables that pass the check of
    `wfCheck` and are the automaton of the Lean `FlatTable` `f`, and tokens whose terminals are
    those of `input`: `parse` ends as the machine (`ResRel`, the final stack and nodes), the
    machine's end corresponds to a run `R` of `Exec` on the Rust tree table (`RunSim`, with
    spans), and the same number of steps of the Lean tree table on `input` is `R` with each
    token index replaced by the token's value. -/
theorem parse_lean {W : Type} {NT NN S P : Usize} (tokens : Slice Token)
    (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (fuel : Usize) (hfuel : fuel.val ≤ 2 ^ 62) (hplat : System.Platform.numBits = 64)
    (f : Runtime.Exec.FlatTable W) (input : List (Nat × W))
    (hwf : (rowsOf action goto default_reduce lhs rhs_len eof).Wf S.val NT.val NN.val P.val)
    (hflag : NT.val ≤ Spec.prodFlag ∧ P.val ≤ Spec.prodFlag)
    (hsame : ∀ (e : Nat) (sem : Nat → List Nat → Nat),
      Spec.SameAutomaton ((rowsOf action goto default_reduce lhs rhs_len eof).tables.exec e sem)
        f.toExecTable S.val NT.val NN.val P.val)
    (hterms : ∀ t ∈ tokens.val, t.term.val < NT.val)
    (hin : input.map (·.1) = tokens.val.map (·.term.val)) :
    parse tokens stack nodes action goto default_reduce lhs rhs_len eof fuel ⦃
      res stack' nodes' =>
      ∃ (stop : Spec.MStop) (stk : List Spec.MEntry) (nd : List Spec.MNode)
        (R : Runtime.Exec.Result (Spec.Tree Nat) ⊕
          (Runtime.Exec.Stack (Spec.Tree Nat) × List (Nat × Spec.Tree Nat))),
        ResRel stop res ∧ stack'.val.map entryNat = stk ∧ nodes'.val.map nodeNat = nd ∧
        Spec.RunSim (tokens.val.map tokNat) (stop, stk, nd) R ∧
        Spec.stepN (Spec.treeTable f.toExecTable) fuel.val [] (Spec.treeInput input) =
          Spec.mapStep (Spec.Tree.map (Spec.leafVal f.toExecTable input)) R ⦄ := by
  have hk := kwf_of_check action goto default_reduce lhs rhs_len eof hwf hflag
  have htermsN : ∀ t ∈ tokens.val.map tokNat, t.term < NT.val := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hterms t' ht'
  have hmwf : Spec.MWf (confOf tokens action goto default_reduce lhs rhs_len eof) :=
    ⟨htermsN, by simpa [confOf, tablesOf, rowsOf] using hwf.eof, hflag.1⟩
  refine Aeneas.Std.WP.spec_mono
    (parse_correct tokens stack nodes action goto default_reduce lhs rhs_len eof fuel hfuel
      hplat hk hmwf) ?_
  rintro ⟨res, stack', nodes'⟩ ⟨stop, stk, nd, hres, hs, hn, hrun⟩
  refine ⟨stop, stk, nd, _, hres, hs, hn, hrun, ?_⟩
  have hin' : input.map (·.1) = (tokens.val.map tokNat).map (·.term) := by
    rw [hin]; simp [tokNat]
  have := Spec.lean_stepN (rowsOf action goto default_reduce lhs rhs_len eof) f
    (tokens.val.map tokNat) input hwf hsame htermsN hin' fuel.val
  rw [this]
  simp only [confOf, tablesOf_eq]

end lpg_kernel.Proof
