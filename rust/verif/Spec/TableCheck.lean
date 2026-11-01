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

import Spec.Tables
import Spec.TableAgree

/-!
The Rust tables of a grammar, as lists of numbers, and the checks that a grammar's instance
runs by computation in the kernel (`decide +kernel`).

* `RustRows` is the content of the Rust arrays: rows of the action and goto tables, and the
  three per-state or per-production tables. `RustRows.tables` reads them as the kernel does.
* `RustRows.wfCheck` checks that the tables stay inside their rectangle (`TblWf`).
* `sameAutomaton_flat` turns equalities of lists between the Rust rows and the arrays of a
  Lean `FlatTable` into `SameAutomaton`. Each equality is decided by the kernel.
* The Lean generator writes large tables compressed: the non-default cells, which
  `buildDense` expands. Evaluating `buildDense` in the kernel is quadratic, so `mergeEq`
  compares the Rust rows with the cells directly, and `buildDense_toList` says what that
  means for the expanded array.
-/

namespace Spec

open Runtime.Exec

variable {V W : Type}

/-! ### The Rust tables as lists -/

/-- The content of a grammar's Rust tables. `nn` is the number of nonterminals: the kernel's
    model reads `lhs` past its end as `nn`, a column that no goto row has. -/
structure RustRows where
  action : List (List Nat)
  goto : List (List Nat)
  defRed : List Nat
  lhs : List Nat
  rhs : List Nat
  eof : Nat
  nn : Nat

/-- A cell of a table of rows, `d` out of range. -/
def rowCell (rows : List (List Nat)) (s t d : Nat) : Nat :=
  ((rows[s]?).bind (·[t]?)).getD d

/-- The tables as the kernel reads them. -/
def RustRows.tables (r : RustRows) : RustTables where
  numStates := r.action.length
  eof := r.eof
  action := fun s t => rowCell r.action s t 0
  goto := fun s n => rowCell r.goto s n 0
  defaultReduce := fun s => (r.defRed[s]?).getD noneCell
  lhs := fun p => (r.lhs[p]?).getD r.nn
  rhsLen := fun p => (r.rhs[p]?).getD 0

/-- An action cell names a state or a production in range. -/
def actOk (S P x : Nat) : Bool :=
  (x % 2 != 1 || x / 2 < S) && (x == 0 || x % 2 != 0 || x / 2 - 1 < P)

/-- The tables stay inside the rectangle of `S` states, `NT` terminals, `NN` nonterminals and
    `P` productions, and the sizes are those. -/
def RustRows.wfCheck (r : RustRows) (S NT NN P : Nat) : Bool :=
  0 < S && r.eof < NT && r.nn == NN &&
  r.action.length == S && r.action.all (fun row => row.length == NT && row.all (actOk S P)) &&
  r.goto.length == S &&
    r.goto.all (fun row => row.length == NN && row.all (fun x => x == noneCell || x < S)) &&
  r.defRed.length == S && r.defRed.all (fun x => x == noneCell || x < P) &&
  r.lhs.length == P && r.lhs.all (· < NN) && r.rhs.length == P

/-- What `wfCheck` says, as propositions. -/
structure RustRows.Wf (r : RustRows) (S NT NN P : Nat) : Prop where
  start : 0 < S
  eof : r.eof < NT
  nn : r.nn = NN
  actLen : r.action.length = S
  actRows : ∀ row ∈ r.action, row.length = NT ∧ ∀ x ∈ row, actOk S P x = true
  gotoLen : r.goto.length = S
  gotoRows : ∀ row ∈ r.goto, row.length = NN ∧ ∀ x ∈ row, x = noneCell ∨ x < S
  defRedLen : r.defRed.length = S
  defRed : ∀ x ∈ r.defRed, x = noneCell ∨ x < P
  lhsLen : r.lhs.length = P
  lhs : ∀ x ∈ r.lhs, x < NN
  rhsLen : r.rhs.length = P

theorem RustRows.wf_of_check {r : RustRows} {S NT NN P : Nat} (h : r.wfCheck S NT NN P = true) :
    r.Wf S NT NN P := by
  simp only [RustRows.wfCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, fun row hr => ⟨(h5 row hr).1, (h5 row hr).2⟩, h6, h7, h8, h9, h10, h11,
    h12⟩

theorem rowCell_of_lt {rows : List (List Nat)} {s t d W : Nat} (hs : s < rows.length)
    (hw : ∀ row ∈ rows, row.length = W) (ht : t < W) :
    ∃ row x, row ∈ rows ∧ x ∈ row ∧ rowCell rows s t d = x := by
  have hrow := List.getElem_mem hs
  have ht' : t < (rows[s]'hs).length := by rw [hw _ hrow]; exact ht
  exact ⟨_, _, hrow, List.getElem_mem ht',
    by simp [rowCell, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem ht']⟩

theorem RustRows.tblWf {r : RustRows} {S NT NN P : Nat} (h : r.Wf S NT NN P) (e : V)
    (sem : Nat → List V → V) : TblWf (r.tables.exec e sem) S NT NN P where
  start := h.start
  eof := h.eof
  shift := by
    intro s t s' hs ht ha
    have hs' : s < r.action.length := by rw [h.actLen]; exact hs
    obtain ⟨row, x, hm, hx, hc⟩ :=
      rowCell_of_lt (d := 0) hs' (fun row hr => (h.actRows row hr).1) ht
    have hok := (h.actRows _ hm).2 _ hx
    simp only [RustTables.exec, RustRows.tables, hc, decodeAct] at ha
    simp only [actOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      beq_iff_eq] at hok
    split at ha
    · cases ha
    · split at ha
      · cases ha; omega
      · cases ha
  reduce := by
    intro s t p hs ht ha
    have hs' : s < r.action.length := by rw [h.actLen]; exact hs
    obtain ⟨row, x, hm, hx, hc⟩ :=
      rowCell_of_lt (d := 0) hs' (fun row hr => (h.actRows row hr).1) ht
    have hok := (h.actRows _ hm).2 _ hx
    simp only [RustTables.exec, RustRows.tables, hc, decodeAct] at ha
    simp only [actOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      beq_iff_eq] at hok
    split at ha
    · cases ha
    · split at ha
      · cases ha
      · cases ha; omega
  goto := by
    intro s n s' hs hn hg
    have hs' : s < r.goto.length := by rw [h.gotoLen]; exact hs
    obtain ⟨row, x, hm, hx, hc⟩ :=
      rowCell_of_lt (d := 0) hs' (fun row hr => (h.gotoRows row hr).1) hn
    have hok := (h.gotoRows _ hm).2 _ hx
    simp only [RustTables.exec, RustRows.tables, hc, decodeOpt] at hg
    split at hg
    · cases hg
    · cases hg; omega
  defRed := by
    intro s p hs hd
    have hs' : s < r.defRed.length := by rw [h.defRedLen]; exact hs
    have hok := h.defRed _ (List.getElem_mem hs')
    simp only [RustTables.exec, RustRows.tables, List.getElem?_eq_getElem hs', Option.getD_some,
      decodeOpt] at hd
    split at hd
    · cases hd
    · cases hd; omega
  lhs := by
    intro p hp
    have hp' : p < r.lhs.length := by rw [h.lhsLen]; exact hp
    simp only [RustTables.exec, RustRows.tables, List.getElem?_eq_getElem hp', Option.getD_some]
    exact h.lhs _ (List.getElem_mem hp')

/-! ### Comparison with a Lean `FlatTable` -/

theorem flatten_getElem? {α : Type} (rows : List (List α)) (W : Nat)
    (hw : ∀ row ∈ rows, row.length = W) (s t : Nat) (hs : s < rows.length) (ht : t < W) :
    rows.flatten[s * W + t]? = (rows[s]?).bind (·[t]?) := by
  induction rows generalizing s with
  | nil => simp at hs
  | cons row rows ih =>
    have hrow : row.length = W := hw row (List.mem_cons_self ..)
    cases s with
    | zero =>
      simp only [List.flatten_cons, Nat.zero_mul, Nat.zero_add, List.getElem?_cons_zero,
        Option.bind_some]
      rw [List.getElem?_append_left (by omega)]
    | succ s =>
      simp only [List.flatten_cons, List.getElem?_cons_succ]
      rw [List.getElem?_append_right (by rw [hrow]; simp [Nat.succ_mul]; omega)]
      rw [show s.succ * W + t - row.length = s * W + t by rw [hrow, Nat.succ_mul]; omega]
      exact ih (fun r hr => hw r (List.mem_cons_of_mem _ hr)) s (by simp at hs; omega)

theorem getD_flat_eq {α : Type} (a : Array α) (rows : List (List Nat)) (dec : Nat → α) (W : Nat)
    (hw : ∀ row ∈ rows, row.length = W) (ha : a.toList = rows.flatten.map dec) (d : α) (e : Nat)
    (s t : Nat) (hs : s < rows.length) (ht : t < W) :
    a.getD (s * W + t) d = dec (rowCell rows s t e) := by
  have h1 := flatten_getElem? rows W hw s t hs ht
  have hrs : t < (rows[s]'hs).length := by rw [hw _ (List.getElem_mem _)]; exact ht
  have hc : rowCell rows s t e = (rows[s]'hs)[t]'hrs := by
    simp [rowCell, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hrs]
  rw [List.getElem?_eq_getElem hs, Option.bind_some, List.getElem?_eq_getElem hrs] at h1
  have h2 : a.toList[s * W + t]? = some (dec ((rows[s]'hs)[t]'hrs)) := by
    rw [ha, List.getElem?_map, h1]; rfl
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h2, hc]
  rfl

theorem getD_list_eq {α : Type} (a : Array α) (xs : List Nat) (dec : Nat → α)
    (ha : a.toList = xs.map dec) (d : α) (e i : Nat) (hi : i < xs.length) :
    a.getD i d = dec ((xs[i]?).getD e) := by
  have h2 : a.toList[i]? = some (dec (xs[i]'hi)) := by
    rw [ha, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h2, List.getElem?_eq_getElem hi]
  rfl

/-- The Rust rows and a Lean `FlatTable` are the same automaton if the Lean arrays are the
    Rust rows, decoded and flattened. -/
theorem sameAutomaton_flat (r : RustRows) (f : FlatTable W) {S NT NN P : Nat}
    (hwf : r.Wf S NT NN P) (e : V) (sem : Nat → List V → V)
    (hstart : f.startState = 0) (heof : f.eof.1 = r.eof) (haw : f.actWidth = NT)
    (hgw : f.gotoWidth = NN)
    (hact : f.actionData.toList = r.action.flatten.map decodeAct)
    (hgoto : f.gotoData.toList = r.goto.flatten.map decodeOpt)
    (hdr : f.defRedData.toList = r.defRed.map decodeOpt)
    (hlhs : f.lhsData.toList = r.lhs) (hlen : f.lenData.toList = r.rhs) :
    SameAutomaton (r.tables.exec e sem) f.toExecTable S NT NN P where
  start := hstart
  eof := heof
  action := by
    intro s t hs ht
    simp only [FlatTable.toExecTable, RustTables.exec, RustRows.tables, haw]
    exact getD_flat_eq _ _ _ _ (fun row hr => (hwf.actRows row hr).1) hact _ _ _ _
      (by rw [hwf.actLen]; exact hs) ht
  goto := by
    intro s n hs hn
    simp only [FlatTable.toExecTable, RustTables.exec, RustRows.tables, hgw]
    exact getD_flat_eq _ _ _ _ (fun row hr => (hwf.gotoRows row hr).1) hgoto _ _ _ _
      (by rw [hwf.gotoLen]; exact hs) hn
  defRed := by
    intro s hs
    simp only [FlatTable.toExecTable, RustTables.exec, RustRows.tables]
    exact getD_list_eq _ _ _ hdr _ _ _ (by rw [hwf.defRedLen]; exact hs)
  lhs := by
    intro p hp
    simp only [FlatTable.toExecTable, RustTables.exec, RustRows.tables]
    have := getD_list_eq f.lhsData r.lhs id (by simpa using hlhs) 0 r.nn p
      (by rw [hwf.lhsLen]; exact hp)
    simpa using this
  rhs := by
    intro p hp
    simp only [FlatTable.toExecTable, RustTables.exec, RustRows.tables]
    have := getD_list_eq f.lenData r.rhs id (by simpa using hlen) 0 0 p
      (by rw [hwf.rhsLen]; exact hp)
    simpa using this

/-! ### Compressed Lean tables -/

/-- The generator's `buildDense`, which each compressed parser module defines (the grammar's
    instance proves its copy equal to this one by `rfl`). -/
def buildDense {α : Type} (n : Nat) (dflt : α) (cells : Array (Nat × α)) : Array α := Id.run do
  let mut a : Array α := Array.replicate n dflt
  for (i, v) in cells do a := a.set! i v
  return a

/-- `xs` is the dense list that the sorted `cells` describe, from index `i` on, with `d`
    elsewhere. -/
def mergeEq {α : Type} [DecidableEq α] (d : α) : List α → List (Nat × α) → Nat → Bool
  | [], cs, _ => cs.isEmpty
  | x :: xs, [], i => x == d && mergeEq d xs [] (i + 1)
  | x :: xs, (j, v) :: cs, i =>
    if j = i then x == v && mergeEq d xs cs (i + 1)
    else i < j && x == d && mergeEq d xs ((j, v) :: cs) (i + 1)

theorem buildDense_eq_foldl {α : Type} (n : Nat) (d : α) (cells : Array (Nat × α)) :
    buildDense n d cells =
      cells.toList.foldl (fun a (c : Nat × α) => a.set! c.1 c.2) (Array.replicate n d) := by
  simp [buildDense, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]

theorem mergeEq_foldl {α : Type} [DecidableEq α] (d : α) :
    ∀ (xs : List α) (cs : List (Nat × α)) (i : Nat) (a : Array α),
      a.size = i + xs.length → a.toList.drop i = List.replicate xs.length d →
      mergeEq d xs cs i = true →
      (cs.foldl (fun a (c : Nat × α) => a.set! c.1 c.2) a).toList = a.toList.take i ++ xs := by
  intro xs
  induction xs with
  | nil =>
    intro cs i a hsz _ h
    cases cs with
    | nil =>
      simp only [List.foldl_nil, List.append_nil]
      rw [List.take_of_length_le (by simp at hsz ⊢; omega)]
    | cons c cs => simp [mergeEq] at h
  | cons x xs ih =>
    intro cs i a hsz hdrop h
    have hai : a.toList[i]? = some d := by
      have : (a.toList.drop i)[0]? = some d := by rw [hdrop]; simp
      simpa using this
    have hdrop1 : a.toList.drop (i + 1) = List.replicate xs.length d := by
      rw [← List.drop_drop, hdrop]; simp
    have htake : a.toList.take (i + 1) = a.toList.take i ++ [d] := by
      rw [List.take_add_one, hai]; rfl
    cases cs with
    | nil =>
      simp only [mergeEq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih [] (i + 1) a (by simp at hsz ⊢; omega) hdrop1 h
      simp only [List.foldl_nil] at this ⊢
      rw [htake] at this
      simpa using this
    | cons c cs =>
      obtain ⟨j, v⟩ := c
      simp only [mergeEq] at h
      split at h
      · rename_i hj
        subst hj
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        have hlt : j < a.size := by simp at hsz; omega
        have hsz' : (a.set! j x).size = (j + 1) + xs.length := by simp at hsz ⊢; omega
        have hdrop' : (a.set! j x).toList.drop (j + 1) = List.replicate xs.length d := by
          simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
          rw [List.drop_set_of_lt (by omega)]
          exact hdrop1
        have := ih cs (j + 1) (a.set! j x) hsz' hdrop' h
        simp only [List.foldl_cons]
        rw [this]
        simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
        rw [List.take_add_one, List.getElem?_set_self (by simpa using hlt),
          List.take_set_of_le (by omega)]
        simp
      · rename_i hj
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨_, rfl⟩, h⟩ := h
        have := ih ((j, v) :: cs) (i + 1) a (by simp at hsz ⊢; omega) hdrop1 h
        rw [this, htake]; simp

/-- What `mergeEq` says about `buildDense`. -/
theorem buildDense_toList {α : Type} [DecidableEq α] (n : Nat) (d : α) (cells : Array (Nat × α))
    (xs : List α) (hn : n = xs.length) (h : mergeEq d xs cells.toList 0 = true) :
    (buildDense n d cells).toList = xs := by
  rw [buildDense_eq_foldl]
  have := mergeEq_foldl d xs cells.toList 0 (Array.replicate n d) (by simp [hn]) (by simp [hn]) h
  simpa using this

end Spec
