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

import Kernel.Funs
import Spec.MachineSim

/-!
The body of the loop of `lpg_kernel::parse`, as extracted by Aeneas, is `Spec.mbody`.

`Corr` relates the variables of the Rust loop (vectors of `Entry` and `Node`, `Usize`s, a
`U32`) to the variables of the machine (lists of `Nat`s). `KWf` collects what the tables must
satisfy for the Rust to run without a panic or an overflow: every index it computes is in
range and every number fits its type. The grammar's instance checks it by computation.
-/

open Aeneas Aeneas.Std Result ControlFlow
open lpg_kernel

namespace lpg_kernel.Proof

/-! ### From Aeneas values to numbers -/

def entryNat (e : Entry) : Spec.MEntry := ⟨e.state.val, e.start.val⟩
def nodeNat (n : Node) : Spec.MNode := ⟨n.kind.val, n.start.val, n.«end».val⟩
def tokNat (t : Token) : Spec.MTok := ⟨t.term.val, t.start.val, t.«end».val⟩

/-- The cell `(i, j)` of a table of rows, `d` if it is out of range. -/
def cell2 {m n : Usize} (a : Array (Array U16 n) m) (i j d : Nat) : Nat :=
  (((a.val[i]?).bind fun r => r.val[j]?).map (·.val)).getD d

/-- The cell `i` of a table, `d` if it is out of range. -/
def cell1 {n : Usize} (a : Array U16 n) (i d : Nat) : Nat :=
  ((a.val[i]?).map (·.val)).getD d

/-- The tables the kernel is called with, as numbers. -/
def tablesOf {NT NN S P : Usize} (action : Array (Array U16 NT) S)
    (goto : Array (Array U16 NN) S) (default_reduce : Array U16 S)
    (lhs rhs_len : Array U16 P) (eof : U16) : Spec.RustTables where
  numStates := S.val
  eof := eof.val
  action := fun s t => cell2 action s t 0
  goto := fun s n => cell2 goto s n 0
  defaultReduce := fun s => cell1 default_reduce s Spec.noneCell
  lhs := fun p => cell1 lhs p NN.val
  rhsLen := fun p => cell1 rhs_len p 0

/-- The configuration of the machine that the kernel's arguments denote. -/
def confOf {NT NN S P : Usize} (tokens : Slice Token) (action : Array (Array U16 NT) S)
    (goto : Array (Array U16 NN) S) (default_reduce : Array U16 S)
    (lhs rhs_len : Array U16 P) (eof : U16) : Spec.MConf where
  tables := tablesOf action goto default_reduce lhs rhs_len eof
  nt := NT.val
  toks := tokens.val.map tokNat

/-- What the tables must satisfy for the loop to run without a panic: every state and
    production they name is in range, and the numbers are small enough. Written with lookups
    that may fail, so that it says nothing about indices out of range. (Checked per grammar.) -/
structure KWf {NT NN S P : Usize} (action : Array (Array U16 NT) S)
    (goto : Array (Array U16 NN) S) (default_reduce : Array U16 S)
    (lhs rhs_len : Array U16 P) : Prop where
  /-- There is a state 0. -/
  hasStart : 0 < S.val
  /-- Productions have room for the flag bit that marks them in the trace. -/
  prods : P.val ≤ Spec.prodFlag
  /-- So do terminals. -/
  terms : NT.val ≤ Spec.prodFlag
  /-- A shift goes to a state, a reduce is by a production. -/
  action : ∀ (s t : Nat) (r : Array U16 NT) (x : U16), action.val[s]? = some r → r.val[t]? = some x →
    (x.val % 2 = 1 → x.val / 2 < S.val) ∧ (x.val ≠ 0 → x.val % 2 = 0 → x.val / 2 - 1 < P.val)
  /-- A goto is absent or a state. -/
  goto : ∀ (s n : Nat) (r : Array U16 NN) (x : U16), goto.val[s]? = some r → r.val[n]? = some x →
    x.val = Spec.noneCell ∨ x.val < S.val
  /-- A default reduction is absent or a production. -/
  defaultReduce : ∀ (s : Nat) (x : U16), default_reduce.val[s]? = some x →
    x.val = Spec.noneCell ∨ x.val < P.val
  /-- A production's left-hand side is a nonterminal. -/
  lhs : ∀ (p : Nat) (x : U16), lhs.val[p]? = some x → x.val < NN.val


/-! ### Arithmetic facts -/

/-- Setting the flag bit of a production number is adding the flag. -/
theorem or_flag (x : U16) (hx : x.val < 32768) : (PROD_FLAG ||| x).val = 32768 + x.val := by
  rw [UScalar.val_or]
  have h1 : PROD_FLAG.val = 32768 := by unfold PROD_FLAG; rfl
  have h2 := Nat.two_pow_add_eq_or_of_lt (i := 15) (b := x.val) (by simpa using hx) 1
  rw [h1]
  simpa using h2.symm

theorem cell1_of_get? {n : Usize} (a : Array U16 n) (i d : Nat) (x : U16)
    (h : a.val[i]? = some x) : cell1 a i d = x.val := by
  simp [cell1, h]

theorem cell2_of_get? {m n : Usize} (a : Array (Array U16 n) m) (i j d : Nat) (r : Array U16 n)
    (x : U16) (h : a.val[i]? = some r) (h' : r.val[j]? = some x) : cell2 a i j d = x.val := by
  simp [cell2, h, h']

/-! ### The loop variables -/

/-- The variables of the Rust loop are the variables `m` of the machine, with the bounds that
    keep the Rust from overflowing: `F0` is the fuel the run started with, `fuel` what is left. -/
structure Corr {NT NN S P : Usize} (c : Spec.MConf)
    (F0 : Nat) (m : Spec.MState) (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node)
    (ti : Usize) (prev_end : U32) (state : Usize) (fuel : Usize) : Prop where
  stackEq : stack.val.map entryNat = m.stack
  nodesEq : nodes.val.map nodeNat = m.nodes
  tiEq : ti.val = m.ti
  prevEndEq : prev_end.val = m.prevEnd
  stateEq : state.val = m.state
  /-- Every state on the stack, and the current one, is a state of the tables. -/
  stackLt : ∀ e ∈ stack.val, e.state.val < S.val
  stateLt : state.val < S.val
  /-- The stack is never empty. -/
  nonempty : stack.val ≠ []
  /-- Room: each step adds at most one entry or node and consumes one unit of fuel. -/
  roomStack : stack.val.length + fuel.val ≤ F0 + 1
  roomNodes : nodes.val.length + fuel.val ≤ F0
  roomTi : ti.val + fuel.val ≤ F0

/-- A Rust result and the way the machine stops correspond. -/
def ResRel : Spec.MStop → core.result.Result Unit ParseError → Prop
  | .ok, .Ok () => True
  | .err tk st tm, .Err e => e.token.val = tk ∧ e.state.val = st ∧ e.term.val = tm
  | _, _ => False

/-- The outcome of the body is that of `Spec.mbody`. -/
def BodyPost {NT NN S P : Usize} (c : Spec.MConf) (F0 : Nat) :
    (Spec.MState × Nat) ⊕ (Spec.MStop × List Spec.MEntry × List Spec.MNode) →
    ControlFlow
      ((alloc.vec.Vec Entry) × (alloc.vec.Vec Node) × Usize × U32 × Usize × Usize)
      ((core.result.Result Unit ParseError) × (alloc.vec.Vec Entry) × (alloc.vec.Vec Node)) →
    Prop
  | .inl (m', f'), .cont (stack', nodes', ti', prev_end', state', fuel') =>
      Corr (NT := NT) (NN := NN) (S := S) (P := P) c F0 m' stack' nodes' ti' prev_end' state' fuel'
        ∧ fuel'.val = f'
  | .inr (stop, stk, nd), .done (res, stack', nodes') =>
      ResRel stop res ∧ stack'.val.map entryNat = stk ∧ nodes'.val.map nodeNat = nd
  | _, _ => False

/-! ### The helpers of the loop -/

@[step]
theorem first_start_spec (stack : alloc.vec.Vec Entry) (base n : Usize) (prev_end : U32)
    (h : n.val > 0 → base.val < stack.val.length) :
    first_start stack base n prev_end ⦃ r =>
      r.val = if n.val > 0 then ((stack.val.map entryNat).getD base.val ⟨0, 0⟩).start
        else prev_end.val ⦄ := by
  unfold first_start
  by_cases hn : n > 0#usize
  · have hn' : n.val > 0 := by simpa using hn
    simp only [hn, ↓reduceIte, hn']
    have hb := h hn'
    step*
    simp [entryNat, List.getD_eq_getElem?_getD, List.getElem?_map, hb, *]
  · have hn' : ¬ n.val > 0 := by simpa using hn
    simp [hn, hn']

@[step]
theorem lookahead_spec (tokens : Slice Token) (ti : Usize) (eof : U16) (prev_end : U32) :
    lookahead tokens ti eof prev_end ⦃ r =>
      ((tokens.val.map tokNat)[ti.val]?.getD ⟨eof.val, prev_end.val, prev_end.val⟩) =
        ⟨r.1.val, r.2.1.val, r.2.2.val⟩ ⦄ := by
  unfold lookahead
  by_cases h : ti < Slice.len tokens
  · have h' : ti.val < tokens.val.length := by simpa using h
    simp only [h, ↓reduceIte]
    step*
    simp [tokNat, List.getElem?_map, h', *]
  · have h' : ¬ ti.val < tokens.val.length := by simpa using h
    simp [h, List.getElem?_eq_none_iff.mpr (by simpa using h')]

/-- `Spec.mreduce`, with the values its `let`s compute named. -/
theorem mreduce_rewrite (c : Spec.MConf) (m : Spec.MState) (prod n startV topV gV : Nat)
    (hn : c.tables.rhsLen prod = n) (hlt : ¬ n ≥ m.stack.length)
    (hstart : (if n > 0 then (m.stack.getD (m.stack.length - n) ⟨0, 0⟩).start else m.prevEnd) =
      startV)
    (htop : ((m.stack.take (m.stack.length - n)).getD (m.stack.length - n - 1) ⟨0, 0⟩).state =
      topV)
    (hg : c.tables.goto topV (c.tables.lhs prod) = gV) :
    Spec.mreduce c m prod =
      if gV = Spec.noneCell then
        .inr (.ok, m.stack.take (m.stack.length - n), m.nodes ++ [⟨Spec.prodFlag + prod, startV, m.prevEnd⟩])
      else
        .inl { m with stack := m.stack.take (m.stack.length - n) ++ [⟨gV, startV⟩]
                      nodes := m.nodes ++ [⟨Spec.prodFlag + prod, startV, m.prevEnd⟩]
                      state := gV } := by
  simp only [Spec.mreduce, hn, hlt, ↓reduceIte, hstart, htop, hg]

set_option hygiene false in
/-- In a leaf of `reduce_spec` where the stack is long enough: the facts that tie the values
    the Rust computed (`n`, `base`, `start`, `top`, `g`, the new stack and nodes) to the
    machine's, and the rewriting of `Spec.mreduce` with them. The names are those of the
    context that `step*` produces. -/
macro "reduce_facts" : tactic => `(tactic| (
  have hi' : i = x0 := by
    have : rhs_len.val[prod.val]? = some i := by rw [i_post]; exact List.getElem?_eq_getElem _
    rw [hx0] at this; exact (Option.some.inj this).symm
  have hn' : n.val = x0.val := by simp [n_post, hi']
  have hcell : cell1 rhs_len prod.val 0 = n.val := by rw [cell1_of_get? _ _ _ _ hx0, hn']
  have hlt' : ¬ n.val ≥ (List.map entryNat stack.val).length := by
    simpa [hmlen] using ‹¬n ≥ stack.len›
  have hbaseEq : base.val = stack.val.length - n.val := by rw [base_post]; simp
  have hstart : (if n.val > 0 then ((List.map entryNat stack.val).getD
        ((List.map entryNat stack.val).length - n.val) ⟨0, 0⟩).start else mprev) = start.val := by
    rw [hmlen, ← hbaseEq, start_post, hprev]
  have hstack1m : stack1.val.map entryNat =
      (List.map entryNat stack.val).take ((List.map entryNat stack.val).length - n.val) := by
    rw [hmlen, ← hbaseEq, ← List.map_take, stack1_post]
  have htop : ((List.take ((List.map entryNat stack.val).length - n.val)
        (List.map entryNat stack.val)).getD
        ((List.map entryNat stack.val).length - n.val - 1) ⟨0, 0⟩).state = top.val := by
    rw [hmlen, ← hbaseEq, ← List.map_take, ← stack1_post, ← i3_post,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    have : stack1.val[i3.val]? = some e := by rw [e_post]; exact List.getElem?_eq_getElem _
    rw [this]
    simp [entryNat, top_post]
  have h4 : cell1 lhs prod.val NN.val = i5.val := by
    rw [cell1_of_get? lhs prod.val NN.val i4 (by rw [i4_post]; exact List.getElem?_eq_getElem _)]
    simp [i5_post]
  have hrowA : goto.val[top.val]? = some a := by rw [a_post]; exact List.getElem?_eq_getElem _
  have hcellA : a.val[i5.val]? = some i6 := by rw [i6_post]; exact List.getElem?_eq_getElem _
  have hgoto : cell2 goto top.val (cell1 lhs prod.val NN.val) 0 = g.val := by
    rw [h4, cell2_of_get? goto top.val i5.val _ a i6 hrowA hcellA]
    simp [g_post]
  have hi7 : i7.val = prod.val := by
    have : prod.val < 65536 := by have := hk.prods; unfold Spec.prodFlag at this; omega
    simp [i7_post]; omega
  have hi8 : i8.val = Spec.prodFlag + prod.val := by
    have h1 : i7.val < 32768 := by
      have := hk.prods; unfold Spec.prodFlag at this; omega
    rw [i8_post, show (PROD_FLAG ||| i7).val = 32768 + i7.val from or_flag i7 h1, hi7]
    rfl
  have hnodes1m : nodes1.val.map nodeNat =
      List.map nodeNat nodes.val ++ [⟨Spec.prodFlag + prod.val, start.val, mprev⟩] := by
    rw [nodes1_post, List.map_append]
    simp [nodeNat, hi8, hprev]
  have hrw := mreduce_rewrite (confOf tokens action goto default_reduce lhs rhs_len eof)
    ⟨List.map entryNat stack.val, List.map nodeNat nodes.val, mti, mprev, mstate⟩
    prod.val n.val start.val top.val g.val
    (by simp only [confOf, tablesOf]; exact hcell) hlt' hstart htop
    (by simp only [confOf, tablesOf]; exact hgoto)
  rw [hrw]))

/-- The outcome of a reduction, as the kernel's `reduce` returns it, is that of
    `Spec.mreduce`. -/
def ReducePost {S : Usize} (m : Spec.MState) (stack : alloc.vec.Vec Entry)
    (nodes : alloc.vec.Vec Node) :
    Spec.MRes → Reduced × alloc.vec.Vec Entry × alloc.vec.Vec Node → Prop
  | .inl m', (.Next g, stack', nodes') =>
      g.val = m'.state ∧ g.val < S.val ∧
        stack'.val.map entryNat = m'.stack ∧ nodes'.val.map nodeNat = m'.nodes ∧
        (∀ e ∈ stack'.val, e.state.val < S.val) ∧
        stack'.val.length ≤ stack.val.length + 1 ∧ nodes'.val.length = nodes.val.length + 1 ∧
        m'.ti = m.ti ∧ m'.prevEnd = m.prevEnd ∧ stack'.val ≠ []
  | .inr (.ok, stk, nd), (.Accept, stack', nodes') =>
      stack'.val.map entryNat = stk ∧ nodes'.val.map nodeNat = nd
  | .inr (.err tk st tm, stk, nd), (.Inconsistent, stack', nodes') =>
      tk = m.ti ∧ st = m.state ∧ tm = Spec.termInconsistent ∧
        stack'.val.map entryNat = stk ∧ nodes'.val.map nodeNat = nd
  | _, _ => False

theorem reduce_spec {NT NN S P : Usize} (tokens : Slice Token)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (prod : Usize) (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node) (prev_end : U32)
    (m : Spec.MState)
    (hk : KWf action goto default_reduce lhs rhs_len)
    (hprod : prod.val < P.val)
    (hstack : stack.val.map entryNat = m.stack) (hnodes : nodes.val.map nodeNat = m.nodes)
    (hprev : prev_end.val = m.prevEnd)
    (hlt : ∀ e ∈ stack.val, e.state.val < S.val)
    (hne : stack.val ≠ [])
    (hroomS : stack.val.length < Usize.max) (hroomN : nodes.val.length < Usize.max) :
    reduce prod stack nodes prev_end goto lhs rhs_len ⦃ r stack' nodes' =>
      ReducePost (S := S) m stack nodes
        (Spec.mreduce (confOf tokens action goto default_reduce lhs rhs_len eof) m
          prod.val) (r, stack', nodes') ⦄ := by
  obtain ⟨mstack, mnodes, mti, mprev, mstate⟩ := m
  simp only at hstack hnodes hprev
  subst hstack hnodes
  have hrl : ∃ x, rhs_len.val[prod.val]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
  obtain ⟨x0, hx0⟩ := hrl
  have hmlen : (List.map entryNat stack.val).length = stack.val.length := by simp
  unfold reduce
  step*
  · -- the stack is shorter than the production
    have hi' : i = x0 := by
      have : rhs_len.val[prod.val]? = some i := by rw [i_post]; exact List.getElem?_eq_getElem _
      rw [hx0] at this; exact (Option.some.inj this).symm
    have hn' : n.val = x0.val := by simp [n_post, hi']
    have hcell : cell1 rhs_len prod.val 0 = n.val := by rw [cell1_of_get? _ _ _ _ hx0, hn']
    have hge : n.val ≥ stack.val.length := by simpa using ‹n ≥ stack.len›
    simp only [Spec.mreduce, confOf, tablesOf, hcell, hmlen, hge, ↓reduceIte, ReducePost]
    simp
  · -- `top` is a state
    have he : e ∈ stack.val := by
      have h1 : e ∈ stack1.val := by rw [e_post]; exact List.getElem_mem _
      rw [stack1_post] at h1
      exact List.mem_of_mem_take h1
    have h1 := hlt e he
    have h2 : top.val = e.state.val := by simp [top_post]
    have h3 : goto.val.length = S.val := Array.property goto
    show top.val < goto.val.length
    omega
  · -- `lhs[prod]` is a nonterminal
    have h1 : lhs.val[prod.val]? = some i4 := by rw [i4_post]; exact List.getElem?_eq_getElem _
    have h2 := hk.lhs _ _ h1
    have h3 : i5.val = i4.val := by simp [i5_post]
    have h4 : a.val.length = NN.val := Array.property a
    show i5.val < a.val.length
    omega
  · -- no goto: accept
    reduce_facts
    have hgn : g.val = Spec.noneCell := by
      have : g = i9 := ‹g = i9›
      simp [this, i9_post, NONE, global_simps, Spec.noneCell]
    simp [hgn, ReducePost, hstack1m, hnodes1m]
  · -- a goto: the reduction is made
    reduce_facts
    have hgn : ¬ g.val = Spec.noneCell := by
      intro h; apply ‹¬g = i9›
      apply UScalar.eq_of_val_eq
      simp [i9_post, NONE, global_simps, Spec.noneCell, h]
    simp only [hgn, ↓reduceIte, ReducePost]
    have hg6 : g.val = i6.val := by simp [g_post]
    have hi10 : i10.val = g.val := by
      have : g.val < 65536 := by rw [hg6]; scalar_tac
      simp [i10_post]; omega
    have hgS : g.val < S.val := by
      have h1 := hk.goto top.val i5.val a i6 hrowA hcellA
      have h2 : i6.val ≠ Spec.noneCell := by rw [← hg6]; exact hgn
      rw [hg6]
      omega
    refine ⟨trivial, hgS, ?_, hnodes1m, ?_, ?_, ?_, trivial, trivial, ?_⟩
    · rw [stack2_post, List.map_append, hstack1m]
      simp [entryNat, hi10]
    · intro e he
      rw [stack2_post] at he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · rw [stack1_post] at he
        exact hlt e (List.mem_of_mem_take he)
      · show i10.val < S.val
        rw [hi10]
        exact hgS
    · rw [stack2_post, List.length_append, stack1_post]
      simp only [List.length_take, List.length_singleton]
      omega
    · rw [nodes1_post]
      simp
    · rw [stack2_post]
      simp

/-! ### The body of the loop -/

@[step]
theorem term_oof : TERM_OUT_OF_FUEL ⦃ x => x.val = Spec.termOutOfFuel ⦄ := by
  unfold TERM_OUT_OF_FUEL
  step*
  all_goals first
    | scalar_tac
    | (simp_all [Spec.termOutOfFuel, U16.rMax])

theorem term_inc : TERM_INCONSISTENT.val = 65535 := by
  unfold TERM_INCONSISTENT; rfl

theorem none_val : NONE.val = 65535 := by
  unfold NONE; rfl

theorem and_one_val (a : Usize) : (a &&& 1#usize).val = a.val % 2 := by
  rw [UScalar.val_and]
  have : (1#usize).val = 1 := by simp
  rw [this, Nat.and_one_is_mod]

theorem shr_one_val (a i6 : Usize) (h : i6.val = a.val >>> 1) : i6.val = a.val / 2 := by
  rw [h, Nat.shiftRight_eq_div_pow]

/-- Both places where the loop reduces call `reduce` and dispatch on its result in the same
    way. If the machine's iteration is a reduction by `prod`, so is the loop's. -/
theorem body_reduce_case {NT NN S P : Usize} (tokens : Slice Token)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node) (ti : Usize) (prev_end : U32)
    (state : Usize) (fuel fuel1 : Usize) (prod : Usize) (F0 : Nat)
    (hF0 : F0 ≤ 2 ^ 62) (hplat : System.Platform.numBits = 64)
    (hk : KWf action goto default_reduce lhs rhs_len)
    (hstLt : ∀ e ∈ stack.val, e.state.val < S.val)
    (hne : stack.val ≠ [])
    (hroomS : stack.val.length + fuel.val ≤ F0 + 1)
    (hroomN : nodes.val.length + fuel.val ≤ F0) (hroomT : ti.val + fuel.val ≤ F0)
    (hprod : prod.val < P.val) (hfz : fuel.val ≠ 0) (hfuel1 : fuel1.val = fuel.val - 1) :
    (do
      let (r, stack1, nodes1) ← reduce prod stack nodes prev_end goto lhs rhs_len
      match r with
      | Reduced.Next g => ok (cont (stack1, nodes1, ti, prev_end, g, fuel1))
      | Reduced.Accept => ok (done (core.result.Result.Ok (), stack1, nodes1))
      | Reduced.Inconsistent =>
        ok (done (core.result.Result.Err
          ({ token := ti, state := state, term := TERM_INCONSISTENT } : ParseError),
          stack1, nodes1)))
      ⦃ r' =>
        BodyPost (NT := NT) (NN := NN) (S := S) (P := P)
          (confOf tokens action goto default_reduce lhs rhs_len eof) F0
          (match Spec.mreduce (confOf tokens action goto default_reduce lhs rhs_len eof)
              ({ stack := stack.val.map entryNat, nodes := nodes.val.map nodeNat, ti := ti.val,
                 prevEnd := prev_end.val, state := state.val } : Spec.MState)
              prod.val with
            | .inl m' => .inl (m', fuel.val - 1)
            | .inr out => .inr out) r' ⦄ := by
  have hmax : 2 ^ 62 + 2 < Usize.max := by scalar_tac
  have hfpos : 1 ≤ fuel.val := by omega
  refine Aeneas.Std.WP.spec_bind
    (reduce_spec tokens action goto default_reduce lhs rhs_len eof prod stack nodes
      prev_end
      ({ stack := stack.val.map entryNat, nodes := nodes.val.map nodeNat, ti := ti.val,
         prevEnd := prev_end.val, state := state.val } : Spec.MState)
      hk hprod rfl rfl rfl hstLt hne (by omega) (by omega)) ?_
  rintro ⟨r, stack1, nodes1⟩ hpost
  generalize Spec.mreduce _ _ prod.val = mr at hpost ⊢
  rcases mr with m' | ⟨stop, stk, nd⟩
  · cases r with
    | Next g =>
      obtain ⟨hg, hgS, hs1, hn1, hlt1, hl1, hl2, hti', hpe', hne'⟩ := hpost
      refine (Aeneas.Std.WP.spec_ok _).mpr ?_
      refine ⟨⟨hs1, hn1, hti'.symm, hpe'.symm, hg, hlt1, hgS, hne', ?_, ?_, ?_⟩, hfuel1⟩
      · omega
      · omega
      · omega
    | Accept => simp [ReducePost] at hpost
    | Inconsistent => simp [ReducePost] at hpost
  · cases stop with
    | ok =>
      cases r with
      | Accept =>
        refine (Aeneas.Std.WP.spec_ok _).mpr ?_
        exact ⟨trivial, hpost.1, hpost.2⟩
      | Next g => simp [ReducePost] at hpost
      | Inconsistent => simp [ReducePost] at hpost
    | err tk st tm =>
      cases r with
      | Inconsistent =>
        obtain ⟨htk, hst, htm, hs1, hn1⟩ := hpost
        refine (Aeneas.Std.WP.spec_ok _).mpr ?_
        refine ⟨⟨htk.symm, hst.symm, ?_⟩, hs1, hn1⟩
        rw [htm, term_inc]; rfl
      | Next g => simp [ReducePost] at hpost
      | Accept => simp [ReducePost] at hpost

set_option hygiene false in
/-- In a leaf of `body_spec` where there is no default reduction: the facts that tie the
    Rust values (the step budget, the default-reduce cell, the lookahead) to the machine's. -/
macro "look_facts" : tactic => `(tactic| (
  have hfz : fuel.val ≠ 0 := by
    intro h; apply ‹¬fuel = 0#usize›; exact UScalar.eq_of_val_eq (by simpa using h)
  have hix : i = xd := by
    have : default_reduce.val[state.val]? = some i := by
      rw [i_post]; exact List.getElem?_eq_getElem _
    rw [hxd] at this; exact (Option.some.inj this).symm
  have hdrv : dr.val = xd.val := by simp [dr_post, hix]
  have hi1 : i1.val = Spec.noneCell := by simp [i1_post, NONE, global_simps, Spec.noneCell]
  have hdr : dr.val = Spec.noneCell := by
    have : dr.val = i1.val := by simpa using ‹¬(dr != i1) = true›
    rw [this]; exact hi1
  have hcell : (confOf tokens action goto default_reduce lhs rhs_len eof).tables.defaultReduce
      state.val = Spec.noneCell := by
    show cell1 default_reduce state.val Spec.noneCell = Spec.noneCell
    rw [cell1_of_get? _ _ _ _ hxd, ← hdrv]; exact hdr
  have hlook : (confOf tokens action goto default_reduce lhs rhs_len eof).look
      ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩ =
      ⟨term.val, tstart.val, tend.val⟩ := by
    unfold Spec.MConf.look
    simpa [confOf, tablesOf] using term_post
  have hi2 : i2.val = term.val := by simp [i2_post]))

set_option hygiene false in
/-- In a leaf of `body_spec` where the terminal is in range: the action cell. -/
macro "act_facts" : tactic => `(tactic| (
  have hi3 : i3.val = term.val := by simp [i3_post]
  have hrowA : action.val[state.val]? = some a := by
    rw [a_post]; exact List.getElem?_eq_getElem _
  have hcellA : a.val[term.val]? = some i4 := by
    rw [← hi3, i4_post]; exact List.getElem?_eq_getElem _
  have ha1 : a1.val = i4.val := by simp [a1_post]
  have hact : (confOf tokens action goto default_reduce lhs rhs_len eof).tables.action
      state.val term.val = a1.val := by
    show cell2 action state.val term.val 0 = a1.val
    rw [cell2_of_get? action state.val term.val 0 a i4 hrowA hcellA, ha1]))

theorem body_spec {NT NN S P : Usize} (tokens : Slice Token)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node) (ti : Usize) (prev_end : U32)
    (state : Usize) (fuel : Usize) (m : Spec.MState) (F0 : Nat)
    (hF0 : F0 ≤ 2 ^ 62) (hplat : System.Platform.numBits = 64)
    (hk : KWf action goto default_reduce lhs rhs_len)
    (hc : Corr (NT := NT) (NN := NN) (S := S) (P := P)
      (confOf tokens action goto default_reduce lhs rhs_len eof) F0 m stack nodes ti
      prev_end state fuel) :
    parse_loop.body tokens action goto default_reduce lhs rhs_len eof stack nodes ti
        prev_end state fuel ⦃ r =>
      BodyPost (NT := NT) (NN := NN) (S := S) (P := P)
        (confOf tokens action goto default_reduce lhs rhs_len eof) F0
        (Spec.mbody (confOf tokens action goto default_reduce lhs rhs_len eof)
          fuel.val m) r ⦄ := by
  obtain ⟨hstk, hnds, hti, hpe, hst, hstLt, hstateLt, hne, hroomS, hroomN, hroomT⟩ := hc
  obtain ⟨mstack, mnodes, mti, mprev, mstate⟩ := m
  simp only at hstk hnds hti hpe hst
  subst hstk hnds hti hpe hst
  obtain ⟨xd, hxd⟩ : ∃ x, default_reduce.val[state.val]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by have := Array.property default_reduce; omega)⟩
  have hmax : 2 ^ 62 + 2 < Usize.max := by scalar_tac
  unfold parse_loop.body
  step*
  · -- out of fuel
    have hi : i.val = Spec.termOutOfFuel := ‹_›
    have hf : fuel.val = 0 := by rw [‹fuel = 0#usize›]; rfl
    rw [Spec.mbody_zero _ (by simpa using hf)]
    simp [BodyPost, ResRel, hi]
  · -- a default reduction
    have hfz : fuel.val ≠ 0 := by
      intro h; apply ‹¬fuel = 0#usize›; exact UScalar.eq_of_val_eq (by simpa using h)
    have hix : i = xd := by
      have : default_reduce.val[state.val]? = some i := by
        rw [i_post]; exact List.getElem?_eq_getElem _
      rw [hxd] at this; exact (Option.some.inj this).symm
    have hdrv : dr.val = xd.val := by simp [dr_post, hix]
    have hi1 : i1.val = Spec.noneCell := by simp [i1_post, NONE, global_simps, Spec.noneCell]
    have hne' : dr.val ≠ Spec.noneCell := by
      intro h; apply (by simpa using ‹(dr != i1) = true› : dr ≠ i1)
      exact UScalar.eq_of_val_eq (by rw [h, hi1])
    have hP : dr.val < P.val := by
      rcases hk.defaultReduce state.val xd hxd with h | h
      · exact absurd (by rw [hdrv]; exact h) hne'
      · rw [hdrv]; exact h
    have hcell : (confOf tokens action goto default_reduce lhs rhs_len eof).tables.defaultReduce
        state.val = dr.val := by
      show cell1 default_reduce state.val Spec.noneCell = dr.val
      rw [cell1_of_get? _ _ _ _ hxd, hdrv]
    have hmb : Spec.mbody (confOf tokens action goto default_reduce lhs rhs_len eof)
        fuel.val ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩ =
        (match Spec.mreduce (confOf tokens action goto default_reduce lhs rhs_len eof)
            ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩
            dr.val with
          | .inl m' => .inl (m', fuel.val - 1)
          | .inr out => .inr out) := by
      rw [Spec.mbody_pos _ hfz, Spec.mstep_default (by simp only []; rw [hcell]; exact hne'),
        hcell]
      rfl
    rw [hmb]
    exact body_reduce_case tokens action goto default_reduce lhs rhs_len eof stack
      nodes ti prev_end state fuel fuel1 dr F0 hF0 hplat hk hstLt hne hroomS hroomN hroomT hP
      hfz (by simpa using fuel1_post)
  · -- the terminal is out of range
    look_facts
    have hge : ((confOf tokens action goto default_reduce lhs rhs_len eof).look
        ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term ≥ (confOf tokens action goto default_reduce lhs rhs_len eof).nt := by
      rw [hlook]; show term.val ≥ NT.val; rw [← hi2]; simpa using ‹i2 ≥ NT›
    rw [Spec.mbody_pos _ hfz, Spec.mstep_term hcell hge]
    simp [BodyPost, ResRel, hlook]
  · -- no action
    look_facts
    act_facts
    have hnle : ¬ ((confOf tokens action goto default_reduce lhs rhs_len eof).look
        ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term ≥ (confOf tokens action goto default_reduce lhs rhs_len eof).nt := by
      rw [hlook]; show ¬ term.val ≥ NT.val; rw [← hi2]; simpa using ‹¬i2 ≥ NT›
    have hact' : (confOf tokens action goto default_reduce lhs rhs_len eof).tables.action
        state.val ((confOf tokens action goto default_reduce lhs rhs_len eof).look ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term = 0 := by
      rw [hlook]; rw [hact]; rw [‹a1 = 0#usize›]; rfl
    rw [Spec.mbody_pos _ hfz, Spec.mstep_error hcell hnle hact']
    simp [BodyPost, ResRel, hlook]
  · -- a shift
    look_facts
    act_facts
    have hnle : ¬ ((confOf tokens action goto default_reduce lhs rhs_len eof).look
        ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term ≥ (confOf tokens action goto default_reduce lhs rhs_len eof).nt := by
      rw [hlook]; show ¬ term.val ≥ NT.val; rw [← hi2]; simpa using ‹¬i2 ≥ NT›
    have hact' : (confOf tokens action goto default_reduce lhs rhs_len eof).tables.action
        state.val ((confOf tokens action goto default_reduce lhs rhs_len eof).look ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term = a1.val := by
      rw [hlook]; exact hact
    have hne0 : a1.val ≠ 0 := fun h => ‹¬a1 = 0#usize› (UScalar.eq_of_val_eq (by simpa using h))
    have hodd : a1.val % 2 = 1 := by
      rw [← and_one_val, ← i5_post, ‹i5 = 1#usize›]; rfl
    have h6 := shr_one_val a1 i6 i6_post
    have hacts := hk.action state.val term.val a i4 hrowA hcellA
    have hSlt : a1.val / 2 < S.val := by
      have := hacts.1 (by rw [← ha1]; exact hodd)
      rw [ha1]; exact this
    have hi4b : i4.val < 65536 := by scalar_tac
    have hi7 : i7.val = a1.val / 2 := by
      have : i6.val < 65536 := by omega
      simp [i7_post]; omega
    rw [Spec.mbody_pos _ hfz, Spec.mstep_shift hcell hnle (by rw [hact']; exact hne0)
      (by rw [hact']; exact hodd)]
    simp only [hlook, hact, BodyPost]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simpa using fuel1_post⟩
    · rw [stack1_post, List.map_append]; simp [entryNat, hi7]
    · rw [nodes1_post, List.map_append]; simp [nodeNat]
    · simpa using ti1_post
    · rfl
    · exact h6
    · intro e he
      rw [stack1_post] at he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hstLt e he
      · show i7.val < S.val
        rw [hi7]; exact hSlt
    · rw [h6]; exact hSlt
    · rw [stack1_post]; simp
    · rw [stack1_post]; simp only [List.length_append, List.length_singleton]
      have := fuel1_post; omega
    · rw [nodes1_post]; simp only [List.length_append, List.length_singleton]
      have := fuel1_post; omega
    · have := ti1_post; have := fuel1_post; omega
  · -- `prod` does not underflow
    have h1 : i5.val = a1.val % 2 := by rw [i5_post, and_one_val]
    have h2 : ¬ i5.val = 1 := fun h => ‹¬i5 = 1#usize› (UScalar.eq_of_val_eq (by simpa using h))
    have h3 : a1.val ≠ 0 := fun h => ‹¬a1 = 0#usize› (UScalar.eq_of_val_eq (by simpa using h))
    have h4 := shr_one_val a1 i6 i6_post
    show 1 ≤ i6.val
    omega
  · -- a reduction by an action
    look_facts
    act_facts
    have hnle : ¬ ((confOf tokens action goto default_reduce lhs rhs_len eof).look
        ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term ≥ (confOf tokens action goto default_reduce lhs rhs_len eof).nt := by
      rw [hlook]; show ¬ term.val ≥ NT.val; rw [← hi2]; simpa using ‹¬i2 ≥ NT›
    have hact' : (confOf tokens action goto default_reduce lhs rhs_len eof).tables.action
        state.val ((confOf tokens action goto default_reduce lhs rhs_len eof).look ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩).term = a1.val := by
      rw [hlook]; exact hact
    have hne0 : a1.val ≠ 0 := fun h => ‹¬a1 = 0#usize› (UScalar.eq_of_val_eq (by simpa using h))
    have hi5 : i5.val = a1.val % 2 := by rw [i5_post, and_one_val]
    have heven : ¬ a1.val % 2 = 1 := by
      intro h; apply ‹¬i5 = 1#usize›; exact UScalar.eq_of_val_eq (by rw [hi5, h]; rfl)
    have h6 := shr_one_val a1 i6 i6_post
    have hprodv : prod.val = a1.val / 2 - 1 := by rw [prod_post, h6]
    have hacts := hk.action state.val term.val a i4 hrowA hcellA
    have hP : prod.val < P.val := by
      rw [hprodv, ha1]
      exact hacts.2 (by rw [← ha1]; exact hne0) (by rw [← ha1]; omega)
    have hmb : Spec.mbody (confOf tokens action goto default_reduce lhs rhs_len eof) fuel.val ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩ =
        (match Spec.mreduce (confOf tokens action goto default_reduce lhs rhs_len eof) ⟨stack.val.map entryNat, nodes.val.map nodeNat, ti.val, prev_end.val, state.val⟩ prod.val with
          | .inl m' => .inl (m', fuel.val - 1)
          | .inr out => .inr out) := by
      rw [Spec.mbody_pos _ hfz, Spec.mstep_reduce hcell hnle (by rw [hact']; exact hne0)
        (by rw [hact']; exact heven), hact', hprodv]
      rfl
    rw [hmb]
    exact body_reduce_case tokens action goto default_reduce lhs rhs_len eof stack
      nodes ti prev_end state fuel fuel1 prod F0 hF0 hplat hk hstLt hne hroomS hroomN hroomT hP
      hfz (by simpa using fuel1_post)

/-! ### The loop -/

/-- The result of the kernel is the end of the machine's run. -/
def LoopPost (out : Spec.MStop × List Spec.MEntry × List Spec.MNode) :
    (core.result.Result Unit ParseError) × alloc.vec.Vec Entry × alloc.vec.Vec Node → Prop
  | (res, stack', nodes') =>
      ResRel out.1 res ∧ stack'.val.map entryNat = out.2.1 ∧ nodes'.val.map nodeNat = out.2.2

theorem loop_spec {NT NN S P : Usize} (tokens : Slice Token)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node) (ti : Usize) (prev_end : U32)
    (state : Usize) (fuel : Usize) (m : Spec.MState) (F0 : Nat)
    (hF0 : F0 ≤ 2 ^ 62) (hplat : System.Platform.numBits = 64)
    (hk : KWf action goto default_reduce lhs rhs_len)
    (hc : Corr (NT := NT) (NN := NN) (S := S) (P := P)
      (confOf tokens action goto default_reduce lhs rhs_len eof) F0 m stack nodes ti
      prev_end state fuel) :
    parse_loop tokens stack nodes action goto default_reduce lhs rhs_len eof ti
        prev_end state fuel ⦃ r =>
      LoopPost (Spec.mrunN (confOf tokens action goto default_reduce lhs rhs_len eof)
        fuel.val m) r ⦄ := by
  unfold parse_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun x => x.2.2.2.2.2.val)
    (inv := fun x => ∃ m', Corr (NT := NT) (NN := NN) (S := S) (P := P)
      (confOf tokens action goto default_reduce lhs rhs_len eof) F0 m'
        x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧
      Spec.mrunN (confOf tokens action goto default_reduce lhs rhs_len eof)
        x.2.2.2.2.2.val m' =
      Spec.mrunN (confOf tokens action goto default_reduce lhs rhs_len eof) fuel.val m)
    (post := fun r => LoopPost
      (Spec.mrunN (confOf tokens action goto default_reduce lhs rhs_len eof)
        fuel.val m) r)
  · rintro ⟨st, nd, ti', pe, sta, f⟩ ⟨m', hc', hrun⟩
    refine Aeneas.Std.WP.spec_mono
      (body_spec tokens action goto default_reduce lhs rhs_len eof st nd ti' pe sta f
        m' F0 hF0 hplat hk hc') ?_
    intro r hr
    rw [Spec.mrunN_eq] at hrun
    cases hmb : Spec.mbody (confOf tokens action goto default_reduce lhs rhs_len eof)
        f.val m' with
    | inl mf =>
      obtain ⟨m'', f'⟩ := mf
      rw [hmb] at hr hrun
      cases r with
      | cont x' =>
        obtain ⟨st', nd', ti'', pe', sta', f''⟩ := x'
        obtain ⟨hcorr, hf⟩ := hr
        refine ⟨⟨m'', hcorr, ?_⟩, ?_⟩
        · simpa [hf] using hrun
        · have : f.val ≠ 0 := by
            intro h0
            rw [Spec.mbody_zero _ h0] at hmb
            simp at hmb
          have h1 : f' = f.val - 1 := by
            rw [Spec.mbody_pos _ this] at hmb
            cases hms : Spec.mstep (confOf tokens action goto default_reduce lhs rhs_len eof
             ) m' with
            | inl mm => rw [hms] at hmb; simp at hmb; omega
            | inr o => rw [hms] at hmb; simp at hmb
          show f''.val < f.val
          omega
      | done y => exact absurd hr (by simp [BodyPost])
    | inr out =>
      rw [hmb] at hr hrun
      cases r with
      | done y =>
        obtain ⟨st', nd', ti'⟩ := (⟨y.1, y.2.1, y.2.2⟩ : _ × _ × _)
        obtain ⟨hres, hs, hn⟩ := hr
        rw [← hrun]
        exact ⟨hres, hs, hn⟩
      | cont x' => exact absurd hr (by simp [BodyPost])
  · exact ⟨m, hc, rfl⟩

/-! ### The kernel -/

theorem parse_spec {NT NN S P : Usize} (tokens : Slice Token)
    (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (fuel : Usize) (hfuel : fuel.val ≤ 2 ^ 62) (hplat : System.Platform.numBits = 64)
    (hk : KWf action goto default_reduce lhs rhs_len) :
    parse tokens stack nodes action goto default_reduce lhs rhs_len eof fuel ⦃
      res stack' nodes' =>
      LoopPost (Spec.mrunN (confOf tokens action goto default_reduce lhs rhs_len eof)
        fuel.val Spec.MState.init) (res, stack', nodes') ⦄ := by
  unfold parse
  step*
  refine Aeneas.Std.WP.spec_mono
    (loop_spec tokens action goto default_reduce lhs rhs_len eof stack2 nodes1
      0#usize 0#u32 0#usize fuel Spec.MState.init fuel.val hfuel hplat hk ?_) ?_
  · have hS := hk.hasStart
    have hs2 : stack2.val = [⟨0#u16, 0#u32⟩] := by simp [stack2_post, stack1_post]
    have hn1 : nodes1.val = [] := by simpa using nodes1_post
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs2]; simp [Spec.MState.init, entryNat]
    · rw [hn1]; simp [Spec.MState.init]
    · simp [Spec.MState.init]
    · simp [Spec.MState.init]
    · simp [Spec.MState.init]
    · intro e he; rw [hs2] at he; simp at he; subst he; simpa using hS
    · simpa using hS
    · rw [hs2]; simp
    · rw [hs2]; simp; omega
    · rw [hn1]; simp
    · simp
  · intro r hr; exact hr

/-- **The kernel's `parse` is the machine.** Under the table conditions `KWf`, the kernel
    returns, for any buffers, the result of the machine's run, and the machine's run
    corresponds to `Exec` on the tree-building table: the same number of steps, the same
    reject (state and terminal), the same accept. -/
theorem parse_correct {NT NN S P : Usize} (tokens : Slice Token)
    (stack : alloc.vec.Vec Entry) (nodes : alloc.vec.Vec Node)
    (action : Array (Array U16 NT) S) (goto : Array (Array U16 NN) S)
    (default_reduce : Array U16 S) (lhs rhs_len : Array U16 P) (eof : U16)
    (fuel : Usize) (hfuel : fuel.val ≤ 2 ^ 62) (hplat : System.Platform.numBits = 64)
    (hk : KWf action goto default_reduce lhs rhs_len)
    (hwf : Spec.MWf (confOf tokens action goto default_reduce lhs rhs_len eof)) :
    parse tokens stack nodes action goto default_reduce lhs rhs_len eof fuel ⦃
      res stack' nodes' =>
      ∃ (stop : Spec.MStop) (stk : List Spec.MEntry) (nd : List Spec.MNode),
        ResRel stop res ∧ stack'.val.map entryNat = stk ∧ nodes'.val.map nodeNat = nd ∧
        Spec.RunSim (tokens.val.map tokNat) (stop, stk, nd)
          (Spec.stepN (Spec.traceTable
            (confOf tokens action goto default_reduce lhs rhs_len eof)) fuel.val []
            (Spec.traceInputFrom 0 (tokens.val.map tokNat))) ⦄ := by
  refine Aeneas.Std.WP.spec_mono
    (parse_spec tokens stack nodes action goto default_reduce lhs rhs_len eof fuel
      hfuel hplat hk) ?_
  rintro ⟨res, stack', nodes'⟩ ⟨hres, hs, hn⟩
  exact ⟨_, _, _, hres, hs, hn, Spec.sim_run_init hwf fuel.val⟩

end lpg_kernel.Proof
