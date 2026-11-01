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

import Spec.Machine
import Spec.Spans

/-!
The machine of `Spec/Machine.lean` refines `Exec.step` on the tree-building table.

`Rel c m stk input` relates the variables `m` of the Rust loop to a stack `stk` of trees and
the remaining input of `Exec.step (traceTable c)`:

* the states of the machine's stack are those of the cells (and the initial state 0);
* the kinds of the machine's nodes are the postorder trace of the forest on the stack, bottom
  tree first;
* the input is the tokens from `ti` on.

`sim_step` says that one iteration of the machine and one step of `Exec` stay related, or end
in the same way. `sim_run` does it for `n` iterations.
-/

namespace Spec

open Runtime.Exec

/-! ### The specification side -/

/-- The table the machine is compared with: the tree-building table of the tables of `c`.
    The value of a leaf is the index of its token (the end-of-input leaf has the index
    `toks.length`). -/
def traceTable (c : MConf) : ExecTable (Tree Nat) :=
  treeTable (c.tables.exec c.toks.length (fun _ _ => 0))

/-- The input of `traceTable c` for the tokens `ts`, which start at index `k`. -/
def traceInputFrom : Nat → List MTok → List (Nat × Tree Nat)
  | _, [] => []
  | k, t :: ts => (t.term, .leaf t.term k) :: traceInputFrom (k + 1) ts

section
variable (c : MConf)

@[simp] theorem traceTable_action :
    (traceTable c).action = fun s t => decodeAct (c.tables.action s t) := rfl
@[simp] theorem traceTable_goto :
    (traceTable c).goto = fun s n => decodeOpt (c.tables.goto s n) := rfl
@[simp] theorem traceTable_defaultReduce :
    (traceTable c).defaultReduce = fun s => decodeOpt (c.tables.defaultReduce s) := rfl
@[simp] theorem traceTable_prodLhs : (traceTable c).prodLhs = c.tables.lhs := rfl
@[simp] theorem traceTable_prodRhsLen : (traceTable c).prodRhsLen = c.tables.rhsLen := rfl
@[simp] theorem traceTable_startState : (traceTable c).startState = 0 := rfl
@[simp] theorem traceTable_eof :
    (traceTable c).eof = (c.tables.eof, .leaf c.tables.eof c.toks.length) := rfl
@[simp] theorem traceTable_sem (p : Nat) (args : List (Tree Nat)) :
    (traceTable c).sem p args = .node p args := rfl

end

/-! ### Facts about stacks -/

variable {V : Type}

theorem popN_go_eq (n : Nat) (stk : Stack V) (acc : List V) :
    popN.go n stk acc =
      if n ≤ stk.length then
        some ((stk.take n).reverse.map (·.2) ++ acc, stk.drop n)
      else none := by
  induction n generalizing stk acc with
  | zero => simp [popN.go]
  | succ n ih =>
    cases stk with
    | nil => simp [popN.go]
    | cons hd tl =>
      obtain ⟨s, v⟩ := hd
      rw [popN.go, ih]
      by_cases h : n ≤ tl.length
      · simp [h]
      · simp [h]

theorem popN_eq (n : Nat) (stk : Stack V) :
    popN n stk =
      if n ≤ stk.length then
        some ((stk.take n).reverse.map (·.2), stk.drop n)
      else none := by
  simp [popN, popN_go_eq]

/-! ### Spans -/

/-- The trace with spans of the forest on a stack, from the bottom tree to the top one, and the
    starts of the trees and the end of the last token. -/
def annOf (c : MConf) (stk : Stack (Tree Nat)) : List MNode × List Nat × Nat :=
  Tree.annForest c.toks 0 (stk.reverse.map (·.2))

/-- The annotation of the leaf of the lookahead is the lookahead, whatever the position. -/
theorem ann_leaf_look (c : MConf) (m : MState) :
    Tree.ann c.toks m.prevEnd (.leaf (c.look m).term (min m.ti c.toks.length)) =
      ([⟨(c.look m).term, (c.look m).start, (c.look m).stop⟩],
       (c.look m).start, (c.look m).stop) := by
  by_cases hlt : m.ti < c.toks.length
  · have hmin : min m.ti c.toks.length = m.ti := by omega
    have hg : c.toks[m.ti]? = some c.toks[m.ti] := List.getElem?_eq_getElem hlt
    simp [Tree.ann, hmin, hg, MConf.look]
  · have hmin : min m.ti c.toks.length = c.toks.length := by omega
    have hg : c.toks[c.toks.length]? = none := by simp
    simp [Tree.ann, hmin, hg, MConf.look, List.getElem?_eq_none_iff.mpr (by omega : c.toks.length ≤ m.ti)]

/-- Splitting the forest of a stack at the `n` top trees. -/
theorem forest_split (stk : Stack (Tree Nat)) (n : Nat) :
    stk.reverse.map (·.2) =
      (stk.drop n).reverse.map (·.2) ++ (stk.take n).reverse.map (·.2) := by
  rw [← List.map_append, ← List.reverse_append, List.take_append_drop]

/-- The trees that stay on a stack when the `n` top ones are popped, and the ones popped (the
    children of the new node), bottom first. -/
def redA (stk : Stack (Tree Nat)) (n : Nat) : List (Tree Nat) := (stk.drop n).reverse.map (·.2)
def redB (stk : Stack (Tree Nat)) (n : Nat) : List (Tree Nat) := (stk.take n).reverse.map (·.2)

/-- Their annotations. -/
def annA (toks : List MTok) (stk : Stack (Tree Nat)) (n : Nat) :=
  Tree.annForest toks 0 (redA stk n)
def annB (toks : List MTok) (stk : Stack (Tree Nat)) (n : Nat) :=
  Tree.annForest toks (annA toks stk n).2.2 (redB stk n)

/-- What a reduction does to the annotation of a forest. -/
theorem ann_reduce (toks : List MTok) (stk : Stack (Tree Nat)) (n p : Nat) :
    Tree.annForest toks 0 (stk.reverse.map (·.2)) =
      ((annA toks stk n).1 ++ (annB toks stk n).1, (annA toks stk n).2.1 ++ (annB toks stk n).2.1,
       (annB toks stk n).2.2) ∧
    Tree.annForest toks 0 (redA stk n ++ [Tree.node p (redB stk n)]) =
      ((annA toks stk n).1 ++ ((annB toks stk n).1 ++
          [⟨prodFlag + p, (annB toks stk n).2.1.headD (annA toks stk n).2.2,
            (annB toks stk n).2.2⟩]),
       (annA toks stk n).2.1 ++ [(annB toks stk n).2.1.headD (annA toks stk n).2.2],
       (annB toks stk n).2.2) := by
  constructor
  · rw [forest_split stk n, annForest_append]
    rfl
  · rw [annForest_append, annForest_cons, annForest_nil, annForest_node]
    simp [annA, annB]

theorem annB_nil (toks : List MTok) (stk : Stack (Tree Nat)) :
    annB toks stk 0 = ([], [], (annA toks stk 0).2.2) := by
  simp [annB, redB]

theorem annA_length (toks : List MTok) (stk : Stack (Tree Nat)) (n : Nat) :
    (annA toks stk n).2.1.length = stk.length - n := by
  simp [annA, redA, annForest_length]

theorem annB_length (toks : List MTok) (stk : Stack (Tree Nat)) (n : Nat) (hn : n ≤ stk.length) :
    (annB toks stk n).2.1.length = n := by
  simp [annB, redB, annForest_length]; omega

/-! ### The relation -/

/-- The number of tokens that a trace has shifted: its nodes that are not reductions. -/
def tokCount (nodes : List MNode) : Nat := nodes.countP fun n => decide (n.kind < prodFlag)

/-- The machine variables `m` are the stack `stk` of trees and the remaining input `input` of
    `Exec`. -/
structure Rel (c : MConf) (m : MState) (stk : Stack (Tree Nat))
    (input : List (Nat × Tree Nat)) : Prop where
  state : m.state = topState (traceTable c) stk
  stack : m.stack.map (·.state) = 0 :: stk.reverse.map (·.1)
  nodes : m.nodes.map (·.kind) = (stk.reverse.flatMap fun p => p.2.events).map Event.code
  input : input = traceInputFrom m.ti (c.toks.drop m.ti)
  /-- The token index is the number of tokens shifted. -/
  ti : m.ti = tokCount m.nodes
  /-- The nodes, with their spans, are the annotated trace of the forest. -/
  spanNodes : m.nodes = (annOf c stk).1
  /-- The start of each stack entry is the start of its tree. -/
  spanStarts : m.stack.map (·.start) = 0 :: (annOf c stk).2.1
  /-- The end of the previous token is the one the forest ends at. -/
  spanPrev : m.prevEnd = (annOf c stk).2.2

/-- The tables and the tokens are well-formed enough for the machine to be `Exec`: every
    terminal that the machine looks up is in range. -/
structure MWf (c : MConf) : Prop where
  terms : ∀ t ∈ c.toks, t.term < c.nt
  eof : c.tables.eof < c.nt
  /-- Terminals do not use the flag bit of a production. -/
  ntFlag : c.nt ≤ prodFlag

theorem Rel.init (c : MConf) :
    Rel c MState.init [] (traceInputFrom 0 c.toks) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp [MState.init]
  · simp [MState.init, annOf]
  · simp [MState.init, annOf]
  · simp [MState.init, annOf]

theorem look_term_lt {c : MConf} (hwf : MWf c) (m : MState) : (c.look m).term < c.nt := by
  unfold MConf.look
  cases h : c.toks[m.ti]? with
  | none => simpa using hwf.eof
  | some t =>
    simp only [Option.getD_some]
    exact hwf.terms t (List.mem_of_getElem? h)

/-- The first element of the remaining input is the lookahead; the leaf's value is the index of
    the token, and past the last token it is the number of tokens. -/
theorem getD_input {c : MConf} {m : MState} {input : List (Nat × Tree Nat)}
    (h : input = traceInputFrom m.ti (c.toks.drop m.ti)) :
    input.getD 0 (traceTable c).eof =
      ((c.look m).term, .leaf (c.look m).term (min m.ti c.toks.length)) := by
  subst h
  by_cases hlt : m.ti < c.toks.length
  · have hd : c.toks.drop m.ti = c.toks[m.ti] :: c.toks.drop (m.ti + 1) :=
      List.drop_eq_getElem_cons hlt
    rw [hd]
    have hmin : min m.ti c.toks.length = m.ti := by omega
    simp [traceInputFrom, MConf.look, hlt, hmin]
  · have hd : c.toks.drop m.ti = [] := List.drop_of_length_le (by omega)
    rw [hd]
    have hmin : min m.ti c.toks.length = c.toks.length := by omega
    simp [traceInputFrom, MConf.look, hlt, hmin]

/-- The remaining input after the lookahead. -/
theorem drop_input {c : MConf} {m : MState} {input : List (Nat × Tree Nat)}
    (h : input = traceInputFrom m.ti (c.toks.drop m.ti)) :
    input.drop 1 = traceInputFrom (m.ti + 1) (c.toks.drop (m.ti + 1)) := by
  subst h
  by_cases hlt : m.ti < c.toks.length
  · have hd : c.toks.drop m.ti = c.toks[m.ti] :: c.toks.drop (m.ti + 1) :=
      List.drop_eq_getElem_cons hlt
    rw [hd]
    simp [traceInputFrom]
  · have hd : c.toks.drop m.ti = [] := List.drop_of_length_le (by omega)
    have hd' : c.toks.drop (m.ti + 1) = [] := List.drop_of_length_le (by omega)
    rw [hd, hd']
    simp [traceInputFrom]

/-! ### Lists -/

theorem getD_cons_length (a : Nat) (l : List Nat) :
    (a :: l).getD l.length 0 = (l.getLast?).getD a := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, List.getD_cons_succ, ih]
    cases t <;> simp [List.getLast?_cons]

theorem entry_getD_state (l : List MEntry) (i : Nat) :
    (l.getD i ⟨0, 0⟩).state = (l.map (·.state)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem entry_getD_start (l : List MEntry) (i : Nat) :
    (l.getD i ⟨0, 0⟩).start = (l.map (·.start)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

/-- The starts of the entries that stay on the stack after popping the entries of the `n`
    top trees. -/
theorem starts_take (stack : List MEntry) (sa sb : List Nat) (n : Nat)
    (h : stack.map (·.start) = 0 :: (sa ++ sb)) (hb : sb.length = n)
    (hl : stack.length = sa.length + n + 1) :
    (stack.take (stack.length - n)).map (·.start) = 0 :: sa := by
  have h1 : stack.length - n = sa.length + 1 := by omega
  rw [List.map_take, h, h1, List.take_succ_cons, List.take_left' rfl]

/-- The start of the first entry popped, or the previous end if none is. -/
theorem starts_get (stack : List MEntry) (sa sb : List Nat) (n pe : Nat)
    (h : stack.map (·.start) = 0 :: (sa ++ sb)) (hb : sb.length = n)
    (hl : stack.length = sa.length + n + 1) :
    (if n > 0 then (stack.getD (stack.length - n) ⟨0, 0⟩).start else pe) = sb.headD pe := by
  by_cases hn : n > 0
  · have h1 : stack.length - n = sa.length + 1 := by omega
    rw [if_pos hn, entry_getD_start, h, h1, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self]
    cases sb with
    | nil => simp at hb; omega
    | cons x xs => simp
  · have : sb = [] := by
      apply List.eq_nil_of_length_eq_zero; omega
    subst this
    simp [hn]

theorem topState_trace (c : MConf) (rest : Stack (Tree Nat)) :
    topState (traceTable c) rest = ((rest.reverse.map (·.1)).getLast?).getD 0 := by
  cases rest with
  | nil => rfl
  | cons hd tl => simp [topState, List.reverse_cons, List.getLast?_append]

theorem take_cells (stk : Stack (Tree Nat)) (n : Nat) (hn : n ≤ stk.length) :
    (stk.drop n).reverse = stk.reverse.take (stk.length - n) := by
  rw [List.take_reverse]
  congr 2
  omega

theorem drop_cells (stk : Stack (Tree Nat)) (n : Nat) (hn : n ≤ stk.length) :
    (stk.take n).reverse = stk.reverse.drop (stk.length - n) := by
  rw [List.drop_reverse]
  congr 2
  omega

theorem events_node (p : Nat) (cs : List (Tree Nat)) :
    (Tree.node p cs).events = cs.flatMap Tree.events ++ [.red p] := by
  have : ∀ cs : List (Tree Nat), Tree.eventsList cs = cs.flatMap Tree.events := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ih => simp [Tree.eventsList, ih]
  simp [Tree.events, this]

/-- The trace after a reduction: the nodes of the trees below the reduced ones, then the trace
    of the new node. -/
theorem trace_reduce (stk : Stack (Tree Nat)) (n p : Nat) (hn : n ≤ stk.length) :
    (stk.reverse.flatMap fun q => q.2.events) ++ [.red p] =
      ((stk.drop n).reverse.flatMap fun q => q.2.events) ++
        (Tree.node p ((stk.take n).reverse.map (·.2))).events := by
  rw [events_node, List.flatMap_map]
  have : stk.reverse = (stk.drop n).reverse ++ (stk.take n).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [this]
  simp [List.flatMap_append, List.append_assoc]

/-! ### One step -/

/-- The outcome of one iteration of the machine corresponds to the outcome of one step of
    `Exec`: both continue in related states, or both stop in the same way. -/
inductive Sim (c : MConf) (m : MState) :
    MRes → Result (Tree Nat) ⊕ (Stack (Tree Nat) × List (Nat × Tree Nat)) → Prop where
  /-- Both continue. -/
  | cont {m' : MState} {stk' : Stack (Tree Nat)} {input' : List (Nat × Tree Nat)} :
      Rel c m' stk' input' → Sim c m (.inl m') (.inr (stk', input'))
  /-- No action for the lookahead `t` in the state. -/
  | reject {t : Nat} (htk : m.ti = tokCount m.nodes) :
      Sim c m (.inr (.err m.ti m.state t, m.stack, m.nodes)) (.inl (.reject m.state t))
  /-- A reduction that cannot be made (the stack is too short). -/
  | inconsistent {msg : String} (htk : m.ti = tokCount m.nodes) :
      Sim c m (.inr (.err m.ti m.state termInconsistent, m.stack, m.nodes)) (.inl (.err msg))
  /-- Both accept. `rest` is the forest below the tree that was built; the nodes are its
      trace followed by the trace of `tree`. -/
  | accept {st : List MEntry} {nd : List MNode} {tree : Tree Nat} (rest : Stack (Tree Nat))
      (h : nd.map (·.kind) =
        (rest.reverse.flatMap (fun q => q.2.events) ++ tree.events).map Event.code)
      (hs : nd = (Tree.annForest c.toks 0 (rest.reverse.map (·.2) ++ [tree])).1) :
      Sim c m (.inr (.ok, st, nd)) (.inl (.ok tree))

theorem sim_reduce {c : MConf} {m : MState} {stk : Stack (Tree Nat)}
    {input : List (Nat × Tree Nat)} (hwf : MWf c) (h : Rel c m stk input) (p : Nat) :
    Sim c m (mreduce c m p)
      (match reduce (traceTable c) p stk with
       | .inl r => .inl r
       | .inr stk' => .inr (stk', input)) := by
  have hlenS : m.stack.length = stk.length + 1 := by
    have := congrArg List.length h.stack
    simpa using this
  simp only [mreduce, reduce, traceTable_prodRhsLen, popN_eq]
  by_cases hn : c.tables.rhsLen p ≥ m.stack.length
  · have hn' : ¬ c.tables.rhsLen p ≤ stk.length := by omega
    simp only [hn, hn', ↓reduceIte]
    exact Sim.inconsistent h.ti
  · have hn1 : c.tables.rhsLen p ≤ stk.length := by omega
    simp only [hn, hn1, ↓reduceIte]
    generalize hN : c.tables.rhsLen p = n at *
    have hbase : m.stack.length - n = (stk.length - n) + 1 := by omega
    have hstack1 : (m.stack.take (m.stack.length - n)).map (·.state) =
        0 :: (stk.drop n).reverse.map (·.1) := by
      rw [List.map_take, h.stack, hbase, List.take_succ_cons, take_cells stk n hn1, List.map_take]
    have htop : ((m.stack.take (m.stack.length - n)).getD (m.stack.length - n - 1)
        ⟨0, 0⟩).state = topState (traceTable c) (stk.drop n) := by
      rw [entry_getD_state, hstack1, topState_trace]
      have : m.stack.length - n - 1 = ((stk.drop n).reverse.map (·.1)).length := by
        simp; omega
      rw [this, getD_cons_length]
    rw [htop]
    generalize hG : c.tables.goto (topState (traceTable c) (stk.drop n)) (c.tables.lhs p) = gcell
    have hnodes : m.nodes.map (·.kind) ++ [prodFlag + p] =
        ((stk.drop n).reverse.flatMap (fun q => q.2.events) ++
          (Tree.node p ((stk.take n).reverse.map (·.2))).events).map Event.code := by
      rw [h.nodes]
      have e := congrArg (List.map Event.code) (trace_reduce stk n p hn1)
      simpa [Event.code] using e
    -- spans
    have hl1 := (ann_reduce c.toks stk n p).1
    have hl2 := (ann_reduce c.toks stk n p).2
    have hAlen := annA_length c.toks stk n
    have hBlen := annB_length c.toks stk n hn1
    have hOf : annOf c stk = ((annA c.toks stk n).1 ++ (annB c.toks stk n).1,
        (annA c.toks stk n).2.1 ++ (annB c.toks stk n).2.1, (annB c.toks stk n).2.2) := hl1
    have hst : m.stack.map (·.start) =
        0 :: ((annA c.toks stk n).2.1 ++ (annB c.toks stk n).2.1) := by
      rw [h.spanStarts, hOf]
    have hsl : m.stack.length = (annA c.toks stk n).2.1.length + n + 1 := by omega
    have hprev : m.prevEnd = (annB c.toks stk n).2.2 := by
      have := h.spanPrev; rw [hOf] at this; exact this
    have hstart : (if n > 0 then (m.stack.getD (m.stack.length - n) ⟨0, 0⟩).start
        else m.prevEnd) = (annB c.toks stk n).2.1.headD (annA c.toks stk n).2.2 := by
      by_cases hn0 : n > 0
      · have := starts_get m.stack _ _ n m.prevEnd hst hBlen hsl
        rw [if_pos hn0] at this ⊢
        rw [this]
        cases hb : (annB c.toks stk n).2.1 with
        | nil => rw [hb] at hBlen; simp at hBlen; omega
        | cons x xs => simp
      · have hn0' : n = 0 := by omega
        subst hn0'
        rw [if_neg hn0, annB_nil] at *
        simpa using hprev
    have hnew : m.nodes ++ [⟨prodFlag + p, (annB c.toks stk n).2.1.headD (annA c.toks stk n).2.2,
          m.prevEnd⟩] =
        (annA c.toks stk n).1 ++ ((annB c.toks stk n).1 ++
          [⟨prodFlag + p, (annB c.toks stk n).2.1.headD (annA c.toks stk n).2.2,
            (annB c.toks stk n).2.2⟩]) := by
      rw [h.spanNodes, hOf, hprev]; simp
    have hOf' : ∀ g, annOf c ((g, Tree.node p ((stk.take n).reverse.map (·.2))) :: stk.drop n) =
        ((annA c.toks stk n).1 ++ ((annB c.toks stk n).1 ++
          [⟨prodFlag + p, (annB c.toks stk n).2.1.headD (annA c.toks stk n).2.2,
            (annB c.toks stk n).2.2⟩]),
         (annA c.toks stk n).2.1 ++ [(annB c.toks stk n).2.1.headD (annA c.toks stk n).2.2],
         (annB c.toks stk n).2.2) := by
      intro g
      rw [← hl2]
      simp [annOf, redA, redB]
    rw [hstart]
    simp only [traceTable_goto, traceTable_prodLhs, hG, traceTable_sem]
    by_cases hg : gcell = noneCell
    · simp only [hg, decodeOpt, ↓reduceIte]
      refine Sim.accept (stk.drop n) (by simpa using hnodes) ?_
      show _ = (Tree.annForest c.toks 0 (redA stk n ++ [Tree.node p (redB stk n)])).1
      rw [hl2]
      exact hnew
    · simp only [hg, decodeOpt, ↓reduceIte]
      refine Sim.cont ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hstack1]
      · simpa using hnodes
      · exact h.input
      · have hnlt : ¬ (prodFlag + p < prodFlag) := Nat.not_lt.mpr (Nat.le_add_right _ _)
        have := h.ti
        unfold tokCount at this ⊢
        simpa [List.countP_append, hnlt] using this
      · rw [hOf']; exact hnew
      · rw [hOf', List.map_append, starts_take m.stack _ _ n hst hBlen hsl]
        simp
      · rw [hOf']; exact hprev

theorem annOf_cons (c : MConf) (stk : Stack (Tree Nat)) (g : Nat) (t : Tree Nat) :
    annOf c ((g, t) :: stk) =
      ((annOf c stk).1 ++ (Tree.ann c.toks (annOf c stk).2.2 t).1,
       (annOf c stk).2.1 ++ [(Tree.ann c.toks (annOf c stk).2.2 t).2.1],
       (Tree.ann c.toks (annOf c stk).2.2 t).2.2) := by
  have : annOf c ((g, t) :: stk) = Tree.annForest c.toks 0 (stk.reverse.map (·.2) ++ [t]) := by
    simp [annOf]
  rw [this, annForest_append]
  simp [annOf, annForest_cons]

theorem sim_reduce_inl {c : MConf} {m : MState} {stk : Stack (Tree Nat)}
    {input : List (Nat × Tree Nat)} (hwf : MWf c) (h : Rel c m stk input) (p : Nat)
    {r : Result (Tree Nat)} (hr : reduce (traceTable c) p stk = .inl r) :
    Sim c m (mreduce c m p) (.inl r) := by
  have := sim_reduce hwf h p
  rw [hr] at this
  exact this

theorem sim_reduce_inr {c : MConf} {m : MState} {stk : Stack (Tree Nat)}
    {input : List (Nat × Tree Nat)} (hwf : MWf c) (h : Rel c m stk input) (p : Nat)
    {stk' : Stack (Tree Nat)} (hr : reduce (traceTable c) p stk = .inr stk') :
    Sim c m (mreduce c m p) (.inr (stk', input)) := by
  have := sim_reduce hwf h p
  rw [hr] at this
  exact this

theorem sim_step {c : MConf} {m : MState} {stk : Stack (Tree Nat)}
    {input : List (Nat × Tree Nat)} (hwf : MWf c) (h : Rel c m stk input) :
    Sim c m (mstep c m) (step (traceTable c) stk input) := by
  have hs : topState (traceTable c) stk = m.state := h.state.symm
  simp only [Runtime.Exec.step, mstep, hs, traceTable_defaultReduce]
  by_cases hdr : c.tables.defaultReduce m.state = noneCell
  · simp only [hdr, decodeOpt, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [getD_input h.input]
    have hlt := look_term_lt hwf m
    have hnle : ¬ (c.look m).term ≥ c.nt := by omega
    simp only [traceTable_action, hnle, ↓reduceIte]
    generalize ha : c.tables.action m.state (c.look m).term = a
    simp only [decodeAct]
    by_cases ha0 : a = 0
    · simp only [ha0, ↓reduceIte]
      exact Sim.reject h.ti
    · by_cases hodd : a % 2 = 1
      · simp only [ha0, hodd, ↓reduceIte]
        have hl := ann_leaf_look c m
        rw [h.spanPrev] at hl
        refine Sim.cont ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [h.stack]
        · simp [h.nodes, Tree.events, Event.code]
        · exact drop_input h.input
        · have hlt' : (c.look m).term < prodFlag := Nat.lt_of_lt_of_le hlt hwf.ntFlag
          have := h.ti
          unfold tokCount at this ⊢
          simp [List.countP_append, hlt']
          omega
        · rw [annOf_cons, hl, h.spanNodes]
        · rw [annOf_cons, hl]; simp [h.spanStarts]
        · rw [annOf_cons, hl]
      · simp only [ha0, hodd, ↓reduceIte]
        cases hr : reduce (traceTable c) (a / 2 - 1) stk with
        | inl r => simp only; exact sim_reduce_inl hwf h _ hr
        | inr stk' => simp only; exact sim_reduce_inr hwf h _ hr
  · simp only [hdr, decodeOpt, ↓reduceIte, ne_eq, not_false_eq_true]
    cases hr : reduce (traceTable c) (c.tables.defaultReduce m.state) stk with
    | inl r => simp only; exact sim_reduce_inl hwf h _ hr
    | inr stk' => simp only; exact sim_reduce_inr hwf h _ hr

/-! ### Runs -/

/-- The end of a run of the machine corresponds to the result of `stepN`. -/
inductive RunSim (toks : List MTok) :
    MStop × List MEntry × List MNode →
      Result (Tree Nat) ⊕ (Stack (Tree Nat) × List (Nat × Tree Nat)) → Prop where
  /-- The machine ran out of fuel, and `Exec` did not stop in as many steps. -/
  | fuel {tk st : Nat} {stk : List MEntry} {nd : List MNode}
      {stk' : Stack (Tree Nat)} {input' : List (Nat × Tree Nat)} :
      RunSim toks (.err tk st termOutOfFuel, stk, nd) (.inr (stk', input'))
  /-- `Exec` rejects in the same state on the same terminal. The token index is the number of
      tokens that were shifted. -/
  | reject {tk st t : Nat} {stk : List MEntry} {nd : List MNode} (htk : tk = tokCount nd) :
      RunSim toks (.err tk st t, stk, nd) (.inl (.reject st t))
  /-- `Exec` fails because a reduction pops more cells than there are. -/
  | inconsistent {tk st : Nat} {stk : List MEntry} {nd : List MNode} {msg : String}
      (htk : tk = tokCount nd) :
      RunSim toks (.err tk st termInconsistent, stk, nd) (.inl (.err msg))
  /-- `Exec` accepts the tree `tree`; the nodes are the trace of the forest `rest` below it,
      then the trace of `tree`. -/
  | accept {stk : List MEntry} {nd : List MNode} {tree : Tree Nat} (rest : Stack (Tree Nat))
      (h : nd.map (·.kind) =
        (rest.reverse.flatMap (fun q => q.2.events) ++ tree.events).map Event.code)
      (hs : nd = (Tree.annForest toks 0 (rest.reverse.map (·.2) ++ [tree])).1) :
      RunSim toks (.ok, stk, nd) (.inl (.ok tree))

theorem sim_run {c : MConf} (hwf : MWf c) (n : Nat) :
    ∀ (m : MState) (stk : Stack (Tree Nat)) (input : List (Nat × Tree Nat)),
      Rel c m stk input → RunSim c.toks (mrunN c n m) (stepN (traceTable c) n stk input) := by
  induction n with
  | zero => intro m stk input _; exact RunSim.fuel
  | succ n ih =>
    intro m stk input h
    have hs := sim_step hwf h
    simp only [mrunN, stepN]
    revert hs
    generalize mstep c m = r1
    generalize step (traceTable c) stk input = r2
    intro hs
    cases hs with
    | cont h' => exact ih _ _ _ h'
    | reject htk => exact RunSim.reject htk
    | inconsistent htk => exact RunSim.inconsistent htk
    | accept rest hn hs => exact RunSim.accept rest hn hs

/-- From the initial variables: the run of the machine on `c` with `n` units of fuel
    corresponds to `n` steps of `Exec` on the tree-building table. -/
theorem sim_run_init {c : MConf} (hwf : MWf c) (n : Nat) :
    RunSim c.toks (mrunN c n MState.init)
      (stepN (traceTable c) n [] (traceInputFrom 0 c.toks)) :=
  sim_run hwf n _ _ _ (Rel.init c)

end Spec
