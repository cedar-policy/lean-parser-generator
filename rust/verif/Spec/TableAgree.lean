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

import Spec.Fuel
import Spec.Trace

/-!
Two tables that agree where the parser looks are the same parser.

The tables that the Rust kernel reads are arrays with a fixed number of rows and columns; the
Lean tables are flat arrays read with `getD`, so a lookup outside the rectangle is not
comparable (a column past the last one reads the next row). `Agree` therefore compares the
tables only for `s < S`, `t < NT`, `n < NN` and `p < P`, and `TblWf` says that the table never
leaves that rectangle: a shift goes to a state, a goto gives a state, a reduction is by a
production, the left-hand side of a production is a nonterminal.

`stepN_sim` then says that `n` steps of the one table on a stack and an input are `n` steps of
the other on the same stack and input with `f` applied to the values, whenever the stack
only holds states below `S` and the input only terminals below `NT`. With `f = id` the two
tables simply agree; with `f` a map between trees it is the comparison of two tree-building
tables whose leaves differ (token indices in the Rust model, token values in Lean).
-/

namespace Spec

open Runtime.Exec

variable {V W : Type}

/-- The table stays inside the `S × NT` rectangle of actions, the `S × NN` rectangle of gotos
    and the `P` productions. -/
structure TblWf (T : ExecTable V) (S NT NN P : Nat) : Prop where
  start : T.startState < S
  eof : T.eof.1 < NT
  shift : ∀ s t s', s < S → t < NT → T.action s t = .shift s' → s' < S
  reduce : ∀ s t p, s < S → t < NT → T.action s t = .reduce p → p < P
  goto : ∀ s n s', s < S → n < NN → T.goto s n = some s' → s' < S
  defRed : ∀ s p, s < S → T.defaultReduce s = some p → p < P
  lhs : ∀ p, p < P → T.prodLhs p < NN

/-- `T'` is `T` inside the rectangle, with `f` applied to the values. -/
structure Agree (T : ExecTable V) (T' : ExecTable W) (f : V → W) (S NT NN P : Nat) : Prop where
  start : T'.startState = T.startState
  eof : T'.eof.1 = T.eof.1
  eofv : T'.eof.2 = f T.eof.2
  action : ∀ s t, s < S → t < NT → T'.action s t = T.action s t
  goto : ∀ s n, s < S → n < NN → T'.goto s n = T.goto s n
  defRed : ∀ s, s < S → T'.defaultReduce s = T.defaultReduce s
  lhs : ∀ p, p < P → T'.prodLhs p = T.prodLhs p
  rhs : ∀ p, p < P → T'.prodRhsLen p = T.prodRhsLen p
  sem : ∀ p args, T'.sem p (args.map f) = f (T.sem p args)

theorem popN_go_mem (n : Nat) (stk : Stack V) (acc : List V) (args : List V) (rest : Stack V)
    (h : popN.go n stk acc = some (args, rest)) : ∀ e ∈ rest, e ∈ stk := by
  induction n generalizing stk acc with
  | zero =>
    simp [popN.go] at h
    obtain ⟨_, rfl⟩ := h
    intro e he; exact he
  | succ n ih =>
    cases stk with
    | nil => simp [popN.go] at h
    | cons hd tl =>
      obtain ⟨s, v⟩ := hd
      simp only [popN.go] at h
      intro e he
      exact List.mem_cons_of_mem _ (ih tl (v :: acc) h e he)

theorem popN_mem (n : Nat) (stk : Stack V) (args : List V) (rest : Stack V)
    (h : popN n stk = some (args, rest)) : ∀ e ∈ rest, e ∈ stk :=
  popN_go_mem n stk [] args rest h

section
variable {T : ExecTable V} {T' : ExecTable W} {f : V → W} {S NT NN P : Nat}

theorem topState_lt (hT : TblWf T S NT NN P) (stk : Stack V) (hs : ∀ e ∈ stk, e.1 < S) :
    topState T stk < S := by
  cases stk with
  | nil => exact hT.start
  | cons hd tl => exact hs hd (List.mem_cons_self ..)

theorem topState_sim (hA : Agree T T' f S NT NN P) (stk : Stack V) :
    topState T' (mapStack f stk) = topState T stk := by
  cases stk with
  | nil => exact hA.start
  | cons hd tl => rfl

theorem reduce_sim (hT : TblWf T S NT NN P) (hA : Agree T T' f S NT NN P) (p : Nat)
    (hp : p < P) (stk : Stack V) (hs : ∀ e ∈ stk, e.1 < S) :
    reduce T' p (mapStack f stk) = mapReduce f (reduce T p stk) ∧
    ∀ stk', reduce T p stk = .inr stk' → ∀ e ∈ stk', e.1 < S := by
  unfold reduce
  rw [hA.rhs p hp, popN_map]
  cases hpop : popN (T.prodRhsLen p) stk with
  | none => simp [mapReduce, mapResult]
  | some r =>
    obtain ⟨args, rest⟩ := r
    have hrest : ∀ e ∈ rest, e.1 < S := fun e he => hs e (popN_mem _ _ _ _ hpop e he)
    have htop := topState_lt hT rest hrest
    have hlhs := hT.lhs p hp
    simp only [Option.map_some]
    rw [topState_sim hA, hA.goto _ _ htop (hA.lhs p hp ▸ hlhs), hA.lhs p hp]
    cases hg : T.goto (topState T rest) (T.prodLhs p) with
    | none =>
      simp [mapReduce, mapResult, hA.sem]
    | some s' =>
      have hs' := hT.goto _ _ s' htop hlhs hg
      refine ⟨by simp [mapReduce, mapStack, hA.sem], ?_⟩
      intro stk' h
      simp only [Sum.inr.injEq] at h
      subst h
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hs'
      · exact hrest e he

theorem step_sim (hT : TblWf T S NT NN P) (hA : Agree T T' f S NT NN P)
    (stk : Stack V) (input : List (Nat × V))
    (hs : ∀ e ∈ stk, e.1 < S) (hi : ∀ e ∈ input, e.1 < NT) :
    step T' (mapStack f stk) (mapInput f input) = mapStep f (step T stk input) ∧
    ∀ stk' input', step T stk input = .inr (stk', input') →
      (∀ e ∈ stk', e.1 < S) ∧ (∀ e ∈ input', e.1 < NT) := by
  have htop := topState_lt hT stk hs
  have hget : (input.getD 0 T.eof).1 < NT := by
    cases input with
    | nil => exact hT.eof
    | cons hd tl => exact hi hd (List.mem_cons_self ..)
  have hget' : (mapInput f input).getD 0 T'.eof = ((input.getD 0 T.eof).1, f (input.getD 0 T.eof).2) := by
    cases input with
    | nil => simpa [mapInput] using Prod.ext hA.eof hA.eofv
    | cons hd tl => simp [mapInput]
  have hdrop : ∀ e ∈ input.drop 1, e.1 < NT := fun e he =>
    hi e (List.mem_of_mem_drop he)
  simp only [step, topState_sim hA, hA.defRed _ htop]
  cases hd : T.defaultReduce (topState T stk) with
  | some p =>
    have hp := hT.defRed _ _ htop hd
    obtain ⟨h1, h2⟩ := reduce_sim hT hA p hp stk hs
    simp only [hd]
    rw [h1]
    cases hr : reduce T p stk with
    | inl r => simp [mapReduce, mapStep]
    | inr stk' =>
      refine ⟨by simp [mapReduce, mapStep], ?_⟩
      intro a b h
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h2 _ hr, hi⟩
  | none =>
    simp only [hd]
    rw [hget']
    simp only
    rw [hA.action _ _ htop hget]
    cases ha : T.action (topState T stk) (input.getD 0 T.eof).1 with
    | shift s' =>
      have hs' := hT.shift _ _ s' htop hget ha
      refine ⟨by simp [mapStep, mapStack, mapInput], ?_⟩
      intro a b h
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hdrop⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hs'
      · exact hs e he
    | reduce p =>
      have hp := hT.reduce _ _ p htop hget ha
      obtain ⟨h1, h2⟩ := reduce_sim hT hA p hp stk hs
      simp only
      rw [h1]
      cases hr : reduce T p stk with
      | inl r => simp [mapReduce, mapStep]
      | inr stk' =>
        refine ⟨by simp [mapReduce, mapStep], ?_⟩
        intro a b h
        simp only [Sum.inr.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨h2 _ hr, hi⟩
    | accept =>
      cases stk with
      | nil => simp [mapStack, mapStep, mapResult]
      | cons hd tl => simp [mapStack, mapStep, mapResult]
    | error => simp [mapStep, mapResult]

theorem stepN_sim (hT : TblWf T S NT NN P) (hA : Agree T T' f S NT NN P) (n : Nat) :
    ∀ (stk : Stack V) (input : List (Nat × V)),
      (∀ e ∈ stk, e.1 < S) → (∀ e ∈ input, e.1 < NT) →
      stepN T' n (mapStack f stk) (mapInput f input) = mapStep f (stepN T n stk input) := by
  induction n with
  | zero => intro stk input _ _; simp [stepN, mapStep]
  | succ n ih =>
    intro stk input hs hi
    obtain ⟨h1, h2⟩ := step_sim hT hA stk input hs hi
    simp only [stepN]
    rw [h1]
    cases hst : step T stk input with
    | inl r => simp [mapStep]
    | inr si =>
      obtain ⟨stk', input'⟩ := si
      obtain ⟨hs', hi'⟩ := h2 stk' input' hst
      simp only [mapStep, Sum.map_inr]
      exact ih stk' input' hs' hi'

end

/-! ### Changing the values of the leaves -/

mutual
/-- Apply `g` to the values of the leaves. -/
def Tree.map (g : V → W) : Tree V → Tree W
  | .leaf t v => .leaf t (g v)
  | .node p cs => .node p (Tree.mapList g cs)

def Tree.mapList (g : V → W) : List (Tree V) → List (Tree W)
  | [] => []
  | c :: cs => Tree.map g c :: Tree.mapList g cs
end

theorem Tree.mapList_eq_map (g : V → W) (cs : List (Tree V)) :
    Tree.mapList g cs = cs.map (Tree.map g) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Tree.mapList, ih]

theorem Tree.map_node (g : V → W) (p : Nat) (cs : List (Tree V)) :
    Tree.map g (.node p cs) = .node p (cs.map (Tree.map g)) := by
  simp [Tree.map, Tree.mapList_eq_map]

/-- `R` and `L` are the same automaton inside the rectangle: everything but the values. -/
structure SameAutomaton (R : ExecTable V) (L : ExecTable W) (S NT NN P : Nat) : Prop where
  start : L.startState = R.startState
  eof : L.eof.1 = R.eof.1
  action : ∀ s t, s < S → t < NT → L.action s t = R.action s t
  goto : ∀ s n, s < S → n < NN → L.goto s n = R.goto s n
  defRed : ∀ s, s < S → L.defaultReduce s = R.defaultReduce s
  lhs : ∀ p, p < P → L.prodLhs p = R.prodLhs p
  rhs : ∀ p, p < P → L.prodRhsLen p = R.prodRhsLen p

/-- The tree tables of the same automaton agree, with `Tree.map g` on the values, if `g` maps
    the end-of-input value of the one to that of the other. -/
theorem agree_tree {R : ExecTable V} {L : ExecTable W} {S NT NN P : Nat}
    (h : SameAutomaton R L S NT NN P) (g : V → W) (hg : g R.eof.2 = L.eof.2) :
    Agree (treeTable R) (treeTable L) (Tree.map g) S NT NN P where
  start := h.start
  eof := h.eof
  eofv := by simp [treeTable, Tree.map, hg, h.eof]
  action := h.action
  goto := h.goto
  defRed := h.defRed
  lhs := h.lhs
  rhs := h.rhs
  sem := by intro p args; simp [treeTable, Tree.map_node]

theorem tblWf_tree {R : ExecTable V} {S NT NN P : Nat} (h : TblWf R S NT NN P) :
    TblWf (treeTable R) S NT NN P where
  start := h.start
  eof := h.eof
  shift := h.shift
  reduce := h.reduce
  goto := h.goto
  defRed := h.defRed
  lhs := h.lhs

/-! ### More fuel -/

theorem stepN_mono (T : ExecTable V) {n m : Nat} (hnm : n ≤ m) (stk : Stack V)
    (input : List (Nat × V)) {r : Result V} (h : stepN T n stk input = .inl r) :
    stepN T m stk input = .inl r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [stepN_add, h]

/-- `Exec.run` with `logN`, when it does not time out, is the result of any number of steps
    beyond `2 ^ logN`. -/
theorem run_of_stepN (T : ExecTable V) (input : List (Nat × V)) (logN n : Nat)
    (hn : 2 ^ logN ≤ n) (h : run T input logN ≠ .timeout) :
    stepN T n [] input = .inl (run T input logN) := by
  rw [run_eq_stepN] at h ⊢
  cases hs : stepN T (2 ^ logN) [] input with
  | inl r => simp only; exact stepN_mono T hn _ _ hs
  | inr _ => rw [hs] at h; exact absurd rfl h

end Spec
