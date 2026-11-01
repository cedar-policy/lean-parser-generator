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
The parse tree of `Runtime.Exec.run`, and the fact that the semantic actions only evaluate it.

The Rust parser returns a postorder trace of the reductions it made and the tokens it
shifted, not a semantic value. This file defines that trace on the Lean side and proves that
it is all there is to `Exec.run`: running a table with any semantic actions gives the result
of evaluating, with those actions, the tree that the same table builds when its action is
"make a node". So a statement about the trace is a statement about every semantics of the
grammar at once, and the Rust trace only needs to be compared with the tree.

* `Tree V` is the parse tree. A leaf is a shifted token (its terminal and its value); a node
  is a reduction (its production and its children, left to right).
* `Tree.events` is the postorder trace of a tree: the list the Rust parser writes (without
  spans, which Lean's `Exec` does not have; see the end of this file).
* `treeTable tbl` is `tbl` with the action "make a node" and the token values wrapped as
  leaves.
* `run_eq_eval`: `run tbl input = (run (treeTable tbl) (treeInput input)).map eval`, for
  every table, input and fuel. This includes the failure cases: the same fuel gives the same
  `reject`, `timeout` or `err`.
-/

namespace Spec

open Runtime.Exec

variable {V W : Type}

/-! ### Trees and their postorder -/

/-- A parse tree whose leaves carry the value of a shifted token. -/
inductive Tree (V : Type) where
  /-- A shifted token: its terminal index and its value. -/
  | leaf (term : Nat) (val : V)
  /-- A reduction by production `prod`; the children are its right-hand side, left to right. -/
  | node (prod : Nat) (children : List (Tree V))

/-- An element of a postorder trace. -/
inductive Event where
  | tok (term : Nat)
  | red (prod : Nat)
  deriving DecidableEq, Repr

mutual
/-- The value of a tree: leaves give their value, a node applies the action of its production
    to the values of its children. -/
def Tree.eval (sem : Nat → List V → V) : Tree V → V
  | .leaf _ v => v
  | .node p cs => sem p (Tree.evalList sem cs)

def Tree.evalList (sem : Nat → List V → V) : List (Tree V) → List V
  | [] => []
  | c :: cs => Tree.eval sem c :: Tree.evalList sem cs
end

mutual
/-- The postorder trace of a tree: the trace of the children, then the node itself. -/
def Tree.events : Tree V → List Event
  | .leaf t _ => [.tok t]
  | .node p cs => Tree.eventsList cs ++ [.red p]

def Tree.eventsList : List (Tree V) → List Event
  | [] => []
  | c :: cs => Tree.events c ++ Tree.eventsList cs
end

theorem Tree.evalList_eq_map (sem : Nat → List V → V) (cs : List (Tree V)) :
    Tree.evalList sem cs = cs.map (Tree.eval sem) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Tree.evalList, ih]

@[simp] theorem Tree.eval_leaf (sem : Nat → List V → V) (t : Nat) (v : V) :
    Tree.eval sem (.leaf t v) = v := rfl

theorem Tree.eval_node (sem : Nat → List V → V) (p : Nat) (cs : List (Tree V)) :
    Tree.eval sem (.node p cs) = sem p (cs.map (Tree.eval sem)) := by
  simp [Tree.eval, Tree.evalList_eq_map]

/-! ### The tree-building table -/

/-- `tbl` with the semantic action "make a node", on token values wrapped as leaves. Only the
    action and the end-of-input value change; the automaton is `tbl`'s. -/
def treeTable (tbl : ExecTable V) : ExecTable (Tree V) where
  numStates := tbl.numStates
  startState := tbl.startState
  eof := (tbl.eof.1, .leaf tbl.eof.1 tbl.eof.2)
  action := tbl.action
  goto := tbl.goto
  defaultReduce := tbl.defaultReduce
  prodLhs := tbl.prodLhs
  prodRhsLen := tbl.prodRhsLen
  sem := fun p args => .node p args

/-- The input of `treeTable tbl` for the input `input` of `tbl`. -/
def treeInput (input : List (Nat × V)) : List (Nat × Tree V) :=
  input.map fun (t, v) => (t, .leaf t v)

/-! ### Mapping results -/

/-- Apply `f` to the value of an accepted result. -/
def mapResult (f : V → W) : Result V → Result W
  | .ok v => .ok (f v)
  | .reject s t => .reject s t
  | .timeout => .timeout
  | .err m => .err m

/-- Apply `f` to the values of a stack. -/
def mapStack (f : V → W) : Stack V → Stack W :=
  List.map fun (s, v) => (s, f v)

/-- Apply `f` to the values of an input. -/
def mapInput (f : V → W) : List (Nat × V) → List (Nat × W) :=
  List.map fun (t, v) => (t, f v)

/-- Apply `f` to the values in the outcome of a reduction. -/
def mapReduce (f : V → W) : Result V ⊕ Stack V → Result W ⊕ Stack W :=
  Sum.map (mapResult f) (mapStack f)

/-- Apply `f` to the values in the outcome of a step. -/
def mapStep (f : V → W) :
    Result V ⊕ (Stack V × List (Nat × V)) → Result W ⊕ (Stack W × List (Nat × W)) :=
  Sum.map (mapResult f) fun (stk, input) => (mapStack f stk, mapInput f input)

/-! ### The step relation -/

section
variable (tbl : ExecTable V)

@[simp] theorem treeTable_goto : (treeTable tbl).goto = tbl.goto := rfl
@[simp] theorem treeTable_prodLhs : (treeTable tbl).prodLhs = tbl.prodLhs := rfl
@[simp] theorem treeTable_prodRhsLen : (treeTable tbl).prodRhsLen = tbl.prodRhsLen := rfl
@[simp] theorem treeTable_action : (treeTable tbl).action = tbl.action := rfl
@[simp] theorem treeTable_defaultReduce : (treeTable tbl).defaultReduce = tbl.defaultReduce := rfl

theorem topState_map (stk : Stack (Tree V)) :
    topState (treeTable tbl) stk = topState tbl (mapStack (Tree.eval tbl.sem) stk) := by
  cases stk with
  | nil => rfl
  | cons hd tl => rfl

theorem popN_go_map (f : V → W) (n : Nat) (stk : Stack V) (acc : List V) :
    popN.go n (mapStack f stk) (acc.map f) =
      (popN.go n stk acc).map fun (args, rest) => (args.map f, mapStack f rest) := by
  induction n generalizing stk acc with
  | zero => simp [popN.go]
  | succ n ih =>
    cases stk with
    | nil => simp [popN.go, mapStack]
    | cons hd tl =>
      obtain ⟨s, v⟩ := hd
      simpa [mapStack, popN.go] using ih tl (v :: acc)

theorem popN_map (f : V → W) (n : Nat) (stk : Stack V) :
    popN n (mapStack f stk) =
      (popN n stk).map fun (args, rest) => (args.map f, mapStack f rest) := by
  simpa [popN] using popN_go_map f n stk []

/-- A reduction commutes with evaluation: reducing the evaluated stack by `tbl` is evaluating
    the result of reducing the stack of trees by `treeTable tbl`. -/
theorem reduce_map (p : Nat) (stk : Stack (Tree V)) :
    reduce tbl p (mapStack (Tree.eval tbl.sem) stk) =
      mapReduce (Tree.eval tbl.sem) (reduce (treeTable tbl) p stk) := by
  unfold reduce
  rw [treeTable_prodRhsLen, popN_map]
  cases hpop : popN (tbl.prodRhsLen p) stk with
  | none => rfl
  | some r =>
    obtain ⟨args, rest⟩ := r
    simp only [Option.map_some, treeTable_goto, treeTable_prodLhs, ← topState_map tbl rest]
    cases hg : tbl.goto (topState (treeTable tbl) rest) (tbl.prodLhs p) with
    | none => simp [mapReduce, mapResult, treeTable, Tree.eval_node]
    | some s' => simp [mapReduce, mapStack, treeTable, Tree.eval_node]

theorem getD_map (input : List (Nat × Tree V)) :
    (mapInput (Tree.eval tbl.sem) input).getD 0 tbl.eof =
      ((input.getD 0 (treeTable tbl).eof).1,
       Tree.eval tbl.sem (input.getD 0 (treeTable tbl).eof).2) := by
  cases input with
  | nil => simp [mapInput, treeTable]
  | cons hd tl => simp [mapInput]

/-- A step commutes with evaluation. -/
theorem step_map (stk : Stack (Tree V)) (input : List (Nat × Tree V)) :
    step tbl (mapStack (Tree.eval tbl.sem) stk) (mapInput (Tree.eval tbl.sem) input) =
      mapStep (Tree.eval tbl.sem) (step (treeTable tbl) stk input) := by
  unfold step
  rw [← topState_map tbl stk]
  rw [treeTable_defaultReduce]
  cases hd : tbl.defaultReduce (topState (treeTable tbl) stk) with
  | some p =>
    simp only [hd]
    rw [reduce_map]
    cases reduce (treeTable tbl) p stk with
    | inl r => simp [mapReduce, mapStep]
    | inr stk' => simp [mapReduce, mapStep]
  | none =>
    simp only [hd]
    rw [getD_map, treeTable_action]
    obtain ⟨t, tr⟩ := input.getD 0 (treeTable tbl).eof
    simp only
    cases tbl.action (topState (treeTable tbl) stk) t with
    | shift s' =>
      simp [mapStep, mapStack, mapInput]
    | reduce p =>
      simp only
      rw [reduce_map]
      cases reduce (treeTable tbl) p stk with
      | inl r => simp [mapReduce, mapStep]
      | inr stk' => simp [mapReduce, mapStep]
    | accept =>
      cases stk with
      | nil => simp [mapStack, mapStep, mapResult]
      | cons hd tl => simp [mapStack, mapStep, mapResult]
    | error => simp [mapStep, mapResult]

/-- The logarithmic-fuel iteration commutes with evaluation. -/
theorem parseFix_map (logN : Nat) (stk : Stack (Tree V)) (input : List (Nat × Tree V)) :
    parseFix tbl (mapStack (Tree.eval tbl.sem) stk) (mapInput (Tree.eval tbl.sem) input) logN =
      mapStep (Tree.eval tbl.sem) (parseFix (treeTable tbl) stk input logN) := by
  induction logN generalizing stk input with
  | zero => exact step_map tbl stk input
  | succ n ih =>
    simp only [parseFix, ih]
    cases parseFix (treeTable tbl) stk input n with
    | inl r => simp [mapStep]
    | inr si =>
      obtain ⟨stk', input'⟩ := si
      simp only [mapStep, Sum.map_inr]
      exact ih stk' input'

theorem run_map (input : List (Nat × Tree V)) (logN : Nat) :
    run tbl (mapInput (Tree.eval tbl.sem) input) logN =
      mapResult (Tree.eval tbl.sem) (run (treeTable tbl) input logN) := by
  unfold run
  have h := parseFix_map tbl logN [] input
  simp only [mapStack, List.map_nil] at h
  rw [h]
  cases parseFix (treeTable tbl) [] input logN with
  | inl r => simp [mapStep]
  | inr _ => simp [mapStep, mapResult]

end

/-- **`Exec.run` only evaluates the parse tree.** Running `tbl` on `input` is evaluating, with
    the actions of `tbl`, the result of running the tree-building table on the same input, with
    the same fuel. In particular `tbl` accepts, rejects (at the same state and terminal), times
    out or fails exactly when `treeTable tbl` does. -/
theorem run_eq_eval (tbl : ExecTable V) (input : List (Nat × V)) (logN : Nat) :
    run tbl input logN =
      mapResult (Tree.eval tbl.sem) (run (treeTable tbl) (treeInput input) logN) := by
  have h : mapInput (Tree.eval tbl.sem) (treeInput input) = input := by
    simp [mapInput, treeInput, List.map_map, Function.comp_def]
  have := run_map tbl (treeInput input) logN
  rwa [h] at this

end Spec
