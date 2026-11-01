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
import Spec.Trace

/-!
The spans of a trace.

The Rust parser gives every node of its trace a byte span, and Lean's `Exec` has none (and
gives an empty production the span `0..0`). The convention of the Rust parser is therefore
part of its specification, and this file states it as a function of the tree:

* a leaf, a shifted token, has the span of that token in the lexer's output; its value is the
  index of the token, and the end-of-input terminal read after the last token is a leaf with
  an index past the tokens, whose span is empty, at the end of the previous token;
* a reduction ends where the previous token ended, and starts where its first child starts, or,
  with no children, at the same place.

`Tree.ann toks prev t` is the trace of `t` with spans, where `prev` is the end of the token
before `t`, together with the start of `t` and the end of the last token in it (the `prev` of
whatever follows). `annForest` does it for the trees of a stack, from bottom to top.
-/

namespace Spec

mutual
/-- The postorder trace of a tree with spans, the start of the tree and the end of the last
    token up to its end. -/
def Tree.ann (toks : List MTok) (prev : Nat) : Tree Nat → List MNode × Nat × Nat
  | .leaf t k =>
    match toks[k]? with
    | some tok => ([⟨t, tok.start, tok.stop⟩], tok.start, tok.stop)
    | none => ([⟨t, prev, prev⟩], prev, prev)
  | .node p cs =>
    match Tree.annForest toks prev cs with
    | (ns, ss, pr) => (ns ++ [⟨prodFlag + p, ss.headD prev, pr⟩], ss.headD prev, pr)

/-- The same for trees side by side: the trace, the starts of the trees, and the end of the
    last token. -/
def Tree.annForest (toks : List MTok) (prev : Nat) :
    List (Tree Nat) → List MNode × List Nat × Nat
  | [] => ([], [], prev)
  | c :: cs =>
    match Tree.ann toks prev c with
    | (n1, s1, p1) =>
      match Tree.annForest toks p1 cs with
      | (n2, s2, p2) => (n1 ++ n2, s1 :: s2, p2)
end

@[simp] theorem annForest_nil (toks : List MTok) (prev : Nat) :
    Tree.annForest toks prev [] = ([], [], prev) := by
  simp [Tree.annForest]

theorem annForest_cons (toks : List MTok) (prev : Nat) (c : Tree Nat) (cs : List (Tree Nat)) :
    Tree.annForest toks prev (c :: cs) =
      ((Tree.ann toks prev c).1 ++ (Tree.annForest toks (Tree.ann toks prev c).2.2 cs).1,
       (Tree.ann toks prev c).2.1 :: (Tree.annForest toks (Tree.ann toks prev c).2.2 cs).2.1,
       (Tree.annForest toks (Tree.ann toks prev c).2.2 cs).2.2) := by
  simp [Tree.annForest]

theorem annForest_node (toks : List MTok) (prev p : Nat) (cs : List (Tree Nat)) :
    Tree.ann toks prev (.node p cs) =
      ((Tree.annForest toks prev cs).1 ++
         [⟨prodFlag + p, (Tree.annForest toks prev cs).2.1.headD prev,
           (Tree.annForest toks prev cs).2.2⟩],
       (Tree.annForest toks prev cs).2.1.headD prev, (Tree.annForest toks prev cs).2.2) := by
  simp [Tree.ann]

/-- The number of starts is the number of trees. -/
theorem annForest_length (toks : List MTok) (ts : List (Tree Nat)) :
    ∀ prev, (Tree.annForest toks prev ts).2.1.length = ts.length := by
  induction ts with
  | nil => intro prev; simp
  | cons c cs ih => intro prev; rw [annForest_cons]; simp [ih]

/-- A forest is annotated one part after the other. -/
theorem annForest_append (toks : List MTok) (xs ys : List (Tree Nat)) :
    ∀ prev, Tree.annForest toks prev (xs ++ ys) =
      ((Tree.annForest toks prev xs).1 ++
         (Tree.annForest toks (Tree.annForest toks prev xs).2.2 ys).1,
       (Tree.annForest toks prev xs).2.1 ++
         (Tree.annForest toks (Tree.annForest toks prev xs).2.2 ys).2.1,
       (Tree.annForest toks (Tree.annForest toks prev xs).2.2 ys).2.2) := by
  induction xs with
  | nil => intro prev; simp
  | cons c cs ih =>
    intro prev
    rw [List.cons_append, annForest_cons, ih, annForest_cons]
    simp [List.append_assoc]

end Spec
