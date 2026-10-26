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
/-
Construct the nullable and FIRST sets by a fixpoint over the grammar.
  * `nullable`  : which nonterminals derive the empty string;
  * `firstSets` : the FIRST set (set of terminal indices) of each nonterminal.

Both iterate a monotone fixpoint. They feed Pager closure and the generated
`nullableNt`/`firstNt` certificate annotations.

See tests in `test/pager/ConstructionRegressionTest.lean`.
-/
public import LeanParserGenerator.IR.Grammar


@[expose] public section

namespace Construct

open IR

/-- Sorted-insert into a sorted, duplicate-free list of nats (our set repr).
  TODO: can we improve that repr and maintain the decidability of the generated
  proof obligations?
-/
def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insertNat x ys

/-- Union of two nat-sets (kept sorted and duplicate-free). -/
def unionNat (a b : List Nat) : List Nat := b.foldl (fun acc x => insertNat x acc) a

/-! ### Nullable -/

/-- Is a symbol nullable under the current nullable-assignment `cur`? -/
def symNullable (cur : Array Bool) : Sym → Bool
  | .term _ => false
  | .nonterm i => cur.getD i false

/-- One monotone step of the nullable fixpoint: a nonterminal is nullable if any
    of its productions has an all-nullable right-hand side. -/
def nullableStep (g : Grammar) (cur : Array Bool) : Array Bool :=
  (Array.range g.numNonterminals).map (fun nt =>
    (g.prodsFor nt).any (fun (_, p) => p.rhs.all (symNullable cur)))

/-- The nullable set of a grammar: iterate `nullableStep` to a fixpoint. At most
    `numNonterminals` iterations are needed (each adds ≥1 nonterminal or stops). -/
partial def nullable (g : Grammar) : Array Bool :=
  let rec loop (cur : Array Bool) (fuel : Nat) : Array Bool :=
    match fuel with
    | 0 => cur
    | fuel + 1 =>
      let next := nullableStep g cur
      if next == cur then cur else loop next fuel
  loop (Array.replicate g.numNonterminals false) (g.numNonterminals + 1)

/-! ### FIRST -/

/-- FIRST of a symbol under the current first-set assignment. -/
def firstOfSym (_nul : Array Bool) (first : Array (List Nat)) : Sym → List Nat
  | .term t => [t]
  | .nonterm i => first.getD i []

/-- FIRST of a symbol sequence: accumulate FIRST across a nullable prefix. -/
def firstOfSeq (nul : Array Bool) (first : Array (List Nat)) : List Sym → List Nat
  | [] => []
  | s :: rest =>
    let fs := firstOfSym nul first s
    if symNullable nul s then unionNat fs (firstOfSeq nul first rest) else fs

/-- One monotone step of the FIRST fixpoint. -/
def firstStep (g : Grammar) (nul : Array Bool) (cur : Array (List Nat)) :
    Array (List Nat) :=
  (Array.range g.numNonterminals).map (fun nt =>
    (g.prodsFor nt).foldl
      (fun acc (_, p) => unionNat acc (firstOfSeq nul cur p.rhs))
      (cur.getD nt []))

/-- The FIRST sets of a grammar: iterate `firstStep` to a fixpoint. -/
partial def firstSets (g : Grammar) : Array (List Nat) :=
  let nul := nullable g
  let rec loop (cur : Array (List Nat)) (fuel : Nat) : Array (List Nat) :=
    match fuel with
    | 0 => cur
    | fuel + 1 =>
      let next := firstStep g nul cur
      if next == cur then cur else loop next fuel
  loop (Array.replicate g.numNonterminals []) (g.numNonterminals * g.numTerminals + 1)

/-- FIRST of a sequence, exposed with a grammar's own nullable/first tables. -/
def firstOfSeqIn (g : Grammar) (rhs : List Sym) : List Nat :=
  firstOfSeq (nullable g) (firstSets g) rhs

end Construct
