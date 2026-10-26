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
The LR(0) automaton skeleton.

Builds the canonical collection of LR(0) item sets for a grammar:
  * `augment`     : add a fresh start nonterminal `S'` and end terminal `$`,
                    plus the production `S' → S $`;
  * `closure`     : complete an item set under the •-before-nonterminal rule;
  * goto          : the transition on a grammar symbol;
  * `build`       : the worklist that discovers all states and transitions.

The state numbering and cores are reused by legacy SLR diagnostics and by the
LR(1)/Pager construction (`Construct/LR1.lean`).
-/
public import LeanParserGenerator.Construct.Analysis


@[expose] public section

namespace Construct

open IR

/-- An LR(0) item: a production index and the dot position within its RHS. -/
structure Item where
  /-- Index into the (augmented) grammar's `prods`. -/
  prod : Nat
  /-- Dot position: `0 ≤ dot ≤ rhs.length`. -/
  dot : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- An LR(1) item exposed to construction and certificate generation: an LR(0)
    core plus its sorted terminal lookahead set. -/
structure AnnItem where
  /-- Production index in the augmented grammar. -/
  prod : Nat
  /-- Dot position in the production right-hand side. -/
  dot : Nat
  /-- Sorted, duplicate-free terminal lookaheads. -/
  lookaheads : List Nat
  deriving Repr, DecidableEq, Hashable, Inhabited

/-- Strict lexicographic order on items (`prod`, then `dot`). -/
def Item.lt (a b : Item) : Bool :=
  a.prod < b.prod || (a.prod == b.prod && a.dot < b.dot)

/-- A state is a canonicalized (sorted, duplicate-free) set of items. -/
abbrev ItemSet := List Item

/-- Sorted-insert an item into an `ItemSet`. -/
def insertItem (x : Item) : ItemSet → ItemSet
  | [] => [x]
  | y :: ys =>
    if x == y then y :: ys
    else if Item.lt x y then x :: y :: ys
    else y :: insertItem x ys

/-- Canonicalize a list of items into a sorted, duplicate-free `ItemSet`. -/
def normItems (l : List Item) : ItemSet := l.foldl (fun acc x => insertItem x acc) []

/-- Augment a grammar with a fresh end terminal `$`, a fresh start nonterminal
    `S'`, and the production `S' → S $`. Returns the augmented grammar together
    with the index of that production. Original terminal/nonterminal/production
    indices are preserved.

    Including `$` in the augmented production is essential for completeness: it
    makes the start language prefix-free and propagates only `$` as the lookahead
    of original start productions, while the completed augmented production can
    reduce independently of the following padded stream. -/
def augment (g : Grammar) : Grammar × Nat :=
  let augProd : Prod :=
    ⟨g.numNonterminals, [.nonterm g.start, .term g.numTerminals]⟩
  let g' : Grammar := {
    numTerminals := g.numTerminals + 1
    numNonterminals := g.numNonterminals + 1
    prods := g.prods.push augProd
    start := g.numNonterminals
    termNames := g.termNames.push "$"
    nontermNames := g.nontermNames.push "S'"
  }
  (g', g.prods.size)

/-- The symbol immediately after the dot, if any. -/
def Item.next (g : Grammar) (it : Item) : Option Sym :=
  match g.prods[it.prod]? with
  | some p => p.rhs[it.dot]?
  | none => none

/-- The closure of an item set: repeatedly, for every item `A → α•Bβ` with `B` a
    nonterminal, add `B → •γ` for each production of `B`. -/
partial def closure (g : Grammar) (items : ItemSet) : ItemSet :=
  let rec loop (cur : ItemSet) : ItemSet :=
    let added := cur.foldl (fun acc it =>
      match it.next g with
      | some (.nonterm b) =>
          (g.prodsFor b).foldl (fun acc2 (i, _) => insertItem ⟨i, 0⟩ acc2) acc
      | _ => acc) cur
    if added == cur then cur else loop added
  loop (normItems items)

/-- The goto transition: advance the dot past `X` in every item of `items` that
    has `X` right after the dot, then take the closure. -/
def goto (g : Grammar) (items : ItemSet) (X : Sym) : ItemSet :=
  let moved := items.filterMap (fun it =>
    if it.next g = some X then some (Item.mk it.prod (it.dot + 1)) else none)
  closure g (normItems moved)

/-- The set of symbols appearing immediately after a dot in a state (the symbols
    on which the state has outgoing transitions). -/
def outSymbols (g : Grammar) (items : ItemSet) : List Sym :=
  items.foldl (fun acc it =>
    match it.next g with
    | some X => if acc.contains X then acc else acc ++ [X]
    | none => acc) []

/-- The canonical collection of LR(0) item sets, with transitions. -/
structure Collection where
  /-- The discovered states (item sets), indexed by position. State 0 is the
      initial state `closure {S' → •S}`. -/
  states : Array ItemSet
  /-- `trans[i]` lists this state's `(symbol, targetStateIndex)` transitions. -/
  trans : Array (List (Sym × Nat))
  /-- Exact LR(1) items for each final state. Pager construction populates this;
      the LR(0) compatibility builder leaves it empty. -/
  lr1Items : Array (List AnnItem) := #[]
  deriving Repr, Inhabited

/-- Build the canonical collection for an already-augmented grammar with initial
    item `⟨augProd, 0⟩`. Worklist over undiscovered states. -/
partial def buildFrom (g : Grammar) (augProd : Nat) : Collection :=
  let init := closure g [⟨augProd, 0⟩]
  let rec loop (states : Array ItemSet) (trans : Array (List (Sym × Nat)))
      (worklist : List Nat) : Collection :=
    match worklist with
    | [] => ⟨states, trans, #[]⟩
    | i :: rest =>
      match states[i]? with
      | none => loop states trans rest
      | some st =>
        let (states, trans, newWork, edges) :=
          (outSymbols g st).foldl
            (fun (acc : Array ItemSet × Array (List (Sym × Nat)) × List Nat × List (Sym × Nat)) X =>
              let (states, trans, newWork, edges) := acc
              let tgt := goto g st X
              match states.findIdx? (· == tgt) with
              | some j => (states, trans, newWork, edges ++ [(X, j)])
              | none =>
                  let j := states.size
                  (states.push tgt, trans.push [], newWork ++ [j], edges ++ [(X, j)]))
            (states, trans, [], [])
        let trans := trans.set! i edges
        loop states trans (rest ++ newWork)
  loop #[init] #[[]] [0]

/-- Build the canonical collection for a grammar (augmenting it first). Returns the
    augmented grammar, the augmented start production index, and the collection. -/
def build (g : Grammar) : Grammar × Nat × Collection :=
  let (g', augProd) := augment g
  (g', augProd, buildFrom g' augProd)

end Construct
