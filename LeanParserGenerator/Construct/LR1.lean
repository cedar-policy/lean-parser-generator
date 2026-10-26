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
LR(1) items and Pager-compatible automaton construction.

This module is entirely outside the trusted core. It builds canonical LR(1)
closures and transitions, then applies Menhir's two-phase variant of Pager's
algorithm: states with one LR(0) core are maintained as a family of pairwise
weakly-incompatible LR(1) states; compatible states are repeatedly fused; a
second traversal redirects candidate transitions to subsuming family members
and numbers only reachable final states.

The token-wise weak-compatibility criterion is the one used by current Menhir.
Our grammar has no distinguished `error` token, and the augmented `$` terminal
is an ordinary token, so Menhir's extra error/end-of-stream compatibility tests
do not apply here.
-/
public import LeanParserGenerator.Construct.LR0
public import Std.Data.HashMap


@[expose] public section

namespace Construct

open IR

/-! ### Canonical LR(1) item operations -/

/-- Sorted intersection of terminal sets. -/
def interNat (a b : List Nat) : List Nat :=
  a.foldl (fun acc x => if b.contains x then insertNat x acc else acc) []

/-- Set inclusion for terminal sets. -/
def subsetNat (a b : List Nat) : Bool := a.all b.contains

/-- Strict order on annotated items, ignoring lookaheads. -/
def AnnItem.lt (a b : AnnItem) : Bool :=
  a.prod < b.prod || (a.prod == b.prod && a.dot < b.dot)

/-- Insert an LR(1) item, merging lookaheads when its LR(0) core is present. -/
def insertAnnItem (x : AnnItem) : List AnnItem → List AnnItem
  | [] => [x]
  | y :: ys =>
      if x.prod == y.prod && x.dot == y.dot then
        { y with lookaheads := unionNat y.lookaheads x.lookaheads } :: ys
      else if AnnItem.lt x y then x :: y :: ys
      else y :: insertAnnItem x ys

/-- Canonicalize LR(1) items by core and merge equal-core lookahead sets. -/
def normAnnItems (items : List AnnItem) : List AnnItem :=
  items.foldl (fun acc item => insertAnnItem item acc) []

/-- Erase lookaheads from an LR(1) state. -/
def annItemCore (items : List AnnItem) : ItemSet :=
  items.map fun item => ⟨item.prod, item.dot⟩

/-- Lookaheads of an item at an aligned state position. -/
def looksAt (items : List AnnItem) (i : Nat) : List Nat :=
  match items[i]? with
  | some item => item.lookaheads
  | none => []

/-- Close LR(1) items under `A → α • B β [L]`: productions of `B` receive
    `FIRST(β)` and also `L` when `β` is nullable. -/
partial def lr1Closure (g : Grammar) (nul : Array Bool) (fst : Array (List Nat))
    (items : List AnnItem) : List AnnItem :=
  let rec loop (current : List AnnItem) : List AnnItem :=
    let next := current.foldl (fun acc item =>
      match g.prods[item.prod]? with
      | none => acc
      | some prod =>
        match prod.rhs[item.dot]? with
        | some (.nonterm nt) =>
          let rest := prod.rhs.drop (item.dot + 1)
          let inherited :=
            if rest.all (symNullable nul) then item.lookaheads else []
          let closureLooks := unionNat (firstOfSeq nul fst rest) inherited
          (g.prodsFor nt).foldl (fun acc' (prodIdx, _) =>
            insertAnnItem ⟨prodIdx, 0, closureLooks⟩ acc') acc
        | _ => acc) (normAnnItems current)
    if next == current then current else loop next
  loop (normAnnItems items)

/-- Advance an LR(1) state across one grammar symbol and close the result. -/
def lr1Goto (g : Grammar) (nul : Array Bool) (fst : Array (List Nat))
    (items : List AnnItem) (symbol : Sym) : List AnnItem :=
  let moved := items.foldl (fun acc item =>
    match g.prods[item.prod]? with
    | some prod =>
      if prod.rhs[item.dot]? == some symbol then
        insertAnnItem ⟨item.prod, item.dot + 1, item.lookaheads⟩ acc
      else acc
    | none => acc) []
  lr1Closure g nul fst moved

/-- Initial state for `S' → • S $`. Every terminal is a future lookahead so the
    resulting certificate satisfies the validator's `StartFuture` property;
    closure still gives original start productions only `$`. -/
def lr1Start (g : Grammar) (nul : Array Bool) (fst : Array (List Nat))
    (augProd : Nat) : List AnnItem :=
  lr1Closure g nul fst [⟨augProd, 0, List.range g.numTerminals⟩]

/-! ### Pager state relations -/

/-- Pointwise inclusion between same-core LR(1) states. -/
def lr1Subset (candidate state : List AnnItem) : Bool :=
  annItemCore candidate == annItemCore state &&
    (List.range candidate.length).all fun i =>
      subsetNat (looksAt candidate i) (looksAt state i)

/-- Pointwise union of same-core LR(1) states. -/
def lr1Union (left right : List AnnItem) : List AnnItem :=
  right.foldl (fun acc item => insertAnnItem item acc) left

/-- Menhir's token-wise weak Pager compatibility criterion. For each distinct
    pair of item cores, every token conflict introduced by union must already
    occur in one of the original states. Compatibility is intentionally not
    transitive, hence fusion repeatedly rechecks the growing candidate. -/
def pagerCompatible (left right : List AnnItem) : Bool :=
  if annItemCore left != annItemCore right then false
  else
    (List.range left.length).all fun i =>
      (List.range i).all fun j =>
        let lᵢ := looksAt left i
        let lⱼ := looksAt left j
        let rᵢ := looksAt right i
        let rⱼ := looksAt right j
        subsetNat (interNat rᵢ lⱼ) (unionNat lᵢ rⱼ) &&
          subsetNat (interNat lᵢ rⱼ) (unionNat rᵢ lⱼ)

/-- One family of discovered LR(1) states sharing an LR(0) core. -/
structure PagerFamily where
  core : ItemSet
  states : List (List AnnItem)
  deriving Repr, Inhabited

/-- Retrieve the family for a core. -/
def getFamily (families : List PagerFamily) (core : ItemSet) : List (List AnnItem) :=
  match families.find? (fun family => family.core == core) with
  | some family => family.states
  | none => []

/-- Replace or create the family for a core. -/
def setFamily (families : List PagerFamily) (core : ItemSet)
    (states : List (List AnnItem)) : List PagerFamily :=
  if families.any (fun family => family.core == core) then
    families.map fun family => if family.core == core then { family with states } else family
  else families ++ [⟨core, states⟩]

/-- Repeatedly fuse a candidate with compatible members of its family. -/
partial def fusePager (candidate : List AnnItem) (family : List (List AnnItem)) :
    List (List AnnItem) × List AnnItem :=
  match family.find? (pagerCompatible candidate) with
  | none => (family ++ [candidate], candidate)
  | some state =>
    let family' := family.filter (· != state)
    fusePager (lr1Union candidate state) family'

/-- Examine a candidate during Pager's first traversal. A candidate already
    subsumed by a family member is discarded; otherwise all compatible family
    members are fused and the resulting new state is scheduled. -/
def examinePager (families : List PagerFamily) (candidate : List AnnItem) :
    List PagerFamily × Option (List AnnItem) :=
  let core := annItemCore candidate
  let family := getFamily families core
  if family.any (lr1Subset candidate) then (families, none)
  else
    let (family', fused) := fusePager candidate family
    (setFamily families core family', some fused)

/-- First Pager traversal: discover and fuse state families without committing
    to final graph edges. -/
partial def discoverPager (g : Grammar) (nul : Array Bool) (fst : Array (List Nat))
    (root : List AnnItem) : List PagerFamily :=
  let rec loop (families : List PagerFamily) (frontier : List (List AnnItem)) :
      List PagerFamily :=
    match frontier with
    | [] => families
    | state :: rest =>
      let (families', frontier') :=
        (outSymbols g (annItemCore state)).foldl
          (fun (acc : List PagerFamily × List (List AnnItem)) symbol =>
            let (families, frontier) := acc
            let candidate := lr1Goto g nul fst state symbol
            let (families, scheduled) := examinePager families candidate
            match scheduled with
            | some next => (families, next :: frontier)
            | none => (families, frontier))
          (families, rest)
      loop families' frontier'
  loop [⟨annItemCore root, [root]⟩] [root]

/-- Redirect a candidate to the deterministic first final family member that
    subsumes it. Pager's first phase guarantees that one exists. -/
def redirectPager (families : List PagerFamily) (candidate : List AnnItem) :
    Option (List AnnItem) :=
  (getFamily families (annItemCore candidate)).find? (lr1Subset candidate)

/-- Number the reachable redirected graph in a second traversal. State 0 is the
    redirected augmented-start state, preserving the verified emitter's initial
    versus non-initial state representation. -/
partial def numberPager (g : Grammar) (nul : Array Bool) (fst : Array (List Nat))
    (root : List AnnItem) (families : List PagerFamily) : Collection :=
  let finalRoot := (redirectPager families root).getD root
  -- `index` maps each already-discovered state to its number, so the dedup lookup
  -- is O(1) instead of `states.findIdx?`'s linear scan over full item lists (which
  -- made numbering O(states² × itemsize)). It mirrors `states` exactly: a state is
  -- pushed to `states` and inserted into `index` together, so numbering order — and
  -- therefore the emitted automaton — is unchanged.
  let rec loop (states : Array (List AnnItem)) (index : Std.HashMap (List AnnItem) Nat)
      (trans : Array (List (Sym × Nat))) (worklist : List Nat) : Collection :=
    match worklist with
    | [] =>
      { states := states.map annItemCore
        trans
        lr1Items := states }
    | stateIdx :: rest =>
      match states[stateIdx]? with
      | none => loop states index trans rest
      | some state =>
        let (states, index, trans, newWork, edges) :=
          (outSymbols g (annItemCore state)).foldl
            (fun (acc : Array (List AnnItem) × Std.HashMap (List AnnItem) Nat ×
                Array (List (Sym × Nat)) × List Nat × List (Sym × Nat)) symbol =>
              let (states, index, trans, newWork, edges) := acc
              let candidate := lr1Goto g nul fst state symbol
              let target := (redirectPager families candidate).getD candidate
              match index[target]? with
              | some targetIdx =>
                (states, index, trans, newWork, edges ++ [(symbol, targetIdx)])
              | none =>
                let targetIdx := states.size
                (states.push target, index.insert target targetIdx, trans.push [],
                  newWork ++ [targetIdx], edges ++ [(symbol, targetIdx)]))
            (states, index, trans, [], [])
        let trans := trans.set! stateIdx edges
        loop states index trans (rest ++ newWork)
  loop #[finalRoot] (Std.HashMap.emptyWithCapacity.insert finalRoot 0) #[[]] [0]

/-- Construct the final Pager automaton for an already augmented grammar. -/
def pagerFrom (g : Grammar) (augProd : Nat) : Collection :=
  let nul := nullable g
  let fst := firstSets g
  let root := lr1Start g nul fst augProd
  numberPager g nul fst root (discoverPager g nul fst root)

/-- Construct the final Pager collection while augmenting the grammar. -/
def buildPager (g : Grammar) : Grammar × Nat × Collection :=
  let (g', augProd) := augment g
  (g', augProd, pagerFrom g' augProd)

end Construct
