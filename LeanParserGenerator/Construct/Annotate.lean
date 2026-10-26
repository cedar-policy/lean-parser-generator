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
Certificate annotations for the dependent specification.

The verified `Runtime.Automaton` comes with five *annotations* that the safety and
completeness validators (`safeValidator`, `completeValidator`) check at build
time via `native_decide`:

  * `lastSymb   : NonInitState → Symbol`      — incoming edge symbol of a state;
  * `pastSymb   : NonInitState → List Symbol` — symbols just below the top;
  * `pastStates : NonInitState → List StateSet` — the states that can sit at each
                  depth below the top (a list of *sets* of states);
  * `items      : State → List Item`          — the LR(1) item cores + lookaheads;
  * `nullableNt`, `firstNt`                    — reused from `Construct/Analysis`.
See `Runtime.Validator.Safe` and `Runtime.Validator.Complete` for how these
annotations enter the safety and completeness checks.

The graph annotations are derived from the final Pager `Collection`; `items` is
the exact `lr1Items` payload used to build reduction tables. They are not trusted:
if Pager construction or this deriver is wrong, generated `safetyValidation` or
`completenessValidation` fails to elaborate, rejecting the parser at compile
time. The annotations serve only as the automaton certificate; once validation
succeeds they are no longer needed operationally.

The derivation from the final graph:
  * reverse transitions to obtain predecessors;
  * `lastSymb s` = the common symbol labelling edges into `s`;
  * `pastSymb`/`pastStates` = a backward breadth-first walk from `s`;
  * `items s` = the exact closed LR(1) state selected by Pager.

State-set predicates are shared and deduplicated: `stateSets` is the pool of
distinct sets, and `pastStates s` is a list of indices into it.
-/
public import LeanParserGenerator.Construct.Tables


@[expose] public section

namespace Construct

open IR

/-- The full annotation certificate for an augmented grammar's automaton. All
    fields are indexed by final Pager state number (state `0` is initial).
    `pastStates` entries index into the shared `stateSets` pool. -/
structure Annotations where
  /-- Number of LR(0) states. -/
  numStates : Nat
  /-- `lastSymb[i]` — the incoming symbol of state `i` (`none` for the initial
      state, which has no incoming edge). -/
  lastSymb : Array (Option Sym)
  /-- `pastSymb[i]` — symbols just below the top, head nearest the top. -/
  pastSymb : Array (List Sym)
  /-- `pastStates[i]` — for each depth below the top, an index into `stateSets`. -/
  pastStates : Array (List Nat)
  /-- The deduplicated pool of state sets (each a sorted list of state indices).
      Referenced by `pastStates`. -/
  stateSets : Array (List Nat)
  /-- `items[i]` — the LR(1) items of state `i`. -/
  items : Array (List AnnItem)
  deriving Repr, Inhabited

/-! ### Deriving the annotations from the LR(0) collection -/

/-- Reverse the transition graph: `preds[j]` lists `(X, i)` for every edge
    `i --X--> j`. Head order is unspecified; callers treat each level as a set. -/
def reverseEdges (col : Collection) : Array (List (Sym × Nat)) := Id.run do
  let n := col.states.size
  let mut preds : Array (List (Sym × Nat)) := Array.replicate n []
  for i in [0:n] do
    for e in col.trans[i]! do
      let (X, j) := e
      if j < n then
        preds := preds.set! j ((X, i) :: preds[j]!)
  return preds

/-- Sorted-insert into a dedup'd `Nat` list (ascending). -/
def insSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x == y then y :: ys
               else if x < y then x :: y :: ys
               else y :: insSorted x ys

/-- Canonicalize a list of state indices into a sorted, duplicate-free set. -/
def normSet (l : List Nat) : List Nat := l.foldl (fun acc x => insSorted x acc) []

/-- Intern a state set into the pool, returning `(pool', index)`; reuses an
    existing identical set. -/
def internSet (pool : Array (List Nat)) (s : List Nat) : Array (List Nat) × Nat :=
  match pool.findIdx? (· == s) with
  | some i => (pool, i)
  | none => (pool.push s, pool.size)

/-- `lastSymb[i]`: the symbol on any edge into state `i`. In an LR(0) automaton
    every incoming edge of a state carries the same symbol, so the first
    predecessor's symbol is representative. The initial state (no predecessor)
    gets `none`. -/
def lastSymbOf (preds : Array (List (Sym × Nat))) : Array (Option Sym) :=
  preds.map (fun ps => ps.head?.map Prod.fst)

/-- Longest common prefix of two symbol lists. -/
def commonPrefix : List Sym → List Sym → List Sym
  | x :: xs, y :: ys => if x = y then x :: commonPrefix xs ys else []
  | _, _ => []

/-- `headSymbs lastSymb pastSymb i = lastSymb i :: pastSymb i` (empty for the
    initial state, which has no `lastSymb`). -/
def headSymbsOf (lastSymb : Array (Option Sym)) (pastSymb : Array (List Sym))
    (i : Nat) : List Sym :=
  match lastSymb[i]! with
  | some X => X :: pastSymb[i]!
  | none => []

/-- Compute `pastSymb` as a fixpoint. Invariant to satisfy (safety validator):
    for every edge `p --X--> s`, `pastSymb s` is a prefix of `head_symbs p`.
    We take, for each state, the longest common prefix of `head_symbs p` over all
    predecessors `p`; iterating to a fixpoint since `head_symbs` depends on
    `pastSymb`. The initial state keeps `[]`. -/
partial def pastSymbFix (preds : Array (List (Sym × Nat)))
    (lastSymb : Array (Option Sym)) : Array (List Sym) := Id.run do
  let n := preds.size
  let mut cur : Array (List Sym) := Array.replicate n []
  let cap := n + 1
  for _ in [0:cap] do
    let mut next : Array (List Sym) := Array.replicate n []
    for s in [0:n] do
      match preds[s]! with
      | [] => next := next.set! s []            -- initial state
      | (_, p0) :: rest =>
        let mut acc := headSymbsOf lastSymb cur p0
        for e in rest do
          acc := commonPrefix acc (headSymbsOf lastSymb cur e.2)
        next := next.set! s acc
    if next == cur then return cur
    cur := next
  return cur

/-- Compute `pastStates` (and the shared set pool). For each state, level `d`
    holds the *set* of states that can be `d+1` below the top: level 0 = the
    predecessors of `s`; level `d+1` = predecessors of the level-`d` set. The list
    length matches `pastSymb`'s "one more than symbols" shape: it stops when the
    frontier's predecessors are empty (only initial states remain). -/
partial def pastStatesFix (preds : Array (List (Sym × Nat)))
    (pastSymb : Array (List Sym)) : Array (List Nat) × Array (List Nat) := Id.run do
  let n := preds.size
  let mut pool : Array (List Nat) := #[]
  let mut result : Array (List Nat) := Array.replicate n []
  for s in [0:n] do
    let depth := (pastSymb[s]!).length + 1
    let mut idxs : List Nat := []
    let mut frontier : List Nat := [s]
    for _ in [0:depth] do
      let mut nextSet : List Nat := []
      for q in frontier do
        for e in preds[q]! do
          nextSet := insSorted e.2 nextSet
      if nextSet.isEmpty then
        break
      let normed := normSet nextSet
      let (pool', idx) := internSet pool normed
      pool := pool'
      idxs := idxs ++ [idx]
      frontier := normed
    result := result.set! s idxs
  return (pool, result)

/-- Derive the full annotation certificate from the final Pager collection.
    Item lookaheads are the exact states used to construct reduction tables;
    nullable/FIRST are emitted separately from the same grammar analysis. -/
def annotate (_g : Grammar) (col : Collection) : Annotations :=
  let preds := reverseEdges col
  let lastSymb := lastSymbOf preds
  let pastSymb := pastSymbFix preds lastSymb
  let (stateSets, pastStates) := pastStatesFix preds pastSymb
  let items := col.lr1Items
  { numStates := col.states.size
    lastSymb, pastSymb, pastStates, stateSets, items }

end Construct
