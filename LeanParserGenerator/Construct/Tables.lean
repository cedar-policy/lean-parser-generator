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
Pager LR(1) action/goto tables.

Production table generation consumes the final Pager graph and reduces completed
items only on their propagated LR(1) lookaheads. The output remains the same flat
`Tables` data consumed by both emitters. Conflict reports cover shift/reduce and
reduce/reduce clashes in the final automaton.

The former FOLLOW-based SLR(1) builder remains as `buildSLRTables`/`slr` as an
unused diagnostic helper; generated parsers use `pager`.
Everything in this module is untrusted plain data. The trusted validators check
the emitted automaton and certificate at generated-parser compile time.
-/
public import LeanParserGenerator.Construct.LR1


@[expose] public section

namespace Construct

open IR

/-! ### FOLLOW sets (over an augmented grammar) -/

/-- One monotone step of the FOLLOW fixpoint. For every `A → α B β`, add
    `FIRST(β)` to `FOLLOW(B)`, and if `β` is nullable also add `FOLLOW(A)`. -/
def followStep (g : Grammar) (nul : Array Bool) (fst : Array (List Nat))
    (cur : Array (List Nat)) : Array (List Nat) := Id.run do
  let mut nxt := cur
  for pi in [0:g.prods.size] do
    let p := g.prods[pi]!
    let rhs := p.rhs
    for k in [0:rhs.length] do
      match rhs[k]! with
      | .nonterm b =>
          let beta := rhs.drop (k + 1)
          nxt := nxt.set! b (unionNat (nxt.getD b []) (firstOfSeq nul fst beta))
          if beta.all (symNullable nul) then
            nxt := nxt.set! b (unionNat (nxt.getD b []) (cur.getD p.lhs []))
      | _ => pure ()
  return nxt

/-- FOLLOW sets of an augmented grammar. Seeds `FOLLOW(start) = {$}` (the end
    terminal, index `numTerminals - 1` after augmentation) and iterates to a
    fixpoint. -/
partial def followSets (g : Grammar) : Array (List Nat) :=
  let nul := nullable g
  let fst := firstSets g
  let eof := g.numTerminals - 1
  let init := (Array.replicate g.numNonterminals ([] : List Nat)).set! g.start [eof]
  let rec loop (cur : Array (List Nat)) (fuel : Nat) : Array (List Nat) :=
    match fuel with
    | 0 => cur
    | fuel + 1 =>
      let next := followStep g nul fst cur
      if next == cur then cur else loop next fuel
  loop init (g.numNonterminals * g.numTerminals + 1)

/-! ### Action / goto tables -/

/-- A parse-table action. There is no explicit `accept`: acceptance is the
    reduction of the augmented production `S' → S $`, which the interpreter detects
    when the ensuing goto is absent at the initial state. -/
inductive Act where
  | shift : Nat → Act
  | reduce : Nat → Act
  | error : Act
  deriving Repr, DecidableEq, Inhabited

/-- Parse tables for an augmented grammar and numbered LR state graph. -/
structure Tables where
  /-- Number of states. -/
  numStates : Nat
  /-- `action[state][terminal]`. Terminal range includes the end marker `$`. -/
  action : Array (Array Act)
  /-- `goto[state][nonterminal]`. -/
  goto : Array (Array (Option Nat))
  /-- States that reduce a fixed production regardless of lookahead. -/
  defaultReduce : Array (Option Nat)
  /-- Human-readable conflict reports (empty ⇒ the constructed automaton is conflict-free). -/
  conflicts : List String
  deriving Repr, Inhabited

/-- Is the item's dot at the end of its production's right-hand side? -/
def isComplete (g : Grammar) (it : Item) : Bool :=
  match g.prods[it.prod]? with
  | some p => it.dot == p.rhs.length
  | none => false


/-- Build action/goto tables from the exact LR(1) items of a final Pager
    collection. Completed items reduce only on their own lookaheads. -/
def buildTables (g : Grammar) (col : Collection) : Tables := Id.run do
  let numT := g.numTerminals
  let numN := g.numNonterminals
  let numStates := col.states.size
  let mut action := Array.replicate numStates (Array.replicate numT Act.error)
  let mut goto := Array.replicate numStates (Array.replicate numN (none : Option Nat))
  let mut conflicts : List String := []
  for i in [0:numStates] do
    for edge in col.trans.getD i [] do
      let (symbol, target) := edge
      match symbol with
      | .term term => action := action.set! i ((action[i]!).set! term (.shift target))
      | .nonterm nt => goto := goto.set! i ((goto[i]!).set! nt (some target))
    for item in col.lr1Items.getD i [] do
      if isComplete g ⟨item.prod, item.dot⟩ then
        for term in item.lookaheads do
          match (action[i]!)[term]! with
          | .error => action := action.set! i ((action[i]!).set! term (.reduce item.prod))
          | .shift _ =>
              conflicts := conflicts ++
                [s!"shift/reduce conflict in Pager state {i} on terminal {term}"]
          | .reduce otherProd =>
              if otherProd != item.prod then
                conflicts := conflicts ++
                  [s!"reduce/reduce conflict in Pager state {i} on terminal {term} " ++
                    s!"(productions {otherProd} vs {item.prod})"]
  let mut defaultReduce := Array.replicate numStates (none : Option Nat)
  for i in [0:numStates] do
    let row := action[i]!
    let hasShift := row.any fun act => match act with | .shift _ => true | _ => false
    let reductions := row.foldl (fun acc act =>
      match act with | .reduce prod => insertNat prod acc | _ => acc) []
    match reductions with
    | [prod] => if !hasShift then defaultReduce := defaultReduce.set! i (some prod)
    | _ => pure ()
  return ⟨numStates, action, goto, defaultReduce, conflicts⟩

/-- End-to-end Pager construction: augment the grammar, discover/fuse LR(1)
    states, number the final graph, and build item-lookahead action tables. -/
def pager (g : Grammar) : Grammar × Nat × Collection × Tables :=
  let (g', augProd, col) := buildPager g
  (g', augProd, col, buildTables g' col)


end Construct
