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
The completeness validator: the sufficient conditions for automaton completeness
from §3.3 of Validating LR(1) Parsers (Jourdan, Pottier, Leroy). The validator
checks the nullable/FIRST annotations and the LR(1) item certificate against the
action and goto tables. This file defines the semantic certificate property
`Complete`, the executable `completeValidator`, and the validator correctness
theorem `complete_of_completeValidator`.

The item certificate is intentionally untrusted. `StateHasFuture` gives its
meaning: a state contains an item for `prod`, with the given suffix after the dot
and lookahead terminal. The executable checks iterate over the finite alphabets
and the concrete item lists directly; no balanced map is needed to share item
lookups.
-/
public import LeanParserGenerator.Runtime.Automaton


@[expose] public section

set_option linter.unusedSectionVars false

namespace Runtime

open GrammarSig

variable [G : GrammarSig] [A : Automaton]

/-! ### Nullable, FIRST, and item helpers -/

/-- Whether a grammar symbol is nullable according to the certificate. -/
def nullableSymb : GrammarSig.Sym → Bool
  | .T _ => false
  | .NT nt => A.nullableNt nt

/-- Whether every symbol in a word is nullable. -/
def nullableWord (word : List GrammarSig.Sym) : Bool :=
  word.all nullableSymb

/-- Membership in the certified FIRST set of one symbol. -/
def firstSymbCheck (symb : GrammarSig.Sym) (term : G.Terminal) : Bool :=
  match symb with
  | .T t => decide (term = t)
  | .NT nt => decide (term ∈ A.firstNt nt)

/-- Membership in FIRST of a word, accumulating across its nullable prefix. -/
def firstWordCheck : List GrammarSig.Sym → G.Terminal → Bool
  | [], _ => false
  | symb :: rest, term =>
      if nullableSymb symb then
        firstSymbCheck symb term || firstWordCheck rest term
      else
        firstSymbCheck symb term

/-- The suffix to the right of the dot at `dotPos`. Production right-hand sides
    are stored reversed, so restore source order before dropping the prefix. -/
def futureOfProd (prod : G.Production) (dotPos : Nat) : List GrammarSig.Sym :=
  (G.prodRhsRev prod).reverse.drop dotPos

/-- A state contains an LR(1) item for `prod` whose suffix after the dot is
    `future` and whose lookahead set contains `lookahead`. -/
def StateHasFuture (state : AState) (prod : G.Production)
    (future : List GrammarSig.Sym) (lookahead : G.Terminal) : Prop :=
  ∃ item, item ∈ A.items state ∧ item.prod = prod ∧
    future = futureOfProd prod item.dotPos ∧ lookahead ∈ item.lookaheads

/-- The lookaheads certified for `prod` with remaining suffix `future` in `state`,
    gathered from all matching items. Computing it once per (item, target) lets the
    checks below test a whole lookahead set against it, instead of rescanning the
    target's items once per lookahead. -/
def futureLookaheads (state : AState) (prod : G.Production)
    (future : List GrammarSig.Sym) : List G.Terminal :=
  ((A.items state).filter fun item =>
    decide (item.prod = prod) && decide (future = futureOfProd prod item.dotPos)).flatMap
      (·.lookaheads)

/-- `futureLookaheads` is the lookahead relation of `StateHasFuture`. -/
theorem mem_futureLookaheads {state : AState} {prod : G.Production}
    {future : List GrammarSig.Sym} {lookahead : G.Terminal} :
    lookahead ∈ futureLookaheads state prod future ↔
      StateHasFuture state prod future lookahead := by
  simp only [futureLookaheads, StateHasFuture, List.mem_flatMap, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨item, ⟨hitem, hprod, hfuture⟩, hlook⟩
    exact ⟨item, hitem, hprod, hfuture, hlook⟩
  · rintro ⟨item, hitem, hprod, hfuture, hlook⟩
    exact ⟨item, ⟨hitem, hprod, hfuture⟩, hlook⟩

/-- Executable lookup for `StateHasFuture`. -/
def stateHasFutureCheck (state : AState) (prod : G.Production)
    (future : List GrammarSig.Sym) (lookahead : G.Terminal) : Bool :=
  decide (lookahead ∈ futureLookaheads state prod future)

/-- The executable item lookup establishes the semantic item relation. -/
theorem stateHasFuture_of_check {state : AState} {prod : G.Production}
    {future : List GrammarSig.Sym} {lookahead : G.Terminal}
    (h : stateHasFutureCheck state prod future lookahead = true) :
    StateHasFuture state prod future lookahead :=
  mem_futureLookaheads.mp (of_decide_eq_true h)

/-- Every lookahead of `item` is among `known`. -/
def lookaheadsSubset (item : Item) (known : List G.Terminal) : Bool :=
  item.lookaheads.all fun lookahead => decide (lookahead ∈ known)

theorem mem_of_lookaheadsSubset {item : Item} {known : List G.Terminal}
    (h : lookaheadsSubset item known = true) {lookahead : G.Terminal}
    (hlook : lookahead ∈ item.lookaheads) : lookahead ∈ known :=
  of_decide_eq_true ((List.all_eq_true.mp h) lookahead hlook)

/-- The failure case of an item-level check. It holds exactly when the item has no
    lookaheads, so the item-level checks accept the same certificates as checking
    each lookahead separately. -/
def noLookaheads (item : Item) : Bool :=
  item.lookaheads.all fun _ => false

theorem false_of_noLookaheads {item : Item} (h : noLookaheads item = true)
    {lookahead : G.Terminal} (hlook : lookahead ∈ item.lookaheads) : False := by
  have := (List.all_eq_true.mp h) lookahead hlook
  exact Bool.false_ne_true this

/-- Iterate a Boolean condition over every certified item. Each clause quantifies
    over the item's lookaheads itself, so per-item work is shared across them. -/
def allItemsCheck (check : AState → Item → Bool) : Bool :=
  (Finite.all (α := AState)).all fun state =>
    (A.items state).all fun item => check state item

/-- Extract one item result from `allItemsCheck`. -/
theorem item_of_all_check {check : AState → Item → Bool}
    (h : allItemsCheck check = true) (state : AState) (item : Item)
    (hitem : item ∈ A.items state) : check state item = true := by
  have hs := (List.all_eq_true.mp h) state (Finite.mem_all state)
  exact (List.all_eq_true.mp hs) item hitem

/-- Iterate a Boolean condition over every certified item and every one of its
    lookaheads. -/
def allItemLookaheadsCheck (check : AState → Item → G.Terminal → Bool) : Bool :=
  allItemsCheck fun state item => item.lookaheads.all fun lookahead => check state item lookahead

/-- Extract one item/lookahead result from `allItemLookaheadsCheck`. -/
theorem itemLookahead_of_all_check {check : AState → Item → G.Terminal → Bool}
    (h : allItemLookaheadsCheck check = true) (state : AState) (item : Item)
    (hitem : item ∈ A.items state) (lookahead : G.Terminal)
    (hlook : lookahead ∈ item.lookaheads) : check state item lookahead = true :=
  (List.all_eq_true.mp (item_of_all_check h state item hitem)) lookahead hlook

/-! ### The eight completeness properties -/

/-- The nullable annotation is stable under every production. -/
def NullableStable : Prop :=
  ∀ prod : G.Production,
    if nullableWord (G.prodRhsRev prod) then
      A.nullableNt (G.prodLhs prod) = true
    else True

/-- The executable nullable-stability check. -/
def nullableStableCheck : Bool :=
  (Finite.all (α := G.Production)).all fun prod =>
    if nullableWord (G.prodRhsRev prod) then
      A.nullableNt (G.prodLhs prod)
    else true

/-- The FIRST annotation contains FIRST of every production RHS. -/
def FirstStable : Prop :=
  ∀ (prod : G.Production) (term : G.Terminal),
    firstWordCheck (G.prodRhsRev prod).reverse term = true →
      term ∈ A.firstNt (G.prodLhs prod)

/-- The executable FIRST-stability check. -/
def firstStableCheck : Bool :=
  (Finite.all (α := G.Production)).all fun prod =>
    (Finite.all (α := G.Terminal)).all fun term =>
      !firstWordCheck (G.prodRhsRev prod).reverse term ||
        decide (term ∈ A.firstNt (G.prodLhs prod))

/-- Every initial state contains every production of its start nonterminal, with
    every possible lookahead. -/
def StartFuture : Prop :=
  ∀ (init : A.InitState) (prod : G.Production),
    G.prodLhs prod = A.startNt init →
      ∀ term : G.Terminal,
        StateHasFuture (.Init init) prod (G.prodRhsRev prod).reverse term

/-- The executable initial-item check. -/
def startFutureCheck : Bool :=
  (Finite.all (α := A.InitState)).all fun init =>
    (Finite.all (α := G.Production)).all fun prod =>
      if G.prodLhs prod = A.startNt init then
        let known := futureLookaheads (.Init init) prod (G.prodRhsRev prod).reverse
        (Finite.all (α := G.Terminal)).all fun term => decide (term ∈ known)
      else true

/-- A terminal immediately after an item's dot is shifted to a state containing
    the advanced item with the same lookahead. -/
def TerminalShift : Prop :=
  ∀ (state : AState) (prod : G.Production) (future : List GrammarSig.Sym)
      (lookahead : G.Terminal),
    StateHasFuture state prod future lookahead →
      match future with
      | .T term :: rest =>
          match A.actionTable state with
          | .Lookahead actions =>
              match actions term with
              | .Shift target _ => StateHasFuture (.Ninit target) prod rest lookahead
              | _ => False
          | _ => False
      | _ => True

/-- Check terminal advancement for one concrete certified item. -/
def terminalShiftItemCheck (state : AState) (item : Item) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | .T term :: rest =>
      match A.actionTable state with
      | .Lookahead actions =>
          match actions term with
          | .Shift target _ =>
              lookaheadsSubset item (futureLookaheads (.Ninit target) item.prod rest)
          | _ => noLookaheads item
      | _ => noLookaheads item
  | _ => true

/-- The executable terminal-shift check. -/
def terminalShiftCheck : Bool :=
  allItemsCheck terminalShiftItemCheck

/-- A completed item reduces its production for every certified lookahead. -/
def EndReduce : Prop :=
  ∀ (state : AState) (prod : G.Production) (future : List GrammarSig.Sym)
      (lookahead : G.Terminal),
    StateHasFuture state prod future lookahead →
      match future with
      | [] =>
          match A.actionTable state with
          | .DefaultReduce reduced => reduced = prod
          | .Lookahead actions =>
              match actions lookahead with
              | .Reduce reduced => reduced = prod
              | _ => False
      | _ => True

/-- Check reduction behavior for one concrete certified item/lookahead. -/
def endReduceItemCheck (state : AState) (item : Item)
    (lookahead : G.Terminal) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | [] =>
      match A.actionTable state with
      | .DefaultReduce reduced => decide (reduced = item.prod)
      | .Lookahead actions =>
          match actions lookahead with
          | .Reduce reduced => decide (reduced = item.prod)
          | _ => false
  | _ => true

/-- The executable end-reduction check. -/
def endReduceCheck : Bool :=
  allItemLookaheadsCheck endReduceItemCheck

/-- A nonterminal immediately after an item's dot has a goto to a state
    containing the advanced item with the same lookahead. -/
def NonTerminalGoto : Prop :=
  ∀ (state : AState) (prod : G.Production) (future : List GrammarSig.Sym)
      (lookahead : G.Terminal),
    StateHasFuture state prod future lookahead →
      match future with
      | .NT nt :: rest =>
          match A.gotoTable state nt with
          | some ⟨target, _⟩ => StateHasFuture (.Ninit target) prod rest lookahead
          | none => False
      | _ => True

/-- Check nonterminal advancement for one concrete certified item. -/
def nonTerminalGotoItemCheck (state : AState) (item : Item) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | .NT nt :: rest =>
      match A.gotoTable state nt with
      | some ⟨target, _⟩ =>
          lookaheadsSubset item (futureLookaheads (.Ninit target) item.prod rest)
      | none => noLookaheads item
  | _ => true

/-- The executable nonterminal-goto check. -/
def nonTerminalGotoCheck : Bool :=
  allItemsCheck nonTerminalGotoItemCheck

/-- The start nonterminal has no goto from an initial state: reducing the
    augmented production is the interpreter's acceptance case. -/
def StartGoto : Prop :=
  ∀ init : A.InitState,
    match A.gotoTable (.Init init) (A.startNt init) with
    | none => True
    | some _ => False

/-- The executable start-goto check. -/
def startGotoCheck : Bool :=
  (Finite.all (α := A.InitState)).all fun init =>
    match A.gotoTable (.Init init) (A.startNt init) with
    | none => true
    | some _ => false

/-- Item sets are closed under productions of a nonterminal after the dot, with
    lookaheads from FIRST of the remaining suffix and, when it is nullable, the
    original item's lookahead. -/
def NonTerminalClosed : Prop :=
  ∀ (state : AState) (prod : G.Production) (future : List GrammarSig.Sym)
      (lookahead : G.Terminal),
    StateHasFuture state prod future lookahead →
      match future with
      | .NT nt :: rest =>
          ∀ nextProd : G.Production, G.prodLhs nextProd = nt →
            (if nullableWord rest then
               StateHasFuture state nextProd (futureOfProd nextProd 0) lookahead
             else True) ∧
            (∀ nextLookahead : G.Terminal,
              firstWordCheck rest nextLookahead = true →
                StateHasFuture state nextProd (futureOfProd nextProd 0) nextLookahead)
      | _ => True

/-- Check closure for one concrete certified item. FIRST of the suffix is computed
    once per item, and the lookaheads certified for each expansion once per
    expansion, not once per lookahead and terminal. -/
def nonTerminalClosedItemCheck (state : AState) (item : Item) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | .NT nt :: rest =>
      let firsts := (Finite.all (α := G.Terminal)).filter (firstWordCheck rest)
      item.lookaheads.isEmpty ||
      (Finite.all (α := G.Production)).all fun nextProd =>
        if G.prodLhs nextProd = nt then
          let known := futureLookaheads state nextProd (futureOfProd nextProd 0)
          (!nullableWord rest || lookaheadsSubset item known) &&
          firsts.all fun nextLookahead => decide (nextLookahead ∈ known)
        else true
  | _ => true

/-- The executable item-closure check. -/
def nonTerminalClosedCheck : Bool :=
  allItemsCheck nonTerminalClosedItemCheck

/-- The automaton certificate is complete: all eight completeness properties
    hold. -/
def Complete : Prop :=
  NullableStable ∧ FirstStable ∧ StartFuture ∧ TerminalShift ∧ EndReduce ∧
    NonTerminalGoto ∧ StartGoto ∧ NonTerminalClosed

/-- The executable completeness validator. -/
def completeValidator : Bool :=
  nullableStableCheck && firstStableCheck && startFutureCheck &&
    terminalShiftCheck && endReduceCheck && nonTerminalGotoCheck &&
    startGotoCheck && nonTerminalClosedCheck

/-! ### Correctness of the executable checks -/

theorem nullableStable_of_check (h : nullableStableCheck = true) : NullableStable := by
  intro prod
  have hp := (List.all_eq_true.mp h) prod (Finite.mem_all prod)
  cases hn : nullableWord (G.prodRhsRev prod) <;>
    simp [hn] at hp ⊢
  exact hp

theorem firstStable_of_check (h : firstStableCheck = true) : FirstStable := by
  intro prod term hfirst
  have hp := (List.all_eq_true.mp h) prod (Finite.mem_all prod)
  have ht := (List.all_eq_true.mp hp) term (Finite.mem_all term)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at ht
  rcases ht with hnot | hmem
  · rw [hfirst] at hnot
    simp at hnot
  · exact of_decide_eq_true hmem

theorem startFuture_of_check (h : startFutureCheck = true) : StartFuture := by
  intro init prod hlhs term
  have hi := (List.all_eq_true.mp h) init (Finite.mem_all init)
  have hp := (List.all_eq_true.mp hi) prod (Finite.mem_all prod)
  rw [ite_eq_left hlhs] at hp
  have ht := (List.all_eq_true.mp hp) term (Finite.mem_all term)
  exact mem_futureLookaheads.mp (of_decide_eq_true ht)

theorem terminalShift_of_check (h : terminalShiftCheck = true) : TerminalShift := by
  intro state prod future lookahead hfuture
  rcases hfuture with ⟨item, hitem, hprod, hfuture, hlook⟩
  subst prod
  subst future
  have hc := item_of_all_check h state item hitem
  cases hf : futureOfProd item.prod item.dotPos with
  | nil => trivial
  | cons symb rest =>
    cases symb with
    | NT _ => trivial
    | T term =>
      cases ha : A.actionTable state with
      | DefaultReduce _ =>
        exact (false_of_noLookaheads (by simpa [terminalShiftItemCheck, hf, ha] using hc) hlook).elim
      | Lookahead actions =>
        cases hs : actions term with
        | Shift target proof =>
          have hsub : lookaheadsSubset item
              (futureLookaheads (.Ninit target) item.prod rest) = true := by
            simpa [terminalShiftItemCheck, hf, ha, hs] using hc
          have htarget := mem_futureLookaheads.mp (mem_of_lookaheadsSubset hsub hlook)
          simpa only [hf, ha, hs] using htarget
        | Reduce _ =>
          exact (false_of_noLookaheads (by simpa [terminalShiftItemCheck, hf, ha, hs] using hc) hlook).elim
        | Fail =>
          exact (false_of_noLookaheads (by simpa [terminalShiftItemCheck, hf, ha, hs] using hc) hlook).elim

theorem endReduce_of_check (h : endReduceCheck = true) : EndReduce := by
  intro state prod future lookahead hfuture
  rcases hfuture with ⟨item, hitem, hprod, hfuture, hlook⟩
  subst prod
  subst future
  have hc := itemLookahead_of_all_check h state item hitem lookahead hlook
  cases hf : futureOfProd item.prod item.dotPos with
  | cons symb rest => trivial
  | nil =>
    cases ha : A.actionTable state with
    | DefaultReduce reduced =>
      have heq : reduced = item.prod :=
        of_decide_eq_true (by simpa [endReduceItemCheck, hf, ha] using hc)
      simpa only [hf, ha] using heq
    | Lookahead actions =>
      cases hr : actions lookahead with
      | Reduce reduced =>
        have heq : reduced = item.prod :=
          of_decide_eq_true (by simpa [endReduceItemCheck, hf, ha, hr] using hc)
        simpa only [hf, ha, hr] using heq
      | Shift _ _ => simp [endReduceItemCheck, hf, ha, hr] at hc
      | Fail => simp [endReduceItemCheck, hf, ha, hr] at hc

theorem nonTerminalGoto_of_check (h : nonTerminalGotoCheck = true) : NonTerminalGoto := by
  intro state prod future lookahead hfuture
  rcases hfuture with ⟨item, hitem, hprod, hfuture, hlook⟩
  subst prod
  subst future
  have hc := item_of_all_check h state item hitem
  cases hf : futureOfProd item.prod item.dotPos with
  | nil => trivial
  | cons symb rest =>
    cases symb with
    | T _ => trivial
    | NT nt =>
      cases hg : A.gotoTable state nt with
      | none =>
        exact (false_of_noLookaheads (by simpa [nonTerminalGotoItemCheck, hf, hg] using hc) hlook).elim
      | some target =>
        have hsub : lookaheadsSubset item
            (futureLookaheads (.Ninit target.1) item.prod rest) = true := by
          simpa [nonTerminalGotoItemCheck, hf, hg] using hc
        have htarget := mem_futureLookaheads.mp (mem_of_lookaheadsSubset hsub hlook)
        simpa only [hf, hg] using htarget

theorem startGoto_of_check (h : startGotoCheck = true) : StartGoto := by
  intro init
  have hi := (List.all_eq_true.mp h) init (Finite.mem_all init)
  cases hg : A.gotoTable (.Init init) (A.startNt init) with
  | none => trivial
  | some target => simp [hg] at hi

theorem nonTerminalClosed_of_check (h : nonTerminalClosedCheck = true) :
    NonTerminalClosed := by
  intro state prod future lookahead hfuture
  rcases hfuture with ⟨item, hitem, hprod, hfuture, hlook⟩
  subst prod
  subst future
  have hc := item_of_all_check h state item hitem
  cases hf : futureOfProd item.prod item.dotPos with
  | nil => trivial
  | cons symb rest =>
    cases symb with
    | T _ => trivial
    | NT nt =>
      intro nextProd hlhs
      have hne : item.lookaheads.isEmpty = false := by
        cases hl : item.lookaheads with
        | nil => simp [hl] at hlook
        | cons _ _ => rfl
      have hc' : ((Finite.all (α := G.Production)).all fun nextProd =>
          if G.prodLhs nextProd = nt then
            (!nullableWord rest ||
                lookaheadsSubset item
                  (futureLookaheads state nextProd (futureOfProd nextProd 0))) &&
              ((Finite.all (α := G.Terminal)).filter (firstWordCheck rest)).all fun nextLookahead =>
                decide (nextLookahead ∈ futureLookaheads state nextProd (futureOfProd nextProd 0))
          else true) = true := by
        simpa [nonTerminalClosedItemCheck, hf, hne] using hc
      have hp := (List.all_eq_true.mp hc') nextProd (Finite.mem_all nextProd)
      rw [ite_eq_left hlhs] at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hnullable, hfirst⟩ := hp
      constructor
      · cases hn : nullableWord rest with
        | false => simp
        | true =>
          simp only [ite_true]
          rw [hn] at hnullable
          exact mem_futureLookaheads.mp
            (mem_of_lookaheadsSubset (by simpa using hnullable) hlook)
      · intro nextLookahead hfirstMem
        have hmem : nextLookahead ∈ (Finite.all (α := G.Terminal)).filter (firstWordCheck rest) :=
          List.mem_filter.mpr ⟨Finite.mem_all nextLookahead, hfirstMem⟩
        exact mem_futureLookaheads.mp
          (of_decide_eq_true ((List.all_eq_true.mp hfirst) nextLookahead hmem))

/-- **Validator correctness.** Successful Boolean completeness validation
    establishes the semantic `Complete` certificate property. -/
theorem complete_of_completeValidator (h : completeValidator = true) : Complete := by
  simp only [completeValidator, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hnullable, hfirst⟩, hstart⟩, hshift⟩, hreduce⟩, hgoto⟩,
    hstartGoto⟩, hclosed⟩ := h
  exact ⟨nullableStable_of_check hnullable,
    firstStable_of_check hfirst,
    startFuture_of_check hstart,
    terminalShift_of_check hshift,
    endReduce_of_check hreduce,
    nonTerminalGoto_of_check hgoto,
    startGoto_of_check hstartGoto,
    nonTerminalClosed_of_check hclosed⟩

end Runtime
