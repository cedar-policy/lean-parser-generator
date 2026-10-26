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

/-- Executable lookup for `StateHasFuture`. -/
def stateHasFutureCheck (state : AState) (prod : G.Production)
    (future : List GrammarSig.Sym) (lookahead : G.Terminal) : Bool :=
  (A.items state).any fun item =>
    decide (item.prod = prod) &&
      (decide (future = futureOfProd prod item.dotPos) &&
        decide (lookahead ∈ item.lookaheads))

/-- The executable item lookup establishes the semantic item relation. -/
theorem stateHasFuture_of_check {state : AState} {prod : G.Production}
    {future : List GrammarSig.Sym} {lookahead : G.Terminal}
    (h : stateHasFutureCheck state prod future lookahead = true) :
    StateHasFuture state prod future lookahead := by
  rcases List.any_eq_true.mp h with ⟨item, hmem, hi⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  exact ⟨item, hmem, hi.1, hi.2.1, hi.2.2⟩

/-- Iterate a Boolean condition over every certified item and every one of its
    lookaheads. Most completeness clauses have this shape. -/
def allItemLookaheadsCheck (check : AState → Item → G.Terminal → Bool) : Bool :=
  (Finite.all (α := AState)).all fun state =>
    (A.items state).all fun item =>
      item.lookaheads.all fun lookahead => check state item lookahead

/-- Extract one item/lookahead result from `allItemLookaheadsCheck`. -/
theorem itemLookahead_of_all_check {check : AState → Item → G.Terminal → Bool}
    (h : allItemLookaheadsCheck check = true) (state : AState) (item : Item)
    (hitem : item ∈ A.items state) (lookahead : G.Terminal)
    (hlook : lookahead ∈ item.lookaheads) : check state item lookahead = true := by
  have hs := (List.all_eq_true.mp h) state (Finite.mem_all state)
  have hi := (List.all_eq_true.mp hs) item hitem
  exact (List.all_eq_true.mp hi) lookahead hlook

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
        (Finite.all (α := G.Terminal)).all fun term =>
          stateHasFutureCheck (.Init init) prod (G.prodRhsRev prod).reverse term
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

/-- Check terminal advancement for one concrete certified item/lookahead. -/
def terminalShiftItemCheck (state : AState) (item : Item)
    (lookahead : G.Terminal) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | .T term :: rest =>
      match A.actionTable state with
      | .Lookahead actions =>
          match actions term with
          | .Shift target _ => stateHasFutureCheck (.Ninit target) item.prod rest lookahead
          | _ => false
      | _ => false
  | _ => true

/-- The executable terminal-shift check. -/
def terminalShiftCheck : Bool :=
  allItemLookaheadsCheck terminalShiftItemCheck

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

/-- Check nonterminal advancement for one concrete certified item/lookahead. -/
def nonTerminalGotoItemCheck (state : AState) (item : Item)
    (lookahead : G.Terminal) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | .NT nt :: rest =>
      match A.gotoTable state nt with
      | some ⟨target, _⟩ => stateHasFutureCheck (.Ninit target) item.prod rest lookahead
      | none => false
  | _ => true

/-- The executable nonterminal-goto check. -/
def nonTerminalGotoCheck : Bool :=
  allItemLookaheadsCheck nonTerminalGotoItemCheck

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

/-- Check closure for one concrete certified item/lookahead. -/
def nonTerminalClosedItemCheck (state : AState) (item : Item)
    (lookahead : G.Terminal) : Bool :=
  match futureOfProd item.prod item.dotPos with
  | .NT nt :: rest =>
      (Finite.all (α := G.Production)).all fun nextProd =>
        if G.prodLhs nextProd = nt then
          (if nullableWord rest then
             stateHasFutureCheck state nextProd (futureOfProd nextProd 0) lookahead
           else true) &&
          (Finite.all (α := G.Terminal)).all fun nextLookahead =>
            if firstWordCheck rest nextLookahead then
              stateHasFutureCheck state nextProd (futureOfProd nextProd 0) nextLookahead
            else true
        else true
  | _ => true

/-- The executable item-closure check. -/
def nonTerminalClosedCheck : Bool :=
  allItemLookaheadsCheck nonTerminalClosedItemCheck

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
  exact stateHasFuture_of_check ht

theorem terminalShift_of_check (h : terminalShiftCheck = true) : TerminalShift := by
  intro state prod future lookahead hfuture
  rcases hfuture with ⟨item, hitem, hprod, hfuture, hlook⟩
  subst prod
  subst future
  have hc := itemLookahead_of_all_check h state item hitem lookahead hlook
  cases hf : futureOfProd item.prod item.dotPos with
  | nil => trivial
  | cons symb rest =>
    cases symb with
    | NT _ => trivial
    | T term =>
      cases ha : A.actionTable state with
      | DefaultReduce _ => simp [terminalShiftItemCheck, hf, ha] at hc
      | Lookahead actions =>
        cases hs : actions term with
        | Shift target proof =>
          have htarget := stateHasFuture_of_check
            (by simpa [terminalShiftItemCheck, hf, ha, hs] using hc)
          simpa only [hf, ha, hs] using htarget
        | Reduce _ => simp [terminalShiftItemCheck, hf, ha, hs] at hc
        | Fail => simp [terminalShiftItemCheck, hf, ha, hs] at hc

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
  have hc := itemLookahead_of_all_check h state item hitem lookahead hlook
  cases hf : futureOfProd item.prod item.dotPos with
  | nil => trivial
  | cons symb rest =>
    cases symb with
    | T _ => trivial
    | NT nt =>
      cases hg : A.gotoTable state nt with
      | none => simp [nonTerminalGotoItemCheck, hf, hg] at hc
      | some target =>
        have htarget := stateHasFuture_of_check
          (by simpa [nonTerminalGotoItemCheck, hf, hg] using hc)
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
  have hc := itemLookahead_of_all_check h state item hitem lookahead hlook
  cases hf : futureOfProd item.prod item.dotPos with
  | nil => trivial
  | cons symb rest =>
    cases symb with
    | T _ => trivial
    | NT nt =>
      intro nextProd hlhs
      have hc' : (Finite.all (α := G.Production)).all (fun nextProd =>
          if G.prodLhs nextProd = nt then
            (if nullableWord rest then
               stateHasFutureCheck state nextProd (futureOfProd nextProd 0) lookahead
             else true) &&
            (Finite.all (α := G.Terminal)).all (fun nextLookahead =>
              if firstWordCheck rest nextLookahead then
                stateHasFutureCheck state nextProd (futureOfProd nextProd 0) nextLookahead
              else true)
          else true) = true := by
        simpa [nonTerminalClosedItemCheck, hf] using hc
      have hp := (List.all_eq_true.mp hc') nextProd (Finite.mem_all nextProd)
      rw [ite_eq_left hlhs] at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hnullable, hfirst⟩ := hp
      constructor
      · cases hn : nullableWord rest with
        | false => simp
        | true =>
          simp only [ite_true]
          rw [ite_eq_left (by simpa using hn)] at hnullable
          exact stateHasFuture_of_check hnullable
      · intro nextLookahead hfirstMem
        have ht := (List.all_eq_true.mp hfirst) nextLookahead (Finite.mem_all nextLookahead)
        rw [ite_eq_left (by simpa using hfirstMem)] at ht
        exact stateHasFuture_of_check ht

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
