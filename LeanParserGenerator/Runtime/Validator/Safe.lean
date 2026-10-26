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
The safety validator: the sufficient conditions for automaton safety from §3.2 of
Validating LR(1) Parsers (Jourdan, Pottier, Leroy). It checks the certificate
annotations (`pastSymb`, `pastStates`) against the action/goto tables so that the
interpreter's stack invariant is maintained. This file proves the validator
correctness theorem `safe_of_safeValidator`: successful Boolean validation
establishes `Safe`. `Runtime/Safety.lean` then proves that `Safe` implies
interpreter Err-freedom.

Structure:

  * `Prefix` / `isPrefix` — the structural prefix relation on symbol lists, plus
    its boolean decision procedure.
  * `PrefixPred` / `isPrefixPred` — a "prefix" on lists of state predicates, where
    `f₂` entailing `f₁` (`f₂ x → f₁ x` for every state `x`) replaces list-head
    equality.
  * `StateValidAfterPop` / `isStateValidAfterPop` — the reachable states after
    popping a production's RHS, read off the `pastStates` annotation.
  * The five safety predicates: `ShiftHeadSymbs`, `GotoHeadSymbs`,
    `ShiftPastState`, `GotoPastState`, `ReduceOk`, their boolean checkers, and the
    aggregate `Safe : Prop` / `safeValidator : Bool`.
  * The **validator correctness theorem** `safeValidator = true → Safe`,
    discharged by direct induction.

Where the conditions quantify over a finite alphabet, we use `Finite.all`
together with `List.all` and relate the two with `List.all_eq_true`.
-/
public import LeanParserGenerator.Runtime.Automaton


@[expose] public section

set_option linter.unusedSectionVars false

namespace Runtime

open GrammarSig

variable [G : GrammarSig] [A : Automaton]

/-! ### State helpers

`pastState`, `headSymbs` and `headStates` extend the per-non-init-state
annotations to all states (an initial state has an empty history). -/

/-- The singleton predicate for a state: true exactly on that state. -/
def singletonStatePred (s : AState) : AState → Bool := fun s' => decide (s = s')

/-- `pastStates`, extended for all states (empty for an initial state). -/
def pastState : AState → List (AState → Bool)
  | .Init _ => []
  | .Ninit nis => A.pastStates nis

/-- The symbols known at the top of the stack in a state: the last symbol plus the
    `pastSymb` annotation. -/
def headSymbs : AState → List GrammarSig.Sym
  | .Init _ => []
  | .Ninit s => A.lastSymb s :: A.pastSymb s

/-- The state predicates known for the stack in a state: this state's singleton
    predicate on top of its `pastStates`. -/
def headStates (s : AState) : List (AState → Bool) :=
  singletonStatePred s :: pastState s

/-! ### Prefix on symbol lists -/

/-- Structural prefix: `l₁` is a prefix of `l₂` when they agree cell-by-cell for
    the length of `l₁`. -/
inductive Prefix : List GrammarSig.Sym → List GrammarSig.Sym → Prop where
  | nil (l : List GrammarSig.Sym) : Prefix [] l
  | cons {l₁ l₂ : List GrammarSig.Sym} (x : GrammarSig.Sym) :
      Prefix l₁ l₂ → Prefix (x :: l₁) (x :: l₂)

/-- Boolean decision procedure for `Prefix`. -/
def isPrefix : List GrammarSig.Sym → List GrammarSig.Sym → Bool
  | [], _ => true
  | _ :: _, [] => false
  | t₁ :: q₁, t₂ :: q₂ => decide (t₁ = t₂) && isPrefix q₁ q₂

/-- `isPrefix` reflects `Prefix`. -/
theorem prefix_of_isPrefix : ∀ {l₁ l₂ : List GrammarSig.Sym},
    isPrefix l₁ l₂ = true → Prefix l₁ l₂
  | [], l₂, _ => .nil l₂
  | _ :: _, [], h => by simp [isPrefix] at h
  | t₁ :: q₁, t₂ :: q₂, h => by
    simp only [isPrefix, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨he, hp⟩ := h
    subst he
    exact .cons t₁ (prefix_of_isPrefix hp)

/-- `Prefix` is transitive. -/
theorem Prefix.trans {l₁ l₂ l₃ : List GrammarSig.Sym}
    (h₁₂ : Prefix l₁ l₂) (h₂₃ : Prefix l₂ l₃) : Prefix l₁ l₃ := by
  induction h₁₂ generalizing l₃ with
  | nil => exact .nil l₃
  | cons x h ih =>
    cases h₂₃ with
    | cons _ h₂₃' => exact .cons x (ih h₂₃')

/-! ### Prefix on state-predicate lists

Because the state-history assumptions are predicates, "prefix" becomes
entailment: `f₂` entails `f₁` (`f₂ x` implies `f₁ x` for every state `x`). -/

/-- Entailment-prefix on lists of state predicates. -/
inductive PrefixPred : List (AState → Bool) → List (AState → Bool) → Prop where
  | nil (l : List (AState → Bool)) : PrefixPred [] l
  | cons {l₁ l₂ : List (AState → Bool)} {f₁ f₂ : AState → Bool}
      (h : ∀ x, f₂ x = true → f₁ x = true) :
      PrefixPred l₁ l₂ → PrefixPred (f₁ :: l₁) (f₂ :: l₂)

/-- Boolean decision procedure for `PrefixPred`: for each aligned pair, `f₂ x`
    implies `f₁ x` on every (finite) state. -/
def isPrefixPred : List (AState → Bool) → List (AState → Bool) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | f₁ :: q₁, f₂ :: q₂ =>
    (Finite.all (α := AState)).all (fun x => !f₂ x || f₁ x) && isPrefixPred q₁ q₂

/-- `isPrefixPred` reflects `PrefixPred`. -/
theorem prefixPred_of_isPrefixPred : ∀ {l₁ l₂ : List (AState → Bool)},
    isPrefixPred l₁ l₂ = true → PrefixPred l₁ l₂
  | [], l₂, _ => .nil l₂
  | _ :: _, [], h => by simp [isPrefixPred] at h
  | f₁ :: q₁, f₂ :: q₂, h => by
    simp only [isPrefixPred, Bool.and_eq_true] at h
    obtain ⟨hall, hrest⟩ := h
    refine .cons (fun x hx => ?_) (prefixPred_of_isPrefixPred hrest)
    have := (List.all_eq_true.mp hall) x (Finite.mem_all x)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h0 | h1
    · rw [hx] at h0; exact absurd h0 (by simp)
    · exact h1

/-- `PrefixPred` is transitive: predicate entailments compose pointwise. -/
theorem PrefixPred.trans {l₁ l₂ l₃ : List (AState → Bool)}
    (h₁₂ : PrefixPred l₁ l₂) (h₂₃ : PrefixPred l₂ l₃) : PrefixPred l₁ l₃ := by
  induction h₁₂ generalizing l₃ with
  | nil => exact .nil l₃
  | @cons q₁ q₂ f₁ f₂ h₂₁ hq ih =>
    cases h₂₃ with
    | @cons _ q₃ _ f₃ h₃₂ hq₂₃ =>
      exact .cons (fun x hx => h₂₁ x (h₃₂ x hx)) (ih hq₂₃)

/-! ### Reachable states after a pop -/

/-- The states reachable after popping the symbols `toPop` from a stack, given the
    state-predicate annotation `annot` of the current state. -/
inductive StateValidAfterPop (s : AState) :
    List GrammarSig.Sym → List (AState → Bool) → Prop where
  | nil1 {p : AState → Bool} {pl : List (AState → Bool)} :
      p s = true → StateValidAfterPop s [] (p :: pl)
  | nil2 {sl : List GrammarSig.Sym} : StateValidAfterPop s sl []
  | cons {st : GrammarSig.Sym} {sq : List GrammarSig.Sym}
      {p : AState → Bool} {pl : List (AState → Bool)} :
      StateValidAfterPop s sq pl → StateValidAfterPop s (st :: sq) (p :: pl)

/-- Boolean form of `StateValidAfterPop`. -/
def isStateValidAfterPop (s : AState) :
    List GrammarSig.Sym → List (AState → Bool) → Bool
  | _, [] => true
  | [], p :: _ => p s
  | _ :: sl, _ :: pl => isStateValidAfterPop s sl pl

/-- If the boolean check succeeds then the relation holds. -/
theorem stateValidAfterPop_of_isStateValidAfterPop (s : AState) :
    ∀ (sl : List GrammarSig.Sym) (pl : List (AState → Bool)),
      isStateValidAfterPop s sl pl = true → StateValidAfterPop s sl pl
  | _, [], _ => .nil2
  | [], _ :: _, h => .nil1 h
  | _ :: sl, _ :: pl, h => .cons (stateValidAfterPop_of_isStateValidAfterPop s sl pl h)

/-- The contrapositive used to discharge the reduce check: if the boolean check
    is `false`, no state is valid after the pop, so the implication is vacuous. -/
theorem not_stateValidAfterPop_of_isStateValidAfterPop_false (s : AState) :
    ∀ (sl : List GrammarSig.Sym) (pl : List (AState → Bool)),
      isStateValidAfterPop s sl pl = false → ¬ StateValidAfterPop s sl pl
  | sl, [], hb, hv => by
    cases sl <;> simp [isStateValidAfterPop] at hb
  | [], p :: pl, hb, hv => by
    cases hv with
    | nil1 hp => rw [isStateValidAfterPop] at hb; rw [hp] at hb; exact absurd hb (by simp)
  | st :: sl, p :: pl, hb, hv => by
    cases hv with
    | cons hv' =>
      exact not_stateValidAfterPop_of_isStateValidAfterPop_false s sl pl
        (by rw [isStateValidAfterPop] at hb; exact hb) hv'

/-! ### The five safety predicates and their checkers -/

/-- After a shift, the destination state's `pastSymb` is a prefix of the source
    state's head symbols. -/
def ShiftHeadSymbs : Prop :=
  ∀ s : AState,
    match A.actionTable s with
    | .Lookahead awp => ∀ t : G.Terminal,
        match awp t with
        | .Shift s2 _ => Prefix (A.pastSymb s2) (headSymbs s)
        | _ => True
    | _ => True

/-- Boolean checker for `ShiftHeadSymbs`. -/
def shiftHeadSymbsCheck : Bool :=
  (Finite.all (α := AState)).all fun s =>
    match A.actionTable s with
    | .Lookahead awp => (Finite.all (α := G.Terminal)).all fun t =>
        match awp t with
        | .Shift s2 _ => isPrefix (A.pastSymb s2) (headSymbs s)
        | _ => true
    | _ => true

/-- When a goto happens, the destination state's `pastSymb` is a prefix of the
    source state's head symbols. -/
def GotoHeadSymbs : Prop :=
  ∀ (s : AState) (nt : G.NonTerminal),
    match A.gotoTable s nt with
    | some ⟨s2, _⟩ => Prefix (A.pastSymb s2) (headSymbs s)
    | none => True

/-- Boolean checker for `GotoHeadSymbs`. -/
def gotoHeadSymbsCheck : Bool :=
  (Finite.all (α := AState)).all fun s =>
    (Finite.all (α := G.NonTerminal)).all fun nt =>
      match A.gotoTable s nt with
      | some ⟨s2, _⟩ => isPrefix (A.pastSymb s2) (headSymbs s)
      | none => true

/-- The state-history assumptions are preserved by a shift. -/
def ShiftPastState : Prop :=
  ∀ s : AState,
    match A.actionTable s with
    | .Lookahead awp => ∀ t : G.Terminal,
        match awp t with
        | .Shift s2 _ => PrefixPred (A.pastStates s2) (headStates s)
        | _ => True
    | _ => True

/-- Boolean checker for `ShiftPastState`. -/
def shiftPastStateCheck : Bool :=
  (Finite.all (α := AState)).all fun s =>
    match A.actionTable s with
    | .Lookahead awp => (Finite.all (α := G.Terminal)).all fun t =>
        match awp t with
        | .Shift s2 _ => isPrefixPred (A.pastStates s2) (headStates s)
        | _ => true
    | _ => true

/-- The state-history assumptions are preserved by a goto. -/
def GotoPastState : Prop :=
  ∀ (s : AState) (nt : G.NonTerminal),
    match A.gotoTable s nt with
    | some ⟨s2, _⟩ => PrefixPred (A.pastStates s2) (headStates s)
    | none => True

/-- Boolean checker for `GotoPastState`. -/
def gotoPastStateCheck : Bool :=
  (Finite.all (α := AState)).all fun s =>
    (Finite.all (α := G.NonTerminal)).all fun nt =>
      match A.gotoTable s nt with
      | some ⟨s2, _⟩ => isPrefixPred (A.pastStates s2) (headStates s)
      | none => true

/-- A state is valid for reducing a production when the production's RHS is a
    prefix of the state's head symbols, and after popping the RHS a goto is always
    defined (or we are at an initial state whose start symbol is the LHS). -/
def ValidForReduce (s : AState) (prod : G.Production) : Prop :=
  Prefix (G.prodRhsRev prod) (headSymbs s) ∧
  ∀ stateNew : AState,
    StateValidAfterPop stateNew (G.prodRhsRev prod) (headStates s) →
    match A.gotoTable stateNew (G.prodLhs prod) with
    | none =>
      match stateNew with
      | .Init i => G.prodLhs prod = A.startNt i
      | .Ninit _ => False
    | _ => True

/-- Boolean checker for `ValidForReduce`. -/
def validForReduceCheck (s : AState) (prod : G.Production) : Bool :=
  isPrefix (G.prodRhsRev prod) (headSymbs s) &&
  (Finite.all (α := AState)).all fun stateNew =>
    if isStateValidAfterPop stateNew (G.prodRhsRev prod) (headStates s) then
      match A.gotoTable stateNew (G.prodLhs prod) with
      | none =>
        match stateNew with
        | .Init i => decide (G.prodLhs prod = A.startNt i)
        | .Ninit _ => false
      | _ => true
    else true

/-- Every state that reduces is valid for that reduction. -/
def ReduceOk : Prop :=
  ∀ s : AState,
    match A.actionTable s with
    | .Lookahead awp => ∀ t : G.Terminal,
        match awp t with
        | .Reduce p => ValidForReduce s p
        | _ => True
    | .DefaultReduce p => ValidForReduce s p

/-- Boolean checker for `ReduceOk`. -/
def reduceOkCheck : Bool :=
  (Finite.all (α := AState)).all fun s =>
    match A.actionTable s with
    | .Lookahead awp => (Finite.all (α := G.Terminal)).all fun t =>
        match awp t with
        | .Reduce p => validForReduceCheck s p
        | _ => true
    | .DefaultReduce p => validForReduceCheck s p

/-! ### The aggregate validator -/

/-- The automaton is safe: the conjunction of the five checks. -/
def Safe : Prop :=
  ShiftHeadSymbs ∧ GotoHeadSymbs ∧ ShiftPastState ∧ GotoPastState ∧ ReduceOk

/-- The boolean safety validator, run at build time via `native_decide`. -/
def safeValidator : Bool :=
  shiftHeadSymbsCheck && gotoHeadSymbsCheck && shiftPastStateCheck &&
  gotoPastStateCheck && reduceOkCheck

/-! ### Validator correctness: Boolean success establishes `Safe` -/

/-- `validForReduceCheck` reflects `ValidForReduce`. -/
theorem validForReduce_of_check {s : AState} {prod : G.Production}
    (h : validForReduceCheck s prod = true) : ValidForReduce s prod := by
  simp only [validForReduceCheck, Bool.and_eq_true] at h
  obtain ⟨hpre, hgoto⟩ := h
  refine ⟨prefix_of_isPrefix hpre, ?_⟩
  intro stateNew hvalid
  have hbody := (List.all_eq_true.mp hgoto) stateNew (Finite.mem_all stateNew)
  by_cases hb : isStateValidAfterPop stateNew (G.prodRhsRev prod) (headStates s) = true
  · rw [ite_eq_left hb] at hbody
    -- Match in the same order so the dependent branches align.
    revert hbody
    cases hg : A.gotoTable stateNew (G.prodLhs prod) with
    | some _ => intro _; trivial
    | none =>
      cases stateNew with
      | Init i => intro hb'; exact of_decide_eq_true hb'
      | Ninit n => intro hb'; exact absurd hb' (by simp)
  · -- Guard false: then `hvalid` is impossible.
    exact absurd hvalid
      (not_stateValidAfterPop_of_isStateValidAfterPop_false stateNew _ _
        (by simp only [Bool.not_eq_true] at hb; exact hb))

/-- **Validator correctness.** If Boolean safety validation succeeds, the
    automaton satisfies `Safe`. -/
theorem safe_of_safeValidator (h : safeValidator = true) : Safe := by
  simp only [safeValidator, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [shiftHeadSymbsCheck] at h1
  simp only [gotoHeadSymbsCheck] at h2
  simp only [shiftPastStateCheck] at h3
  simp only [gotoPastStateCheck] at h4
  simp only [reduceOkCheck] at h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ShiftHeadSymbs
    intro s
    have hs := (List.all_eq_true.mp h1) s (Finite.mem_all s)
    revert hs
    cases A.actionTable s with
    | DefaultReduce _ => intro _; trivial
    | Lookahead awp =>
      intro hs t
      have ht := (List.all_eq_true.mp hs) t (Finite.mem_all t)
      revert ht
      cases awp t with
      | Shift s2 e => intro ht; exact prefix_of_isPrefix ht
      | Reduce _ => intro _; trivial
      | Fail => intro _; trivial
  · -- GotoHeadSymbs
    intro s nt
    have hs := (List.all_eq_true.mp h2) s (Finite.mem_all s)
    have hnt := (List.all_eq_true.mp hs) nt (Finite.mem_all nt)
    revert hnt
    cases A.gotoTable s nt with
    | some se => intro hnt; exact prefix_of_isPrefix hnt
    | none => intro _; trivial
  · -- ShiftPastState
    intro s
    have hs := (List.all_eq_true.mp h3) s (Finite.mem_all s)
    revert hs
    cases A.actionTable s with
    | DefaultReduce _ => intro _; trivial
    | Lookahead awp =>
      intro hs t
      have ht := (List.all_eq_true.mp hs) t (Finite.mem_all t)
      revert ht
      cases awp t with
      | Shift s2 e => intro ht; exact prefixPred_of_isPrefixPred ht
      | Reduce _ => intro _; trivial
      | Fail => intro _; trivial
  · -- GotoPastState
    intro s nt
    have hs := (List.all_eq_true.mp h4) s (Finite.mem_all s)
    have hnt := (List.all_eq_true.mp hs) nt (Finite.mem_all nt)
    revert hnt
    cases A.gotoTable s nt with
    | some se => intro hnt; exact prefixPred_of_isPrefixPred hnt
    | none => intro _; trivial
  · -- ReduceOk
    intro s
    have hs := (List.all_eq_true.mp h5) s (Finite.mem_all s)
    revert hs
    cases A.actionTable s with
    | DefaultReduce p => intro hs; exact validForReduce_of_check hs
    | Lookahead awp =>
      intro hs t
      have ht := (List.all_eq_true.mp hs) t (Finite.mem_all t)
      revert ht
      cases awp t with
      | Shift _ _ => intro _; trivial
      | Reduce p => intro ht; exact validForReduce_of_check ht
      | Fail => intro _; trivial

end Runtime
