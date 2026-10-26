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
Safety (internal-error freedom) of the LR interpreter: the operational payoff of
the safety conditions in §3.2 of Validating LR(1) Parsers (Jourdan, Pottier,
Leroy). The boolean validator and its Prop model live in
`Runtime/Validator/Safe.lean`; this file proves once and for all:

* a recursively stated stack invariant records that the current state's
  `pastSymb` and `pastStates` annotations hold of the concrete stack;
* validated reductions can always pop their RHS, and a missing goto is either the
  valid start-production acceptance case or impossible;
* shifts and gotos preserve the invariant;
* therefore `step`, `parseFix`, and `parse` never return `.Err` under `Safe` (and,
  via `safe_of_safeValidator`, from a successful safety validation proof).
-/
public import LeanParserGenerator.Runtime.Interpreter
public import LeanParserGenerator.Runtime.Validator.Safe


@[expose] public section

set_option linter.unusedSectionVars false

namespace Runtime

open Grammar

variable [G : Grammar] [A : Automaton]

/-- Symbols carried by the concrete automaton stack, top first. -/
def symbStackOfStack : Stack → List Grammar.Sym
  | [] => []
  | ⟨s, _⟩ :: stk => A.lastSymb s :: symbStackOfStack stk

/-- Singleton predicates for the concrete state stack, top first, terminated by
    the initial state. -/
def stateStackOfStack (init : A.InitState) : Stack → List (AState → Bool)
  | [] => [singletonStatePred (.Init init)]
  | ⟨s, _⟩ :: stk => singletonStatePred (.Ninit s) :: stateStackOfStack init stk

/-- The safety stack invariant. At every suffix, the top state's symbol and state
    annotations are prefixes (predicate-entailment prefixes for states) of the
    concrete stack. -/
def StackInvariant (init : A.InitState) : Stack → Prop
  | [] =>
      Prefix (headSymbs (.Init init)) [] ∧
      PrefixPred (headStates (.Init init)) (stateStackOfStack init [])
  | ⟨s, _⟩ :: stk =>
      Prefix (headSymbs (.Ninit s)) (A.lastSymb s :: symbStackOfStack stk) ∧
      PrefixPred (headStates (.Ninit s))
        (singletonStatePred (.Ninit s) :: stateStackOfStack init stk) ∧
      StackInvariant init stk

/-- The empty parser stack satisfies the invariant. -/
theorem stackInvariant_nil (init : A.InitState) : StackInvariant init [] := by
  refine ⟨.nil [], ?_⟩
  exact .cons (fun _ h => h) (.nil [])

/-- Symbol-prefix component at the current stack state. -/
theorem StackInvariant.symbs {init : A.InitState} {stk : Stack}
    (h : StackInvariant init stk) :
    Prefix (headSymbs (stateOfStack init stk)) (symbStackOfStack stk) := by
  cases stk with
  | nil => exact h.1
  | cons cell rest =>
    obtain ⟨s, sem⟩ := cell
    exact h.1

/-- State-predicate-prefix component at the current stack state. -/
theorem StackInvariant.states {init : A.InitState} {stk : Stack}
    (h : StackInvariant init stk) :
    PrefixPred (headStates (stateOfStack init stk)) (stateStackOfStack init stk) := by
  cases stk with
  | nil => exact h.2
  | cons cell rest =>
    obtain ⟨s, sem⟩ := cell
    exact h.2.1

/-- Removing the top cell preserves the recursively stored invariant. -/
theorem StackInvariant.tail {init : A.InitState} {s : A.NonInitState}
    {sem : G.semT (A.lastSymb s)} {stk : Stack}
    (h : StackInvariant init (⟨s, sem⟩ :: stk)) : StackInvariant init stk :=
  h.2.2

/-- Push a state whose annotations are justified by the current state. This is the
    common preservation argument for both shift and goto transitions. -/
theorem StackInvariant.push {init : A.InitState} {stk : Stack}
    (hInv : StackInvariant init stk) (stateNew : A.NonInitState)
    (sem : G.semT (A.lastSymb stateNew))
    (hSymbs : Prefix (A.pastSymb stateNew) (headSymbs (stateOfStack init stk)))
    (hStates : PrefixPred (A.pastStates stateNew) (headStates (stateOfStack init stk))) :
    StackInvariant init (⟨stateNew, sem⟩ :: stk) := by
  refine ⟨.cons (A.lastSymb stateNew) (hSymbs.trans hInv.symbs), ?_, hInv⟩
  exact .cons (fun _ hx => hx) (hStates.trans hInv.states)

/-! ### Safe popping -/

/-- Invert a nonempty structural prefix. -/
theorem Prefix.cons_inv {x y : Grammar.Sym} {xs ys : List Grammar.Sym}
    (h : Prefix (x :: xs) (y :: ys)) : x = y ∧ Prefix xs ys := by
  cases h with
  | cons _ htail => exact ⟨rfl, htail⟩

/-- With no symbols to pop, a predicate prefix of the concrete state stack
    validates the current state. This is the base case of the pop lemma. -/
theorem stateValidAfterPop_nil_of_prefixPred (init : A.InitState) (stk : Stack)
    (lpred : List (AState → Bool))
    (hPred : PrefixPred lpred (stateStackOfStack init stk)) :
    StateValidAfterPop (stateOfStack init stk) [] lpred := by
  cases lpred with
  | nil => exact .nil2
  | cons p ps =>
    cases stk with
    | nil =>
      cases hPred with
      | cons hp _ =>
        exact .nil1 (hp (.Init init) (by simp [singletonStatePred]))
    | cons cell rest =>
      obtain ⟨s, sem⟩ := cell
      cases hPred with
      | cons hp _ =>
        exact .nil1 (hp (.Ninit s) (by simp [singletonStatePred]))

/-- A prefix-certified pop succeeds, preserves the recursive stack invariant, and
    leaves a state allowed by the supplied state-predicate annotation. This
    combines invariant preservation and state validity across the pop. -/
theorem pop_safe (init : A.InitState) :
    ∀ (syms : List Grammar.Sym) (stk : Stack)
      (action : arrowsRight B (syms.map G.semT)) (lpred : List (AState → Bool)),
      StackInvariant init stk →
      Prefix syms (symbStackOfStack stk) →
      PrefixPred lpred (stateStackOfStack init stk) →
      ∃ (stk' : Stack) (res : B),
        pop syms stk action = some (stk', res) ∧
        StackInvariant init stk' ∧
        StateValidAfterPop (stateOfStack init stk') syms lpred := by
  intro syms
  induction syms with
  | nil =>
    intro stk action lpred hInv _ hPred
    exact ⟨stk, action, rfl, hInv, stateValidAfterPop_nil_of_prefixPred init stk lpred hPred⟩
  | cons t syms ih =>
    intro stk action lpred hInv hPrefix hPred
    cases stk with
    | nil =>
      exact absurd hPrefix (by intro h; cases h)
    | cons cell rest =>
      obtain ⟨stateTop, semTop⟩ := cell
      obtain ⟨ht, hPrefixTail⟩ := hPrefix.cons_inv
      have heq : A.lastSymb stateTop = t := ht.symm
      have hInvTail := hInv.tail
      cases lpred with
      | nil =>
        obtain ⟨stk', res, hpop, hInv', _⟩ :=
          ih rest (action (castSem heq semTop)) [] hInvTail hPrefixTail (.nil _)
        refine ⟨stk', res, ?_, hInv', .nil2⟩
        simp only [pop, dite_eq_left heq]
        exact hpop
      | cons p ps =>
        cases hPred with
        | cons _ hPredTail =>
          obtain ⟨stk', res, hpop, hInv', hValid⟩ :=
            ih rest (action (castSem heq semTop)) ps hInvTail hPrefixTail hPredTail
          refine ⟨stk', res, ?_, hInv', .cons hValid⟩
          simp only [pop, dite_eq_left heq]
          exact hpop

/-! ### Safe reduction and one-step execution -/

variable {S : Type} [TokenStream S G.Token]

/-- The property needed of an interpreter step: internal error is impossible and
    every progress result carries an invariant stack. -/
def StepResultInvariant (init : A.InitState) : StepResult S init → Prop
  | .Err _ => False
  | .Progress stk _ => StackInvariant init stk
  | .Fail _ _ => True
  | .Accept _ _ => True

/-- A validator-approved reduction cannot hit either `reduceStep` error branch;
    if it follows a goto, the resulting stack satisfies the invariant. -/
theorem reduceStep_safe (hSafe : Safe) (init : A.InitState) (stk : Stack)
    (prod : G.Production) (stream : S) (hInv : StackInvariant init stk)
    (hValid : ValidForReduce (stateOfStack init stk) prod) :
    StepResultInvariant init (reduceStep init stk prod stream) := by
  obtain ⟨stk', sem, hpop, hInv', hStateValid⟩ :=
    pop_safe init (G.prodRhsRev prod) stk (G.prodAction prod)
      (headStates (stateOfStack init stk)) hInv
      (hValid.1.trans hInv.symbs) hInv.states
  unfold reduceStep
  cases hgoto : A.gotoTable (stateOfStack init stk') (G.prodLhs prod) with
  | some target =>
    obtain ⟨stateNew, e⟩ := target
    have hGotoSymbs := hSafe.2.1 (stateOfStack init stk') (G.prodLhs prod)
    have hGotoStates := hSafe.2.2.2.1 (stateOfStack init stk') (G.prodLhs prod)
    rw [hgoto] at hGotoSymbs hGotoStates
    simpa only [hpop, hgoto, StepResultInvariant] using
      hInv'.push stateNew (castSem e sem) hGotoSymbs hGotoStates
  | none =>
    have hMissing := hValid.2 (stateOfStack init stk') hStateValid
    rw [hgoto] at hMissing
    cases stk' with
    | nil =>
      have hStart : G.prodLhs prod = A.startNt init := by
        simpa only [stateOfStack] using hMissing
      simp [hpop, hgoto, hStart, StepResultInvariant]
    | cons cell rest =>
      obtain ⟨s, cellSem⟩ := cell
      change False at hMissing
      exact hMissing.elim

/-- One interpreter step cannot return `.Err` from an invariant stack under
    `Safe`; shifts and reductions preserve the invariant on progress. -/
theorem step_safe (hSafe : Safe) (init : A.InitState) (stk : Stack) (stream : S)
    (hInv : StackInvariant init stk) : StepResultInvariant init (step init stk stream) := by
  let current := stateOfStack init stk
  cases haction : A.actionTable current with
  | DefaultReduce prod =>
    have hValid := hSafe.2.2.2.2 current
    rw [haction] at hValid
    unfold step
    rw [show stateOfStack init stk = current from rfl, haction]
    exact reduceStep_safe hSafe init stk prod stream hInv hValid
  | Lookahead awt =>
    let tok := TokenStream.head stream
    let term := G.tokenTerm tok
    have hReduce := hSafe.2.2.2.2 current
    have hShiftSymbs := hSafe.1 current
    have hShiftStates := hSafe.2.2.1 current
    rw [haction] at hReduce hShiftSymbs hShiftStates
    cases hlook : awt term with
    | Shift stateNew e =>
      have hs := hShiftSymbs term
      have hp := hShiftStates term
      rw [hlook] at hs hp
      unfold step
      rw [show stateOfStack init stk = current from rfl, haction]
      simp only [tok, term, hlook]
      exact hInv.push stateNew (castSem e (G.tokenSem tok)) hs hp
    | Reduce prod =>
      have hValid := hReduce term
      rw [hlook] at hValid
      unfold step
      rw [show stateOfStack init stk = current from rfl, haction]
      simp only [tok, term, hlook]
      exact reduceStep_safe hSafe init stk prod stream hInv hValid
    | Fail =>
      unfold step
      rw [show stateOfStack init stk = current from rfl, haction]
      simp only [tok, term, hlook, StepResultInvariant]

/-! ### Fuel iteration and public Err-freedom theorem -/

/-- Every bounded execution preserves the one-step safety property. In
    particular, an `.Err` result is impossible at any fuel depth. -/
theorem parseFix_safe (hSafe : Safe) (init : A.InitState) (logN : Nat) :
    ∀ (stk : Stack) (stream : S), StackInvariant init stk →
      StepResultInvariant init (parseFix init stk stream logN) := by
  induction logN with
  | zero =>
    intro stk stream hInv
    exact step_safe hSafe init stk stream hInv
  | succ n ih =>
    intro stk stream hInv
    have hFirst := ih stk stream hInv
    cases hres : parseFix init stk stream n with
    | Progress stk' stream' =>
      rw [hres] at hFirst
      simpa only [parseFix, hres] using ih stk' stream' hFirst
    | Fail st tok =>
      simpa only [parseFix, hres] using hFirst
    | Accept sem stream' =>
      simpa only [parseFix, hres] using hFirst
    | Err msg =>
      simpa only [parseFix, hres] using hFirst

/-- Predicate selecting exactly the forbidden `ParseResult.Err` outcome. -/
def ParseResultErrFree (init : A.InitState) : ParseResult S init → Prop
  | .Err _ => False
  | .Fail _ _ => True
  | .Timeout => True
  | .Parsed _ _ => True

/-- **Safety / Err-freedom of the interpreter.** A `Safe` automaton can reject,
    time out, or accept, but `parse` cannot report an internal automaton error. -/
theorem parse_err_free (hSafe : Safe) (init : A.InitState) (stream : S) (logN : Nat) :
    ParseResultErrFree init (parse init stream logN) := by
  have hRun := parseFix_safe hSafe init logN [] stream (stackInvariant_nil init)
  unfold parse
  cases hres : parseFix init [] stream logN with
  | Fail st tok => trivial
  | Accept sem stream' => trivial
  | Progress stk' stream' => trivial
  | Err msg =>
    rw [hres] at hRun
    exact hRun

/-- Equality-style form of `parse_err_free`: no concrete error message can be the
    parser result. -/
theorem parse_ne_err (hSafe : Safe) (init : A.InitState) (stream : S) (logN : Nat)
    (msg : String) : parse init stream logN ≠ ParseResult.Err msg := by
  intro hErr
  have h := parse_err_free hSafe init stream logN
  rw [hErr] at h
  exact h

/-- A successful safety validation proof supplies the `Safe` proposition required
    for Err-freedom. Generated code normally derives and exposes that proposition
    as `safety`. -/
theorem parse_err_free_of_safeValidator
    (hValidation : safeValidator (G := G.toGrammarSig) (A := A) = true)
    (init : A.InitState) (stream : S) (logN : Nat) :
    ParseResultErrFree init (parse init stream logN) :=
  parse_err_free (safe_of_safeValidator hValidation) init stream logN

/-- Equality-style Err-freedom corollary from a safety validation proof. -/
theorem parse_ne_err_of_safeValidator
    (hValidation : safeValidator (G := G.toGrammarSig) (A := A) = true)
    (init : A.InitState) (stream : S) (logN : Nat) (msg : String) :
    parse init stream logN ≠ ParseResult.Err msg :=
  parse_ne_err (safe_of_safeValidator hValidation) init stream logN msg

end Runtime
