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
Soundness of the LR interpreter: the soundness result of §3.1 of Validating
LR(1) Parsers (Jourdan, Pottier, Leroy). We prove `parseCorrect`: if `parse`
returns `Parsed sem rest`, then the consumed prefix of the input has a parse tree
whose semantic value is `sem`.

Soundness concerns only `Parsed`; it needs no safety assumption. Safety separately
rules out the interpreter's explicit `Err` result.

The core is an invariant `WordHasStackSemantics word stk`: the stack is a
concatenation of sub-words, each carrying the semantic value of a parse tree for
that cell's incoming symbol. `pop`, `reduceStep`, `step` and `parseFix` all
preserve it, and at `Accept` it yields a parse tree for the whole consumed word.
-/
public import LeanParserGenerator.Runtime.Interpreter


@[expose] public section

set_option linter.unusedSectionVars false

namespace Runtime

open Grammar

variable [G : Grammar] [A : Automaton]

/-- The stack invariant: `word` splits into consecutive sub-words, one per stack
    cell (bottom-to-top), where each cell's stored semantic value is `ptSem` of
    some parse tree for that cell's incoming symbol over its sub-word. -/
inductive WordHasStackSemantics : List G.Token → Stack → Prop where
  | nil : WordHasStackSemantics [] []
  | cons {wordq : List G.Token} {stackq : Stack}
      (hq : WordHasStackSemantics wordq stackq)
      {wordt : List G.Token} (s : A.NonInitState)
      (pt : ParseTree (A.lastSymb s) wordt) :
      WordHasStackSemantics (wordq ++ wordt) (⟨s, ptSem pt⟩ :: stackq)

/-- Cast a parse tree along an equality of head symbols. -/
def castPT {a b : Sym} {word : List G.Token} (h : a = b) (pt : ParseTree a word) :
    ParseTree b word := h ▸ pt

/-- `ptSem` commutes with `castPT`/`castSem`: casting the tree then taking its
    semantics equals taking semantics then casting the value. -/
theorem ptSem_castPT {a b : Sym} {word : List G.Token} (h : a = b)
    (pt : ParseTree a word) : ptSem (castPT h pt) = castSem h (ptSem pt) := by
  subst h; rfl
/-- Specification of `pop` on a semantically-valid stack. If `pop syms stk action`
    succeeds with `(stk', res)` and the whole `word` has stack semantics on `stk`,
    then `word` splits as `wordStk' ++ wordRes`, the popped part is described by a
    parse-tree-list `ptl : ParseTreeList syms wordRes` with `ptlSem ptl action =
    res`, and the remainder `stk'` still has stack semantics on `wordStk'`. -/
theorem pop_spec {B : Type} :
    ∀ (syms : List Sym) (stk : Stack) (action : arrowsRight B (syms.map G.semT))
      (stk' : Stack) (res : B) (word : List G.Token),
      pop syms stk action = some (stk', res) →
      WordHasStackSemantics word stk →
      ∃ (wordStk' wordRes : List G.Token) (ptl : ParseTreeList syms wordRes),
        wordStk' ++ wordRes = word ∧
        WordHasStackSemantics wordStk' stk' ∧
        ptlSem ptl action = res := by
  intro syms
  induction syms with
  | nil =>
    intro stk action stk' res word hpop hword
    simp only [pop, Option.some.injEq] at hpop
    obtain ⟨hstk, hres⟩ := Prod.mk.injEq .. |>.mp hpop
    exact ⟨word, [], .nil, by simp, hstk ▸ hword, by simp only [ptlSem]; exact hres⟩
  | cons t syms ih =>
    intro stk action stk' res word hpop hword
    cases hword with
    | nil => simp [pop] at hpop
    | @cons wordq stackq hq wordt sTop pt =>
      simp only [pop] at hpop
      split at hpop
      · next hsym =>
        obtain ⟨wordStk', wordRes, ptl, hsplit, hrest, hsem⟩ :=
          ih stackq (action (castSem hsym (ptSem pt))) stk' res wordq hpop hq
        refine ⟨wordStk', wordRes ++ wordt, ?_, ?_, ?_, ?_⟩
        · exact .cons ptl (castPT hsym pt)
        · -- word equality: (wordStk' ++ wordRes) ++ wordt = wordq ++ wordt
          rw [← List.append_assoc, hsplit]
        · exact hrest
        · -- semantics: consing pt then folding = folding with the applied action
          simp only [ptlSem, ptSem_castPT]; exact hsem
      · exact absurd hpop (by simp)

variable {S : Type} [AS : AppStream S G.Token]

open AppStream (appList appList_shift appList_nil)

/-- `reduceStep` preserves the stack-semantics invariant, and on `Accept`
    exhibits a parse tree for the whole consumed word. -/
theorem reduceStep_invariant (init : A.InitState) (stk : Stack) (prod : G.Production)
    (s : S) (word : List G.Token) (hword : WordHasStackSemantics word stk) :
    match reduceStep (S := S) init stk prod s with
    | .Accept sem s' => ∃ pt : ParseTree (.NT (A.startNt init)) word, s = s' ∧ ptSem pt = sem
    | .Progress stk' s' => s = s' ∧ WordHasStackSemantics word stk'
    | .Fail _ _ => True
    | .Err _ => True := by
  unfold reduceStep
  cases hpop : pop (G.prodRhsRev prod) stk (G.prodAction prod) with
  | none => simp
  | some result =>
    obtain ⟨stk', sem⟩ := result
    obtain ⟨wordStk', wordRes, ptl, hsplit, hrest, hsem⟩ :=
      pop_spec _ _ _ _ _ word hpop hword
    have hsem' : sem = ptSem (ParseTree.nonTerminal prod ptl) := by
      simp only [ptSem]; exact hsem.symm
    subst hsem'
    simp only []
    cases hgoto : A.gotoTable (stateOfStack init stk') (G.prodLhs prod) with
    | some se =>
      obtain ⟨stateNew, e⟩ := se
      refine ⟨rfl, ?_⟩
      rw [show castSem e (ptSem (ParseTree.nonTerminal prod ptl))
            = ptSem (castPT e (ParseTree.nonTerminal prod ptl)) from
          (ptSem_castPT e _).symm]
      rw [← hsplit]
      exact .cons hrest stateNew (castPT e (ParseTree.nonTerminal prod ptl))
    | none =>
      cases hrest with
      | nil =>
        by_cases h : G.prodLhs prod = A.startNt init
        · simp only [h, dite_eq_left]
          subst hsplit
          refine ⟨castPT (congrArg (fun nt => (Symbol.NT nt : Sym)) h)
                    (ParseTree.nonTerminal prod ptl), True.intro, ?_⟩
          simp only [ptSem_castPT, List.nil_append]
        · simp only [h, dite_eq_right, not_false_iff]
      | cons _ _ _ => exact True.intro

section Sound

/-- One `step` preserves the reconstruction `appList word s` and the stack
    invariant; on `Accept` it exhibits a parse tree. -/
theorem step_invariant (init : A.InitState) (stk : Stack) (s : S)
    (word : List G.Token) (hword : WordHasStackSemantics word stk) :
    match step (S := S) init stk s with
    | .Accept sem s' =>
        ∃ (wordNew : List G.Token) (pt : ParseTree (.NT (A.startNt init)) wordNew),
          appList word s = appList wordNew s' ∧ ptSem pt = sem
    | .Progress stkNew s' =>
        ∃ wordNew, appList word s = appList wordNew s' ∧ WordHasStackSemantics wordNew stkNew
    | .Fail _ _ => True
    | .Err _ => True := by
  cases haction : A.actionTable (stateOfStack init stk) with
  | DefaultReduce prod =>
    have hstep : step (S := S) init stk s = reduceStep init stk prod s := by
      unfold step; rw [haction]
    rw [hstep]
    have hr := reduceStep_invariant (S := S) init stk prod s word hword
    cases hrs : reduceStep (S := S) init stk prod s with
    | Accept sem s' =>
      rw [hrs] at hr; obtain ⟨pt, hbuf, hsem⟩ := hr
      exact ⟨word, pt, by rw [hbuf], hsem⟩
    | Progress stk' s' =>
      rw [hrs] at hr; obtain ⟨hbuf, hinv⟩ := hr
      exact ⟨word, by rw [hbuf], hinv⟩
    | Fail _ _ => exact True.intro
    | Err _ => exact True.intro
  | Lookahead awt =>
    cases hawt : awt (G.tokenTerm (TokenStream.head s)) with
    | Shift stateNew e =>
      have hstep : step (S := S) init stk s
          = .Progress (⟨stateNew, castSem e (G.tokenSem (TokenStream.head s))⟩ :: stk)
              (TokenStream.tail s) := by
        unfold step; rw [haction]; simp only [hawt]
      rw [hstep]
      refine ⟨word ++ [TokenStream.head s], appList_shift word s, ?_⟩
      have hcell : G.tokenSem (TokenStream.head s)
          = ptSem (ParseTree.terminal (TokenStream.head s)) := by
        simp only [ptSem]
      rw [hcell, ← ptSem_castPT e (ParseTree.terminal (TokenStream.head s))]
      exact .cons hword stateNew (castPT e (ParseTree.terminal (TokenStream.head s)))
    | Reduce prod =>
      have hstep : step (S := S) init stk s = reduceStep init stk prod s := by
        unfold step; rw [haction]; simp only [hawt]
      rw [hstep]
      have hr := reduceStep_invariant (S := S) init stk prod s word hword
      cases hrs : reduceStep (S := S) init stk prod s with
      | Accept sem s' =>
        rw [hrs] at hr; obtain ⟨pt, hbuf, hsem⟩ := hr
        exact ⟨word, pt, by rw [hbuf], hsem⟩
      | Progress stk' s' =>
        rw [hrs] at hr; obtain ⟨hbuf, hinv⟩ := hr
        exact ⟨word, by rw [hbuf], hinv⟩
      | Fail _ _ => exact True.intro
      | Err _ => exact True.intro
    | Fail =>
      have hstep : step (S := S) init stk s
          = .Fail (stateOfStack init stk) (TokenStream.head s) := by
        unfold step; rw [haction]; simp only [hawt]
      rw [hstep]; exact True.intro

/-- `parseFix` preserves the invariant across all its iterations. -/
theorem parseFix_invariant (init : A.InitState) (logN : Nat) :
    ∀ (stk : Stack) (s : S) (word : List G.Token),
      WordHasStackSemantics word stk →
      match parseFix (S := S) init stk s logN with
      | .Accept sem s' =>
          ∃ (wordNew : List G.Token) (pt : ParseTree (.NT (A.startNt init)) wordNew),
            appList word s = appList wordNew s' ∧ ptSem pt = sem
      | .Progress stkNew s' =>
          ∃ wordNew, appList word s = appList wordNew s' ∧ WordHasStackSemantics wordNew stkNew
      | .Fail _ _ => True
      | .Err _ => True := by
  induction logN with
  | zero =>
    intro stk s word hword
    exact step_invariant init stk s word hword
  | succ n ih =>
    intro stk s word hword
    have h1 := ih stk s word hword
    simp only [parseFix]
    cases hpf : parseFix (S := S) init stk s n with
    | Accept sem s' => rw [hpf] at h1; simpa using h1
    | Progress stk' s' =>
      rw [hpf] at h1; obtain ⟨wordNew, hbuf, hinv⟩ := h1
      have h2 := ih stk' s' wordNew hinv
      dsimp only
      cases hpf2 : parseFix (S := S) init stk' s' n with
      | Accept sem s'' =>
        rw [hpf2] at h2; obtain ⟨wN, pt, hbuf2, hsem⟩ := h2
        exact ⟨wN, pt, by rw [hbuf, hbuf2], hsem⟩
      | Progress stk'' s'' =>
        rw [hpf2] at h2; obtain ⟨wN, hbuf2, hinv2⟩ := h2
        exact ⟨wN, by rw [hbuf, hbuf2], hinv2⟩
      | Fail _ _ => exact True.intro
      | Err _ => exact True.intro
    | Fail _ _ => rw [hpf] at h1; simp
    | Err _ => exact True.intro

/-- **Soundness of the interpreter.** If `parse` accepts with semantic value `sem`
    and remaining stream `rest`, then the consumed prefix `word` of the input has
    a parse tree whose semantic value is `sem`, and the original stream is `word`
    prepended to `rest`. Holds with no safety assumption. -/
theorem parseCorrect (init : A.InitState) (s : S) (logN : Nat) :
    match parse (S := S) init s logN with
    | .Parsed sem s' =>
        ∃ (word : List G.Token) (pt : ParseTree (.NT (A.startNt init)) word),
          s = appList word s' ∧ ptSem pt = sem
    | _ => True := by
  unfold parse
  have h := parseFix_invariant (S := S) init logN [] s [] .nil
  cases hpf : parseFix (S := S) init [] s logN with
  | Accept sem s' =>
    rw [hpf] at h; obtain ⟨word, pt, hbuf, hsem⟩ := h
    refine ⟨word, pt, ?_, hsem⟩
    rw [← AppStream.appList_nil (Token := G.Token) s]; exact hbuf
  | Fail st tok => exact True.intro
  | Progress _ _ => exact True.intro
  | Err _ => exact True.intro

end Sound

end Runtime
