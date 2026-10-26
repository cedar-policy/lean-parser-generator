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
Operational completeness and semantic unambiguity: the completeness result of
§3.3 of Validating LR(1) Parsers (Jourdan, Pottier, Leroy), plus the
unambiguity corollary. Given the semantic `Complete` certificate property, a
parse tree drives the deterministic LR interpreter through exactly one action per
tree node. Sufficient logarithmic fuel therefore returns that tree's semantic
value and the exact residual stream; insufficient fuel can only time out.
-/
public import LeanParserGenerator.Runtime.Correct
public import LeanParserGenerator.Runtime.Validator.Complete


@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Runtime

open Grammar
open AppStream (appList appList_append appList_nil)

variable [G : Grammar] [A : Automaton]
variable {S : Type} [AS : AppStream S G.Token]

/-! ### Nullable and FIRST correctness supplied by `Complete` -/

/-- Every parse tree contains at least one node. -/
@[simp] theorem ptSize_pos {head : Grammar.Sym} {word : List G.Token}
    (pt : ParseTree head word) : 0 < ptSize pt := by
  cases pt <;> simp [ptSize]

/-- Nullability is insensitive to word reversal. -/
theorem nullableWord_reverse (word : List Grammar.Sym) :
    nullableWord word.reverse = nullableWord word := by
  simp [nullableWord, List.all_reverse]

/-- A parse tree for the empty word has a nullable head symbol. -/
theorem nullable_correct (hComplete : Complete) {head : Grammar.Sym}
    {word : List G.Token} (hword : word = []) (pt : ParseTree head word) :
    nullableSymb head = true :=
  ParseTree.rec
    (motive_1 := fun head word _ => word = [] → nullableSymb head = true)
    (motive_2 := fun heads word _ => word = [] → nullableWord heads = true)
    (fun _ h => by simp at h)
    (fun prod {word} _ ih h => by
      have hstable := hComplete.1 prod
      have hnull := ih h
      rw [hnull] at hstable
      exact hstable)
    (fun _ => rfl)
    (fun {headsQ} {wordQ} _ {headT} {wordT} _ ihq iht h => by
      have hwordQ : wordQ = [] := by cases wordQ <;> simp_all
      have hwordT : wordT = [] := by cases wordT <;> simp_all
      simp only [nullableWord, List.all_cons, Bool.and_eq_true]
      exact ⟨iht hwordT, ihq hwordQ⟩)
    pt hword

/-- A parse-tree list for the empty word has an all-nullable symbol list. -/
theorem nullable_list_correct (hComplete : Complete) {heads : List Grammar.Sym}
    {word : List G.Token} (hword : word = []) (ptl : ParseTreeList heads word) :
    nullableWord heads = true :=
  ParseTreeList.rec
    (motive_1 := fun head word _ => word = [] → nullableSymb head = true)
    (motive_2 := fun heads word _ => word = [] → nullableWord heads = true)
    (fun _ h => by simp at h)
    (fun prod {word} _ ih h => by
      have hstable := hComplete.1 prod
      have hnull := ih h
      rw [hnull] at hstable
      exact hstable)
    (fun _ => rfl)
    (fun {headsQ} {wordQ} _ {headT} {wordT} _ ihq iht h => by
      have hwordQ : wordQ = [] := by cases wordQ <;> simp_all
      have hwordT : wordT = [] := by cases wordT <;> simp_all
      simp only [nullableWord, List.all_cons, Bool.and_eq_true]
      exact ⟨iht hwordT, ihq hwordQ⟩)
    ptl hword

/-- FIRST of an append consists of FIRST of the left word, plus FIRST of the
    right word when the left word is nullable. -/
theorem firstWordCheck_append (left right : List Grammar.Sym) (term : G.Terminal) :
    firstWordCheck (left ++ right) term = true ↔
      firstWordCheck left term = true ∨
        (nullableWord left = true ∧ firstWordCheck right term = true) := by
  induction left with
  | nil => simp [firstWordCheck, nullableWord]
  | cons symb rest ih =>
    cases hn : nullableSymb symb with
    | false =>
      simp only [List.cons_append, firstWordCheck, hn, ite_false,
        nullableWord, List.all_cons, Bool.false_and, Bool.false_eq_true,
        false_and]
      simp
    | true =>
      simp only [List.cons_append, firstWordCheck, hn, ite_true, Bool.or_eq_true,
        nullableWord, List.all_cons, Bool.true_and, ih]
      constructor <;> intro h
      · rcases h with h | h | ⟨hnull, hr⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨hnull, hr⟩
      · rcases h with (h | h) | ⟨hnull, hr⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hnull, hr⟩)

/-- The first token of a nonempty parse tree belongs to FIRST of its head. -/
theorem first_correct (hComplete : Complete) {head : Grammar.Sym}
    {word : List G.Token} (tok : G.Token) (rest : List G.Token)
    (hword : word = tok :: rest) (pt : ParseTree head word) :
    firstSymbCheck head (G.tokenTerm tok) = true :=
  ParseTree.rec
    (motive_1 := fun head word _ => ∀ tok rest, word = tok :: rest →
      firstSymbCheck head (G.tokenTerm tok) = true)
    (motive_2 := fun heads word _ => ∀ tok rest, word = tok :: rest →
      firstWordCheck heads.reverse (G.tokenTerm tok) = true)
    (fun leaf tok rest h => by obtain ⟨rfl, rfl⟩ := h; simp [firstSymbCheck])
    (fun prod {word} _ ih tok rest h => by
      simp only [firstSymbCheck, decide_eq_true_eq]
      exact hComplete.2.1 prod (G.tokenTerm tok) (ih tok rest h))
    (fun _ _ h => by simp at h)
    (fun {headsQ} {wordQ} q {headT} {wordT} _ ihq iht tok rest h => by
      rw [List.reverse_cons, firstWordCheck_append]
      cases wordQ with
      | nil =>
        right
        have hwordT : wordT = tok :: rest := by simpa using h
        refine ⟨?_, ?_⟩
        · rw [nullableWord_reverse]
          exact nullable_list_correct hComplete rfl q
        · simpa [firstWordCheck] using iht tok rest hwordT
      | cons qtok qrest =>
        left
        have hcons : qtok :: (qrest ++ wordT) = tok :: rest := by
          simpa only [List.cons_append] using h
        have htok : qtok = tok := (List.cons.inj hcons).1
        subst qtok
        exact ihq tok qrest rfl)
    pt tok rest hword

/-- The first token of a nonempty parse-tree list belongs to FIRST of the
    source-order symbol sequence (the stored head list is reversed). -/
theorem first_list_correct (hComplete : Complete) {heads : List Grammar.Sym}
    {word : List G.Token} (tok : G.Token) (rest : List G.Token)
    (hword : word = tok :: rest) (ptl : ParseTreeList heads word) :
    firstWordCheck heads.reverse (G.tokenTerm tok) = true :=
  ParseTreeList.rec
    (motive_1 := fun head word _ => ∀ tok rest, word = tok :: rest →
      firstSymbCheck head (G.tokenTerm tok) = true)
    (motive_2 := fun heads word _ => ∀ tok rest, word = tok :: rest →
      firstWordCheck heads.reverse (G.tokenTerm tok) = true)
    (fun leaf tok rest h => by obtain ⟨rfl, rfl⟩ := h; simp [firstSymbCheck])
    (fun prod {word} _ ih tok rest h => by
      simp only [firstSymbCheck, decide_eq_true_eq]
      exact hComplete.2.1 prod (G.tokenTerm tok) (ih tok rest h))
    (fun _ _ h => by simp at h)
    (fun {headsQ} {wordQ} q {headT} {wordT} _ ihq iht tok rest h => by
      rw [List.reverse_cons, firstWordCheck_append]
      cases wordQ with
      | nil =>
        right
        have hwordT : wordT = tok :: rest := by simpa using h
        refine ⟨?_, ?_⟩
        · rw [nullableWord_reverse]
          exact nullable_list_correct hComplete rfl q
        · simpa [firstWordCheck] using iht tok rest hwordT
      | cons qtok qrest =>
        left
        have hcons : qtok :: (qrest ++ wordT) = tok :: rest := by
          simpa only [List.cons_append] using h
        have htok : qtok = tok := (List.cons.inj hcons).1
        subst qtok
        exact ihq tok qrest rfl)
    ptl tok rest hword

/-! ### Dotted parse trees and zippers -/

mutual
/-- A parse tree with a hole, represented from the hole toward the root. -/
inductive PtZipper (init : A.InitState) (fullWord : List G.Token) :
    (holeSymb : Grammar.Sym) → (holeWord : List G.Token) → Type
  | top {holeSymb : Grammar.Sym} {holeWord : List G.Token}
      (head_eq : holeSymb = .NT (A.startNt init))
      (word_eq : holeWord = fullWord) :
      PtZipper init fullWord holeSymb holeWord
  | cons {headsQ : List Grammar.Sym} {wordQ : List G.Token}
      (ptl : ParseTreeList headsQ wordQ)
      {headT : Grammar.Sym} {wordT : List G.Token}
      (ptlz : PtlZipper init fullWord (headT :: headsQ) (wordQ ++ wordT)) :
      PtZipper init fullWord headT wordT

/-- A parse-tree-list zipper with a hole. -/
inductive PtlZipper (init : A.InitState) (fullWord : List G.Token) :
    (holeSymbs : List Grammar.Sym) → (holeWord : List G.Token) → Type
  | nonTerminal {prod : G.Production} {word : List G.Token}
      (ptz : PtZipper init fullWord (.NT (G.prodLhs prod)) word) :
      PtlZipper init fullWord (G.prodRhsRev prod) word
  | cons {headsQ : List Grammar.Sym} {wordQ : List G.Token}
      {headT : Grammar.Sym} {wordT : List G.Token}
      (pt : ParseTree headT wordT)
      (ptlz : PtlZipper init fullWord (headT :: headsQ) (wordQ ++ wordT)) :
      PtlZipper init fullWord headsQ wordQ
end

/-- A dotted parse tree: the next parser action is either a reduction or shift. -/
inductive PtDot (init : A.InitState) (fullWord : List G.Token) where
  | reduce (prod : G.Production) {word : List G.Token}
      (ptl : ParseTreeList (G.prodRhsRev prod) word)
      (ptz : PtZipper init fullWord (.NT (G.prodLhs prod)) word) : PtDot init fullWord
  | shift (tok : G.Token) {headsQ : List Grammar.Sym} {wordQ : List G.Token}
      (ptl : ParseTreeList headsQ wordQ)
      (ptlz : PtlZipper init fullWord
        (.T (G.tokenTerm tok) :: headsQ) (wordQ ++ [tok])) : PtDot init fullWord

section ZipperObservers

variable {init : A.InitState} {fullWord : List G.Token} (bufEnd : S)

mutual
/-- Fill a tree zipper with a semantic value. -/
def ptzSem : {head : Grammar.Sym} → {word : List G.Token} →
    PtZipper init fullWord head word → G.semT head →
      G.semT (.NT (A.startNt init))
  | _, _, .top head_eq _, sem => castSem head_eq sem
  | _, _, .cons ptl ptlz, sem =>
      ptlzSem ptlz (fun B action =>
        have action' : G.semT _ → arrowsRight B _ := action
        ptlSem ptl (action' sem))

/-- Fill a parse-tree-list zipper with a continuation. -/
def ptlzSem : {heads : List Grammar.Sym} → {word : List G.Token} →
    PtlZipper init fullWord heads word →
      (∀ B : Type, arrowsRight B (heads.map G.semT) → B) →
      G.semT (.NT (A.startNt init))
  | _, _, .nonTerminal (prod := prod) ptz, k =>
      ptzSem ptz (k _ (G.prodAction prod))
  | _, _, .cons (headT := hT) pt ptlz, k =>
      ptlzSem ptlz (fun B action =>
        have action' : G.semT hT → arrowsRight B _ := action
        k B (action' (ptSem pt)))
end

/-- Semantic value represented by a dotted parse tree. -/
def ptdSem : PtDot init fullWord → G.semT (.NT (A.startNt init))
  | .reduce prod ptl ptz => ptzSem ptz (ptlSem ptl (G.prodAction prod))
  | .shift tok ptl ptlz =>
      ptlzSem ptlz
        (fun B action =>
          have action' : G.semT (.T (G.tokenTerm tok)) → arrowsRight B _ := action
          ptlSem ptl (action' (G.tokenSem tok)))

mutual
/-- Residual stream at a tree zipper. -/
def ptzBuffer : {head : Grammar.Sym} → {word : List G.Token} →
    PtZipper init fullWord head word → S
  | _, _, .top _ _ => bufEnd
  | _, _, .cons _ ptlz => ptlzBuffer ptlz

/-- Residual stream at a parse-tree-list zipper. -/
def ptlzBuffer : {heads : List Grammar.Sym} → {word : List G.Token} →
    PtlZipper init fullWord heads word → S
  | _, _, .nonTerminal ptz => ptzBuffer ptz
  | _, _, .cons (wordT := wordT) _ ptlz => appList wordT (ptlzBuffer ptlz)
end

/-- Residual stream at a dotted parse tree. -/
def ptdBuffer : PtDot init fullWord → S
  | .reduce _ _ ptz => ptzBuffer (bufEnd := bufEnd) ptz
  | .shift tok _ ptlz => appList [tok] (ptlzBuffer (bufEnd := bufEnd) ptlz)

/-- Production whose item contains a parse-tree-list zipper's dot. -/
def ptlzProd : {heads : List Grammar.Sym} → {word : List G.Token} →
    PtlZipper init fullWord heads word → G.Production
  | _, _, .nonTerminal (prod := prod) _ => prod
  | _, _, .cons _ ptlz => ptlzProd ptlz

/-- Symbols after a parse-tree-list zipper's dot, in source order. -/
def ptlzFuture : {heads : List Grammar.Sym} → {word : List G.Token} →
    PtlZipper init fullWord heads word → List Grammar.Sym
  | _, _, .nonTerminal _ => []
  | _, _, .cons (headT := headT) _ ptlz => headT :: ptlzFuture ptlz

/-- Lookahead terminal of the item represented by a parse-tree-list zipper. -/
def ptlzLookahead : {heads : List Grammar.Sym} → {word : List G.Token} →
    PtlZipper init fullWord heads word → G.Terminal
  | _, _, .nonTerminal ptz => G.tokenTerm (TokenStream.head (ptzBuffer (bufEnd := bufEnd) ptz))
  | _, _, .cons _ ptlz => ptlzLookahead ptlz

mutual
/-- Number of actions represented above a parse-tree-list zipper. -/
def ptlzCost : {heads : List Grammar.Sym} → {word : List G.Token} →
    PtlZipper init fullWord heads word → Nat
  | _, _, .nonTerminal ptz => ptzCost ptz
  | _, _, .cons pt ptlz => ptSize pt + ptlzCost ptlz

/-- Number of actions represented above a tree zipper. -/
def ptzCost : {head : Grammar.Sym} → {word : List G.Token} →
    PtZipper init fullWord head word → Nat
  | _, _, .top _ _ => 0
  | _, _, .cons _ ptlz => 1 + ptlzCost ptlz
end

/-- Number of parser actions remaining after the current dotted action. -/
def ptdCost : PtDot init fullWord → Nat
  | .reduce _ _ ptz => ptzCost ptz
  | .shift _ _ ptlz => 1 + ptlzCost ptlz

end ZipperObservers

/-! ### Stack compatibility -/

/-- A parse-tree list describes the top fragment between `stk` and `stk0`. -/
def PtlStackCompat (stk0 : Stack) :
    {heads : List Grammar.Sym} → {word : List G.Token} →
      ParseTreeList heads word → Stack → Prop
  | [], _, .nil, stk => stk0 = stk
  | _ :: _, _, .cons q pt, stk =>
      match stk with
      | [] => False
      | ⟨state, sem⟩ :: rest =>
          PtlStackCompat stk0 q rest ∧
          ∃ h : A.lastSymb state = _, castSem h sem = ptSem pt

/-- Stack compatibility makes `pop` return exactly the represented semantics. -/
theorem pop_of_ptlStackCompat {B : Type} (stk0 : Stack) :
    ∀ {heads : List Grammar.Sym} {word : List G.Token}
      (ptl : ParseTreeList heads word) (stk : Stack)
      (action : arrowsRight B (heads.map G.semT)),
      PtlStackCompat stk0 ptl stk →
        pop heads stk action = some (stk0, ptlSem ptl action) := by
  intro heads word ptl
  cases ptl with
  | nil =>
    intro stk action h
    subst stk
    simp only [pop, ptlSem]
  | @cons headsQ wordQ q headT wordT pt =>
    intro stk action h
    cases stk with
    | nil => exact h.elim
    | cons cell rest =>
      obtain ⟨state, sem⟩ := cell
      obtain ⟨hq, heq⟩ := h
      rcases heq with ⟨hsym, hsem⟩
      simp only [pop, dite_eq_left hsym]
      rw [hsem]
      simpa only [ptlSem] using
        pop_of_ptlStackCompat stk0 q rest (action (ptSem pt)) hq

section Compatibility

variable (init : A.InitState) (fullWord : List G.Token) (bufEnd : S)

mutual
/-- A stack is compatible with a tree zipper. -/
def PtZipperStackCompat : {head : Grammar.Sym} → {word : List G.Token} →
    Stack → PtZipper init fullWord head word → Prop
  | _, _, stk, .top _ _ => stk = []
  | head, _, stk, .cons ptl ptlz =>
      ∃ stk0,
        StateHasFuture (stateOfStack init stk) (ptlzProd ptlz)
          (head :: ptlzFuture ptlz) (ptlzLookahead (bufEnd := bufEnd) ptlz) ∧
        PtlStackCompat stk0 ptl stk ∧
        PtlZipperStackCompat stk0 ptlz

/-- A stack is compatible with a parse-tree-list zipper. -/
def PtlZipperStackCompat : {heads : List Grammar.Sym} → {word : List G.Token} →
    Stack → PtlZipper init fullWord heads word → Prop
  | _, _, stk, .nonTerminal ptz => PtZipperStackCompat stk ptz
  | _, _, stk, .cons _ ptlz => PtlZipperStackCompat stk ptlz
end

/-- A stack is compatible with a dotted parse tree. -/
def PtDotStackCompat (ptd : PtDot init fullWord) (stk : Stack) : Prop :=
  match ptd with
  | .reduce prod ptl ptz =>
      ∃ stk0,
        StateHasFuture (stateOfStack init stk) prod []
          (G.tokenTerm (TokenStream.head (ptzBuffer (bufEnd := bufEnd) ptz))) ∧
        PtlStackCompat stk0 ptl stk ∧
        PtZipperStackCompat init fullWord bufEnd stk0 ptz
  | .shift tok ptl ptlz =>
      ∃ stk0,
        StateHasFuture (stateOfStack init stk) (ptlzProd ptlz)
          (.T (G.tokenTerm tok) :: ptlzFuture ptlz)
          (ptlzLookahead (bufEnd := bufEnd) ptlz) ∧
        PtlStackCompat stk0 ptl stk ∧
        PtlZipperStackCompat init fullWord bufEnd stk0 ptlz

end Compatibility

/-! ### Zipper item facts -/

/-- The symbols already represented by a list zipper plus its future reconstruct
    the enclosing production's reversed RHS. -/
theorem ptlzFuture_prod {init : A.InitState} {fullWord : List G.Token}
    {heads : List Grammar.Sym} {word : List G.Token}
    (ptlz : PtlZipper init fullWord heads word) :
    (ptlzFuture ptlz).reverse ++ heads = G.prodRhsRev (ptlzProd ptlz) :=
  PtlZipper.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun heads _ ptlz =>
      (ptlzFuture ptlz).reverse ++ heads = G.prodRhsRev (ptlzProd ptlz))
    (fun _ _ => True.intro)
    (fun {headsQ} {wordQ} _ {headT} {wordT} _ _ => True.intro)
    (fun _ _ => by simp [ptlzFuture, ptlzProd])
    (fun _ rest ih => by
      simpa only [ptlzFuture, ptlzProd, List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih)
    ptlz

/-- The next stream terminal is either in FIRST of the zipper future, or is the
    inherited lookahead when that future is nullable. -/
theorem ptlzFuture_first (hComplete : Complete) {init : A.InitState}
    {fullWord : List G.Token} (bufEnd : S) {heads : List Grammar.Sym}
    {word : List G.Token} (ptlz : PtlZipper init fullWord heads word) :
    firstWordCheck (ptlzFuture ptlz)
        (G.tokenTerm (TokenStream.head (ptlzBuffer (bufEnd := bufEnd) ptlz))) = true ∨
      (G.tokenTerm (TokenStream.head (ptlzBuffer (bufEnd := bufEnd) ptlz)) =
          ptlzLookahead (bufEnd := bufEnd) ptlz ∧
        nullableWord (ptlzFuture ptlz) = true) :=
  PtlZipper.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ ptlz =>
      firstWordCheck (ptlzFuture ptlz)
          (G.tokenTerm (TokenStream.head (ptlzBuffer (bufEnd := bufEnd) ptlz))) = true ∨
        (G.tokenTerm (TokenStream.head (ptlzBuffer (bufEnd := bufEnd) ptlz)) =
            ptlzLookahead (bufEnd := bufEnd) ptlz ∧
          nullableWord (ptlzFuture ptlz) = true))
    (fun _ _ => True.intro)
    (fun {headsQ} {wordQ} _ {headT} {wordT} _ _ => True.intro)
    (fun _ _ => Or.inr ⟨rfl, rfl⟩)
    (fun {headsQ} {wordQ} {headT} {wordT} pt rest ih => by
      cases wordT with
      | nil =>
        have hnull := nullable_correct hComplete rfl pt
        simp only [ptlzBuffer, appList_nil] at ih ⊢
        rcases ih with hfirst | ⟨hlook, hrestNull⟩
        · left
          simp [ptlzFuture, firstWordCheck, hnull, hfirst]
        · right
          refine ⟨hlook, ?_⟩
          simp only [ptlzFuture, nullableWord, List.all_cons, Bool.and_eq_true]
          exact ⟨hnull, hrestNull⟩
      | cons tok tail =>
        have hfirst := first_correct hComplete tok tail rfl pt
        left
        simp only [ptlzBuffer, AppStream.head_appList_cons]
        cases hn : nullableSymb headT <;>
          simp [ptlzFuture, firstWordCheck, hn, hfirst])
    ptlz


/-! ### Building and advancing dotted parse trees -/

/-
The traversal descends to the leftmost leaf of a parse tree. We define it by
direct structural matching on `ParseTree`/`ParseTreeList`, recursing on intrinsic
size. The enclosing production's reversed RHS is definitionally `headT :: headsQ`
at each `.cons`, so zipper construction needs no transport or cast.
-/

/-- A non-nil witness for a reversed head-symbol list, computed from a
    parse-tree list without destructuring its dependent contents. This option
    trick lets `buildPt` decide reduce-vs-descend without pattern-matching a
    value whose type index (`prodRhsRev prod`) is a stuck application. -/
def isNotNil {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word) :
    Option (match heads with | [] => Empty | _ :: _ => Unit) :=
  match heads, word, ptl with
  | _, _, .nil => none
  | _, _, .cons _ _ => some Unit.unit

/-- If a parse-tree list has no non-nil witness then it is `.nil` (size zero). -/
theorem ptlSize_eq_zero_of_isNotNil_none {heads : List Grammar.Sym}
    {word : List G.Token} (ptl : ParseTreeList heads word)
    (h : isNotNil ptl = none) : ptlSize ptl = 0 := by
  cases ptl with
  | nil => rfl
  | cons q t => simp only [isNotNil, reduceCtorEq] at h

/-- If a parse-tree list has no non-nil witness then it recognizes the empty
    word. -/
theorem word_eq_nil_of_isNotNil_none {heads : List Grammar.Sym}
    {word : List G.Token} (ptl : ParseTreeList heads word)
    (h : isNotNil ptl = none) : word = [] := by
  cases ptl with
  | nil => rfl
  | cons q t => simp only [isNotNil, reduceCtorEq] at h

/-- If a parse-tree list has no non-nil witness then its head-symbol list is
    empty. -/
theorem heads_eq_nil_of_isNotNil_none {heads : List Grammar.Sym}
    {word : List G.Token} (ptl : ParseTreeList heads word)
    (h : isNotNil ptl = none) : heads = [] := by
  cases ptl with
  | nil => rfl
  | cons q t => simp only [isNotNil, reduceCtorEq] at h

/-- An empty parse-tree list is stack-compatible with any stack, taking that same
    stack as its base. -/
theorem ptlStackCompat_self_of_isNotNil_none {heads : List Grammar.Sym}
    {word : List G.Token} (ptl : ParseTreeList heads word)
    (h : isNotNil ptl = none) (stk : Stack) : PtlStackCompat stk ptl stk := by
  cases ptl with
  | nil => simp only [PtlStackCompat]
  | cons q t => simp only [isNotNil, reduceCtorEq] at h

/-- Casting a semantic value forward then back is the identity. -/
theorem castSem_symm_castSem {a b : Grammar.Sym} (h : a = b) (x : G.semT a) :
    castSem h.symm (castSem h x) = x := by
  cases h; rfl

mutual
/-- Descend from a parse tree to its first parser action. -/
def buildPt {init : A.InitState} {fullWord : List G.Token}
    {head : Grammar.Sym} {word : List G.Token}
    (pt : ParseTree head word) (ptz : PtZipper init fullWord head word) :
    PtDot init fullWord :=
  match pt with
  | .terminal tok =>
      match ptz with
      | .top head_eq _ => nomatch head_eq
      | .cons ptl ptlz => .shift tok ptl ptlz
  | .nonTerminal prod ptl =>
      match isNotNil ptl with
      | none => .reduce prod ptl ptz
      | some hne => buildPtRec ptl hne (.nonTerminal ptz)
termination_by 2 * ptSize pt
decreasing_by
  simp only [ptSize]
  omega

/-- Descend through a not-yet-recognized reversed parse-tree list (with a proof it
    is nonempty) to its leftmost tree, under the enclosing item's zipper. The
    head-symbol index is a variable, so the constructor matches type-check with no
    dependent cast. -/
def buildPtRec {init : A.InitState} {fullWord : List G.Token}
    {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word)
    (hne : match heads with | [] => Empty | _ :: _ => Unit)
    (ptlz : PtlZipper init fullWord heads word) :
    PtDot init fullWord :=
  match ptl with
  | .nil => hne.elim
  | .cons q t =>
      match isNotNil q with
      | none => buildPt t (.cons q ptlz)
      | some hq => buildPtRec q hq (.cons t ptlz)
termination_by 2 * ptlSize ptl + 1
decreasing_by
  · simp only [ptlSize]; have _ := ptSize_pos t; omega
  · simp only [ptlSize]; have hpos := ptSize_pos t; omega
end

/-- Continue after one tree has been recognized in a list zipper. -/
def continuePtl {init : A.InitState} {fullWord : List G.Token}
    {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word) (ptlz : PtlZipper init fullWord heads word) :
    PtDot init fullWord :=
  match ptlz with
  | .nonTerminal (prod := prod) ptz => .reduce prod ptl ptz
  | .cons pt rest => buildPt pt (.cons ptl rest)

/-- Advance after a reduction, accepting exactly at the top zipper. -/
def nextReduce {init : A.InitState} {fullWord : List G.Token}
    (prod : G.Production) {word : List G.Token}
    (ptl : ParseTreeList (G.prodRhsRev prod) word)
    (ptz : PtZipper init fullWord (.NT (G.prodLhs prod)) word) :
    Option (PtDot init fullWord) :=
  match (generalizing := true) ptz with
  | .top _ _ => none
  | .cons prefixPtl ptlz =>
      some (continuePtl (.cons prefixPtl (.nonTerminal prod ptl)) ptlz)

/-- Advance the parse-tree traversal by one parser action. -/
def nextPtd {init : A.InitState} {fullWord : List G.Token} :
    PtDot init fullWord → Option (PtDot init fullWord)
  | .shift tok ptl ptlz => some (continuePtl (.cons ptl (.terminal tok)) ptlz)
  | .reduce prod ptl ptz => nextReduce prod ptl ptz

/-- Iterate `nextPtd` with the same doubling schedule as `parseFix`. -/
def nextPtdIter {init : A.InitState} {fullWord : List G.Token}
    (ptd : PtDot init fullWord) : Nat → Option (PtDot init fullWord)
  | 0 => nextPtd ptd
  | n + 1 =>
      match nextPtdIter ptd n with
      | none => none
      | some ptd' => nextPtdIter ptd' n

/-! ### Traversal preserves semantics -/

mutual
/-- Descending into a tree preserves the represented root semantic value. -/
theorem buildPt_sem {init : A.InitState} {fullWord : List G.Token}
    {head : Grammar.Sym} {word : List G.Token}
    (pt : ParseTree head word) (ptz : PtZipper init fullWord head word) :
    ptzSem ptz (ptSem pt) = ptdSem (buildPt pt ptz) := by
  match pt, ptz with
  | .terminal tok, .top head_eq _ => nomatch head_eq
  | .terminal tok, .cons ptl ptlz =>
      simp only [buildPt.eq_def, ptdSem, ptzSem, ptSem]
  | .nonTerminal prod ptl, ptz =>
      simp only [buildPt, ptSem]
      split
      · next hn =>
        simp only [ptdSem]
      · next hne _ =>
        have ih := buildPtRec_sem ptl hne (PtlZipper.nonTerminal ptz)
        simp only [ptlzSem] at ih ⊢
        exact ih
termination_by 2 * ptSize pt
decreasing_by
  simp only [ptSize]
  omega

/-- Descending through a nonempty tree list preserves semantics. -/
theorem buildPtRec_sem {init : A.InitState} {fullWord : List G.Token}
    {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word)
    (hne : match heads with | [] => Empty | _ :: _ => Unit)
    (ptlz : PtlZipper init fullWord heads word) :
    ptlzSem ptlz (fun _ action => ptlSem ptl action) =
      ptdSem (buildPtRec ptl hne ptlz) := by
  match ptl, hne, ptlz with
  | .nil, hne, _ => exact hne.elim
  | .cons q t, _, ptlz =>
      rw [buildPtRec.eq_def]
      simp only [ptlSem]
      cases hq : isNotNil q with
      | none =>
        simp only []
        have ih := buildPt_sem t (PtZipper.cons q ptlz)
        simp only [ptzSem] at ih ⊢
        exact ih
      | some hq' =>
        simp only []
        have ih := buildPtRec_sem q hq' (PtlZipper.cons t ptlz)
        simpa only [ptlzSem] using ih
termination_by 2 * ptlSize ptl + 1
decreasing_by
  · simp only [ptlSize]; have _ := ptSize_pos t; omega
  · simp only [ptlSize]; have hpos := ptSize_pos t; omega
end

/-- Continuing after a recognized tree-list preserves semantics. -/
theorem continuePtl_sem {init : A.InitState} {fullWord : List G.Token}
    {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word) (ptlz : PtlZipper init fullWord heads word) :
    ptlzSem ptlz (fun _ action => ptlSem ptl action) =
      ptdSem (continuePtl ptl ptlz) := by
  cases ptlz with
  | nonTerminal ptz => simp [continuePtl, ptlzSem, ptdSem]
  | cons pt rest =>
    have ih := buildPt_sem pt (PtZipper.cons ptl rest)
    simpa [continuePtl, ptlzSem, ptzSem] using ih

/-- One dotted traversal step preserves semantics when another dot remains. -/
theorem nextPtd_sem {init : A.InitState} {fullWord : List G.Token}
    (ptd : PtDot init fullWord) :
    match nextPtd ptd with
    | none => True
    | some ptd' => ptdSem ptd = ptdSem ptd' := by
  cases ptd with
  | shift tok ptl ptlz =>
    simpa [nextPtd, ptdSem, ptSem, ptlSem] using
      continuePtl_sem (ParseTreeList.cons ptl (ParseTree.terminal tok)) ptlz
  | reduce prod ptl ptz =>
    cases ptz with
    | top _ _ => trivial
    | cons prefixPtl ptlz =>
      simpa [nextPtd, nextReduce, ptdSem, ptSem, ptzSem, ptlSem] using
        continuePtl_sem (ParseTreeList.cons prefixPtl (.nonTerminal prod ptl)) ptlz

/-- Iterating the traversal preserves semantics whenever it does not run out of
    dots. -/
theorem nextPtdIter_sem {init : A.InitState} {fullWord : List G.Token}
    (ptd : PtDot init fullWord) (logN : Nat) :
    match nextPtdIter ptd logN with
    | none => True
    | some ptd' => ptdSem ptd = ptdSem ptd' := by
  induction logN generalizing ptd with
  | zero => simpa only [nextPtdIter] using nextPtd_sem ptd
  | succ n ih =>
    have ih1 := ih ptd
    cases hpd : nextPtdIter ptd n with
    | none => simp only [nextPtdIter, hpd]
    | some ptd' =>
      rw [hpd] at ih1
      have ih2 := ih ptd'
      cases hpd2 : nextPtdIter ptd' n with
      | none => simp only [nextPtdIter, hpd, hpd2]
      | some ptd'' =>
        rw [hpd2] at ih2
        simp only [nextPtdIter, hpd, hpd2]
        rw [ih1, ih2]

/-! ### Traversal cost matches the parser's action count -/

section Cost

variable {init : A.InitState} {fullWord : List G.Token}

mutual
/-- Descending into a tree spends exactly one action plus the remaining cost. -/
theorem buildPt_cost {head : Grammar.Sym} {word : List G.Token}
    (pt : ParseTree head word) (ptz : PtZipper init fullWord head word) :
    ptSize pt + ptzCost ptz = ptdCost (buildPt pt ptz) + 1 := by
  match pt, ptz with
  | .terminal tok, .top head_eq _ => nomatch head_eq
  | .terminal tok, .cons ptl ptlz =>
      simp only [buildPt.eq_def, ptSize, ptzCost, ptdCost]
      omega
  | .nonTerminal prod ptl, ptz =>
      simp only [buildPt, ptSize]
      split
      · next hn =>
        have hnil : ptlSize ptl = 0 := ptlSize_eq_zero_of_isNotNil_none ptl hn
        simp only [ptdCost]
        omega
      · next hne _ =>
        have ih := buildPtRec_cost ptl hne (PtlZipper.nonTerminal ptz)
        simp only [ptlzCost] at ih ⊢
        omega
termination_by 2 * ptSize pt
decreasing_by
  simp only [ptSize]
  omega

/-- Descending through a nonempty list spends its own actions. -/
theorem buildPtRec_cost {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word)
    (hne : match heads with | [] => Empty | _ :: _ => Unit)
    (ptlz : PtlZipper init fullWord heads word) :
    ptlSize ptl + ptlzCost ptlz = ptdCost (buildPtRec ptl hne ptlz) := by
  match ptl, hne, ptlz with
  | .nil, hne, _ => exact hne.elim
  | .cons q t, _, ptlz =>
      rw [buildPtRec.eq_def]
      simp only [ptlSize]
      cases hq : isNotNil q with
      | none =>
        simp only []
        have hnil : ptlSize q = 0 := ptlSize_eq_zero_of_isNotNil_none q hq
        have ih := buildPt_cost t (PtZipper.cons q ptlz)
        simp only [ptzCost] at ih
        omega
      | some hq' =>
        simp only []
        have ih := buildPtRec_cost q hq' (PtlZipper.cons t ptlz)
        simp only [ptlzCost] at ih
        omega
termination_by 2 * ptlSize ptl + 1
decreasing_by
  · simp only [ptlSize]; have _ := ptSize_pos t; omega
  · simp only [ptlSize]; have hpos := ptSize_pos t; omega
end

/-- Continuing after a recognized list spends its cost. -/
theorem continuePtl_cost {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word) (ptlz : PtlZipper init fullWord heads word) :
    ptlzCost ptlz = ptdCost (continuePtl ptl ptlz) := by
  cases ptlz with
  | nonTerminal ptz => simp only [continuePtl, ptlzCost, ptdCost]
  | cons pt rest =>
    have ih := buildPt_cost pt (PtZipper.cons ptl rest)
    simp only [continuePtl, ptlzCost, ptzCost] at ih ⊢
    omega

/-- One traversal step drops the cost by exactly one, unless it is the last. -/
theorem nextPtd_cost (ptd : PtDot init fullWord) :
    match nextPtd ptd with
    | none => ptdCost ptd = 0
    | some ptd' => ptdCost ptd = ptdCost ptd' + 1 := by
  cases ptd with
  | shift tok ptl ptlz =>
    have ih := continuePtl_cost (ParseTreeList.cons ptl (ParseTree.terminal tok)) ptlz
    simp only [nextPtd, ptdCost] at ih ⊢
    omega
  | reduce prod ptl ptz =>
    cases ptz with
    | top _ _ => simp only [nextPtd, nextReduce, ptdCost, ptzCost]
    | cons prefixPtl ptlz =>
      have ih := continuePtl_cost
        (ParseTreeList.cons prefixPtl (.nonTerminal prod ptl)) ptlz
      simp only [nextPtd, nextReduce, ptdCost, ptzCost] at ih ⊢
      omega

/-- Iterated cost: either the traversal runs out within `2^logN` steps (cost
    strictly below the bound) or it consumes exactly `2^logN` and continues. -/
theorem nextPtdIter_cost (ptd : PtDot init fullWord) (logN : Nat) :
    match nextPtdIter ptd logN with
    | none => ptdCost ptd < 2 ^ logN
    | some ptd' => ptdCost ptd = 2 ^ logN + ptdCost ptd' := by
  induction logN generalizing ptd with
  | zero =>
    simp only [nextPtdIter, Nat.pow_zero]
    have h := nextPtd_cost ptd
    cases hpd : nextPtd ptd with
    | none => rw [hpd] at h; omega
    | some ptd' => rw [hpd] at h; omega
  | succ n ih =>
    have ih1 := ih ptd
    cases hpd : nextPtdIter ptd n with
    | none =>
      rw [hpd] at ih1
      simp only [nextPtdIter, hpd, Nat.pow_succ]
      omega
    | some ptd' =>
      rw [hpd] at ih1
      have ih2 := ih ptd'
      cases hpd2 : nextPtdIter ptd' n with
      | none =>
        rw [hpd2] at ih2
        simp only [nextPtdIter, hpd, hpd2, Nat.pow_succ]
        omega
      | some ptd'' =>
        rw [hpd2] at ih2
        simp only [nextPtdIter, hpd, hpd2, Nat.pow_succ]
        omega

end Cost

/-! ### Traversal buffers match the parser's residual input -/

section Buffer

variable {init : A.InitState} {fullWord : List G.Token} (bufEnd : S)

open AppStream (appList appList_append appList_nil)

mutual
/-- Descending into a tree prepends the tree's word to the residual buffer. -/
theorem buildPt_buffer {head : Grammar.Sym} {word : List G.Token}
    (pt : ParseTree head word) (ptz : PtZipper init fullWord head word) :
    appList word (ptzBuffer (bufEnd := bufEnd) ptz)
      = ptdBuffer (bufEnd := bufEnd) (buildPt pt ptz) := by
  match pt, ptz with
  | .terminal tok, .top head_eq _ => nomatch head_eq
  | .terminal tok, .cons ptl ptlz =>
      simp only [buildPt.eq_def, ptdBuffer, ptzBuffer]
  | .nonTerminal prod ptl, ptz =>
      simp only [buildPt]
      split
      · next hn =>
        have hnil : word = [] := word_eq_nil_of_isNotNil_none ptl hn
        subst hnil
        simp only [ptdBuffer, appList_nil]
      · next hne _ =>
        have ih := buildPtRec_buffer ptl hne (PtlZipper.nonTerminal ptz)
        simp only [ptlzBuffer] at ih ⊢
        exact ih
termination_by 2 * ptSize pt
decreasing_by
  simp only [ptSize]
  omega

/-- Descending through a nonempty list prepends its word. -/
theorem buildPtRec_buffer {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word)
    (hne : match heads with | [] => Empty | _ :: _ => Unit)
    (ptlz : PtlZipper init fullWord heads word) :
    appList word (ptlzBuffer (bufEnd := bufEnd) ptlz)
      = ptdBuffer (bufEnd := bufEnd) (buildPtRec ptl hne ptlz) := by
  match ptl, hne, ptlz with
  | .nil, hne, _ => exact hne.elim
  | .cons q t, _, ptlz =>
      rw [buildPtRec.eq_def]
      cases hq : isNotNil q with
      | none =>
        simp only [hq]
        have hwq := word_eq_nil_of_isNotNil_none q hq
        have ih := buildPt_buffer t (PtZipper.cons q ptlz)
        simp only [ptzBuffer] at ih ⊢
        subst hwq
        simpa only [List.nil_append] using ih
      | some hq' =>
        simp only [hq]
        have ih := buildPtRec_buffer q hq' (PtlZipper.cons t ptlz)
        simp only [ptlzBuffer, appList_append] at ih ⊢
        exact ih
termination_by 2 * ptlSize ptl + 1
decreasing_by
  · simp only [ptlSize]; have _ := ptSize_pos t; omega
  · simp only [ptlSize]; have hpos := ptSize_pos t; omega
end

/-- Continuing after a recognized list leaves the buffer unchanged. -/
theorem continuePtl_buffer {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word) (ptlz : PtlZipper init fullWord heads word) :
    ptlzBuffer (bufEnd := bufEnd) ptlz
      = ptdBuffer (bufEnd := bufEnd) (continuePtl ptl ptlz) := by
  cases ptlz with
  | nonTerminal ptz => simp only [continuePtl, ptlzBuffer, ptdBuffer]
  | cons pt rest =>
    have ih := buildPt_buffer (bufEnd := bufEnd) pt (PtZipper.cons ptl rest)
    simp only [continuePtl, ptlzBuffer, ptzBuffer] at ih ⊢
    exact ih

end Buffer

/-! ### Stack compatibility is preserved by descent -/

section StackCompatBuild

variable {init : A.InitState} {fullWord : List G.Token}

/-- `futureOfProd prod 0` is the whole right-hand side in source order. -/
theorem futureOfProd_zero (prod : G.Production) :
    futureOfProd prod 0 = (G.prodRhsRev prod).reverse := by
  simp only [futureOfProd, List.drop_zero]

/- Descending into a tree, or a nonempty list, preserves stack compatibility. -/
mutual
theorem buildPt_stackCompat (hComplete : Complete) (bufEnd : S) {head : Grammar.Sym} {word : List G.Token}
    (pt : ParseTree head word) (ptz : PtZipper init fullWord head word) (stk : Stack)
    (hstk : PtZipperStackCompat init fullWord bufEnd stk ptz) :
    PtDotStackCompat init fullWord bufEnd (buildPt pt ptz) stk := by
  match pt, ptz with
  | .terminal tok, .top head_eq _ => nomatch head_eq
  | .terminal tok, .cons ptl ptlz =>
      rw [buildPt.eq_def]
      simp only [PtDotStackCompat]
      obtain ⟨stk0, hfut, hcompat, hzc⟩ := hstk
      exact ⟨stk0, hfut, hcompat, hzc⟩
  | .nonTerminal prod ptl, ptz =>
      have hfut0 : StateHasFuture (stateOfStack init stk) prod
          ((G.prodRhsRev prod).reverse)
          (G.tokenTerm (TokenStream.head (ptzBuffer (bufEnd := bufEnd) ptz))) := by
        match ptz, hstk with
        | .top head_eq _, hstk =>
            simp only [PtZipperStackCompat] at hstk
            subst hstk
            have hnt : A.startNt init = G.prodLhs prod := by
              have := head_eq
              simp only [Symbol.NT.injEq] at this
              exact this.symm
            simp only [ptzBuffer, stateOfStack]
            exact hComplete.2.2.1 init prod hnt.symm _
        | .cons ptl0 ptlz0, hstk =>
            obtain ⟨stk0, hfut, hcompat, hzc⟩ := hstk
            have hclosed := hComplete.2.2.2.2.2.2.2
              (stateOfStack init stk) (ptlzProd ptlz0)
              (.NT (G.prodLhs prod) :: ptlzFuture ptlz0)
              (ptlzLookahead (bufEnd := bufEnd) ptlz0) hfut
            simp only [] at hclosed
            have hspec := hclosed prod rfl
            rcases ptlzFuture_first hComplete bufEnd ptlz0 with hfirst | ⟨hlook, hnull⟩
            · have hh := hspec.2 _ hfirst
              rw [futureOfProd_zero] at hh
              simpa only [ptzBuffer] using hh
            · rw [hnull] at hspec
              have hh := hspec.1
              simp only [ite_true] at hh
              rw [futureOfProd_zero] at hh
              rw [← hlook] at hh
              simpa only [ptzBuffer] using hh
      simp only [buildPt]
      split
      · next hn =>
        have hwnil : word = [] := word_eq_nil_of_isNotNil_none ptl hn
        subst hwnil
        simp only [PtDotStackCompat]
        refine ⟨stk, ?_, ?_, ?_⟩
        · have hrhsnil : (G.prodRhsRev prod).reverse = [] := by
            have hh := heads_eq_nil_of_isNotNil_none ptl hn
            rw [hh]; rfl
          rw [hrhsnil] at hfut0
          exact hfut0
        · exact ptlStackCompat_self_of_isNotNil_none ptl hn stk
        · exact hstk
      · next hne _ =>
        apply buildPtRec_stackCompat hComplete bufEnd ptl hne (PtlZipper.nonTerminal ptz) stk
        · simp only [PtlZipperStackCompat]; exact hstk
        · simp only [ptlzProd, ptlzLookahead]
          exact hfut0
termination_by 2 * ptSize pt
decreasing_by
  simp only [ptSize]
  omega

/-- Descending through a nonempty list preserves stack compatibility, given the
    enclosing item has its full future ahead. -/
theorem buildPtRec_stackCompat (hComplete : Complete) (bufEnd : S) {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word)
    (hne : match heads with | [] => Empty | _ :: _ => Unit)
    (ptlz : PtlZipper init fullWord heads word) (stk : Stack)
    (hstk : PtlZipperStackCompat init fullWord bufEnd stk ptlz)
    (hfut : StateHasFuture (stateOfStack init stk) (ptlzProd ptlz)
      ((G.prodRhsRev (ptlzProd ptlz)).reverse) (ptlzLookahead (bufEnd := bufEnd) ptlz)) :
    PtDotStackCompat init fullWord bufEnd (buildPtRec ptl hne ptlz) stk := by
  match ptl, hne, ptlz with
  | .nil, hne, _ => exact hne.elim
  | .cons q t, _, ptlz =>
      rw [buildPtRec.eq_def]
      cases hq : isNotNil q with
      | none =>
        simp only [hq]
        have hheads := heads_eq_nil_of_isNotNil_none q hq
        subst hheads
        apply buildPt_stackCompat hComplete bufEnd t (PtZipper.cons q ptlz)
        simp only [PtZipperStackCompat]
        refine ⟨stk, ?_, ?_, ?_⟩
        · -- (prodRhsRev (ptlzProd ptlz)).reverse = headT :: ptlzFuture ptlz
          have hfp := ptlzFuture_prod ptlz
          rw [← hfp] at hfut
          simpa only [List.reverse_append, List.reverse_reverse, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.singleton_append] using hfut
        · exact ptlStackCompat_self_of_isNotNil_none q hq stk
        · exact hstk
      | some hq' =>
        simp only [hq]
        apply buildPtRec_stackCompat hComplete bufEnd q hq' (PtlZipper.cons t ptlz) stk
        · simp only [PtlZipperStackCompat]; exact hstk
        · simp only [ptlzProd, ptlzLookahead]
          exact hfut
termination_by 2 * ptlSize ptl + 1
decreasing_by
  · simp only [ptlSize]; have _ := ptSize_pos t; omega
  · simp only [ptlSize]; have hpos := ptSize_pos t; omega
end

/-- Continuing after a recognized list preserves stack compatibility. -/
theorem continuePtl_stackCompat (hComplete : Complete) (bufEnd : S) {heads : List Grammar.Sym} {word : List G.Token}
    (ptl : ParseTreeList heads word) (ptlz : PtlZipper init fullWord heads word)
    (stk stk0 : Stack)
    (hzc : PtlZipperStackCompat init fullWord bufEnd stk0 ptlz)
    (hc : PtlStackCompat stk0 ptl stk)
    (hfut : StateHasFuture (stateOfStack init stk) (ptlzProd ptlz)
      (ptlzFuture ptlz) (ptlzLookahead (bufEnd := bufEnd) ptlz)) :
    PtDotStackCompat init fullWord bufEnd (continuePtl ptl ptlz) stk := by
  cases ptlz with
  | nonTerminal ptz =>
    simp only [continuePtl, PtDotStackCompat]
    refine ⟨stk0, ?_, hc, ?_⟩
    · simpa only [ptlzProd, ptlzFuture, ptlzLookahead, ptzBuffer] using hfut
    · simpa only [PtlZipperStackCompat] using hzc
  | cons pt rest =>
    apply buildPt_stackCompat hComplete bufEnd pt (PtZipper.cons ptl rest)
    simp only [PtZipperStackCompat]
    refine ⟨stk0, ?_, hc, ?_⟩
    · simpa only [ptlzProd, ptlzFuture, ptlzLookahead] using hfut
    · simpa only [PtlZipperStackCompat] using hzc

end StackCompatBuild

/-! ### One parser step follows the traversal -/

section Operational

variable {init : A.InitState} {fullWord : List G.Token}

/-- A reduce step follows `nextReduce`: it accepts at the top zipper (with the
    represented semantics and the end buffer) or progresses to the stack
    compatible with the next dotted tree. -/
theorem reduceStep_next_ptd (hComplete : Complete) (bufEnd : S) (prod : G.Production) {word : List G.Token}
    (ptl : ParseTreeList (G.prodRhsRev prod) word)
    (ptz : PtZipper init fullWord (.NT (G.prodLhs prod)) word) (stk : Stack)
    (hcompat : PtDotStackCompat init fullWord bufEnd (.reduce prod ptl ptz) stk) :
    match nextReduce prod ptl ptz with
    | none =>
        reduceStep (S := S) init stk prod (ptzBuffer (bufEnd := bufEnd) ptz)
          = .Accept (ptdSem (.reduce prod ptl ptz)) bufEnd
    | some ptd' =>
        ∃ stk',
          reduceStep (S := S) init stk prod (ptzBuffer (bufEnd := bufEnd) ptz)
            = .Progress stk' (ptdBuffer (bufEnd := bufEnd) ptd') ∧
          PtDotStackCompat init fullWord bufEnd ptd' stk' := by
  obtain ⟨stk0, _hfut, hc, hzc⟩ := hcompat
  have hpop := pop_of_ptlStackCompat stk0 ptl stk (G.prodAction prod) hc
  unfold reduceStep
  rw [hpop]
  simp only []
  cases ptz with
  | top head_eq _ =>
    simp only [PtZipperStackCompat] at hzc
    subst hzc
    have hnt : G.prodLhs prod = A.startNt init := by
      have := head_eq; simp only [Symbol.NT.injEq] at this; exact this
    have hgoto := hComplete.2.2.2.2.2.2.1 init
    have hgotoNone : A.gotoTable (stateOfStack init ([] : Stack)) (G.prodLhs prod) = none := by
      rw [show stateOfStack init ([] : Stack) = State.Init init from rfl, hnt]
      cases hg : A.gotoTable (State.Init init) (A.startNt init) with
      | none => rfl
      | some tgt => rw [hg] at hgoto; exact hgoto.elim
    simp only [nextReduce, ptdSem, ptzSem, ptzBuffer, hgotoNone, dite_eq_left hnt]
  | cons prefixPtl ptlz =>
    obtain ⟨stk1, hfut1, hc1, hzc1⟩ := hzc
    -- Completeness supplies the nonterminal goto.
    have hgoto := hComplete.2.2.2.2.2.1 (stateOfStack init stk0) (ptlzProd ptlz)
      (.NT (G.prodLhs prod) :: ptlzFuture ptlz) (ptlzLookahead (bufEnd := bufEnd) ptlz) hfut1
    simp only [] at hgoto
    cases hg : A.gotoTable (stateOfStack init stk0) (G.prodLhs prod) with
    | none => rw [hg] at hgoto; exact hgoto.elim
    | some tgt =>
        obtain ⟨stateNew, e⟩ := tgt
        rw [hg] at hgoto
        rw [show nextReduce prod ptl (.cons prefixPtl ptlz)
              = some (continuePtl (.cons prefixPtl (.nonTerminal prod ptl)) ptlz) from rfl]
        refine ⟨⟨stateNew, castSem e (ptlSem ptl (G.prodAction prod))⟩ :: stk0, ?_, ?_⟩
        · simp only []
          congr 1
          simp only [ptzBuffer]
          exact continuePtl_buffer (bufEnd := bufEnd)
            (.cons prefixPtl (.nonTerminal prod ptl)) ptlz
        · -- stack compatibility of the next dotted tree
          apply continuePtl_stackCompat hComplete bufEnd
            (.cons prefixPtl (.nonTerminal prod ptl)) ptlz _ stk1 hzc1
          · -- PtlStackCompat stk1 (cons prefixPtl (nonTerminal prod ptl)) newStk
            refine ⟨hc1, ?_⟩
            refine ⟨e.symm, ?_⟩
            simp only [ptSem]
            exact castSem_symm_castSem e (ptlSem ptl (G.prodAction prod))
          · -- future for continuePtl
            simpa only [stateOfStack] using hgoto

/-- One interpreter step follows `nextPtd`: it accepts exactly when the traversal
    is finished, otherwise progresses to a stack compatible with the next dotted
    tree. -/
theorem step_next_ptd (hComplete : Complete) (bufEnd : S) (ptd : PtDot init fullWord) (stk : Stack)
    (hcompat : PtDotStackCompat init fullWord bufEnd ptd stk) :
    match nextPtd ptd with
    | none =>
        step (S := S) init stk (ptdBuffer (bufEnd := bufEnd) ptd)
          = .Accept (ptdSem ptd) bufEnd
    | some ptd' =>
        ∃ stk',
          step (S := S) init stk (ptdBuffer (bufEnd := bufEnd) ptd)
            = .Progress stk' (ptdBuffer (bufEnd := bufEnd) ptd') ∧
          PtDotStackCompat init fullWord bufEnd ptd' stk' := by
  cases ptd with
  | reduce prod ptl ptz =>
    obtain ⟨stk0, hfut, hc, hzc⟩ := hcompat
    -- Completeness supplies this reduction.
    have hend := hComplete.2.2.2.2.1 (stateOfStack init stk) prod []
      (G.tokenTerm (TokenStream.head (ptzBuffer (bufEnd := bufEnd) ptz))) hfut
    simp only [] at hend
    have hstep : step (S := S) init stk (ptdBuffer (bufEnd := bufEnd) (.reduce prod ptl ptz))
        = reduceStep (S := S) init stk prod (ptzBuffer (bufEnd := bufEnd) ptz) := by
      simp only [ptdBuffer, step]
      cases ha : A.actionTable (stateOfStack init stk) with
      | DefaultReduce prod' =>
        rw [ha] at hend
        simp only [] at hend
        subst prod'
        simp only []
      | Lookahead awt =>
        rw [ha] at hend
        simp only [] at hend
        cases hl : awt (G.tokenTerm (TokenStream.head (ptzBuffer (bufEnd := bufEnd) ptz))) with
        | Shift s' e => rw [hl] at hend; exact hend.elim
        | Reduce prod' =>
          rw [hl] at hend
          subst prod'
          simp only [hl]
        | Fail => rw [hl] at hend; exact hend.elim
    have hr := reduceStep_next_ptd hComplete bufEnd prod ptl ptz stk ⟨stk0, hfut, hc, hzc⟩
    simp only [nextPtd]
    rw [hstep]
    exact hr
  | shift tok ptl ptlz =>
    obtain ⟨stk0, hfut, hc, hzc⟩ := hcompat
    -- Completeness supplies this shift.
    have hshift := hComplete.2.2.2.1 (stateOfStack init stk) (ptlzProd ptlz)
      (.T (G.tokenTerm tok) :: ptlzFuture ptlz)
      (ptlzLookahead (bufEnd := bufEnd) ptlz) hfut
    simp only [] at hshift
    have hhead : TokenStream.head (ptdBuffer (bufEnd := bufEnd) (.shift tok ptl ptlz)) = tok := by
      simp only [ptdBuffer, AppStream.head_appList_cons]
    have htail : TokenStream.tail (ptdBuffer (bufEnd := bufEnd) (.shift tok ptl ptlz))
        = ptlzBuffer (bufEnd := bufEnd) ptlz := by
      simp only [ptdBuffer, AppStream.tail_appList_cons, AppStream.appList_nil]
    simp only [nextPtd]
    cases ha : A.actionTable (stateOfStack init stk) with
    | DefaultReduce prod' => rw [ha] at hshift; simp only [] at hshift
    | Lookahead awt =>
      rw [ha] at hshift
      simp only [] at hshift
      cases hl : awt (G.tokenTerm tok) with
      | Shift stateNew e =>
        rw [hl] at hshift
        simp only [] at hshift
        refine ⟨⟨stateNew, castSem e (G.tokenSem tok)⟩ :: stk, ?_, ?_⟩
        · simp only [step, ha]
          rw [hhead, hl, htail]
          simp only []
          congr 1
          exact continuePtl_buffer (bufEnd := bufEnd) (.cons ptl (.terminal tok)) ptlz
        · apply continuePtl_stackCompat hComplete bufEnd
            (.cons ptl (.terminal tok)) ptlz _ stk0 hzc
          · refine ⟨hc, ?_⟩
            refine ⟨e.symm, ?_⟩
            simp only [ptSem]
            exact castSem_symm_castSem e (G.tokenSem tok)
          · simpa only [stateOfStack] using hshift
      | Reduce prod' => rw [hl] at hshift; exact hshift.elim
      | Fail => rw [hl] at hshift; exact hshift.elim

/-- The bounded parser loop follows `nextPtdIter`. -/
theorem parseFix_next_ptd_iter (hComplete : Complete) (bufEnd : S) (ptd : PtDot init fullWord) (stk : Stack) (logN : Nat)
    (hcompat : PtDotStackCompat init fullWord bufEnd ptd stk) :
    match nextPtdIter ptd logN with
    | none =>
        parseFix (S := S) init stk (ptdBuffer (bufEnd := bufEnd) ptd) logN
          = .Accept (ptdSem ptd) bufEnd
    | some ptd' =>
        ∃ stk',
          parseFix (S := S) init stk (ptdBuffer (bufEnd := bufEnd) ptd) logN
            = .Progress stk' (ptdBuffer (bufEnd := bufEnd) ptd') ∧
          PtDotStackCompat init fullWord bufEnd ptd' stk' := by
  induction logN generalizing ptd stk with
  | zero =>
    simpa only [nextPtdIter, parseFix] using step_next_ptd hComplete bufEnd ptd stk hcompat
  | succ n ih =>
    have hsem := nextPtdIter_sem ptd n
    have ih1 := ih ptd stk hcompat
    cases hpd : nextPtdIter ptd n with
    | none =>
      rw [hpd] at ih1
      simp only [nextPtdIter, hpd, parseFix, ih1]
    | some ptd' =>
      rw [hpd] at ih1 hsem
      obtain ⟨stk', hstep', hcompat'⟩ := ih1
      have ih2 := ih ptd' stk' hcompat'
      simp only [nextPtdIter, hpd, parseFix, hstep']
      cases hpd2 : nextPtdIter ptd' n with
      | none =>
        rw [hpd2] at ih2
        rw [ih2, hsem]
      | some ptd'' =>
        rw [hpd2] at ih2
        exact ih2

end Operational

/-! ### Operational completeness and semantic unambiguity -/

/-- **Operational completeness of the interpreter.** For a `Complete` automaton and any parse tree of the input `word`, running `parse` on
    `word ++ bufEnd` either
    * returns exactly that tree's semantic value and residual `bufEnd`, within a
      fuel bound `ptSize tree ≤ 2^logN`, or
    * times out, in which case `2^logN` is strictly below the tree's size;
    it can never `Fail` or `Err` along the execution described by the tree. -/
theorem parseComplete (hComplete : Complete) (init : A.InitState)
    (logN : Nat) {word : List G.Token} (bufEnd : S)
    (tree : ParseTree (.NT (A.startNt init)) word) :
    match parse (S := S) init (AppStream.appList word bufEnd) logN with
    | .Parsed sem rest =>
        sem = ptSem tree ∧ rest = bufEnd ∧ ptSize tree ≤ 2 ^ logN
    | .Timeout => 2 ^ logN < ptSize tree
    | .Fail _ _ => False
    | .Err _ => False := by
  have hstk : PtDotStackCompat init word bufEnd (buildPt tree (.top rfl rfl)) [] :=
    buildPt_stackCompat hComplete bufEnd tree (.top rfl rfl) []
      (by simp only [PtZipperStackCompat])
  have hbuf : ptdBuffer (bufEnd := bufEnd) (buildPt tree (.top rfl rfl))
      = AppStream.appList word bufEnd := by
    have h := buildPt_buffer (bufEnd := bufEnd) tree (.top rfl rfl)
    simp only [ptzBuffer] at h
    exact h.symm
  have hsem : ptdSem (buildPt tree (.top rfl rfl)) = ptSem tree := by
    have h := buildPt_sem tree (.top (init := init) (fullWord := word) rfl rfl)
    simp only [ptzSem, castSem] at h
    exact h.symm
  have hcost : ptdCost (buildPt tree (.top (init := init) (fullWord := word) rfl rfl)) + 1
      = ptSize tree := by
    have h := buildPt_cost tree (.top (init := init) (fullWord := word) rfl rfl)
    simp only [ptzCost] at h
    omega
  have hpar := parseFix_next_ptd_iter hComplete bufEnd (buildPt tree (.top rfl rfl)) [] logN hstk
  have hic := nextPtdIter_cost (buildPt tree (.top (init := init) (fullWord := word) rfl rfl)) logN
  unfold parse
  rw [← hbuf]
  cases hpd : nextPtdIter (buildPt tree (.top rfl rfl)) logN with
  | none =>
    rw [hpd] at hpar hic
    rw [hpar, hsem]
    refine ⟨rfl, rfl, ?_⟩
    omega
  | some ptd' =>
    rw [hpd] at hpar hic
    obtain ⟨stk', hprog, _⟩ := hpar
    rw [hprog]
    have hpos : 0 < ptdCost ptd' + 1 := Nat.succ_pos _
    omega

/-- **Semantic unambiguity.** For a `Complete` automaton (and an inhabited token
    type), any two parse trees of the same word have the same semantic value.
    Port of `Main.unambiguity`; unlike Menhir's API, no `Safe` argument is needed
    because this interpreter is total and completeness rules out `.Err` on the
    tree-directed execution. -/
theorem unambiguity (hComplete : Complete) [Inhabited G.Token]
    (init : A.InitState) {word : List G.Token}
    (tree1 tree2 : ParseTree (.NT (A.startNt init)) word) :
    ptSem tree1 = ptSem tree2 := by
  let bufEnd : NatStream G.Token := fun _ => default
  have h1 := parseComplete (S := NatStream G.Token) hComplete init
    (ptSize tree1) (word := word) bufEnd tree1
  have h2 := parseComplete (S := NatStream G.Token) hComplete init
    (ptSize tree1) (word := word) bufEnd tree2
  have hlt : ptSize tree1 < 2 ^ ptSize tree1 := Nat.lt_two_pow_self
  cases hp : parse (S := NatStream G.Token) init (AppStream.appList word bufEnd)
      (ptSize tree1) with
  | Fail st tok => rw [hp] at h1; exact h1.elim
  | Err msg => rw [hp] at h1; exact h1.elim
  | Timeout => rw [hp] at h1; exact absurd h1 (by omega)
  | Parsed sem rest =>
    rw [hp] at h1 h2
    obtain ⟨hs1, _, _⟩ := h1
    obtain ⟨hs2, _, _⟩ := h2
    rw [← hs1, ← hs2]

end Runtime
