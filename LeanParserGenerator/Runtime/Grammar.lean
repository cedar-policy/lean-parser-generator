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
Grammars with dependently-typed semantic values, following §2 of Validating
LR(1) Parsers (Jourdan, Pottier, Leroy). A grammar fixes:
  * alphabets of terminals and non-terminals,
  * for each symbol, the `Type` of its semantic values,
  * an alphabet of productions with left-hand side, (reversed) right-hand side,
    and a curried semantic action,
  * a token type (a terminal paired with a semantic value of its type).

From these we build the `Symbol` type, parse trees, and their semantics
(`ptSem`) and size (`ptSize`).

A grammar is a type class `Grammar`. The interpreter, validators, and theorems
are all parameterized by `[Grammar]`.
-/
public import LeanParserGenerator.Runtime.Alphabet


@[expose] public section

namespace Runtime

/-- A grammar symbol: a terminal or a non-terminal. -/
inductive Symbol (Terminal NonTerminal : Type) where
  | T : Terminal → Symbol Terminal NonTerminal
  | NT : NonTerminal → Symbol Terminal NonTerminal
  deriving DecidableEq

/-- The curried, right-to-left action type: `arrowsRight A [t₁, …, tₙ]` unfolds to
    `t₁ → … → tₙ → A`. Because production right-hand sides are stored reversed,
    this yields actions that consume semantic values in the natural pop order. -/
def arrowsRight (A : Type) : List Type → Type
  | [] => A
  | t :: ts => t → arrowsRight A ts

/-- The **computable signature** of a grammar: the finite index alphabets
    (terminals, non-terminals, productions) and the productions' shape
    (`prodLhs`, `prodRhsRev`) — everything *except* the `Type`-valued semantic
    layer. The safety/completeness validators depend only on this part, so that
    they stay computable (and `native_decide`-able) even though a full `Grammar`
    is `noncomputable` (its `semT` returns `Type`, which Lean's compiler erases).

    The safety validator is therefore stated over the automaton/grammar
    *signature* alone, independent of the semantic-value layer. -/
class GrammarSig where
  Terminal : Type
  [alphT : Alphabet Terminal]
  NonTerminal : Type
  [alphNT : Alphabet NonTerminal]
  Production : Type
  [alphP : Alphabet Production]
  /-- Left-hand side non-terminal of a production. -/
  prodLhs : Production → NonTerminal
  /-- Right-hand side of a production, stored **reversed** (head = top of stack). -/
  prodRhsRev : Production → List (Symbol Terminal NonTerminal)

attribute [instance] GrammarSig.alphT GrammarSig.alphNT GrammarSig.alphP

/-- Abbreviation for the symbol type of the ambient grammar signature. Defined at
    the signature level so the interpreter, validators and theorems all share one
    `Sym`. -/
abbrev GrammarSig.Sym [G : GrammarSig] := Symbol G.Terminal G.NonTerminal

/-- The full data of a grammar: its computable signature (`GrammarSig`) together
    with the semantic layer — a `Type` for each symbol's semantic values, a
    curried action per production, and a token type. The interpreter and the
    soundness/completeness theorems are parameterized by `[Grammar]`; the
    validators only need `[GrammarSig]`. -/
class Grammar extends GrammarSig where
  /-- The semantic-value type of each symbol (`symbol_semantic_type`). -/
  semT : Symbol Terminal NonTerminal → Type
  /-- The semantic action, curried over the reversed right-hand side. -/
  prodAction : (p : Production) →
    arrowsRight (semT (.NT (prodLhs p))) ((prodRhsRev p).map semT)
  /-- The token type and its projections. A token carries a terminal and a
      semantic value of that terminal's type. -/
  Token : Type
  tokenTerm : Token → Terminal
  tokenSem : (tok : Token) → semT (.T (tokenTerm tok))

namespace Grammar

variable [G : Grammar]

/-- Abbreviation for the symbol type of the ambient grammar (via its signature). -/
abbrev Sym := GrammarSig.Sym (G := G.toGrammarSig)

mutual
/-- Parse trees, indexed by the head symbol and the word (list of tokens) they
    recognize. Semantic values live at the leaves. -/
inductive ParseTree : Sym → List G.Token → Type
  /-- A terminal leaf: the single-token word `[tok]` for symbol `T (term tok)`. -/
  | terminal (tok : G.Token) : ParseTree (.T (G.tokenTerm tok)) [tok]
  /-- A non-terminal node from a production and a parse-tree-list for its RHS. -/
  | nonTerminal (p : G.Production) {word : List G.Token} :
      ParseTreeList (G.prodRhsRev p) word → ParseTree (.NT (G.prodLhs p)) word

/-- Parse-tree list for a (reversed) list of head symbols. -/
inductive ParseTreeList : List Sym → List G.Token → Type
  | nil : ParseTreeList [] []
  | cons {headSymsQ : List Sym} {wordQ : List G.Token}
         (q : ParseTreeList headSymsQ wordQ)
         {headSymT : Sym} {wordT : List G.Token}
         (t : ParseTree headSymT wordT) :
      ParseTreeList (headSymT :: headSymsQ) (wordQ ++ wordT)
end

mutual
/-- The semantic value produced by a parse tree. -/
def ptSem : {head : Sym} → {word : List G.Token} → ParseTree head word → G.semT head
  | _, _, .terminal tok => G.tokenSem tok
  | _, _, .nonTerminal p ptl => ptlSem ptl (G.prodAction p)

/-- Fold a parse-tree-list through a curried action. -/
def ptlSem : {A : Type} → {heads : List Sym} → {word : List G.Token} →
    ParseTreeList heads word → arrowsRight A (heads.map G.semT) → A
  | _, _, _, .nil, act => act
  | A, _ :: _, _, .cons (headSymT := hT) q t, act =>
      have act' : G.semT hT → arrowsRight A _ := act
      ptlSem q (act' (ptSem t))
end

@[simp] theorem ptSem_terminal (tok : G.Token) :
    ptSem (ParseTree.terminal tok) = G.tokenSem tok := by
  rw [ptSem.eq_def]

@[simp] theorem ptSem_nonTerminal (p : G.Production) {word : List G.Token}
    (ptl : ParseTreeList (G.prodRhsRev p) word) :
    ptSem (ParseTree.nonTerminal p ptl) = ptlSem ptl (G.prodAction p) := by
  rw [ptSem.eq_def]

@[simp] theorem ptlSem_nil {A : Type}
    (action : arrowsRight A ([].map G.semT)) :
    ptlSem (G := G) ParseTreeList.nil action = action := by
  rw [ptlSem.eq_def]

@[simp] theorem ptlSem_cons {A : Type} {headSymsQ : List G.Sym}
    {wordQ : List G.Token} (q : ParseTreeList headSymsQ wordQ)
    {headSymT : G.Sym} {wordT : List G.Token} (tree : ParseTree headSymT wordT)
    (action : arrowsRight A ((headSymT :: headSymsQ).map G.semT)) :
    ptlSem (ParseTreeList.cons q tree) action =
      ptlSem q (action (ptSem tree)) := by
  rw [ptlSem.eq_def]

mutual
/-- The number of nodes in a parse tree; used to bound parsing fuel in the
    completeness theorem. -/
def ptSize : {head : Sym} → {word : List G.Token} → ParseTree head word → Nat
  | _, _, .terminal _ => 1
  | _, _, .nonTerminal _ ptl => ptlSize ptl + 1

def ptlSize : {heads : List Sym} → {word : List G.Token} →
    ParseTreeList heads word → Nat
  | _, _, .nil => 0
  | _, _, .cons q t => ptSize t + ptlSize q
end

end Grammar

end Runtime
