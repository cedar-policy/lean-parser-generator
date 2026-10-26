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
The LR automaton and its validation certificate, following §2.4 of Validating
LR(1) Parsers (Jourdan, Pottier, Leroy). An automaton over a fixed `[Grammar]`
consists of:
  * alphabets of initial and non-initial states, with `lastSymb` giving the
    symbol recognized just before entering each non-initial state,
  * an action table and a (dependently-typed) goto table,
  * and the certificate **annotations** the safety/completeness validators check:
    `pastSymb`, `pastStates`, `items`, `nullableNt`, `firstNt`.

The dependent proofs carried by `Shift` and `gotoTable` (that the target state's
`lastSymb` matches the shifted/goto symbol) are what make the interpreter's stack
casts well-typed.
-/
public import LeanParserGenerator.Runtime.Grammar


@[expose] public section

namespace Runtime

variable [G : GrammarSig]

/-- A state of the automaton: either the distinguished initial state (per start
    symbol) or a non-initial state. -/
inductive State (InitState NonInitState : Type) where
  | Init : InitState → State InitState NonInitState
  | Ninit : NonInitState → State InitState NonInitState

/-! `State I N` is an alphabet whenever `I` and `N` are (it is essentially `I ⊕ N`).
The safety validator quantifies over all states (`Finite`), compares them
(`singletonStatePred` uses `DecidableEq`), so we derive the full `Alphabet`
stack here from the component alphabets. -/

instance instDecidableEqState {I N : Type} [DecidableEq I] [DecidableEq N] :
    DecidableEq (State I N)
  | .Init a,  .Init b  => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .Ninit a, .Ninit b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by simp [h])
  | .Init _,  .Ninit _ => isFalse (by simp)
  | .Ninit _, .Init _  => isFalse (by simp)

instance instFiniteState {I N : Type} [Finite I] [Finite N] : Finite (State I N) where
  all := (Finite.all (α := I)).map .Init ++ (Finite.all (α := N)).map .Ninit
  mem_all
    | .Init i => List.mem_append.mpr (.inl (List.mem_map.mpr ⟨i, Finite.mem_all i, rfl⟩))
    | .Ninit n => List.mem_append.mpr (.inr (List.mem_map.mpr ⟨n, Finite.mem_all n, rfl⟩))

/-- Comparison on states: initial states precede non-initial ones; within each
    kind, compare the component. -/
instance instComparableState {I N : Type} [Comparable I] [Comparable N] :
    Comparable (State I N) where
  cmp
    | .Init a,  .Init b  => Comparable.cmp a b
    | .Ninit a, .Ninit b => Comparable.cmp a b
    | .Init _,  .Ninit _ => .lt
    | .Ninit _, .Init _  => .gt
  cmp_swap x y := by
    cases x <;> cases y <;> simp only [Ordering.swap] <;>
      first | rfl | exact Comparable.cmp_swap _ _
  cmp_trans {x y z c} hxy hyz := by
    cases x <;> cases y <;> cases z <;>
      simp_all only [] <;>
      first
        | rfl
        | (exact Comparable.cmp_trans hxy hyz)
        | (cases c <;> simp_all)

instance instLawfulComparableState {I N : Type} [LawfulComparable I] [LawfulComparable N] :
    LawfulComparable (State I N) where
  cmp_eq {x y} h := by
    cases x <;> cases y <;>
      first
        | (exact congrArg _ (LawfulComparable.cmp_eq h))
        | (exact absurd h (by simp [Comparable.cmp]))

instance instAlphabetState {I N : Type} [Alphabet I] [Alphabet N] :
    Alphabet (State I N) where
  decEq := instDecidableEqState


/-- The action taken after peeking one lookahead terminal `term`. `Shift` carries
    a proof that the target state's incoming symbol is exactly `T term`, so the
    shifted token's semantic value can be cast into the new stack cell. -/
inductive LookaheadAction (NonInitState : Type)
    (lastSymb : NonInitState → GrammarSig.Sym) (term : G.Terminal) where
  | Shift (s : NonInitState) (h : Symbol.T term = lastSymb s) :
      LookaheadAction NonInitState lastSymb term
  | Reduce (p : G.Production) : LookaheadAction NonInitState lastSymb term
  | Fail : LookaheadAction NonInitState lastSymb term

/-- The action table entry for a state: either a default reduction taken without
    peeking (Menhir's "default action", paper Remark 1), or a per-terminal
    lookahead action. -/
inductive Action (NonInitState : Type) (lastSymb : NonInitState → GrammarSig.Sym) where
  | DefaultReduce (p : G.Production) : Action NonInitState lastSymb
  | Lookahead (f : (term : G.Terminal) → LookaheadAction NonInitState lastSymb term) :
      Action NonInitState lastSymb

/-- An LR(1) item annotation: a production, the dot position, and the set of
    lookahead terminals sharing this core. Consumed by the completeness validator. -/
structure Item where
  prod : G.Production
  dotPos : Nat
  lookaheads : List G.Terminal

/-- The automaton over the ambient grammar: tables plus validation certificate. -/
class Automaton where
  InitState : Type
  [alphInit : Alphabet InitState]
  NonInitState : Type
  [alphNinit : Alphabet NonInitState]
  /-- The symbol recognized just before entering a non-initial state. -/
  lastSymb : NonInitState → GrammarSig.Sym
  /-- The start non-terminal recognized by each initial state. -/
  startNt : InitState → G.NonTerminal
  /-- The action table. -/
  actionTable : State InitState NonInitState → Action NonInitState lastSymb
  /-- The goto table: partial, and dependently typed so the target state's
      incoming symbol is the goto non-terminal. -/
  gotoTable : State InitState NonInitState → (nt : G.NonTerminal) →
    Option { s : NonInitState // Symbol.NT nt = lastSymb s }
  -- ── Certificate annotations (produced by the untrusted generator) ──
  /-- Symbols known to sit just below the top of the stack in this state. -/
  pastSymb : NonInitState → List GrammarSig.Sym
  /-- Predicates the strictly-previous states satisfy in this state. -/
  pastStates : NonInitState → List (State InitState NonInitState → Bool)
  /-- The LR(1) item set of a state (for the completeness validator). -/
  items : State InitState NonInitState → List Item
  /-- Whether a non-terminal derives the empty string. -/
  nullableNt : G.NonTerminal → Bool
  /-- The FIRST set of a non-terminal. -/
  firstNt : G.NonTerminal → List G.Terminal

attribute [instance] Automaton.alphInit Automaton.alphNinit

variable [A : Automaton]

/-- Either the initial state or a non-initial state, for the ambient automaton.
    Used by the interpreter and the safety validator. -/
abbrev AState := State A.InitState A.NonInitState

end Runtime
