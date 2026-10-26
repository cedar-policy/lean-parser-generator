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
The table-driven LR(1) pushdown interpreter: the parser engine of §2.4 in
Validating LR(1) Parsers (Jourdan, Pottier, Leroy). It reads a token stream and
runs the automaton against a fixed `[Grammar]` and `[Automaton]`:

  * the **stack** is a list of cells, each pairing a non-initial state with the
    semantic value of that state's incoming symbol;
  * `step` consults the action table, then either **shifts** (push the lookahead
    token's value), **reduces** (`reduceStep`), **fails**, or **accepts**;
  * `reduceStep` pops the production's right-hand side off the stack, runs the
    semantic action, and follows the goto table;
  * `parseFix` iterates `step` with a base-2 logarithmic step count: the fuel
    parameter is the logarithm of the number of steps, doubled at each level, so
    a small number (≈50) suffices and iteration terminates without a separate
    termination proof.

The engine keeps explicit `StepResult.Err`/`ParseResult.Err` branches instead of
assuming the automaton is safe up front. Soundness is then provable for *every*
automaton, and a malformed certificate stays observable rather than being ruled
out by hypothesis. The safety validator and `Runtime/Safety.lean` prove those
branches unreachable whenever `safeValidator = true`
(`parse_err_free_of_safeValidator`).

Input is read only through the `[TokenStream]` interface, so the engine and its
correctness/safety theorems work for any stream, including the lazy one the lexer
produces.
-/
public import LeanParserGenerator.Runtime.Automaton
public import LeanParserGenerator.Runtime.Buffer


@[expose] public section

namespace Runtime

variable [G : Grammar] [A : Automaton]

/-- The automaton stack: a list of cells, each a non-initial state paired with a
    semantic value for that state's incoming symbol. -/
abbrev Stack := List ((s : A.NonInitState) × G.semT (A.lastSymb s))

/-- Cast a semantic value along an equality of symbols. The equality proof is
    erased at runtime. -/
def castSem {a b : Grammar.Sym} (h : a = b) (x : G.semT a) : G.semT b := h ▸ x

/-- The top state of a stack: the recorded state of the top cell, or the initial
    state when empty. -/
def stateOfStack (init : A.InitState) : Stack → AState
  | [] => .Init init
  | ⟨s, _⟩ :: _ => .Ninit s

/-- Pop the semantic values for `syms` (top of stack first) and feed them to the
    curried `action`, returning the shrunken stack and the action's result.

    Under the safety invariant the stack length and each symbol match are
    guaranteed; here we check the symbol at each cell and return `none` if the
    stack is too short or a symbol does not match. These are the bogus-automaton
    cases ruled out by `Runtime/Safety.lean` under `Safe`. -/
def pop {B : Type} :
    (syms : List Grammar.Sym) → Stack → arrowsRight B (syms.map G.semT) →
    Option (Stack × B)
  | [], stk, action => some (stk, action)
  | t :: _, stk, action =>
    match stk with
    | ⟨s, sem⟩ :: rest =>
        if h : A.lastSymb s = t then
          have action' : G.semT t → arrowsRight B _ := action
          pop _ rest (action' (castSem h sem))
        else none
    | [] => none

/-- The result of one `step`: reject the input (`Fail`), accept with a semantic
    value and the remaining stream (`Accept`), make progress (`Progress`), or hit
    a bogus-automaton case (`Err`). `Runtime/Safety.lean` proves `Err` unreachable
    from an invariant stack under `Safe`. The explicit error observation is used
    before applying the safety theorem. -/
inductive StepResult (S : Type) (init : A.InitState) where
  | Fail : AState → G.Token → StepResult S init
  | Accept : G.semT (.NT (A.startNt init)) → S → StepResult S init
  | Progress : Stack → S → StepResult S init
  | Err : String → StepResult S init

variable {S : Type} [TokenStream S G.Token]

/-- Perform a reduce action: pop the RHS, run the semantic action, then follow the
    goto table (or accept if the goto is the initial state's start symbol). -/
def reduceStep (init : A.InitState) (stk : Stack) (prod : G.Production) (s : S) :
    StepResult S init :=
  match pop (G.prodRhsRev prod) stk (G.prodAction prod) with
  | none => .Err "reduce: stack underflow or symbol mismatch"
  | some (stk', sem) =>
    match A.gotoTable (stateOfStack init stk') (G.prodLhs prod) with
    | some ⟨stateNew, e⟩ =>
        .Progress (⟨stateNew, castSem e sem⟩ :: stk') s
    | none =>
        match stk' with
        | [] =>
            if h : G.prodLhs prod = A.startNt init then
              .Accept (castSem (congrArg (fun nt => (Symbol.NT nt : Grammar.Sym)) h) sem) s
            else .Err "reduce: goto missing and lhs ≠ start symbol"
        | _ :: _ => .Err "reduce: goto missing on non-initial state"

/-- One step of the automaton: consult the action table and shift / reduce / fail
    / accept. -/
def step (init : A.InitState) (stk : Stack) (s : S) : StepResult S init :=
  match A.actionTable (stateOfStack init stk) with
  | .DefaultReduce prod => reduceStep init stk prod s
  | .Lookahead awt =>
    let tok := TokenStream.head s
    match awt (G.tokenTerm tok) with
    | .Shift stateNew e =>
        .Progress (⟨stateNew, castSem e (G.tokenSem tok)⟩ :: stk) (TokenStream.tail s)
    | .Reduce prod => reduceStep init stk prod s
    | .Fail => .Fail (stateOfStack init stk) tok

/-- Iterate `step`. `logNSteps` is the base-2 logarithm of the number of steps:
    each level runs the next-lower level twice, so `2^logNSteps` steps total.
    Structural recursion on `logNSteps`, so no termination proof is needed. -/
def parseFix (init : A.InitState) (stk : Stack) (s : S) :
    Nat → StepResult S init
  | 0 => step init stk s
  | n + 1 =>
    match parseFix init stk s n with
    | .Progress stk' s' => parseFix init stk' s' n
    | sr => sr

/-- The overall result of parsing, with an explicit `Err` for malformed
    automata; validated automata cannot produce it. `Parsed` carries the
    remaining stream. -/
inductive ParseResult (S : Type) (init : A.InitState) where
  | Fail : AState → G.Token → ParseResult S init
  | Timeout : ParseResult S init
  | Parsed : G.semT (.NT (A.startNt init)) → S → ParseResult S init
  | Err : String → ParseResult S init

/-- Parse from the initial state with an empty stack. Runs at most `2^logNSteps`
    steps; a still-in-`Progress` result becomes `Timeout`. -/
def parse (init : A.InitState) (s : S) (logNSteps : Nat) : ParseResult S init :=
  match parseFix init [] s logNSteps with
  | .Fail st tok => .Fail st tok
  | .Accept sem s' => .Parsed sem s'
  | .Progress _ _ => .Timeout
  | .Err msg => .Err msg

end Runtime
