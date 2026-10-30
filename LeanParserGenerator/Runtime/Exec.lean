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
The non-dependent LR engine used by the parser backend.

This is the *unverified* runtime that the executable code-generation backend
targets (see docs/DESIGN.md §9.6). It is deliberately **not** the dependently
typed `Runtime.Interpreter`: there are no per-symbol types, no goto/shift proofs,
and no `Alphabet`/`Grammar`/`Automaton` type classes. The LR stack is a plain
`List (Nat × V)` and semantic actions are ordinary `List V → V` functions, where
`V` is a single value type the generator synthesizes per grammar (a sum with one
constructor per distinct semantic type; no `unsafeCast`).

Everything here is total and closed-form. `Runtime.Refinement` proves generated
tables simulate `Runtime.Interpreter`; bugs in construction or emission therefore
fail the generated refinement obligations.

The generator emits an `ExecTable V` value plus a token-decoding function. `Exec.run`
is the specification; generated parsers run `Runtime.Exec.runFast`
(`Runtime/ExecFast.lean`), which is proved equal to it.
-/


@[expose] public section

namespace Runtime.Exec

/-- A per-state, per-terminal action, with indices already resolved to `Nat`. -/
inductive Act where
  /-- Shift the lookahead token and go to the given state. -/
  | shift : Nat → Act
  /-- Reduce by the given production. -/
  | reduce : Nat → Act
  /-- Accept (only valid at end of input on the augmented start production). -/
  | accept : Act
  /-- No entry: reject. -/
  | error : Act
  deriving Repr, Inhabited, DecidableEq

/-- All the plain-data tables the executable engine needs, over a synthesized
    value type `V`. Produced by the code generator. -/
structure ExecTable (V : Type) where
  /-- Number of automaton states. -/
  numStates : Nat
  /-- The initial state index. -/
  startState : Nat
  /-- The EOF terminal/value used after a finite input list is exhausted. -/
  eof : Nat × V
  /-- `action s t` : the action in state `s` on lookahead terminal `t`. -/
  action : Nat → Nat → Act
  /-- `goto s n` : the state to enter after reducing to nonterminal `n` in state
      `s` (or `none` if there is no such transition). -/
  goto : Nat → Nat → Option Nat
  /-- `defaultReduce s` : if `some p`, state `s` reduces by production `p` without
      consulting the lookahead (Menhir's default action). -/
  defaultReduce : Nat → Option Nat
  /-- `prodLhs p` : the nonterminal index on the left of production `p`. -/
  prodLhs : Nat → Nat
  /-- `prodRhsLen p` : the number of symbols on the right of production `p` (how
      many stack cells a reduce by `p` pops). -/
  prodRhsLen : Nat → Nat
  /-- `sem p args` : the semantic action of production `p`, applied to the popped
      values in left-to-right right-hand-side order. -/
  sem : Nat → List V → V

/-- The stack: a list of `(stateIndex, semanticValue)` cells, top of stack first. -/
abbrev Stack (V : Type) := List (Nat × V)

/-- The outcome of a parse. -/
inductive Result (V : Type) where
  /-- Accepted: the start symbol's semantic value. -/
  | ok : V → Result V
  /-- Rejected at the given state on the given terminal index. -/
  | reject : Nat → Nat → Result V
  /-- Ran out of fuel. -/
  | timeout : Result V
  /-- Internal inconsistency in the tables (e.g. goto missing). Unreachable for
      well-formed generator output. -/
  | err : String → Result V
  deriving Repr, Inhabited

variable {V : Type}

/-- The state on top of the stack, or the start state if empty. -/
def topState (tbl : ExecTable V) : Stack V → Nat
  | [] => tbl.startState
  | (s, _) :: _ => s


/-- A flat parser result is free of internal table inconsistencies. Rejection and
fuel exhaustion are ordinary outcomes; only `.err` is forbidden. -/
def ResultErrFree : Result V → Prop
  | .err _ => False
  | .ok _ | .reject _ _ | .timeout => True

/-- Pop `n` cells off the stack, returning their values in **left-to-right**
    right-hand-side order (the stack has the last RHS symbol on top) and the
    remaining stack. `none` on underflow. -/
def popN (n : Nat) (stk : Stack V) : Option (List V × Stack V) :=
  go n stk []
where
  /-- Accumulate popped values; since we pop top-first, prepending each value
      builds the list back into left-to-right order. -/
  go : Nat → Stack V → List V → Option (List V × Stack V)
  | 0, stk, acc => some (acc, stk)
  | n + 1, (_, v) :: rest, acc => go n rest (v :: acc)
  | _ + 1, [], _ => none

/-- One reduce by production `p`: pop its RHS, run the action, follow `goto`. On
    the augmented start production the `goto` is absent and we accept. -/
def reduce (tbl : ExecTable V) (p : Nat) (stk : Stack V) : Result V ⊕ Stack V :=
  match popN (tbl.prodRhsLen p) stk with
  | none => .inl (.err s!"reduce: stack underflow on production {p}")
  | some (args, stk') =>
    let v := tbl.sem p args
    match tbl.goto (topState tbl stk') (tbl.prodLhs p) with
    | some s' => .inr ((s', v) :: stk')
    | none =>
      -- No goto: this is the accept on the augmented start production.
      .inl (.ok v)

/-- One step: consult the action table (or the default reduction) and shift,
    reduce, accept, or reject. `input` is the remaining terminal indices paired
    with their values; the head is the current lookahead. -/
def step (tbl : ExecTable V) (stk : Stack V) (input : List (Nat × V)) :
    Result V ⊕ (Stack V × List (Nat × V)) :=
  let s := topState tbl stk
  match tbl.defaultReduce s with
  | some p =>
    match reduce tbl p stk with
    | .inl r => .inl r
    | .inr stk' => .inr (stk', input)
  | none =>
    let (t, v) := input.getD 0 tbl.eof
    match tbl.action s t with
    | .shift s' => .inr (((s', v) :: stk), input.drop 1)
    | .reduce p =>
      match reduce tbl p stk with
      | .inl r => .inl r
      | .inr stk' => .inr (stk', input)
    | .accept =>
      match stk with
      | (_, v) :: _ => .inl (.ok v)
      | [] => .inl (.err "accept on empty stack")
    | .error => .inl (.reject s t)

/-- Iterate `step` with logarithmic fuel. Level `0` performs one step; level
    `n + 1` runs level `n` twice when the first run makes progress, for a total
    budget of `2^(n + 1)` steps. This matches `Runtime.parseFix`. -/
def parseFix (tbl : ExecTable V) (stk : Stack V) (input : List (Nat × V)) :
    Nat → Result V ⊕ (Stack V × List (Nat × V))
  | 0 => step tbl stk input
  | logN + 1 =>
    match parseFix tbl stk input logN with
    | .inl result => .inl result
    | .inr (stk', input') => parseFix tbl stk' input' logN

/-- Run the parser defined by `tbl` on the finite `input`. It always terminates,
    in at most `2^logNSteps` steps. A `.timeout` result means it ran out of fuel;
    `.reject` means the input is not in the language. It never returns `.err` when
    the paired dependent instance passes safety validation. -/
def run (tbl : ExecTable V) (input : List (Nat × V)) (logNSteps : Nat := 20) :
    Result V :=
  match parseFix tbl [] input logNSteps with
  | .inl result => result
  | .inr _ => .timeout

/-! ### Inline (closure-free) engine

The generated `ExecTable` fields are thin closures over flat `Array` literals
(`action := fun st t => actionData.getD (st * numT + t) .error`, and similarly for
the other five fields). Each `step` therefore performs several *indirect closure
calls*. Profiling the generated parser (docs/DESIGN.md §13) attributes a measurable share of parse-only
time to that indirection.

`FlatTable` holds the raw arrays and the two row widths directly, and
`runInline`/`stepInline`/`parseFixInline` read them inline — no closure calls.
`runInline_eq_run` proves it equals
`run (FlatTable.toExecTable …)`, so the refinement theorem (`run_refines`,
`parse_eq_dependent`) transfers unchanged: the closure `ExecTable` remains the
specification. The generated backend runs `runFast` (`Runtime/ExecFast.lean`), which
is proved equal to `runInline`. -/

/-- The raw flat parser tables, without the `ExecTable` closure wrappers.
    `actWidth` / `gotoWidth` are the row widths (`numTerminals` / `numNonterminals`). -/
structure FlatTable (V : Type) where
  numStates : Nat
  startState : Nat
  eof : Nat × V
  actWidth : Nat
  gotoWidth : Nat
  actionData : Array Act
  gotoData : Array (Option Nat)
  defRedData : Array (Option Nat)
  lhsData : Array Nat
  lenData : Array Nat
  sem : Nat → List V → V

/-- The `ExecTable` whose closure fields are exactly the ones the emitter writes
    over a `FlatTable`'s arrays. This is definitionally the emitted `table`. -/
def FlatTable.toExecTable (f : FlatTable V) : ExecTable V where
  numStates := f.numStates
  startState := f.startState
  eof := f.eof
  action := fun st t => f.actionData.getD (st * f.actWidth + t) .error
  goto := fun st n => f.gotoData.getD (st * f.gotoWidth + n) none
  defaultReduce := fun st => f.defRedData.getD st none
  prodLhs := fun p => f.lhsData.getD p 0
  prodRhsLen := fun p => f.lenData.getD p 0
  sem := f.sem

/-- Top state for a `FlatTable` — reads `startState` directly, never building the
    closure `ExecTable`. -/
def FlatTable.topState (f : FlatTable V) : Stack V → Nat
  | [] => f.startState
  | (s, _) :: _ => s

/-- One reduce over a `FlatTable`, reading arrays inline (no closures). -/
def reduceInline (f : FlatTable V) (p : Nat) (stk : Stack V) : Result V ⊕ Stack V :=
  match popN (f.lenData.getD p 0) stk with
  | none => .inl (.err s!"reduce: stack underflow on production {p}")
  | some (args, stk') =>
    let v := f.sem p args
    match f.gotoData.getD ((f.topState stk') * f.gotoWidth + f.lhsData.getD p 0) none with
    | some s' => .inr ((s', v) :: stk')
    | none => .inl (.ok v)

/-- One step over a `FlatTable`, reading arrays inline (no closures). -/
def stepInline (f : FlatTable V) (stk : Stack V) (input : List (Nat × V)) :
    Result V ⊕ (Stack V × List (Nat × V)) :=
  let s := f.topState stk
  match f.defRedData.getD s none with
  | some p =>
    match reduceInline f p stk with
    | .inl r => .inl r
    | .inr stk' => .inr (stk', input)
  | none =>
    let (t, v) := input.getD 0 f.eof
    match f.actionData.getD (s * f.actWidth + t) .error with
    | .shift s' => .inr (((s', v) :: stk), input.drop 1)
    | .reduce p =>
      match reduceInline f p stk with
      | .inl r => .inl r
      | .inr stk' => .inr (stk', input)
    | .accept =>
      match stk with
      | (_, v) :: _ => .inl (.ok v)
      | [] => .inl (.err "accept on empty stack")
    | .error => .inl (.reject s t)

/-- Logarithmic-fuel iteration of `stepInline`; mirrors `parseFix`. -/
def parseFixInline (f : FlatTable V) (stk : Stack V) (input : List (Nat × V)) :
    Nat → Result V ⊕ (Stack V × List (Nat × V))
  | 0 => stepInline f stk input
  | logN + 1 =>
    match parseFixInline f stk input logN with
    | .inl result => .inl result
    | .inr (stk', input') => parseFixInline f stk' input' logN

/-- Run the inline (closure-free) engine. `runFast_eq_run` goes through it. -/
def runInline (f : FlatTable V) (input : List (Nat × V)) (logNSteps : Nat := 20) :
    Result V :=
  match parseFixInline f [] input logNSteps with
  | .inl result => result
  | .inr _ => .timeout

/-- `FlatTable.topState` agrees with the closure `topState` on `toExecTable`
    (both read `startState` when empty, the top cell's state otherwise). -/
theorem flatTopState_eq (f : FlatTable V) (stk : Stack V) :
    f.topState stk = topState f.toExecTable stk := by
  cases stk with
  | nil => rfl
  | cons hd tl => rfl

/-- The inline reduce equals the closure `reduce` on the corresponding `ExecTable`. -/
theorem reduceInline_eq (f : FlatTable V) (p : Nat) (stk : Stack V) :
    reduceInline f p stk = reduce f.toExecTable p stk := by
  unfold reduceInline reduce
  simp only [FlatTable.toExecTable]
  cases popN (f.lenData.getD p 0) stk with
  | none => rfl
  | some r =>
    obtain ⟨args, stk'⟩ := r
    cases stk' with
    | nil => rfl
    | cons hd tl => rfl

/-- The inline step equals the closure `step` on the corresponding `ExecTable`. -/
theorem stepInline_eq (f : FlatTable V) (stk : Stack V) (input : List (Nat × V)) :
    stepInline f stk input = step f.toExecTable stk input := by
  unfold stepInline step
  rw [show f.topState stk = topState f.toExecTable stk from
        (by cases stk <;> rfl)]
  -- now both sides consult the same state `s`; the `defaultReduce`/`action`
  -- projections on `toExecTable` are definitionally the array reads, and the
  -- reduce branches agree by `reduceInline_eq`.
  simp only [FlatTable.toExecTable, reduceInline_eq]

/-- The inline log-fuel iteration equals `parseFix` on the corresponding `ExecTable`. -/
theorem parseFixInline_eq (f : FlatTable V) (stk : Stack V) (input : List (Nat × V))
    (logN : Nat) :
    parseFixInline f stk input logN = parseFix f.toExecTable stk input logN := by
  induction logN generalizing stk input with
  | zero => exact stepInline_eq f stk input
  | succ n ih =>
    simp only [parseFixInline, parseFix, ih]

/-- **The inline engine equals the closure engine.** So the generated backend's
    `runInline` returns exactly the specification `run`'s result, and every
    refinement/soundness theorem stated about `run (…toExecTable)` transfers. -/
theorem runInline_eq_run (f : FlatTable V) (input : List (Nat × V)) (logNSteps : Nat) :
    runInline f input logNSteps = run f.toExecTable input logNSteps := by
  simp only [runInline, run, parseFixInline_eq]

/-- The `popN`+`sem` composite: pop the RHS of production `p` and run `sem` on the
    operand list. `reduceInline` is this followed by the goto. The generated fused
    reduces are proved against it (`Runtime/ExecFast.lean`). -/
def popNsem (f : FlatTable V) (p : Nat) (stk : Stack V) : Option (V × Stack V) :=
  (popN (f.lenData.getD p 0) stk).map (fun r => (f.sem p r.1, r.2))

end Runtime.Exec
