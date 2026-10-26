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
Menhir-style syntax-error reporting for the executable parser engine.

Menhir's declarative error scheme (see the Menhir manual, §11 "Error handling",
and F. Pottier, *Reachability and error diagnosis in LR(1) parsers*, 2016)
works like this: when the automaton enters an error, the state number is exposed
to the application, which maps it to a message. `menhir --list-errors`
enumerates every error state together with the set of terminals that *would*
have been accepted there (the `[ SEMI OR EOF ]` shown in a `.messages` file), and
`menhir --compile-errors` turns a hand-edited `.messages` file into a
`message : int -> string` function.

Our executable engine (`Runtime.Exec`) already surfaces the same primitive
information: `Result.reject state terminal` carries the LR state and the
offending lookahead terminal. This module builds the Menhir-style layer on top:

* `expectedAt` — the terminals accepted in a state (Menhir's lookahead set).
* `ParseError` — state, offending terminal, token position, and expected set.
* `diagnose` — run the parser and, on rejection, produce a `ParseError`.
* `ParseError.format` — a human-readable message, with an optional
  `state → message` override (the analog of a compiled `.messages` file).

Like `Runtime.Exec` itself, this layer is **unverified** in the sense that it is
not part of the trusted specification. It is, however, proved *consistent* with
the verified engine: `diagnose_run_agrees` shows the accept/reject/timeout
classification of `diagnose` is exactly that of the verified `Runtime.Exec.run`,
so an error is only ever reported when `run` genuinely rejects.
-/
public import LeanParserGenerator.Runtime.Exec
public import LeanParserGenerator.Runtime.Span


@[expose] public section

namespace Runtime.Exec

variable {V : Type}

/-- The terminals with a non-`error` action in `state`: what the parser would
    have accepted there. This is the analog of the `[ … ]` expected-token set
    that `menhir --list-errors` records for each error state. -/
def expectedAt (tbl : ExecTable V) (numTerminals state : Nat) : List Nat :=
  (List.range numTerminals).filter (fun t => tbl.action state t != Act.error)

/-- A structured syntax error, mirroring the data Menhir exposes at an error
    state via its incremental API. -/
structure ParseError where
  /-- The LR automaton state in which the error occurred. -/
  state : Nat
  /-- The terminal index of the unexpected lookahead token. -/
  lookahead : Nat
  /-- The number of input tokens consumed before the error (0-based index of the
      offending token; equal to the input length when the error is at EOF). -/
  position : Nat
  /-- The terminals that would have been accepted in `state`. -/
  expected : List Nat
  deriving Repr, Inhabited, DecidableEq

/-- The outcome of a diagnosed parse. -/
inductive Diagnostic (V : Type) where
  /-- Accepted with the start symbol's value. -/
  | ok : V → Diagnostic V
  /-- Rejected with a structured syntax error. -/
  | error : ParseError → Diagnostic V
  /-- Ran out of fuel. -/
  | timeout : Diagnostic V
  /-- Internal table inconsistency (unreachable for validated generator output). -/
  | internal : String → Diagnostic V
  deriving Repr, Inhabited

/-! ### Position-tracking runner

`Runtime.Exec.run` discards the remaining input when it stops, so it cannot say
*where* an error occurred. `parseFixD`/`runD` are a thin re-derivation that keep
the remaining input alongside the result. The single `step` primitive is reused
unchanged, so the classification cannot drift (see `diagnose_run_agrees`). -/

/-- Like `Runtime.Exec.parseFix`, but every terminal outcome also carries the
    remaining input at the point it was produced. Note that `step` only consumes
    input on a `shift`, and a `shift` always yields a continuation, so for every
    terminal (`.inl`) outcome the relevant remaining input is exactly `step`'s
    `input` argument. -/
def parseFixD (tbl : ExecTable V) (stk : Stack V) (input : List (Nat × V)) :
    Nat → (Result V × List (Nat × V)) ⊕ (Stack V × List (Nat × V))
  | 0 =>
    match step tbl stk input with
    | .inl r => .inl (r, input)
    | .inr x => .inr x
  | logN + 1 =>
    match parseFixD tbl stk input logN with
    | .inl r => .inl r
    | .inr (stk', input') => parseFixD tbl stk' input' logN

/-- Run the parser, keeping the remaining input at the point it stopped. -/
def runD (tbl : ExecTable V) (input : List (Nat × V)) (logNSteps : Nat := 20) :
    Result V × List (Nat × V) :=
  match parseFixD tbl [] input logNSteps with
  | .inl (r, rem) => (r, rem)
  | .inr (_, rem) => (.timeout, rem)

/-- Diagnose a parse: on rejection, compute the offending position and the set of
    expected terminals. `numTerminals` is the width of the action table (the
    augmented terminal count). -/
def diagnose (tbl : ExecTable V) (numTerminals : Nat) (input : List (Nat × V))
    (logNSteps : Nat := 20) : Diagnostic V :=
  let origLen := input.length
  match runD tbl input logNSteps with
  | (.ok v, _) => .ok v
  | (.reject s t, rem) =>
    .error { state := s, lookahead := t, position := origLen - rem.length,
             expected := expectedAt tbl numTerminals s }
  | (.timeout, _) => .timeout
  | (.err e, _) => .internal e

/-! ### Span-aware diagnosis

The generated executable engine runs at `V = Span × V'` (a stack value carries its
source span). `spanOf` projects that span out of an engine value, so a rejection
can report *where* in the source the offending token is, not just its token index.
For a bare engine (no spans) pass `fun _ => none`. -/

/-- The offending token's source span, if the error is at a real token (not EOF).
    `rem` is the remaining input at the rejection point; its head is the offending
    token, whose engine value carries the span via `spanOf`. -/
def offendingSpan (spanOf : V → Option Span) (rem : List (Nat × V)) : Option Span :=
  match rem with
  | (_, v) :: _ => spanOf v
  | [] => none

/-- Like `diagnose`, but also recovers the offending token's `Span` (via `spanOf`)
    so the error can be rendered as `line:col` against the source. Classification
    is identical to `diagnose`/`run`. -/
def diagnoseSpanned (tbl : ExecTable V) (numTerminals : Nat) (spanOf : V → Option Span)
    (input : List (Nat × V)) (logNSteps : Nat := 20) :
    Diagnostic V × Option Span :=
  let origLen := input.length
  match runD tbl input logNSteps with
  | (.ok v, _) => (.ok v, none)
  | (.reject s t, rem) =>
    (.error { state := s, lookahead := t, position := origLen - rem.length,
              expected := expectedAt tbl numTerminals s },
     offendingSpan spanOf rem)
  | (.timeout, _) => (.timeout, none)
  | (.err e, _) => (.internal e, none)

/-- Render a parse error as `line:col: unexpected TOKEN; expected …`, computing
    line:col from the offending token's span against the original `source`. When
    the error is at EOF (no span), falls back to the token index. Unverified. -/
def ParseError.formatWithSource (e : ParseError) (span : Option Span) (source : String)
    (terminalName : Nat → String)
    (stateMessage : Nat → Option String := fun _ => none) : String :=
  match stateMessage e.state with
  | some msg => msg
  | none =>
    let expected := e.expected.map terminalName
    let expectedStr :=
      if expected.isEmpty then ""
      else "; expected one of: " ++ ", ".intercalate expected
    let loc :=
      match span with
      | some sp => let (line, col) := sp.lineCol source; s!"{line}:{col}"
      | none => s!"token {e.position}"
    s!"{loc}: unexpected {terminalName e.lookahead}{expectedStr} (in parser state {e.state})"

/-! ### Rendering -/

/-- A human-readable message for a `ParseError`. `terminalName` names a terminal
    index; `stateMessage` optionally supplies a custom, per-state message (the
    analog of a Menhir `.messages` entry / compiled `message : int → string`),
    which takes precedence over the auto-generated one. -/
def ParseError.format (e : ParseError) (terminalName : Nat → String)
    (stateMessage : Nat → Option String := fun _ => none) : String :=
  match stateMessage e.state with
  | some msg => msg
  | none =>
    let expected := e.expected.map terminalName
    let expectedStr :=
      if expected.isEmpty then ""
      else "; expected one of: " ++ ", ".intercalate expected
    s!"syntax error at token {e.position}: unexpected {terminalName e.lookahead}{expectedStr} (in parser state {e.state})"

/-! ### Consistency with the verified engine

The diagnostic runner reuses `step`, so its result agrees with `Runtime.Exec.run`
by construction. We make that precise: erasing the extra remaining-input payload
turns `parseFixD` back into `parseFix`, hence `runD` agrees with `run`. This
guarantees a syntax error is reported exactly when the verified parser rejects. -/

theorem parseFixD_toResult (tbl : ExecTable V) :
    ∀ (stk : Stack V) (input : List (Nat × V)) (logN : Nat),
      Sum.map Prod.fst id (parseFixD tbl stk input logN)
        = parseFix tbl stk input logN := by
  intro stk input logN
  induction logN generalizing stk input with
  | zero =>
    simp only [parseFixD, parseFix]
    cases step tbl stk input <;> rfl
  | succ n ih =>
    have hEq := ih stk input
    cases hD : parseFixD tbl stk input n with
    | inl r =>
      have hF : parseFix tbl stk input n = .inl r.1 := by
        rw [← hEq, hD]; rfl
      simp only [parseFixD, parseFix, hD, hF]
      rfl
    | inr p =>
      have hF : parseFix tbl stk input n = .inr p := by
        rw [← hEq, hD]; rfl
      simp only [parseFixD, parseFix, hD, hF]
      exact ih p.1 p.2

/-- The result component of `runD` is exactly `Runtime.Exec.run`. -/
theorem runD_fst_eq_run (tbl : ExecTable V) (input : List (Nat × V)) (logN : Nat) :
    (runD tbl input logN).1 = run tbl input logN := by
  have h := parseFixD_toResult tbl [] input logN
  unfold runD run
  cases hD : parseFixD tbl [] input logN with
  | inl r =>
    have : parseFix tbl [] input logN = .inl r.1 := by rw [← h, hD]; rfl
    rw [this]
  | inr p =>
    have : parseFix tbl [] input logN = .inr p := by rw [← h, hD]; rfl
    rw [this]

/-- `diagnose` classifies accept/reject/timeout exactly as the verified `run`:
    it yields `.ok`/`.error`/`.timeout`/`.internal` iff `run` yields
    `.ok`/`.reject`/`.timeout`/`.err`. In particular a `ParseError` is produced
    precisely when `run` rejects. -/
theorem diagnose_run_agrees (tbl : ExecTable V) (numTerminals : Nat)
    (input : List (Nat × V)) (logN : Nat) :
    (match diagnose tbl numTerminals input logN with
      | .ok _ => 0 | .error _ => 1 | .timeout => 2 | .internal _ => 3)
      = (match run tbl input logN with
          | .ok _ => 0 | .reject _ _ => 1 | .timeout => 2 | .err _ => 3) := by
  have h := runD_fst_eq_run tbl input logN
  unfold diagnose
  cases hD : runD tbl input logN with
  | mk r rem =>
    have hr : r = run tbl input logN := by
      have hh := runD_fst_eq_run tbl input logN
      rw [hD] at hh
      exact hh
    rw [← hr]
    cases r <;> rfl

end Runtime.Exec
