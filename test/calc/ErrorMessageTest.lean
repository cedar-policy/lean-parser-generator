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
`test/calc/ErrorMessageTest.lean` — Menhir-style syntax-error diagnostics emitted
into the generated parser (`terminalName`/`diagnose`/`diagnoseSpanned`/
`errorMessage`), including span-based `line:col` rendering. The engine runs at
`VP := Span × V`; tokens carry spans, so `errorMessage` can locate the error in
the source.
-/
public import calc.CalcParser
meta import calc.CalcParser

public section

open Calc CalcParser Runtime

/-- Does `s` contain `needle` as a substring? -/
private def containsStr (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- Attach dummy spans (position tests use real spans below). -/
private def dummy (toks : List Tok) : List (Positioned Tok) :=
  toks.map Positioned.dummy

/-- Attach an explicit byte span to a token. -/
private def tokAt (t : Tok) (a b : Nat) : Positioned Tok := ⟨t, ⟨⟨a⟩, ⟨b⟩⟩⟩

/-! ### Classification agrees with `parse` -/

/-- `(tokens, parses?)`: `diagnose` is `.ok`/`.error` exactly when `parse`
    succeeds/fails, and `errorMessage` is `none`/`some` accordingly. -/
private def classCases : List (List Tok × Bool) :=
  [ ([.NUM 1, .PLUS, .NUM 2], true),
    ([.NUM 1, .PLUS], false),
    ([.NUM 1, .NUM 2], false) ]

private def classOk : (List Tok × Bool) → Bool
  | (toks, parses) =>
    let input := dummy toks
    let diagOk := match diagnose input with | .ok _ => parses | .error _ => !parses | _ => false
    let msgOk := (errorMessage input).isSome == !parses
    let parseOk := (parse input).isSome == parses
    diagOk && msgOk && parseOk

#guard classCases.all classOk

/-! ### The offending position and expected set -/

-- `1 +`: PLUS with no operand; error at the padded EOF (index 2). A NUM (5) or
-- LPAR (2) can start an operand; PLUS (0) cannot appear here.
#guard match diagnose (dummy [.NUM 1, .PLUS]) with
  | .error e => e.position == 2 && e.expected.contains 5 && e.expected.contains 2
      && !e.expected.contains 0
  | _ => false

-- `1 1`: a second NUM where an operator or EOF was expected.
#guard match diagnose (dummy [.NUM 1, .NUM 2]) with
  | .error e => e.lookahead == 5 && e.expected.contains 0 && e.expected.contains 7
  | _ => false

/-! ### terminalName -/

#guard terminalName 5 == "NUM"
#guard terminalName 7 == "end of input"

/-! ### Rendered messages -/

-- Auto-generated message names the offending token and lists expectations.
#guard match errorMessage (dummy [.NUM 1, .NUM 2]) with
  | some msg => containsStr msg "unexpected NUM" && containsStr msg "expected one of"
  | none => false

-- Custom per-state message overrides the auto-generated text (Menhir `.messages`).
#guard match diagnose (dummy [.NUM 1, .PLUS]) with
  | .error e =>
    errorMessage (dummy [.NUM 1, .PLUS]) (messages := fun st =>
      if st == e.state then some "operand expected after '+'" else none)
      == some "operand expected after '+'"
  | _ => false

/-! ### Span-based line:col rendering

`1 1` over the source `"1 1"`: the offending second `1` is at byte 2, which is
line 1, column 3. `errorMessage` given the source renders that location. -/

private def spannedBad : List (Positioned Tok) :=
  [tokAt (.NUM 1) 0 1, tokAt (.NUM 1) 2 3, tokAt .EOF 3 3]

#guard match errorMessage spannedBad "1 1" with
  | some msg => containsStr msg "1:3" && containsStr msg "unexpected NUM"
  | none => false

#eval IO.println "All error-message tests passed."
