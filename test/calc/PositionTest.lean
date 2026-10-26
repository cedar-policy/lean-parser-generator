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
public import calc.CalcLexer
public import calc.CalcParser
meta import calc.CalcLexer
meta import calc.CalcParser

public section

open CalcParser Runtime

/-! Position handling for the generated calc parser. Spans ride inside the engine
value `VP := Span × V`; a production's span folds as `merge (first) (last)`
(docs/DESIGN.md §6.2). `run` exposes the top-level span; `parse` drops it. -/

/-- Wrap a token with an explicit half-open byte span. -/
private def tokAt (t : Tok) (a b : Nat) : Positioned Tok := ⟨t, ⟨⟨a⟩, ⟨b⟩⟩⟩

/-- The top-level value and span `run` returns, or `none`. -/
private def runSpan (input : List (Positioned Tok)) : Option (Int × Span) :=
  match CalcParser.run input with
  | .ok (sp, .v0 v) => some (v, sp)
  | _ => none

/-- `(tokens, expected value, expected top-level span)`. The span folds
    `merge (first symbol) (last symbol)`; a single symbol folds to its own span. -/
private def cases : List (List (Positioned Tok) × Int × Span) :=
  [ -- `2 + 3`: 2@0..1, +@2..3, 3@4..5 → value 5, span 0..5
    ([tokAt (.NUM 2) 0 1, tokAt .PLUS 2 3, tokAt (.NUM 3) 4 5, tokAt .EOF 5 5], 5, ⟨⟨0⟩, ⟨5⟩⟩),
    -- single number `7`@3..4 → value 7, span 3..4
    ([tokAt (.NUM 7) 3 4, tokAt .EOF 4 4], 7, ⟨⟨3⟩, ⟨4⟩⟩),
    -- `(2 + 3) * 4`: whole span covers the outermost symbols 0..11
    ([tokAt .LPAR 0 1, tokAt (.NUM 2) 1 2, tokAt .PLUS 3 4, tokAt (.NUM 3) 5 6,
      tokAt .RPAR 6 7, tokAt .TIMES 8 9, tokAt (.NUM 4) 10 11, tokAt .EOF 11 11], 20, ⟨⟨0⟩, ⟨11⟩⟩) ]

/-- Check one case: `run` yields the expected value and folded span. -/
private def valueSpanOk : (List (Positioned Tok) × Int × Span) → Bool
  | (input, v, sp) => decide (runSpan input = some (v, sp))

/-- Check one case: `parse` yields the expected value (span dropped). -/
private def valueOk : (List (Positioned Tok) × Int × Span) → Bool
  | (input, v, _) => decide (CalcParser.parse input = some v)

#guard cases.all valueSpanOk

-- `parse` drops the span and returns the value only.
#guard cases.all valueOk
