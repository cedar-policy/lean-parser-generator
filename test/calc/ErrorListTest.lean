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
`test/calc/ErrorListTest.lean` — regression for the Menhir `--list-errors`-style
error-state enumerator (`Emit.errorStates` / `Emit.renderErrorList`).

Run with:  `lake env lean test/calc/ErrorListTest.lean`
-/
public import LeanParserGenerator.Emit.ErrorList
public import LeanParserGenerator.Frontend.File


public section

open Frontend Emit

/-- A tiny grammar: `s → A`. State 0 should expect `A` and reject everything else. -/
def tinyGrammar : String :=
"%tokentype Tok
%token A
%token EOF
%eof EOF
%start s
%%
s :: Nat
  | A { 0 }
"

def tinyErrorStates : Array ErrorState :=
  match parseLig tinyGrammar with
  | .ok s =>
    match prepareGrammar s with
    | .ok p => errorStates s p
    | .error _ => #[]
  | .error _ => #[]

-- There is at least one error state.
#guard tinyErrorStates.size > 0

-- The initial state (0) expects `A` and nothing has an empty expected set here.
#guard tinyErrorStates.any (fun es => es.state == 0 && es.expected.contains "A")

-- Every listed error state genuinely rejects at least one terminal and accepts
-- at least one (a well-formed `.messages` template entry).
#guard tinyErrorStates.all (fun es => es.rejecting.size > 0 && es.expected.size > 0)

-- The rendered template mentions the expected token and the state-message hint.
def tinyRender : String :=
  match parseLig tinyGrammar with
  | .ok s => match prepareGrammar s with
    | .ok p => renderErrorList s p
    | .error _ => ""
  | .error _ => ""

#guard (tinyRender.splitOn "## State ").length > 1
#guard (tinyRender.splitOn "expected one of: A").length > 1

#eval IO.println "All error-list tests passed."
