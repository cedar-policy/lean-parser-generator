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
public import LeanParserGenerator.Frontend.LigLexer
public import LeanParserGenerator.Frontend.Generated.LigParser
/-
The verified `.lig` parser: its main entry point.

`parseLigGen` is the generated-parser counterpart of the hand-written
`Frontend.parseLig`: it tokenizes `.lig` source with the hand-written
`LigLexer.tokenize` (the balanced-brace escape hatch) and parses the token stream
with the LPG-generated `LigParser`, whose actions build the `Surface`. The two
must agree on every `.lig` file; `test/lig/BootstrapAgreementTest.lean` checks
that on the repository's own grammars.
-/


@[expose] public section

namespace Frontend

/-- Parse `.lig` source using the generated `LigParser` over the hand-written
    `LigLexer` token stream. Drop-in for `parseLig`. -/
def parseLigGen (input : String) (_fileName : String := "<lig>") :
    Except String Surface := do
  let toks ← LigLexer.tokenize input
  match LeanParserGenerator.Frontend.Generated.LigParser.parse
      (toks.map Runtime.Positioned.dummy) with
  | some res => res
  | none => .error "lig parse error (generated LigParser rejected the token stream)"

end Frontend
