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
public import cedarentities.CedarEntitiesLexer
public import cedarentities.CedarEntitiesParser

/-!
`test/cedarentities/CorpusTest.lean` — parses every `.cedarentities` file under
`test/cedarentities/corpus/` with the generated `CedarEntitiesLexer`/
`CedarEntitiesParser` and checks it lands in the right bucket:

* `corpus/positive/` — must lex and parse (accepted);
* `corpus/negative/` — must be rejected (a lex error or a `none` parse).

Fails (exits nonzero) if any positive file is rejected or any negative file is
accepted. Run with `lake exe cedarentities-corpus-test`.

An empty file is a *valid* (empty) entity set, so empty files are
parsed rather than skipped; keep empty inputs under `positive/`.
-/


public section

open Entities

/-- Does the parser accept `src`? A lex error counts as "not accepted". -/
private def parses (src : String) : Bool :=
  match CedarEntitiesLexer.tokenize src with
  | .error _ => false
  | .ok toks => (CedarEntitiesParser.parse toks 30).isSome

private def corpusDir : System.FilePath := "test" / "cedarentities" / "corpus"

/-- List the `.cedarentities` files in `dir`, sorted for stable output. -/
private def entitiesFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.pathExists) then
    return #[]
  let entries ← dir.readDir
  let files := entries.filterMap fun e =>
    if e.path.extension == some "cedarentities" then some e.path else none
  return files.qsort (fun a b => a.toString < b.toString)

def main : IO UInt32 := do
  let posFiles ← entitiesFiles (corpusDir / "positive")
  let negFiles ← entitiesFiles (corpusDir / "negative")
  let mut ok := 0
  let mut failures : Array String := #[]
  -- Positive: must parse.
  for path in posFiles do
    let src ← IO.FS.readFile path
    if parses src then
      ok := ok + 1
    else
      failures := failures.push s!"{path}: expected ACCEPT, got REJECT"
  -- Negative: must be rejected.
  for path in negFiles do
    let src ← IO.FS.readFile path
    if parses src then
      failures := failures.push s!"{path}: expected REJECT, got ACCEPT"
    else
      ok := ok + 1
  let total := posFiles.size + negFiles.size
  IO.println s!"cedar entities corpus: {ok}/{total} correct \
    ({posFiles.size} positive, {negFiles.size} negative)"
  for f in failures do
    IO.eprintln s!"  FAIL {f}"
  return (if failures.isEmpty then 0 else 1)
