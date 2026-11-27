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
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Frontend.LigParse
/-
`test/lig/OptionTest.lean` — checks that every `%option` is handled consistently.

`Frontend.optionSpecs` defines the options. This test checks that:

* the hand-written parser (`parseLig`) and the generated one (`parseLigGen`) accept each
  option and produce the same `Options`;
* both reject a missing value, an unknown name, and a value on a flag, and give the
  same message for the first two (up to the ` at byte N` suffix);
* the unknown-option message lists every option;
* every option is named in the README and in the VS Code grammar.

Run with `lake exe lig-option-test` from the repository root.
-/

public section

open Frontend

/-- A grammar that parses, with the given lines inserted before `%start`. -/
private def grammar (extra : String) : String :=
  "%tokentype Tok\n%token A\n%token EOF\n%eof EOF\n" ++ extra ++ "\n%start s\n%%\ns :: Nat\n  | A { 1 }\n"

/-- A value of each kind. -/
private def sampleValue : OptionValue → String
  | .flag => ""
  | .ident => "someFunction"
  | .modulePath => "My.Module.Prefix"
  | .path => "out/dir/generated.rs"

private def optionLine (spec : OptionSpec) : String :=
  let v := sampleValue spec.value
  if v.isEmpty then s!"%option {spec.name}" else s!"%option {spec.name} {v}"

/-- Drop a trailing ` at byte N`. -/
private def stripByte (msg : String) : String :=
  match msg.splitOn " at byte " with
  | [m] => m
  | m :: _ => m
  | [] => msg

private def optionsOf : Except String Surface → Except String Options
  | .ok s => .ok s.options
  | .error e => .error e

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

def main : IO UInt32 := do
  let mut failed := 0
  let check (name : String) (ok : Bool) (detail : String := "") : IO Bool := do
    if ok then IO.println s!"OK   {name}"
    else IO.println s!"FAIL {name}{if detail.isEmpty then "" else "\n  " ++ detail}"
    return ok
  let readme ← IO.FS.readFile "README.md"
  let tmLang ← IO.FS.readFile "editors/vscode/syntaxes/lig.tmLanguage.json"
  for spec in optionSpecs do
    let src := grammar (optionLine spec)
    let hand := optionsOf (parseLig src)
    let gen := optionsOf (parseLigGen src)
    -- The option changes `Options`, and both parsers agree on how.
    let agree := match hand, gen with
      | .ok h, .ok g => h == g && h != ({} : Options)
      | _, _ => false
    unless ← check s!"{spec.name}: both parsers accept it and agree" agree
      s!"hand: {repr hand}\n  gen: {repr gen}" do failed := failed + 1
    -- A valued option without its value is rejected by both, with one message.
    if spec.value != .flag then
      let missing := grammar s!"%option {spec.name}"
      let h := (parseLig missing).toOption
      let g := (parseLigGen missing).toOption
      let hm := match parseLig missing with | .error e => stripByte e | .ok _ => ""
      let gm := match parseLigGen missing with | .error e => stripByte e | .ok _ => ""
      let ok := h.isNone && g.isNone && hm == gm && hm == missingOptionValueMessage spec
      unless ← check s!"{spec.name}: a missing value is rejected with the same message" ok
        s!"hand: {hm}\n  gen:  {gm}" do failed := failed + 1
    else
      let withValue := grammar s!"%option {spec.name} someValue"
      let ok := (parseLig withValue).toOption.isNone && (parseLigGen withValue).toOption.isNone
      unless ← check s!"{spec.name}: a value on a flag is rejected" ok do failed := failed + 1
    unless ← check s!"{spec.name}: documented in README.md" (contains readme s!"%option {spec.name}") do
      failed := failed + 1
    unless ← check s!"{spec.name}: named in the VS Code grammar" (contains tmLang spec.name) do
      failed := failed + 1
  -- An unknown option is rejected by both parsers, and the message lists every option.
  let unknown := grammar "%option no_such_option"
  let hm := match parseLig unknown with | .error e => stripByte e | .ok _ => ""
  let gm := match parseLigGen unknown with | .error e => stripByte e | .ok _ => ""
  unless ← check "unknown option: both reject it with the same message"
      (hm == gm && hm == unknownOptionMessage "no_such_option") s!"hand: {hm}\n  gen:  {gm}" do
    failed := failed + 1
  unless ← check "unknown option: the message lists every option"
      (knownOptions.all (contains hm ·)) do failed := failed + 1
  unless ← check "option names are unique" (knownOptions.eraseDups.length == knownOptions.length) do
    failed := failed + 1
  if failed == 0 then
    IO.println s!"option consistency: {optionSpecs.length} options consistent"
    return 0
  else
    IO.eprintln s!"option consistency FAILED: {failed} check(s)"
    return 1
