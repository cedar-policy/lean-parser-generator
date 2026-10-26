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
Shared string-literal/join combinators for the two emitters.

Both backends still build some source as `String`s (the parts not moved onto
`Syntax`). This module gives them one definition of "a Lean list/array/def literal"
instead of an open-coded `"[" ++ … ++ "]"` in each, which is easy to get wrong on
the empty-list case or spacing. Everything here is a pure `String → …` function.
-/


@[expose] public section

namespace Emit.Builder

/-- A Lean string literal for `value` (`reprStr` gives a `"…"` with standard escapes). -/
def strLit (value : String) : String := reprStr value

/-- A `Nat` literal. -/
def natLit (n : Nat) : String := toString n

/-- An `Option Nat` literal (`none` / `some n`). -/
def optNatLit : Option Nat → String
  | none => "none"
  | some n => s!"some {n}"

/-- Join fragments with a single separator. -/
def joinWith (sep : String) (parts : List String) : String := sep.intercalate parts

/-- Comma-join fragments (`a, b, c`), the inside of a list/array literal. -/
def commaSep (parts : List String) : String := ", ".intercalate parts

/-- Join fragments as consecutive lines (one `\n` between). -/
def lines (parts : List String) : String := "\n".intercalate parts

/-- Join fragments as blank-line-separated blocks (one blank line between). -/
def paras (parts : List String) : String := "\n\n".intercalate parts

/-- A Lean list literal `[a, b, c]` from already-rendered element strings. -/
def listLit (elems : List String) : String := "[" ++ commaSep elems ++ "]"

/-- Rewrite bare `import X` lines in a copied user header block to `public import X`
    so the block is valid inside a generated module file (module system:
    every import in a `module` file must be `public`/`meta`, and unqualified
    `import` is rejected). Lines that are already `public import`/`meta import`,
    blank lines, comments, and non-import lines (e.g. `open`) are left untouched. -/
def publicizeImports (header : String) : String :=
  let rewrite (ln : String) : String :=
    let cs := ln.toList
    let ws := cs.takeWhile (fun c => c == ' ' || c == '\t')
    let rest := cs.drop ws.length
    let restStr := String.ofList rest
    if restStr.startsWith "import " then
      String.ofList ws ++ "public " ++ restStr
    else ln
  "\n".intercalate ((header.splitOn "\n").map rewrite)

/-- A Lean array literal `#[a, b, c]` from already-rendered element strings. -/
def arrayLit (elems : List String) : String := "#[" ++ commaSep elems ++ "]"

/-- A `Nat` list literal `[1, 2, 3]`. -/
def natListLit (l : List Nat) : String := listLit (l.map natLit)

/-- A top-level array-table def: `def {name} : Array {ty} := #[{elems}]`. Used for
    the flat action/goto/length tables. -/
def arrayDef (name ty : String) (elems : List String) : String :=
  s!"def {name} : Array {ty} := " ++ arrayLit elems

end Emit.Builder
