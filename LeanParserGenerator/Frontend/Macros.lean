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

/-!
# Menhir-style parameterized-rule macros

The `.lig` surface allows a handful of built-in parameterized rules, written as
`macro(arg, …)` in any right-hand-side symbol position:

* `list(X)`                          — zero or more `X`, producing `List <ty X>`
* `nonempty_list(X)`                 — one or more `X`, producing `List <ty X>`
* `separated_list(sep, X)`           — zero or more `X` separated by terminal `sep`
* `separated_nonempty_list(sep, X)`  — one or more, separated by `sep`
* `option(X)`                        — zero or one `X`, producing `Option <ty X>`

They are pure sugar: `expandMacros` rewrites each distinct application into a fresh
concrete nonterminal with ordinary alternatives, then replaces the invocation with
that nonterminal's name. Nothing downstream (IR, Pager, the proofs) sees macros, so
this does not change the trust boundary — it only makes list-heavy grammars (e.g. a
grammar that would hand-write ~30 `*_list` nonterminals) readable.

The element type is taken from the referenced rule's declared `::` type; `separated_*`
takes a terminal separator as its first argument, which carries no value and so does
not affect the result type.
-/


@[expose] public section

namespace Frontend.Macros

open Frontend

/-- A parsed macro application `name(arg0, arg1, …)`. -/
structure App where
  name : String
  args : Array String
  deriving Repr, Inhabited

/-- Split `s` at top-level commas (respecting nested parentheses). -/
def splitArgs (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut depth := 0
  let mut cur := ""
  for ch in s.toList do
    if ch == '(' then depth := depth + 1; cur := cur.push ch
    else if ch == ')' then depth := depth - 1; cur := cur.push ch
    else if ch == ',' && depth == 0 then out := out.push cur.trimAscii.toString; cur := ""
    else cur := cur.push ch
  let last := cur.trimAscii.toString
  if last.length > 0 then out := out.push last
  return out

/-- Parse `sym` as a macro application `name(args)`, if it has that shape. -/
def parseApp? (sym : String) : Option App := Id.run do
  let cs := sym.toList
  if cs.isEmpty || cs.getLast! != ')' then return none
  -- find the first '('
  let mut i := 0
  let mut found := false
  for c in cs do
    if c == '(' then found := true; break
    i := i + 1
  if !found then return none
  let name := (String.ofList (cs.take i)).trimAscii.toString
  let inner := String.ofList (cs.drop (i + 1) |>.dropLast)  -- between first '(' and last ')'
  if name.isEmpty then return none
  return some { name := name, args := splitArgs inner }

/-- The set of recognized macro names. -/
def isMacroName (n : String) : Bool :=
  n == "list" || n == "nonempty_list" || n == "option" ||
  n == "separated_list" || n == "separated_nonempty_list"

/-- A filesystem/identifier-safe mangling of an application into a fresh
    nonterminal name: `list(brace)` ⇒ `list_brace`, `separated_list(COMMA, expr)`
    ⇒ `separated_list_COMMA_expr`. -/
def mangle (sym : String) : String :=
  (sym.toList.map (fun c => if c == '(' || c == ',' || c == ' ' then '_'
                            else if c == ')' then ' ' else c)
    |> String.ofList).trimAscii.toString.replace " " "" |>.replace "__" "_"

/-- Look up an element's declared Lean type by name: a nonterminal rule's `::` type,
    or a terminal token's payload type (`Unit` for a valueless token). -/
def tyOf (s : Surface) (nm : String) : Option String :=
  match s.rules.find? (·.lhs == nm) with
  | some r => some r.ty
  | none =>
    match s.tokens.find? (·.name == nm) with
    | some t => some (if t.hasVal then t.ty else "Unit")
    | none => none

/-- Build the alternatives for a macro application, given the mangled self name and
    resolved element type. Returns the rule type and its alternatives, or an error. -/
def synth (self : String) (app : App) (elemTy : String)
    : Except String (String × Array Alt) := do
  let mk (elems : Array (Option String × String)) (action : String) : Alt :=
    { elems := elems.map (fun (b, sy) => { binder := b, sym := sy }), action := action }
  match app.name, app.args.toList with
  | "list", [x] =>
    .ok (s!"List ({elemTy})", #[
      mk #[] "[]",
      mk #[(some "x", x), (some "xs", self)] "x :: xs"])
  | "nonempty_list", [x] =>
    .ok (s!"List ({elemTy})", #[
      mk #[(some "x", x)] "[x]",
      mk #[(some "x", x), (some "xs", self)] "x :: xs"])
  | "option", [x] =>
    .ok (s!"Option ({elemTy})", #[
      mk #[] "none",
      mk #[(some "x", x)] "some x"])
  | "separated_nonempty_list", [sep, x] =>
    .ok (s!"List ({elemTy})", #[
      mk #[(some "x", x)] "[x]",
      mk #[(some "x", x), (none, sep), (some "xs", self)] "x :: xs"])
  | "separated_list", [sep, x] =>
    -- zero or more: empty, or a nonempty separated list (reuses the -nonempty- form)
    .ok (s!"List ({elemTy})", #[
      mk #[] "[]",
      mk #[(some "x", x)] "[x]",
      mk #[(some "x", x), (none, sep), (some "xs", self)] "x :: xs"])
  | n, _ => .error s!"unsupported macro application `{n}` in `{self}`"

/-- Expand all parameterized-rule applications in a surface grammar into concrete
    nonterminals. Idempotent on macro-free grammars. -/
def expandMacros (s : Surface) : Except String Surface := do
  -- 1. Collect every distinct macro application appearing in any rule element.
  let mut apps : Array (String × App) := #[]   -- (originalSym, parsed)
  for r in s.rules do
    for a in r.alts do
      for e in a.elems do
        if let some app := parseApp? e.sym then
          if isMacroName app.name && !(apps.any (·.1 == e.sym)) then
            apps := apps.push (e.sym, app)
  if apps.isEmpty then return s
  -- 2. Synthesize a fresh rule for each application.
  let mut newRules : Array Rule := #[]
  for (orig, app) in apps do
    let self := mangle orig
    -- the element is the LAST argument for list/option, the last for separated_* too
    let elemArg := app.args.back!
    -- element type: if the element is itself an application, its type is List/Option
    -- of the inner element's type; otherwise it's the referenced rule's declared type.
    let elemTy ← match parseApp? elemArg with
      | some inner =>
        let innerElemTy ← match tyOf s inner.args.back! with
          | some t => .ok t
          | none => .error s!"macro element `{inner.args.back!}` has no rule type"
        if inner.name == "option" then .ok s!"Option ({innerElemTy})"
        else .ok s!"List ({innerElemTy})"
      | none =>
        match tyOf s elemArg with
        | some t => .ok t
        | none => .error s!"macro element `{elemArg}` in `{orig}` is not a declared nonterminal"
    let (ruleTy, alts) ← synth self app elemTy
    newRules := newRules.push { lhs := self, ty := ruleTy, alts := alts }
  -- 3. Rewrite invocations to the mangled names throughout all rule elements.
  let rewriteElem := fun (e : Elem) =>
    if (parseApp? e.sym).isSome && isMacroName ((parseApp? e.sym).get!).name
    then { e with sym := mangle e.sym } else e
  let rewriteAlt := fun (a : Alt) => { a with elems := a.elems.map rewriteElem }
  let rewriteRule := fun (r : Rule) => { r with alts := r.alts.map rewriteAlt }
  let baseRules := s.rules.map rewriteRule
  return { s with rules := baseRules ++ newRules }

end Frontend.Macros
