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
`leanparsergenerator --rust-report grammar.lig`: for every parser alternative and
lexer rule, say whether its action can be emitted as Rust and, if not, why
(docs/RUST_PARSER.md).
-/
public import LeanParserGenerator.Emit.Rust.Domain
public import LeanParserGenerator.Frontend.File


@[expose] public section

namespace Emit.Rust

open Frontend

/-- Module names from the `import` lines of a header. -/
def headerImports (header : String) : List String :=
  (header.splitOn "\n").filterMap fun ln =>
    let ln := ln.trimAscii.toString
    if ln.startsWith "import " then some (ln.drop 7).toString.trimAscii.toString else none

/-- Namespaces from the `open` lines of a header. -/
def headerOpens (header : String) : List String :=
  (header.splitOn "\n").flatMap fun ln =>
    let ln := ln.trimAscii.toString
    if ln.startsWith "open " then
      ((ln.drop 5).toString.splitOn " ").filter (fun w => !w.isEmpty && w != "in")
    else []

/-- Names defined with `def` (or `abbrev`) in header text. -/
def headerDefs (header : String) : List String :=
  let ws := (header.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
  let rec go : List String → List String
    | "def" :: n :: rest | "abbrev" :: n :: rest => n :: go rest
    | _ :: rest => go rest
    | [] => []
  go ws

/-- The constructors of the token type, which the lexer module (not the environment)
    defines. -/
def tokenResolver (s : Surface) : Resolver where
  find _ name :=
    let pre := s.tokenType ++ "."
    if name.startsWith pre then
      let c := (name.drop pre.length).toString
      s.tokens.find? (·.name == c) |>.map fun t =>
        ⟨name, .ctor s.tokenType (if t.hasVal then #[Ty.parse t.ty] else #[])⟩
    else none

/-- The analysis context for the parser actions: the header's environment. -/
def parserCtx (s : Surface) (res : Resolver) : Ctx :=
  { res := res.orElse (tokenResolver s), opens := headerOpens s.header,
    headerDefs := headerDefs (s.header ++ "\n" ++ s.lexerHeader) }

/-- The type of the value a symbol carries. -/
def symTy (s : Surface) (sym : String) : Ty :=
  match s.rules.find? (·.lhs == sym) with
  | some r => Ty.parse r.ty
  | none =>
    match s.tokens.find? (·.name == sym) with
    | some t => if t.hasVal then Ty.parse t.ty else .con "Unit" #[]
    | none => .other sym

/-- One row of the report. -/
structure Row where
  where_ : String
  action : String
  analysis : Analysis
  /-- For a lexer rule, the language of its lexeme. -/
  lexeme : Option Lexer.Regex := none

/-- Analyse every parser alternative. -/
def parserRows (s : Surface) (ctx : Ctx) : Array Row := Id.run do
  let mut rows := #[]
  for r in s.rules do
    for h : i in [0:r.alts.size] do
      let alt := r.alts[i]
      let mut vars : List (String × Ty) := []
      for el in alt.elems do
        match el.binder with
        | some b =>
          vars := (b ++ "_span", .con "Runtime.Span" #[]) :: (b, symTy s el.sym) :: vars
        | none => pure ()
      let a := analyzeAction { ctx with vars } alt.action (some (Ty.parse r.ty))
      rows := rows.push { where_ := s!"{r.lhs} #{i}", action := alt.action, analysis := a }
  return rows

/-- Analyse every lexer rule (and the `eof` action). -/
def lexerRows (s : Surface) (ctx : Ctx) : Array Row := Id.run do
  let some spec := s.lexer | return #[]
  let tokTy := some (Ty.con s.tokenType #[])
  let mut rows := #[]
  for mode in spec.modes do
    for h : i in [0:mode.rules.size] do
      let r := mode.rules[i]
      match r.emit with
      | none => pure ()  -- `skip` emits nothing
      | some e =>
        let vars := match r.binder with
          | some b => [(b, Ty.con "String" #[])]
          | none => []
        let a := analyzeAction { ctx with vars } e tokTy
        rows := rows.push { where_ := s!"lexer {mode.name} rule {i}", action := e, analysis := a,
                            lexeme := some r.regex }
  return rows

def clip (s : String) (n : Nat := 90) : String :=
  let s := (s.replace "\n" " ").trimAscii.toString
  let s := " ".intercalate (s.splitOn " " |>.filter (!·.isEmpty))
  if s.length > n then (s.take n).toString ++ "…" else s

/-- Tally strings, in first-seen order. -/
def tally (xs : Array String) : List (String × Nat) :=
  xs.foldl (fun acc x =>
    if acc.any (·.1 == x) then acc.map fun (k, n) => if k == x then (k, n + 1) else (k, n)
    else acc ++ [(x, 1)]) []

def section_ (title : String) (rows : Array Row) (verbose : Bool) : List String := Id.run do
  let ok := rows.filter (·.analysis.emittable)
  let hook := rows.filter (!·.analysis.emittable)
  let mut out : List String := [s!"{title}: {rows.size} actions, {ok.size} emittable, {hook.size} need a hook"]
  if !hook.isEmpty then
    out := out ++ ["  blockers:"]
    for (k, n) in tally (hook.flatMap fun r => r.analysis.blockers.map (·.kind)) do
      out := out ++ [s!"    {n} × {k}"]
    out := out ++ ["  hooks:"]
    for r in hook do
      out := out ++ [s!"    {r.where_}: {clip r.action}"]
      for b in r.analysis.blockers do out := out ++ [s!"        - {b.describe}"]
  -- Constructors and fields are numerous; summarise them and list them only with `-v`.
  let kindOf (u : Used) : String :=
    match u with
    | .ctor _ => "constructor" | .field _ => "structure field" | .known n => s!"known function {n}"
    | u => u.describe
  let usedAll := rows.flatMap (·.analysis.used.map kindOf)
  out := out ++ ["  rules used (number of actions using each):"]
  for (k, n) in tally usedAll do out := out ++ [s!"    {n} × {k}"]
  let distinct (f : Used → Option String) : List String :=
    (rows.flatMap (·.analysis.used.filterMap f)).toList.eraseDups
  let ctors := distinct fun | .ctor n => some n | _ => none
  out := out ++ [s!"    ({ctors.length} distinct constructors)"]
  if verbose then out := out ++ [s!"    constructors: {", ".intercalate ctors}"]
  -- Partial known functions: check the argument language against the domain (D10).
  for r in rows do
    for (fn, recv) in r.analysis.calls do
      match (knownFn? fn).bind (·.domain) with
      | none => pure ()
      | some _ =>
        let v := match r.lexeme with
          | some rx => checkCall rx fn recv
          | none => .notChecked "the argument is a token value of unknown language"
        let dom := ((knownFn? fn).map (·.domainText)).getD ""
        out := out ++ [s!"  domain of {fn} ({dom}) at {r.where_}: {v.describe}"]
  let clones := rows.filter (!·.analysis.clones.isEmpty)
  if !clones.isEmpty then
    out := out ++ [s!"  {clones.size} actions use a variable more than once (copy needed):"]
    for r in clones do
      out := out ++ [s!"    {r.where_}: {", ".intercalate r.analysis.clones.toList}"]
  if verbose then
    out := out ++ ["  emittable:"]
    for r in ok do out := out ++ [s!"    {r.where_}: {clip r.action}"]
  return out

/-- Render the report. `resNote` says where the resolver came from. -/
def report (s : Surface) (res : Resolver) (resNote : String) (verbose : Bool) : String :=
  let ctx := parserCtx s res
  let parser := parserRows s ctx
  let lexer := lexerRows s ctx
  "\n".intercalate (
    [s!"resolver: {resNote}"] ++
    section_ "parser" parser verbose ++
    (if lexer.isEmpty then [] else section_ "lexer" lexer verbose)) ++ "\n"

end Emit.Rust
