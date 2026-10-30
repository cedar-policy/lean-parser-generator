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
The action language of the Rust backend (docs/RUST_PARSER.md, decision D1).

Semantic actions in a `.lig` file are verbatim Lean terms. The Rust backend only
emits the actions that fall in a small subset of Lean: variables, constructor and
function applications, tuples, lists, `::`, `++`, projections, literals. This
module defines that subset as a datatype and a parser for it. It does not use
Lean's own parser: the generator does not know the notation a user `%header`
declares, and the point of the subset is that its syntax is exactly what this file
accepts. Text outside the subset parses to `AExpr.other`, which the classifier
(`Classify.lean`) reports as a blocker.

The parser does not resolve names. A dotted identifier whose first component is a
bound variable becomes a projection/field chain on that variable; every other
dotted identifier is a global name (`AExpr.global`) for the resolver to look up.
-/


@[expose] public section

namespace Emit.Rust

/-- An action term in the supported subset. -/
inductive AExpr where
  /-- A bound variable (an RHS binder, or a lambda parameter). -/
  | var (x : String)
  /-- A global name as written, e.g. `Policy.mk` or `Cedar.Add.fromIdent`. -/
  | global (name : String)
  /-- `.c`: a constructor named relative to the expected type. -/
  | dotIdent (c : String)
  /-- Application `f a₁ … aₙ`. -/
  | app (f : AExpr) (args : Array AExpr)
  /-- `(a, b, …)`, at least two components. -/
  | tuple (es : Array AExpr)
  /-- `[a, b, …]`. -/
  | list (es : Array AExpr)
  /-- `h :: t`. -/
  | cons (h t : AExpr)
  /-- `a ++ b`. -/
  | append (a b : AExpr)
  /-- `e.1`, `e.2`, … (1-based, as in Lean). -/
  | proj (e : AExpr) (i : Nat)
  /-- `e.name`, a method or field access such as `value.toNat!`. -/
  | field (e : AExpr) (name : String)
  /-- `⟨a, b, …⟩`, resolved against the expected type. -/
  | anon (es : Array AExpr)
  /-- `{ f := e, g := e' }`, a structure instance of the expected type. -/
  | structInst (fields : Array (String × AExpr))
  | nat (n : Nat)
  | str (s : String)
  /-- `()`. -/
  | unit
  /-- `fun x₁ … xₙ => body`. -/
  | lam (params : Array String) (body : AExpr)
  /-- Text outside the subset, with a short description of what was found. -/
  | other (what : String)
  deriving Repr, Inhabited, BEq

namespace Action

/-! ### Lexer -/

inductive Tok where
  | ident (s : String)
  /-- `.c` at the start of an argument (preceded by whitespace or an opener). -/
  | dotIdent (c : String)
  /-- `.c` or `.1` glued to the previous token. -/
  | glued (c : String)
  | nat (n : Nat)
  | str (s : String)
  | sym (s : String)
  deriving Repr, BEq, Inhabited

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdCont (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Read an identifier component starting at `i` (which satisfies `isIdStart`),
    including a trailing `!` or `?`. Returns the component and the next index. -/
def readComponent (cs : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  while j < cs.size && isIdCont cs[j]! do j := j + 1
  if j < cs.size && (cs[j]! == '!' || cs[j]! == '?') && !(j + 1 < cs.size && cs[j + 1]! == '=') then
    j := j + 1
  return (String.ofList (cs.extract i j).toList, j)

/-- Tokenize. `none` means a character outside the subset was met, with its text. -/
def tokenize (src : String) : Except String (Array Tok) := Id.run do
  let cs := src.toList.toArray
  let mut out : Array Tok := #[]
  let mut i := 0
  let mut prevGlue := false  -- no whitespace between the previous token and `i`
  while i < cs.size do
    let c := cs[i]!
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      i := i + 1
      prevGlue := false
    else if isIdStart c then
      let (comp, j) := readComponent cs i
      let mut name := comp
      let mut k := j
      -- Dotted continuation: `.` immediately followed by an identifier start or digit.
      while k + 1 < cs.size && cs[k]! == '.' && (isIdStart cs[k + 1]! || cs[k + 1]!.isDigit) do
        if cs[k + 1]!.isDigit then
          let mut m := k + 1
          while m < cs.size && cs[m]!.isDigit do m := m + 1
          name := name ++ "." ++ String.ofList (cs.extract (k + 1) m).toList
          k := m
        else
          let (c2, m) := readComponent cs (k + 1)
          name := name ++ "." ++ c2
          k := m
      out := out.push (.ident name)
      i := k
      prevGlue := true
    else if c == '.' && i + 1 < cs.size && (isIdStart cs[i + 1]! || cs[i + 1]!.isDigit) then
      if cs[i + 1]!.isDigit then
        let mut m := i + 1
        while m < cs.size && cs[m]!.isDigit do m := m + 1
        out := out.push (.glued (String.ofList (cs.extract (i + 1) m).toList))
        i := m
      else
        let (c2, m) := readComponent cs (i + 1)
        out := out.push (if prevGlue then .glued c2 else .dotIdent c2)
        i := m
      prevGlue := true
    else if c.isDigit then
      let mut m := i
      while m < cs.size && cs[m]!.isDigit do m := m + 1
      out := out.push (.nat (String.ofList (cs.extract i m).toList).toNat!)
      i := m
      prevGlue := true
    else if c == '"' then
      let mut m := i + 1
      let mut buf := ""
      while m < cs.size && cs[m]! != '"' do
        if cs[m]! == '\\' && m + 1 < cs.size then
          buf := buf.push cs[m + 1]!
          m := m + 2
        else
          buf := buf.push cs[m]!
          m := m + 1
      if m ≥ cs.size then return .error "unterminated string literal"
      out := out.push (.str buf)
      i := m + 1
      prevGlue := true
    else if c == ':' && i + 1 < cs.size && cs[i + 1]! == ':' then
      out := out.push (.sym "::"); i := i + 2; prevGlue := false
    else if c == '+' && i + 1 < cs.size && cs[i + 1]! == '+' then
      out := out.push (.sym "++"); i := i + 2; prevGlue := false
    else if c == ':' && i + 1 < cs.size && cs[i + 1]! == '=' then
      out := out.push (.sym ":="); i := i + 2; prevGlue := false
    else if c == '=' && i + 1 < cs.size && cs[i + 1]! == '>' then
      out := out.push (.sym "=>"); i := i + 2; prevGlue := false
    else if c == '(' || c == ')' || c == '[' || c == ']' || c == ',' || c == '⟨' || c == '⟩' || c == '{' || c == '}' then
      out := out.push (.sym (String.singleton c)); i := i + 1
      prevGlue := (c == ')' || c == ']' || c == '⟩' || c == '}')
    else
      return .error s!"unsupported character `{c}`"
  return .ok out

/-! ### Parser -/

/-- Parser state: the tokens, the next index, and the variables in scope. -/
structure St where
  toks : Array Tok
  pos : Nat := 0

abbrev P := StateT St (Except String)

def peek? : P (Option Tok) := do
  let s ← get
  return s.toks[s.pos]?

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def expectSym (x : String) : P Unit := do
  match ← peek? with
  | some (.sym y) => if x == y then advance else throw s!"expected `{x}`"
  | _ => throw s!"expected `{x}`"

/-- Turn a dotted identifier into a variable access chain if its first component is in
    scope, else a global name. -/
def mkIdent (scope : List String) (name : String) : AExpr :=
  match name.splitOn "." with
  | [] => .global name
  | first :: rest =>
    if scope.contains first then
      rest.foldl (fun e c =>
        match c.toNat? with
        | some n => .proj e n
        | none => .field e c) (.var first)
    else .global name

/-- Starts an atom (so that juxtaposition can continue an application). -/
def startsAtom : Tok → Bool
  | .ident _ | .dotIdent _ | .nat _ | .str _ => true
  | .sym s => s == "(" || s == "[" || s == "⟨" || s == "{"
  | .glued _ => false

mutual

partial def pExpr (scope : List String) : P AExpr := do
  match ← peek? with
  | some (.ident "fun") =>
    advance
    let mut params : Array String := #[]
    repeat
      match ← peek? with
      | some (.ident x) =>
        if x.contains '.' then throw "dotted lambda parameter"
        params := params.push x; advance
      | some (.sym "=>") => advance; break
      | _ => throw "unsupported lambda parameter"
    if params.isEmpty then throw "lambda without parameters"
    let body ← pExpr (params.toList ++ scope)
    return .lam params body
  | _ => pAppend scope

partial def pAppend (scope : List String) : P AExpr := do
  let mut lhs ← pCons scope
  repeat
    match ← peek? with
    | some (.sym "++") =>
      advance
      let rhs ← pCons scope
      lhs := .append lhs rhs
    | _ => break
  return lhs

partial def pCons (scope : List String) : P AExpr := do
  let h ← pApp scope
  match ← peek? with
  | some (.sym "::") =>
    advance
    let t ← pCons scope
    return .cons h t
  | _ => return h

partial def pApp (scope : List String) : P AExpr := do
  let f ← pPostfix scope
  let mut args : Array AExpr := #[]
  repeat
    match ← peek? with
    | some t =>
      if startsAtom t then args := args.push (← pPostfix scope) else break
    | none => break
  return if args.isEmpty then f else .app f args

partial def pPostfix (scope : List String) : P AExpr := do
  let mut e ← pAtom scope
  repeat
    match ← peek? with
    | some (.glued c) =>
      advance
      e := match c.toNat? with
        | some n => .proj e n
        | none => .field e c
    | _ => break
  return e

partial def pAtom (scope : List String) : P AExpr := do
  match ← peek? with
  | some (.ident x) => advance; return mkIdent scope x
  | some (.dotIdent c) => advance; return .dotIdent c
  | some (.nat n) => advance; return .nat n
  | some (.str s) => advance; return .str s
  | some (.sym "(") =>
    advance
    match ← peek? with
    | some (.sym ")") => advance; return .unit
    | _ =>
      let first ← pExpr scope
      let mut es := #[first]
      repeat
        match ← peek? with
        | some (.sym ",") => advance; es := es.push (← pExpr scope)
        | _ => break
      expectSym ")"
      return if es.size == 1 then es[0]! else .tuple es
  | some (.sym "[") =>
    advance
    match ← peek? with
    | some (.sym "]") => advance; return .list #[]
    | _ =>
      let mut es := #[← pExpr scope]
      repeat
        match ← peek? with
        | some (.sym ",") => advance; es := es.push (← pExpr scope)
        | _ => break
      expectSym "]"
      return .list es
  | some (.sym "{") =>
    advance
    let mut fields : Array (String × AExpr) := #[]
    repeat
      match ← peek? with
      | some (.ident f) =>
        advance
        expectSym ":="
        fields := fields.push (f, ← pExpr scope)
        match ← peek? with
        | some (.sym ",") => advance
        | _ => break
      | _ => break
    expectSym "}"
    if fields.isEmpty then throw "empty structure instance"
    return .structInst fields
  | some (.sym "⟨") =>
    advance
    let mut es := #[← pExpr scope]
    repeat
      match ← peek? with
      | some (.sym ",") => advance; es := es.push (← pExpr scope)
      | _ => break
    expectSym "⟩"
    return .anon es
  | some t => throw s!"unexpected {repr t}"
  | none => throw "unexpected end of action"

end

/-- Parse an action. `scope` lists the variables bound by the production (binder
    names and their `_span` companions). Text outside the subset gives
    `AExpr.other` carrying the reason. -/
def parse (scope : List String) (src : String) : AExpr :=
  match tokenize src with
  | .error e => .other e
  | .ok toks =>
    match (pExpr scope).run { toks } with
    | .error e => .other e
    | .ok (e, st) =>
      if st.pos < toks.size then .other s!"unsupported syntax at token {st.pos}" else e

end Action

end Emit.Rust
