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
Lean types as written in a `.lig` (`policies :: Policies`, `%token <Nat> NUMBER`,
`Option (RelOp × Expr)`), parsed just far enough for the Rust backend: type
constructor applications and products. Anything else (function types, subtypes,
dependent types) is `Ty.other` and keeps its source text.
-/


@[expose] public section

namespace Emit.Rust

/-- A Lean type in the supported subset. -/
inductive Ty where
  /-- `C a₁ … aₙ`, with `C` a possibly dotted name. -/
  | con (name : String) (args : Array Ty)
  /-- `A × B` (right associative, as in Lean). -/
  | prod (a b : Ty)
  /-- `{ x : T // p }`: the base type; the predicate is dropped (a proof obligation). -/
  | sub (base : Ty)
  /-- Outside the subset. -/
  | other (src : String)
  deriving Repr, Inhabited, BEq

namespace Ty

inductive TT where
  | id (s : String) | lp | rp | times
  deriving BEq

def lex (src : String) : Option (Array TT) := Id.run do
  let cs := src.toList.toArray
  let mut out : Array TT := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then i := i + 1
    else if c == '(' then out := out.push .lp; i := i + 1
    else if c == ')' then out := out.push .rp; i := i + 1
    else if c == '×' then out := out.push .times; i := i + 1
    else if c.isAlpha || c == '_' then
      let mut j := i
      while j < cs.size && (cs[j]!.isAlphanum || cs[j]! == '_' || cs[j]! == '\'' || cs[j]! == '.') do
        j := j + 1
      out := out.push (.id (String.ofList (cs.extract i j).toList))
      i := j
    else return none
  return some out

abbrev P := StateT (Array TT × Nat) Option

def peek : P (Option TT) := do
  let (ts, i) ← get
  return ts[i]?

def adv : P Unit := modify fun (ts, i) => (ts, i + 1)

mutual
partial def pProd : P Ty := do
  let a ← pApp
  match ← peek with
  | some .times => adv; return .prod a (← pProd)
  | _ => return a

partial def pApp : P Ty := do
  match ← peek with
  | some (.id n) =>
    adv
    let mut args : Array Ty := #[]
    repeat
      match ← peek with
      | some (.id m) => adv; args := args.push (.con m #[])
      | some .lp => args := args.push (← pAtom)
      | _ => break
    return .con n args
  | _ => pAtom

partial def pAtom : P Ty := do
  match ← peek with
  | some .lp =>
    adv
    let t ← pProd
    match ← peek with
    | some .rp => adv; return t
    | _ => failure
  | some (.id n) => adv; return .con n #[]
  | _ => failure
end

/-- Parse a type written in a `.lig`. -/
partial def parse (src : String) : Ty :=
  let s := src.trimAscii.toString
  if s.startsWith "{" && s.endsWith "}" && s.contains '/' then
    -- `{ x : T // p }`
    match (s.drop 1).toString.splitOn "//" with
    | lhs :: _ :: _ =>
      match lhs.splitOn ":" with
      | _ :: rest@(_ :: _) => .sub (parse (":".intercalate rest))
      | _ => .other src
    | _ => .other src
  else
  match lex src with
  | none => .other src
  | some ts =>
    match (pProd.run (ts, 0)) with
    | some (t, (_, i)) => if i == ts.size then t else .other src
    | none => .other src

/-- The head type constructor's name, if any. -/
def head? : Ty → Option String
  | .con n _ => some n
  | .sub _ => some "Subtype"
  | _ => none

end Ty

end Emit.Rust
