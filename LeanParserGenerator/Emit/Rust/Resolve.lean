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
Name resolution for action analysis (docs/RUST_PARSER.md, decision D2).

An action such as `Policy.mk a b c` is a constructor application only if `Policy.mk`
is a constructor. The classifier asks a `Resolver`, which answers from the Lean
environment of the modules the `.lig` header imports, under the header's `open`s.
The resolver is a function, so the classifier can be tested without an environment
and a different source of truth can replace the environment later.
-/
public import Lean
public import LeanParserGenerator.Emit.Rust.Ty


@[expose] public section

namespace Emit.Rust

/-- What a global name is. Types are the explicit binders' types only. -/
inductive NameKind where
  /-- A constructor of the inductive type `induct`, with its explicit fields. -/
  | ctor (induct : String) (fields : Array Ty)
  /-- A function (any definition that is not a projection), with explicit parameters. -/
  | fn (params : Array Ty)
  /-- A structure projection function. -/
  | proj
  /-- An inductive type. -/
  | type
  /-- Anything else. -/
  | other
  deriving Repr, Inhabited

/-- A resolved global name: its full name and what it is. -/
structure Resolved where
  full : String
  kind : NameKind
  deriving Repr, Inhabited

/-- `find opens name` looks `name` up as written, then under each opened namespace. -/
structure Resolver where
  find : List String → String → Option Resolved
  /-- The field names of a structure, by full type name, in declaration order. -/
  fields : String → Option (Array String) := fun _ => none

namespace Resolver

/-- A resolver that knows nothing. -/
def empty : Resolver := { find := fun _ _ => none }

/-- Try `r` first, then `s`. -/
def orElse (r s : Resolver) : Resolver :=
  { find := fun opens n => (r.find opens n).orElse fun _ => s.find opens n,
    fields := fun n => (r.fields n).orElse fun _ => s.fields n }

open Lean in
/-- A Lean type as a `Ty`. -/
partial def tyOfExpr (e : Expr) : Ty :=
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if n == ``Prod && args.size == 2 then .prod (tyOfExpr args[0]!) (tyOfExpr args[1]!)
    else .con n.toString (args.map tyOfExpr)
  | _ => .other "_"

open Lean in
/-- The types of the explicit binders of `type`, after skipping `skip` binders. -/
partial def explicitDomains (type : Expr) (skip : Nat) : Array Ty :=
  let rec go (t : Expr) (skip : Nat) (acc : Array Ty) : Array Ty :=
    match t with
    | .forallE _ dom body bi =>
      if skip > 0 then go body (skip - 1) acc
      else if bi.isExplicit then go body 0 (acc.push (tyOfExpr dom))
      else go body 0 acc
    | _ => acc
  go type skip #[]

open Lean in
/-- The resolver for an environment. -/
def ofEnv (env : Environment) : Resolver where
  fields n :=
    if isStructure env n.toName then some ((getStructureFields env n.toName).map (·.toString))
    else none
  find opens name :=
    let cands := name :: opens.map (· ++ "." ++ name)
    cands.findSome? fun full =>
      match env.find? full.toName with
      | none => none
      | some ci =>
        let kind : NameKind :=
          match ci with
          | .ctorInfo c => .ctor c.induct.toString (explicitDomains c.type c.numParams)
          | .inductInfo _ => .type
          | .defnInfo _ | .opaqueInfo _ | .thmInfo _ =>
            if (env.getProjectionFnInfo? full.toName).isSome then .proj
            else .fn (explicitDomains ci.type 0)
          | _ => .other
        some ⟨full, kind⟩

open Lean in
/-- Import `mods` and resolve against the result. The module search path comes from
    `LEAN_PATH` (as set by `lake env`) and the toolchain. -/
def ofImports (mods : List String) : IO (Except String Resolver) := do
  try
    initSearchPath (← findSysroot)
    let env ← importModules (mods.map fun m => { module := m.toName }).toArray {}
      (trustLevel := 1024)
    return .ok (ofEnv env)
  catch e =>
    return .error (toString e)

end Resolver

end Emit.Rust
