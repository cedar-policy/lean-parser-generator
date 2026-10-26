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
`test/cedarentities/CedarEntitiesAst.lean` — the concrete syntax tree and token
type for the Cedar entity-data syntax (RFC 0104,
`text/0104-entity-data-syntax.md`).

The tree mirrors the RFC grammar, omitting source-location wrappers and the
error-recovery nodes a tolerant parser would carry. Constructor names follow
Lean conventions. Annotations are not part of RFC 0104 (they are listed as a
"potential future addition"), but the `Annotated` wrapper is kept so an instance
declaration can carry an (currently always empty) annotation list without a
later AST change.
-/


@[expose] public section

namespace Entities

/-- Reserved words. `IDENTIFIER` carries a proof it is none of these, so the
lexer never produces an identifier that collides with a keyword. -/
def keywords : List String :=
  ["namespace", "instance", "in", "tags", "true", "false"]

/-- Application-defined annotation data. Not produced by the RFC 0104 grammar
yet; retained so instances can be wrapped uniformly. -/
structure Annotation where
  key : String
  value : Option String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Wraps a declaration with its annotations (`Annotated<T>`). -/
structure Annotated (α : Type) where
  data : α
  annotations : List Annotation
  deriving Repr, BEq, Inhabited

/-- An entity reference `Path '::' STR`, e.g. `PhotoApp::User::"alice"`.
`ty_path` is the entity type (most significant component first) and `id` is the
quoted entity id, with the surrounding quotes stripped. -/
structure EntityReference where
  ty_path : List String
  id : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- An integer literal as written: a sign flag and the raw magnitude. The
lexer/parser store the magnitude as an arbitrary-precision `Nat` so no
information is lost at parse time; converting to a bounded `Int64` is a separate
transformation (`IntLit.toInt64?`) that can reject out-of-range values. -/
structure IntLit where
  negative : Bool
  magnitude : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

namespace IntLit

/-- The mathematical (unbounded) integer this literal denotes. -/
def toInt (n : IntLit) : Int :=
  if n.negative then -(Int.ofNat n.magnitude) else Int.ofNat n.magnitude

/-- Convert to a signed 64-bit integer, returning `none` when the literal is out
of the `Int64` range `[-2^63, 2^63-1]`. This is where a bad magnitude in the
source is caught, rather than silently wrapping. -/
def toInt64? (n : IntLit) : Option Int64 :=
  if n.negative then
    -- Negatives allow magnitude up to 2^63.
    if n.magnitude ≤ 9223372036854775808 then some (-(Int64.ofNat n.magnitude))
    else none
  else
    if n.magnitude ≤ 9223372036854775807 then some (Int64.ofNat n.magnitude)
    else none

end IntLit

-- The main entity value grammar. `Value` in the RFC is left as a TODO scoped
-- down from the policy grammar; the shape below is the value subset the JSON
-- entity format and the photo-app example use: literals, entity references,
-- sets, records, and extension calls (`ip("…")`, `datetime("…")`).
mutual
inductive EntityValue where
  | evLong : IntLit → EntityValue
  | evString : String → EntityValue
  | evBool : Bool → EntityValue
  | evEntityRef : EntityReference → EntityValue
  | evSet : List EntityValue → EntityValue
  | evRecord : List (String × EntityValue) → EntityValue
  /-- An extension call `fn(args)`; `fn` is the (possibly namespaced) function
  path, most significant component first. -/
  | evExtCall : List String → List EntityValue → EntityValue
  deriving Repr, Inhabited, BEq
end

/-- One instance declaration:
`'instance' EntityRef ['in' EntityRefOrRefs] [['='] Record] ['tags' Tags] ';'`. -/
structure EntityInstance where
  entity_ref : EntityReference
  parents : List EntityReference
  attrs : List (String × EntityValue)
  tags : List (String × EntityValue)
  deriving Repr, Inhabited, BEq

/-- A named namespace block `'namespace' Path '{' … '}'`. -/
structure EntitiesNamespace where
  name : Option String
  instances : List (Annotated EntityInstance)
  deriving Repr, Inhabited, BEq

/-- A top-level item: either a namespace block or a single top-level instance
declaration. Keeping both in one list preserves source order and the RFC's
interleaving of `Namespace` and `EntityInstanceDeclaration`. -/
inductive EntitiesDecl where
  | namespaceDecl : EntitiesNamespace → EntitiesDecl
  | instanceDecl : Annotated EntityInstance → EntitiesDecl
  deriving Repr, Inhabited, BEq

/-- A whole entity-data file. -/
structure Entities where
  decls : List EntitiesDecl
  deriving Repr, Inhabited, BEq

-- Helpers used by the grammar's semantic actions, kept out of the actions so
-- the `.lig` reads close to the RFC productions.

/-- Render a `Path` (component list, most significant first) joined by `::`. -/
def pathToString (components : List String) : String :=
  String.intercalate "::" components

/-- Build an `EntityReference` from a type-path and quoted id. -/
def mkEntityRef (ty_path : List String) (id : String) : EntityReference :=
  ⟨ty_path, id⟩

/-- Wrap an instance with an empty annotation list. -/
def annotate (inst : EntityInstance) : Annotated EntityInstance :=
  ⟨inst, []⟩

/-- A non-negative long literal from a magnitude. -/
def mkLong (magnitude : Nat) : EntityValue :=
  .evLong ⟨false, magnitude⟩

/-- A negative long literal from a magnitude. -/
def mkNegLong (magnitude : Nat) : EntityValue :=
  .evLong ⟨true, magnitude⟩

end Entities
