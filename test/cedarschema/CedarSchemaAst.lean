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
`test/cedar-schema/CedarSchemaAst.lean` — the Cedar schema concrete syntax tree
and token type.

This mirrors `cedar-policy-core/src/validator/cedar_schema/ast.rs` and the
productions in `grammar.lalrpop`, omitting source-location `Node`/`Loc`
wrappers and the annotation-deduplication error path (annotations are kept as a
plain list). Constructor names follow Lean conventions. LALRPOP macros
(`Comma<E>`, `NonEmptyComma<E>`, `Annotated<E>`) are expanded in the grammar
into explicit list productions; the AST only stores the resulting values.
-/


@[expose] public section

namespace CedarSchema

/-- A schema identifier. `grammar.lalrpop`'s `Ident` rejects reserved words with
a `=>?` error; that error path is dropped here, so any accepted `AnyIdent`
becomes an `Ident`. -/
inductive Ident where
  | namespaceKw | entityKw | setKw | appliesToKw
  | principalKw | actionKw | resourceKw | contextKw
  | attributesKw | tagsKw | boolKw | longKw | stringKw | typeKw | inKw | enumKw
  | ident : String → Ident
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A namespaced path: `prefixPath` holds the namespace prefix (most significant
first), `basename` the final component. Mirrors `PathInternal`. -/
structure Path where
  prefixPath : List Ident
  basename : Ident
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Path

/-- `Path::single`: a path with an empty namespace. -/
def single (basename : Ident) : Path := ⟨[], basename⟩

/-- `Path::new`: most significant name first, `basename` last. -/
def new (basename : Ident) (prefixPath : List Ident) : Path := ⟨prefixPath, basename⟩

end Path

namespace Ident

/-- Render an identifier back to its source text, matching `Id`/`AnyId`'s
`to_smolstr`. Used by `Name := Ident`. -/
def toString : Ident → String
  | .namespaceKw => "namespace"
  | .entityKw => "entity"
  | .setKw => "Set"
  | .appliesToKw => "appliesTo"
  | .principalKw => "principal"
  | .actionKw => "action"
  | .resourceKw => "resource"
  | .contextKw => "context"
  | .attributesKw => "attributes"
  | .tagsKw => "tags"
  | .boolKw => "Bool"
  | .longKw => "Long"
  | .stringKw => "String"
  | .typeKw => "type"
  | .inKw => "in"
  | .enumKw => "enum"
  | .ident s => s

end Ident

/-- `Name := Ident` maps an identifier to its string form. -/
def identToString (i : Ident) : String := i.toString

/-- Build a `Path` from a nonempty component list (most significant first): the
last element is the basename, the rest is the prefix. Mirrors the way
`PathInline` accumulates idents. -/
def pathFromComponents : List Ident → Path
  | [] => default
  | components =>
      match components.reverse with
      | [] => default
      | basename :: revPrefix => ⟨revPrefix.reverse, basename⟩

/-- The basename of a component list (its last element). -/
def pathBasename : List Ident → Ident
  | [] => default
  | components => (pathFromComponents components).basename

/-- An entity UID string (`Eid`). -/
structure Eid where
  value : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A schema entity reference name (`QualName`): either an unqualified string or
a `Path :: String`. -/
inductive QualName where
  | unqualified : String → QualName
  | qualified : Path → String → QualName
  deriving Repr, DecidableEq, BEq, Inhabited

/-- One annotation `@key` or `@key("value")`. The dedup step in `ast.rs` is
omitted; annotations are stored in source order. -/
structure Annotation where
  key : Ident
  value : Option String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Wraps a declaration with its annotations (`Annotated<T>`). -/
structure Annotated (α : Type) where
  data : α
  annotations : List Annotation
  deriving Repr, BEq

/-- `principal` or `resource` (`PR`). -/
inductive PR where
  | principal | resource
  deriving Repr, DecidableEq, BEq, Inhabited

mutual

/-- Schema type (`Type`). -/
inductive SType where
  | ident : Path → SType
  | set : SType → SType
  | record : List (Annotated AttrDecl) → SType
  deriving Repr, BEq

/-- One attribute declaration `name ['?'] ':' Type` (`AttrDecl`). `required` is
`true` unless a `?` is present. -/
inductive AttrDecl where
  | mk : (name : String) → (required : Bool) → (ty : SType) → AttrDecl
  deriving Repr, BEq

end

/-- One `appliesTo` clause (`AppDecl`). Context carries either a `Path` or a
record of attribute declarations. -/
inductive AppDecl where
  | pr : PR → Option (List Path) → AppDecl
  | contextPath : Path → AppDecl
  | contextRecord : List (Annotated AttrDecl) → AppDecl
  deriving Repr, BEq

/-- `NonEmpty::collect(ets.into_iter())`: `none` when the list is empty,
`some` otherwise. Used for `PRAppDecl.entity_tys`. -/
def someIfNonEmpty {α : Type} : List α → Option (List α)
  | [] => none
  | xs => some xs

/-- A standard entity declaration (`StandardEntityDecl`). -/
structure StandardEntityDecl where
  names : List Ident
  memberOfTypes : List Path
  attrs : List (Annotated AttrDecl)
  tags : Option SType
  deriving Repr, BEq

/-- An enumerated entity declaration (`EnumEntityDecl`). -/
structure EnumEntityDecl where
  names : List Ident
  choices : List Eid
  deriving Repr, BEq

/-- Entity declaration, standard or enum (`EntityDecl`). -/
inductive EntityDecl where
  | standard : StandardEntityDecl → EntityDecl
  | enum : EnumEntityDecl → EntityDecl
  deriving Repr, BEq

/-- An action declaration (`ActionDecl`). -/
structure ActionDecl where
  names : List String
  parents : Option (List QualName)
  appDecls : Option (List AppDecl)
  deriving Repr, BEq

/-- A common-type declaration (`TypeDecl`). -/
structure TypeDecl where
  name : Ident
  definition : SType
  deriving Repr, BEq

/-- A schema declaration (`Declaration`). -/
inductive Declaration where
  | entity : EntityDecl → Declaration
  | action : ActionDecl → Declaration
  | type : TypeDecl → Declaration
  deriving Repr, BEq

/-- A namespace (`Namespace`): an optional name and its annotated declarations. -/
structure Namespace where
  name : Option Path
  decls : List (Annotated Declaration)
  deriving Repr, BEq

/-- A whole schema (`Schema` = `Vec<Annotated<Namespace>>`). -/
structure Schema where
  namespaces : List (Annotated Namespace)
  deriving Repr, BEq

-- Tokens are generated into `CedarSchemaLexer` from the `%token` declarations
-- (docs/DESIGN.md §9); the parser imports that module for `Tok`.

end CedarSchema
