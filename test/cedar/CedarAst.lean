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
`test/cedar/CedarAst.lean` — the Cedar concrete syntax tree and token type.

This mirrors `cedar-policy-core/src/parser/cst.rs`, omitting source-location
`Node` wrappers, recoverable `Option` nodes, and tolerant-parser error variants.
Constructor names follow Lean conventions; the tree retains every precedence
layer and source-level operator rather than collapsing to Cedar's semantic AST.
-/


@[expose] public section

namespace Cedar

public def keywords : List String :=
  ["principal", "action", "resource", "context", "true", "false",
   "permit", "forbid", "when", "unless", "in", "has", "like", "is",
   "if", "then", "else"]

/-- Any Cedar identifier, including reserved words accepted by CST productions. -/
inductive Ident where
  | principal | action | resource | context
  | trueIdent | falseIdent
  | permit | forbid | when | unless | inIdent | has | like | is
  | ifIdent | thenIdent | elseIdent
  | ident : String → Ident
  | invalid : String → Ident
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A regular or invalid quoted string. The parser only constructs `string`. -/
inductive Str where
  | string : String → Str
  | invalid : String → Str
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A possibly namespaced name; `path` excludes the final component. -/
structure Name where
  path : List Ident
  name : Ident
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Name

/-- Form a name from a nonempty list of components. -/
def fromComponents : List Ident → Name
  | [] => default
  | components =>
      match components.reverse with
      | [] => default
      | name :: reversePath => ⟨reversePath.reverse, name⟩

end Name

/-- Relational operators, including invalid single `=` retained by the CST. -/
inductive RelOp where
  | less | lessEq | greaterEq | greater | notEq | eq | inOp | invalidSingleEq
  deriving Repr, DecidableEq, BEq, Inhabited

inductive AddOp where | plus | minus
  deriving Repr, DecidableEq, BEq, Inhabited

inductive MultOp where | times | divide | mod
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A counted run of unary operators; five or more uses an overflow marker. -/
inductive NegOp where
  | bang : Nat → NegOp
  | overBang
  | dash : Nat → NegOp
  | overDash
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Raw literal values. -/
inductive Literal where
  | trueLit | falseLit
  | num : Nat → Literal
  | str : Str → Literal
  deriving Repr, DecidableEq, BEq, Inhabited

/-- One field initializer in a structured entity reference. -/
structure RefInit where
  field : Ident
  literal : Literal
  deriving Repr, DecidableEq, BEq, Inhabited

/-- An entity UID or structured entity reference. -/
inductive Ref where
  | uid : Name → Str → Ref
  | ref : Name → List RefInit → Ref
  deriving Repr, DecidableEq, BEq, Inhabited

inductive Slot where
  | principal | resource
  | other : String → Slot
  deriving Repr, DecidableEq, BEq, Inhabited

mutual

/-- The outer successful-expression CST node. Error nodes are intentionally omitted. -/
inductive Expr where
  | expr : ExprImpl → Expr
  deriving Repr, BEq

/-- Successful expression payload wrapper from the Cedar CST. -/
inductive ExprImpl where
  | mk : ExprData → ExprImpl
  deriving Repr, BEq

inductive ExprData where
  | or : Or → ExprData
  | ifThenElse : Expr → Expr → Expr → ExprData
  deriving Repr, BEq

/-- Logical-or precedence layer. -/
inductive Or where
  | mk : And → List And → Or
  deriving Repr, BEq

/-- Logical-and precedence layer. -/
inductive And where
  | mk : Relation → List Relation → And
  deriving Repr, BEq

inductive Relation where
  | common : Add → List (RelOp × Add) → Relation
  | has : Add → Add → Relation
  | like : Add → Add → Relation
  | isIn : Add → Add → Option Add → Relation
  deriving Repr, BEq

inductive Add where
  | mk : Mult → List (AddOp × Mult) → Add
  deriving Repr, BEq

inductive Mult where
  | mk : Unary → List (MultOp × Unary) → Mult
  deriving Repr, BEq

inductive Unary where
  | mk : Option NegOp → Member → Unary
  deriving Repr, BEq

inductive Member where
  | mk : Primary → List MemAccess → Member
  deriving Repr, BEq

inductive MemAccess where
  | field : Ident → MemAccess
  | call : List Expr → MemAccess
  | index : Expr → MemAccess
  deriving Repr, BEq

inductive Primary where
  | literal : Literal → Primary
  | ref : Ref → Primary
  | name : Name → Primary
  | slot : Slot → Primary
  | expr : Expr → Primary
  | exprList : List Expr → Primary
  | record : List RecInit → Primary
  deriving Repr, BEq

inductive RecInit where
  | mk : Expr → Expr → RecInit
  deriving Repr, BEq

end

namespace Add

/-- Build the CST `Add` wrapper around an identifier and member accesses.
Used by LALRPOP's special `HAS IF { MemAccess }` diagnostic production. -/
def fromIdent (identifier : Ident) (access : List MemAccess := []) : Add :=
  .mk (.mk (.mk none (.mk (.name ⟨[], identifier⟩) access)) []) []

end Add

namespace Expr

/-- Build the full precedence wrapper around a primary expression. -/
def fromPrimary (primary : Primary) : Expr :=
  .expr (.mk (.or (.mk (.mk (.common (.mk (.mk (.mk none (.mk primary [])) []) []) []) []) [])))

/-- Build the full precedence wrapper around a bare identifier. -/
def fromIdent (identifier : Ident) : Expr := fromPrimary (.name ⟨[], identifier⟩)

end Expr

/-- Application-defined annotation data. -/
structure Annotation where
  key : Ident
  value : Option Str
  deriving Repr, BEq

/-- Policy condition. Empty/recovered expressions are intentionally omitted. -/
structure Cond where
  cond : Ident
  expr : Expr
  deriving Repr, BEq

/-- One scope variable definition in a policy head. -/
structure VariableDef where
  variableName : Ident
  unusedTypeName : Option Name
  entityType : Option Add
  ineq : Option (RelOp × Expr)
  deriving Repr, BEq

structure PolicyImpl where
  annotations : List Annotation
  effect : Ident
  variables : List VariableDef
  conds : List Cond
  deriving Repr, BEq

/-- A successful policy CST node. Tolerant-parser error nodes are omitted. -/
inductive Policy where
  | policy : PolicyImpl → Policy
  deriving Repr, BEq

structure Policies where
  policies : List Policy
  deriving Repr, BEq

end Cedar
