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
public import LeanParserGenerator.Runtime.Span
/-
The abstract syntax of the `rustactions.lig` fixture: a small expression language with
`let` and `print` statements. The Rust actions of the grammar build a different, hand-written
AST (`rust/src/ast.rs`), borrowing its strings from the source.
-/


@[expose] public section

namespace RustActions

inductive Op where
  | add | sub | mul
  deriving Repr, BEq, Inhabited

inductive Expr where
  | num : Int → Expr
  | var : String → Expr
  | str : String → Expr
  | len : Nat → Expr
  | neg : Expr → Expr
  | bin : Op → Expr → Expr → Expr
  | call : String → List Expr → Expr
  | cond : Expr → Expr → Option Expr → Expr
  | pair : Expr × Expr → Expr
  | triple : Expr × Expr × Expr → Expr
  | located : String → Runtime.Span → Expr
  deriving Repr, Inhabited

structure Binding where
  name : String
  value : Expr
  index : Nat
  deriving Repr, Inhabited

inductive Stmt where
  | bind : Binding → Stmt
  | print : Expr → Stmt
  deriving Repr, Inhabited

/-- A type alias, which the Rust generator unfolds. -/
abbrev Stmts := List Stmt

structure Program where
  stmts : Stmts
  count : Nat
  deriving Repr, Inhabited

end RustActions
