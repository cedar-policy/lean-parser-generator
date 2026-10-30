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
The emission rules of the Rust backend, as data (docs/RUST_PARSER.md).

If it is not in this file or in the shape rules of `Classify.lean`, an action is not
emitted. Nothing here is trusted: the Rust that results is checked against the Lean
specification by the verification step, so a wrong entry makes a proof fail rather
than a parser wrong.
-/
public import LeanParserGenerator.Emit.Rust.Resolve
public import LeanParserGenerator.Lexer.Regex


@[expose] public section

namespace Emit.Rust

/-- A Lean library function with a Rust counterpart. -/
structure KnownFn where
  /-- The full Lean name. -/
  name : String
  /-- Number of explicit arguments, including the receiver of a method. -/
  arity : Nat
  /-- The Rust counterpart, for the report. -/
  rust : String
  /-- The result type, when the analysis needs it to type a method chain. -/
  ret : Option Ty := none
  /-- Where the Lean function is meaningful, as a regex over the argument string, if it
      is partial. `Domain.lean` checks that a lexer rule's language is inside it
      (decision D10). -/
  domain : Option Lexer.Regex := none
  /-- The domain as the user would write it, for reports. -/
  domainText : String := ""
  deriving Repr

/-- The known functions (decision D4: a function is emitted only if listed here). -/
def knownFns : List KnownFn := [
  { name := "String.toNat!", arity := 1, rust := "parse_decimal(&str) -> u64",
    ret := some (.con "Nat" #[]), domain := some (Lexer.Regex.plus (Lexer.Regex.range '0' '9')), domainText := "[0-9]+" },
  { name := "String.toInt!", arity := 1, rust := "parse_decimal_signed(&str) -> i64",
    ret := some (.con "Int" #[]), domain := some (Lexer.Regex.cat (Lexer.Regex.opt (Lexer.Regex.char '-'))
      (Lexer.Regex.plus (Lexer.Regex.range '0' '9'))), domainText := "-?[0-9]+" },
  { name := "String.length", arity := 1, rust := "str.chars().count()",
    ret := some (.con "Nat" #[]) },
  { name := "String.replace", arity := 3, rust := "str.replace(pat, to)",
    ret := some (.con "String" #[]) },
  { name := "ToString.toString", arity := 1, rust := "Display for the Rust counterpart of the type",
    ret := some (.con "String" #[]) },
  -- A subtype is represented by its base type; the predicate is a proof obligation.
  { name := "Subtype.val", arity := 1, rust := "identity" } ]

/-- Names from `Init` that are reached through `export` and so are not found by
    `Environment.find?` under the name an action uses. -/
def builtinAliases : List (String × String) := [
  ("toString", "ToString.toString"), ("some", "Option.some"), ("none", "Option.none"),
  ("true", "Bool.true"), ("false", "Bool.false"),
  ("List.nil", "List.nil"), ("List.cons", "List.cons") ]

end Emit.Rust
