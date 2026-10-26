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
Hand-written AST and token type for the IMP `.lig` example — a small imperative
language (arithmetic + boolean expressions + commands). The generated parser
imports this. Token constructor names match the `%token` names in `imp.lig`.
-/


@[expose] public section

namespace Imp

/-- Arithmetic expressions. -/
inductive AExp where
  | num : Int → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  deriving Repr, Inhabited, DecidableEq

/-- Boolean expressions. -/
inductive BExp where
  | tru : BExp
  | fls : BExp
  | le : AExp → AExp → BExp
  | eq : AExp → AExp → BExp
  | not : BExp → BExp
  | and : BExp → BExp → BExp
  deriving Repr, Inhabited, DecidableEq

/-- Commands (statements). -/
inductive Com where
  | skip : Com
  | assign : String → AExp → Com
  | seq : Com → Com → Com
  | ite : BExp → Com → Com → Com
  | while : BExp → Com → Com
  deriving Repr, Inhabited, DecidableEq

/-- IMP tokens. Names match `imp.lig`'s `%token` declarations.-/
inductive Tok where
  | SKIP | IF | THEN | ELSE | WHILE | DO
  | TRUE | FALSE | NOT | AND
  | ASSIGN | SEMI | LPAR | RPAR
  | PLUS | MINUS | TIMES
  | LE | EQ
  | ID : String → Tok
  | NUM : Int → Tok
  | EOF
  deriving Repr, Inhabited, DecidableEq

end Imp
