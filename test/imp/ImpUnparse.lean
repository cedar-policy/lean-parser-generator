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
public import imp.ImpAst

@[expose] public section

namespace ImpUnparse

open Imp

mutual

/-- Commands in the shape produced by `com ::= stmt SEMI com | stmt`.
    Unlike `Imp.Com`, a sequence cannot itself occur as its left statement. -/
inductive PrintableCom where
  | last : PrintableStmt → PrintableCom
  | seq : PrintableStmt → PrintableCom → PrintableCom
  deriving Repr, DecidableEq

inductive PrintableStmt where
  | skip
  | assign : String → AExp → PrintableStmt
  | ite : BExp → PrintableCom → PrintableCom → PrintableStmt
  | while : BExp → PrintableCom → PrintableStmt
  deriving Repr, DecidableEq

end

mutual

def PrintableCom.toCom : PrintableCom → Com
  | .last stmt => stmt.toCom
  | .seq stmt rest => .seq stmt.toCom rest.toCom

def PrintableStmt.toCom : PrintableStmt → Com
  | .skip => .skip
  | .assign name value => .assign name value
  | .ite cond thenBranch elseBranch => .ite cond thenBranch.toCom elseBranch.toCom
  | .while cond body => .while cond body.toCom

end

/-- Fully parenthesized arithmetic printer. The extra parentheses let either
    child inhabit the precedence level required by its production. -/
def unparseAExp : AExp → List Tok
  | .num n => [.NUM n]
  | .var name => [.ID name]
  | .add lhs rhs =>
      [.LPAR] ++
        (unparseAExp lhs ++ [.PLUS] ++ ([.LPAR] ++ unparseAExp rhs ++ [.RPAR])) ++
        [.RPAR]
  | .sub lhs rhs =>
      [.LPAR] ++
        (unparseAExp lhs ++ [.MINUS] ++ ([.LPAR] ++ unparseAExp rhs ++ [.RPAR])) ++
        [.RPAR]
  | .mul lhs rhs =>
      [.LPAR] ++
        (([.LPAR] ++ unparseAExp lhs ++ [.RPAR]) ++ [.TIMES] ++
          ([.LPAR] ++ unparseAExp rhs ++ [.RPAR])) ++
        [.RPAR]

/-- Fully parenthesized boolean printer. -/
def unparseBExp : BExp → List Tok
  | .tru => [.TRUE]
  | .fls => [.FALSE]
  | .le lhs rhs =>
      [.LPAR] ++ (unparseAExp lhs ++ [.LE] ++ unparseAExp rhs) ++ [.RPAR]
  | .eq lhs rhs =>
      [.LPAR] ++ (unparseAExp lhs ++ [.EQ] ++ unparseAExp rhs) ++ [.RPAR]
  | .not value =>
      [.LPAR] ++ ([.NOT] ++ ([.LPAR] ++ unparseBExp value ++ [.RPAR])) ++ [.RPAR]
  | .and lhs rhs =>
      [.LPAR] ++
        (([.LPAR] ++ unparseBExp lhs ++ [.RPAR]) ++ [.AND] ++
          ([.LPAR] ++ unparseBExp rhs ++ [.RPAR])) ++
        [.RPAR]

mutual

def unparsePrintableCom : PrintableCom → List Tok
  | .last stmt => unparsePrintableStmt stmt
  | .seq stmt rest => unparsePrintableStmt stmt ++ [.SEMI] ++ unparsePrintableCom rest

def unparsePrintableStmt : PrintableStmt → List Tok
  | .skip => [.SKIP]
  | .assign name value => [.ID name] ++ [.ASSIGN] ++ unparseAExp value
  | .ite cond thenBranch elseBranch =>
      [.IF] ++ unparseBExp cond ++ [.THEN] ++ [.LPAR] ++
        unparsePrintableCom thenBranch ++ [.RPAR] ++ [.ELSE] ++ [.LPAR] ++
        unparsePrintableCom elseBranch ++ [.RPAR]
  | .while cond body =>
      [.WHILE] ++ unparseBExp cond ++ [.DO] ++ [.LPAR] ++
        unparsePrintableCom body ++ [.RPAR]

end

/-- A total printer for the broader `Com` type. It is faithful on values in the
    image of `PrintableCom.toCom`; left-nested sequences are reassociated by the
    grammar and therefore receive no universal certificate. -/
def unparseCom : Com → List Tok
  | .skip => [.SKIP]
  | .assign name value => [.ID name, .ASSIGN] ++ unparseAExp value
  | .seq first rest => unparseCom first ++ [.SEMI] ++ unparseCom rest
  | .ite cond thenBranch elseBranch =>
      [.IF] ++ unparseBExp cond ++ [.THEN, .LPAR] ++ unparseCom thenBranch ++
        [.RPAR, .ELSE, .LPAR] ++ unparseCom elseBranch ++ [.RPAR]
  | .while cond body =>
      [.WHILE] ++ unparseBExp cond ++ [.DO, .LPAR] ++ unparseCom body ++ [.RPAR]

end ImpUnparse
