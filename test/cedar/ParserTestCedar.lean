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
public import cedar.CedarLexer
public import cedar.CedarParser
-- `native_decide`/`#eval` reduce the generated parser & lexer, so they are meta-imported.
meta import cedar.CedarLexer
meta import cedar.CedarParser


public section

open Lexer Cedar CedarParser

/-! Cedar lexer/parser regressions against `cedar-spec`'s `grammar.lalrpop`.
Positions and recoverable parser-error nodes are intentionally outside this port.
Named Boolean checks avoid `#guard`'s fragile command/layout parsing for nested
CST pattern matches. -/

private def parseStr (input : String) : Option Policies :=
  input |> CedarLexer.tokenize |>.toOption.bind (parse · 30)

private def chkStr (source : String) (expected : Option Policies) : Bool :=
  parseStr source == expected

private def scopeVariable (name : Ident) : VariableDef :=
  VariableDef.mk name none none none

private def policy (effect : Ident) (scopeVariables : List VariableDef)
    (conds : List Cond := []) (annotations : List Annotation := []) : Policy :=
  .policy (PolicyImpl.mk annotations effect scopeVariables conds)

private def numMult (number : Nat) : Mult :=
  .mk (.mk none (.mk (.literal (.num number)) [])) []

private def numAdd (number : Nat) : Add := .mk (numMult number) []

private def conditionExpr (source : String) : Option Expr := do
  let ⟨[Policy.policy parsed]⟩ ← parseStr ("permit(principal) when { " ++ source ++ " };")
    | none
  let [condition] := parsed.conds | none
  some condition.expr

private def rootRelation : Expr → Option Relation
  | .expr (.mk (.or (.mk (.mk relation []) []))) => some relation
  | _ => none

private def rootUnary : Expr → Option Unary
  | .expr (.mk (.or (.mk (.mk (.common (.mk (.mk unary []) []) []) []) []))) => some unary
  | _ => none

private def rootPrimary (expression : Expr) : Option Primary := do
  let .mk none (.mk primary []) ← rootUnary expression | none
  some primary

/-! ## Tokenizer parity -/

private def tokenizerParity : Bool :=
  match CedarLexer.tokenize
      "permit ?principal ?resource ?other foo 123 \"a\\\"b\" == != <= >= :: =" with
  | .ok tokens => tokens ==
      [.PERMIT, .PRINCIPAL_SLOT, .RESOURCE_SLOT, .OTHER_SLOT "?other",
        .IDENTIFIER "foo", .NUMBER 123, .STRINGLIT "a\\\"b", .EQ, .NEQ, .LEQ,
        .GEQ, .COLONCOLON, .SINGLE_EQ, .EOF]
  | .error _ => false

example : tokenizerParity = true := by native_decide

private def commentParity : Bool :=
  match CedarLexer.tokenize "// comment\r\ntrue" with
  | .ok tokens => tokens == [.TRUE, .EOF]
  | .error _ => false

example : commentParity = true := by native_decide

private def multilineStringParity : Bool :=
  match CedarLexer.tokenize "\"line one\nline two\"" with
  | .ok tokens => tokens == [.STRINGLIT "line one\nline two", .EOF]
  | .error _ => false

example : multilineStringParity = true := by native_decide

private def escapedRawNewlineRejected : Bool :=
  match CedarLexer.tokenize "\"\\\n\"" with
  | .error _ => true
  | .ok _ => false

example : escapedRawNewlineRejected = true := by native_decide

/-! ## Policy, annotation, identifier, and comma-list structure -/

private def basicPolicy : Bool :=
  chkStr "permit(principal, action, resource);"
    (some ⟨[policy .permit
      [scopeVariable .principal, scopeVariable .action, scopeVariable .resource]]⟩)

example : basicPolicy = true := by native_decide

private def annotationAndTrailingComma : Bool :=
  match parseStr "@id(\"v\") permit(principal,);" with
  | some ⟨[Policy.policy parsed]⟩ =>
      parsed.annotations == [Annotation.mk (.ident "id") (some (.string "v"))]
  | _ => false

example : annotationAndTrailingComma = true := by native_decide

/-- Effects and condition introducers are `AnyIdent` in the CST grammar; semantic
validation, not parsing, rejects unexpected identifiers. -/
private def permissiveCstIdentifiers : Bool :=
  match parseStr "custom(principal) customCondition { true };" with
  | some ⟨[Policy.policy parsed]⟩ =>
      parsed.effect == .ident "custom" &&
        (match parsed.conds with
        | [condition] => condition.cond == .ident "customCondition"
        | _ => false)
  | _ => false

example : permissiveCstIdentifiers = true := by native_decide

/-- Deprecated `: Name`, current `is Add`, relation constraints, and a trailing
comma all have distinct CST fields. -/
private def scopeFields : Bool :=
  match parseStr
      "permit(principal: Old::Type is New::Type in Group::\"admins\",);" with
  | some ⟨[Policy.policy parsed]⟩ =>
      match parsed.variables with
      | [scope] =>
          scope.unusedTypeName.isSome && scope.entityType.isSome && scope.ineq.isSome
      | _ => false
  | _ => false

example : scopeFields = true := by native_decide

private def adviceIsOrdinaryIdentifier : Bool :=
  match parseStr "permit(principal) advice { true };" with
  | some ⟨[Policy.policy parsed]⟩ =>
      match parsed.conds with
      | [condition] => condition.cond == .ident "advice"
      | _ => false
  | _ => false

example : adviceIsOrdinaryIdentifier = true := by native_decide

private def emptyConditionRejected : Bool :=
  (parseStr "permit(principal) when {};").isNone

example : emptyConditionRejected = true := by native_decide

/-! ## Expression precedence and CST preservation -/

private def arithmeticPrecedence : Bool :=
  match conditionExpr "1 + 2 <= 4" >>= rootRelation with
  | some (.common (.mk initial [(.plus, plusTwo)]) [(.lessEq, four)]) =>
      initial == numMult 1 && plusTwo == numMult 2 && four == numAdd 4
  | _ => false

example : arithmeticPrecedence = true := by native_decide

private def relationChain : Bool :=
  match conditionExpr "1 < 2 < 3" >>= rootRelation with
  | some (.common initial [(.less, two), (.less, three)]) =>
      initial == numAdd 1 && two == numAdd 2 && three == numAdd 3
  | _ => false

example : relationChain = true := by native_decide

private def extendedHasIf : Bool :=
  match conditionExpr "principal has if.foo" >>= rootRelation with
  | some (.has _ (.mk (.mk (.mk none (.mk (.name ⟨[], .ifIdent⟩)
      [.field (.ident "foo")])) []) [])) => true
  | _ => false

example : extendedHasIf = true := by native_decide

private def likeTakesAdd : Bool :=
  match conditionExpr "principal like \"a*\"" >>= rootRelation with
  | some (.like _ _) => true
  | _ => false

example : likeTakesAdd = true := by native_decide

private def isInTakesAdds : Bool :=
  match conditionExpr "principal is User in Group::\"admins\"" >>= rootRelation with
  | some (.isIn _ _ (some _)) => true
  | _ => false

example : isInTakesAdds = true := by native_decide

private def parenthesesPreserved : Bool :=
  match conditionExpr "(true)" >>= rootPrimary with
  | some (.expr _) => true
  | _ => false

example : parenthesesPreserved = true := by native_decide

private def fourBangs : Bool :=
  match conditionExpr "!!!!principal" >>= rootUnary with
  | some (.mk (some (.bang 4)) _) => true
  | _ => false

example : fourBangs = true := by native_decide

private def overBang : Bool :=
  match conditionExpr "!!!!!principal" >>= rootUnary with
  | some (.mk (some .overBang) _) => true
  | _ => false

example : overBang = true := by native_decide

private def mixedUnaryRejected : Bool := (conditionExpr "!-principal").isNone

example : mixedUnaryRejected = true := by native_decide

/-! ## Members, records, references, slots, and trailing commas -/

private def memberAccesses : Bool :=
  match conditionExpr "foo.if(1,)[0]" >>= rootUnary with
  | some (.mk none (.mk (.name ⟨[], .ident "foo"⟩)
      [.field .ifIdent, .call [_], .index _])) => true
  | _ => false

example : memberAccesses = true := by native_decide


private def qualifiedKeywordName : Bool :=
  match conditionExpr "if::then::else" >>= rootPrimary with
  | some (.name ⟨[.ifIdent, .thenIdent], .elseIdent⟩) => true
  | _ => false

example : qualifiedKeywordName = true := by native_decide

private def trueCanBeCalled : Bool :=
  match conditionExpr "true(true)" >>= rootUnary with
  | some (.mk none (.mk (.literal .trueLit) [.call [_]])) => true
  | _ => false

example : trueCanBeCalled = true := by native_decide

private def ifCannotBeCalled : Bool := (conditionExpr "if(true)").isNone

example : ifCannotBeCalled = true := by native_decide

private def trailingListComma : Bool :=
  match conditionExpr "[1, 2,]" >>= rootPrimary with
  | some (.exprList [_, _]) => true
  | _ => false

example : trailingListComma = true := by native_decide

private def recordIfKey : Bool :=
  match conditionExpr "{if: 1, foo: 2,}" >>= rootPrimary with
  | some (.record [_, _]) => true
  | _ => false

example : recordIfKey = true := by native_decide

private def structuredRef : Bool :=
  match conditionExpr "User::{foo: true,}" >>= rootPrimary with
  | some (.ref (.ref ⟨[], .ident "User"⟩ [_])) => true
  | _ => false

example : structuredRef = true := by native_decide

private def specialQualifiedRef : Bool :=
  match conditionExpr "if::Type::\"id\"" >>= rootPrimary with
  | some (.ref (.uid ⟨[.ifIdent], .ident "Type"⟩ (.string "id"))) => true
  | _ => false

example : specialQualifiedRef = true := by native_decide

/-- A special identifier cannot be a singleton `NameInline`, matching LALRPOP. -/
private def specialSingletonRefRejected : Bool :=
  (conditionExpr "if::\"id\"").isNone

example : specialSingletonRefRejected = true := by native_decide

private def otherSlotRetainsQuestionMark : Bool :=
  match conditionExpr "?other" >>= rootPrimary with
  | some (.slot (.other "?other")) => true
  | _ => false

example : otherSlotRetainsQuestionMark = true := by native_decide

private def incompletePolicyRejected : Bool := (parseStr "permit(principal").isNone
private def emptyPolicySet : Bool := parseStr "" == some ⟨[]⟩

example : incompletePolicyRejected = true := by native_decide
example : emptyPolicySet = true := by native_decide
