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
import all cedar.CedarVerified
public import cedar.CedarPrintable
public import cedar.CedarParserRoundtrip
public import cedar.CedarLexerRoundtrip
meta import cedar.CedarLexerRoundtripSupport
meta import cedar.CedarLexer
meta import LeanParserGenerator.Lexer.Roundtrip

@[expose] public section

namespace CedarParserRoundtripProof

open Cedar CedarPrintable Runtime Runtime.Grammar

noncomputable def effectTree : (effect : PrintableEffect) →
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨47, by omega⟩ : CedarVerified.NonTerminal)) [effect.token]
  | .permit => CedarVerified.parseTreeProduction133 CedarVerified.parseTreeProduction119
  | .forbid => CedarVerified.parseTreeProduction133 CedarVerified.parseTreeProduction120

noncomputable def variableIdentTree : (v : PrintableVar) →
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨47, by omega⟩ : CedarVerified.NonTerminal)) [v.token]
  | .principal => CedarVerified.parseTreeProduction133 CedarVerified.parseTreeProduction115
  | .action => CedarVerified.parseTreeProduction133 CedarVerified.parseTreeProduction116
  | .resource => CedarVerified.parseTreeProduction133 CedarVerified.parseTreeProduction117
  | .context => CedarVerified.parseTreeProduction133 CedarVerified.parseTreeProduction118

noncomputable def variableTree (v : PrintableVar) :
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨5, by omega⟩ : CedarVerified.NonTerminal)) [v.token] :=
  CedarVerified.parseTreeProduction9 (variableIdentTree v)
    CedarVerified.parseTreeProduction10 CedarVerified.parseTreeProduction12
    CedarVerified.parseTreeProduction14

mutual

noncomputable def variablesTree : (variables : List PrintableVar) →
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨3, by omega⟩ : CedarVerified.NonTerminal)) (unparseVariables variables)
  | [] => CedarVerified.parseTreeProduction4
  | v :: rest =>
      CedarVerified.parseTreeProduction5 (variableTree v) (variableTailTree rest)

noncomputable def variableTailTree : (variables : List PrintableVar) →
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨4, by omega⟩ : CedarVerified.NonTerminal)) (unparseVariableTail variables)
  | [] => CedarVerified.parseTreeProduction6
  | v :: rest =>
      CedarVerified.parseTreeProduction8 (variableTree v) (variableTailTree rest)

end

noncomputable def policyTree (policy : PrintablePolicy) :
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨2, by omega⟩ : CedarVerified.NonTerminal)) (unparsePolicy policy) :=
  CedarVerified.parseTreeProduction3 CedarVerified.parseTreeProduction137
    (effectTree policy.effect) (variablesTree policy.variables)
    CedarVerified.parseTreeProduction139

noncomputable def policyListTree : (policies : List PrintablePolicy) →
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨48, by omega⟩ : CedarVerified.NonTerminal)) (unparsePolicyList policies)
  | [] => CedarVerified.parseTreeProduction135
  | policy :: rest =>
      CedarVerified.parseTreeProduction136 (policyTree policy) (policyListTree rest)

noncomputable def policiesTree (policies : PrintablePolicies) :
    ParseTree (G := CedarVerified.grammarInst)
      (.NT (⟨0, by omega⟩ : CedarVerified.NonTerminal)) (unparsePolicies policies) :=
  CedarVerified.parseTreeProduction0 (policyListTree policies.policies)

theorem effectTree_sem (effect : PrintableEffect) :
    ptSem (effectTree effect) = effect.toIdent := by
  cases effect with
  | permit =>
      erw [CedarVerified.parseTreeProduction133_sem,
        CedarVerified.parseTreeProduction119_sem]
      rfl
  | forbid =>
      erw [CedarVerified.parseTreeProduction133_sem,
        CedarVerified.parseTreeProduction120_sem]
      rfl

theorem variableIdentTree_sem (v : PrintableVar) :
    ptSem (variableIdentTree v) = v.toIdent := by
  cases v <;>
    erw [CedarVerified.parseTreeProduction133_sem] <;>
    first
    | erw [CedarVerified.parseTreeProduction115_sem]; rfl
    | erw [CedarVerified.parseTreeProduction116_sem]; rfl
    | erw [CedarVerified.parseTreeProduction117_sem]; rfl
    | erw [CedarVerified.parseTreeProduction118_sem]; rfl

theorem variableTree_sem (v : PrintableVar) :
    ptSem (variableTree v) = v.toVariable := by
  unfold variableTree
  erw [CedarVerified.parseTreeProduction9_sem, variableIdentTree_sem,
    CedarVerified.parseTreeProduction10_sem, CedarVerified.parseTreeProduction12_sem,
    CedarVerified.parseTreeProduction14_sem]
  rfl

mutual

theorem variablesTree_sem (variables : List PrintableVar) :
    ptSem (variablesTree variables) = variables.map PrintableVar.toVariable := by
  cases variables with
  | nil =>
      simp only [variablesTree, List.map_nil]
      erw [CedarVerified.parseTreeProduction4_sem]
      rfl
  | cons v rest =>
      simp only [variablesTree, List.map_cons]
      erw [CedarVerified.parseTreeProduction5_sem, variableTree_sem, variableTailTree_sem]
      rfl

theorem variableTailTree_sem (variables : List PrintableVar) :
    ptSem (variableTailTree variables) = variables.map PrintableVar.toVariable := by
  cases variables with
  | nil =>
      simp only [variableTailTree, List.map_nil]
      erw [CedarVerified.parseTreeProduction6_sem]
      rfl
  | cons v rest =>
      simp only [variableTailTree, List.map_cons]
      erw [CedarVerified.parseTreeProduction8_sem, variableTree_sem, variableTailTree_sem]
      rfl

end

theorem policyTree_sem (policy : PrintablePolicy) :
    ptSem (policyTree policy) = policy.toPolicy := by
  unfold policyTree
  erw [CedarVerified.parseTreeProduction3_sem,
    CedarVerified.parseTreeProduction137_sem, effectTree_sem, variablesTree_sem,
    CedarVerified.parseTreeProduction139_sem]
  rfl

theorem policyListTree_sem (policies : List PrintablePolicy) :
    ptSem (policyListTree policies) = policies.map PrintablePolicy.toPolicy := by
  induction policies with
  | nil =>
      simp only [policyListTree, List.map_nil]
      erw [CedarVerified.parseTreeProduction135_sem]
      rfl
  | cons policy rest ih =>
      simp only [policyListTree, List.map_cons]
      erw [CedarVerified.parseTreeProduction136_sem, policyTree_sem, ih]
      rfl

theorem policiesTree_sem (policies : PrintablePolicies) :
    ptSem (policiesTree policies) = policies.toPolicies := by
  unfold policiesTree PrintablePolicies.toPolicies
  erw [CedarVerified.parseTreeProduction0_sem, policyListTree_sem]
  rfl

noncomputable def certificate (policies : PrintablePolicies) :
    CedarParserRoundtrip.Certificate (unparsePolicies policies) policies.toPolicies := by
  refine { tree := ?_, semantics := ?_ }
  · with_unfolding_all exact CedarVerified.parseTreeProduction143 (policiesTree policies)
  · show ptSem (CedarVerified.parseTreeProduction143 (policiesTree policies)) =
      policies.toPolicies
    erw [CedarVerified.parseTreeProduction143_sem]
    exact policiesTree_sem policies

/-- Universal token-level parser roundtrip for restricted printable policies. -/
theorem parse_roundtrip (policies : PrintablePolicies) :
    CedarParser.parse
      ((unparsePolicies policies ++ [Tok.EOF]).map Positioned.dummy)
      (certificate policies).logFuel = some policies.toPolicies :=
  CedarParserRoundtrip.parse_certificate (certificate policies)

private theorem roundtrippable_PERMIT : CedarLexerRoundtrip.RoundtrippableTok Tok.PERMIT := by
  native_decide
private theorem roundtrippable_FORBID : CedarLexerRoundtrip.RoundtrippableTok Tok.FORBID := by
  native_decide
private theorem roundtrippable_PRINCIPAL : CedarLexerRoundtrip.RoundtrippableTok Tok.PRINCIPAL := by
  native_decide
private theorem roundtrippable_ACTION : CedarLexerRoundtrip.RoundtrippableTok Tok.ACTION := by
  native_decide
private theorem roundtrippable_RESOURCE : CedarLexerRoundtrip.RoundtrippableTok Tok.RESOURCE := by
  native_decide
private theorem roundtrippable_CONTEXT : CedarLexerRoundtrip.RoundtrippableTok Tok.CONTEXT := by
  native_decide
private theorem roundtrippable_COMMA : CedarLexerRoundtrip.RoundtrippableTok Tok.COMMA := by
  native_decide
private theorem roundtrippable_LPAREN : CedarLexerRoundtrip.RoundtrippableTok Tok.LPAREN := by
  native_decide
private theorem roundtrippable_RPAREN : CedarLexerRoundtrip.RoundtrippableTok Tok.RPAREN := by
  native_decide
private theorem roundtrippable_SEMICOLON : CedarLexerRoundtrip.RoundtrippableTok Tok.SEMICOLON := by
  native_decide

theorem effect_roundtrippable (effect : PrintableEffect) :
    CedarLexerRoundtrip.RoundtrippableTok effect.token := by
  cases effect
  · exact roundtrippable_PERMIT
  · exact roundtrippable_FORBID

theorem variable_roundtrippable (v : PrintableVar) :
    CedarLexerRoundtrip.RoundtrippableTok v.token := by
  cases v
  · exact roundtrippable_PRINCIPAL
  · exact roundtrippable_ACTION
  · exact roundtrippable_RESOURCE
  · exact roundtrippable_CONTEXT

mutual

theorem variables_roundtrippable (variables : List PrintableVar) :
    Lexer.Forall CedarLexerRoundtrip.RoundtrippableTok (unparseVariables variables) := by
  cases variables with
  | nil => exact .nil
  | cons v rest =>
      exact .cons (variable_roundtrippable v) (variableTail_roundtrippable rest)

theorem variableTail_roundtrippable (variables : List PrintableVar) :
    Lexer.Forall CedarLexerRoundtrip.RoundtrippableTok (unparseVariableTail variables) := by
  cases variables with
  | nil => exact .nil
  | cons v rest =>
      exact .cons roundtrippable_COMMA
        (.cons (variable_roundtrippable v) (variableTail_roundtrippable rest))

end

theorem policy_roundtrippable (policy : PrintablePolicy) :
    Lexer.Forall CedarLexerRoundtrip.RoundtrippableTok (unparsePolicy policy) := by
  have withRParen := (variables_roundtrippable policy.variables).append
    (.cons roundtrippable_RPAREN .nil)
  have suffix := withRParen.append (.cons roundtrippable_SEMICOLON .nil)
  simpa [unparsePolicy] using
    (Lexer.Forall.cons (effect_roundtrippable policy.effect)
      (Lexer.Forall.cons roundtrippable_LPAREN suffix))

theorem policyList_roundtrippable (policies : List PrintablePolicy) :
    Lexer.Forall CedarLexerRoundtrip.RoundtrippableTok (unparsePolicyList policies) := by
  induction policies with
  | nil => exact .nil
  | cons policy rest ih => exact (policy_roundtrippable policy).append ih

theorem unparse_roundtrippable (policies : PrintablePolicies) :
    Lexer.Forall CedarLexerRoundtrip.RoundtrippableTok (unparsePolicies policies) :=
  policyList_roundtrippable policies.policies

/-- Full printable value → tokens → source → lexer → parser roundtrip. -/
theorem full_roundtrip (policies : PrintablePolicies) :
    (CedarLexer.tokenizeBare
      (CedarLexerRoundtrip.render (unparsePolicies policies))).toOption.bind
        (fun tokens => CedarParser.parse (tokens.map Positioned.dummy)
          (certificate policies).logFuel) = some policies.toPolicies := by
  rw [CedarLexerRoundtrip.render_roundtrip _ (unparse_roundtrippable policies)]
  exact CedarParserRoundtrip.parse_certificate (certificate policies)

end CedarParserRoundtripProof
