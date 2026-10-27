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
public import cedar.CedarAst

@[expose] public section

namespace CedarPrintable

open Cedar

inductive PrintableEffect where
  | permit
  | forbid
  deriving Repr, Inhabited, DecidableEq

inductive PrintableVar where
  | principal
  | action
  | resource
  | context
  deriving Repr, Inhabited, DecidableEq

structure PrintablePolicy where
  effect : PrintableEffect
  variables : List PrintableVar
  deriving Repr, Inhabited, DecidableEq

structure PrintablePolicies where
  policies : List PrintablePolicy
  deriving Repr, Inhabited, DecidableEq

namespace PrintableEffect

def toIdent : PrintableEffect → Ident
  | .permit => .permit
  | .forbid => .forbid

def token : PrintableEffect → Tok
  | .permit => .PERMIT
  | .forbid => .FORBID

end PrintableEffect

namespace PrintableVar

def toIdent : PrintableVar → Ident
  | .principal => .principal
  | .action => .action
  | .resource => .resource
  | .context => .context

def toVariable (v : PrintableVar) : VariableDef := {
  variableName := v.toIdent
  unusedTypeName := none
  entityType := none
  ineq := none
}

def token : PrintableVar → Tok
  | .principal => .PRINCIPAL
  | .action => .ACTION
  | .resource => .RESOURCE
  | .context => .CONTEXT

end PrintableVar

namespace PrintablePolicy

def toPolicy (policy : PrintablePolicy) : Policy :=
  .policy {
    annotations := []
    effect := policy.effect.toIdent
    variables := policy.variables.map PrintableVar.toVariable
    conds := []
  }

end PrintablePolicy

namespace PrintablePolicies

def toPolicies (policies : PrintablePolicies) : Policies :=
  ⟨policies.policies.map PrintablePolicy.toPolicy⟩

end PrintablePolicies

mutual

def unparseVariables : List PrintableVar → List Tok
  | [] => []
  | v :: rest => [v.token] ++ unparseVariableTail rest

def unparseVariableTail : List PrintableVar → List Tok
  | [] => []
  | v :: rest => [.COMMA] ++ [v.token] ++ unparseVariableTail rest

end

def unparsePolicy (policy : PrintablePolicy) : List Tok :=
  [] ++ [policy.effect.token] ++ [.LPAREN] ++ unparseVariables policy.variables ++
    [.RPAREN] ++ [] ++ [.SEMICOLON]

def unparsePolicyList : List PrintablePolicy → List Tok
  | [] => []
  | policy :: rest => unparsePolicy policy ++ unparsePolicyList rest

def unparsePolicies (policies : PrintablePolicies) : List Tok :=
  unparsePolicyList policies.policies

end CedarPrintable
