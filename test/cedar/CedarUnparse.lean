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
`test/cedar/CedarUnparse.lean` — the token generator and token renderer for the
Cedar parser roundtrip (DESIGN §16.5).

These reference `Tok` (from the generated `CedarLexer`), so they live here rather
than in `CedarAst.lean` or the `%header`: the shared header is spliced into the
lexer module *before* `Tok` is defined, so a function mentioning `Tok` cannot go
there. `CedarUnparse` imports both the lexer (for `Tok`) and the AST, and the
generated `CedarParserRoundtrip` imports `CedarUnparse` — no cycle.

`unparsePolicies` is the parser-roundtrip primitive (`%option roundtrip_parser
unparsePolicies`): the inverse of what `CedarParser.parse` consumes. `renderTok` is
the formatter's token renderer (`%option roundtrip_format renderTok`): a *complete*
map from every token to surface text that re-lexes to it. Both cover the scope-only
policy sublanguage the roundtrip corpus exercises; a richer example extends the
corpus, not the proof shape.
-/
public import cedar.CedarLexer
public import cedar.CedarAst


@[expose] public section

namespace CedarUnparse

open Cedar

/-- A complete token renderer: every token maps to surface text that the lexer
    re-lexes to the same token. Keywords render to their spelling, value tokens to
    a canonical form, punctuation to its literal. This is the formatter's per-token
    map (`%option roundtrip_format`); completeness is what makes the formatter
    idempotence and the full roundtrip hold. -/
def renderTok : Tok → String
  | .TRUE => "true" | .FALSE => "false" | .IF => "if"
  | .PERMIT => "permit" | .FORBID => "forbid" | .WHEN => "when" | .UNLESS => "unless"
  | .IN => "in" | .HAS => "has" | .LIKE => "like" | .IS => "is"
  | .THEN => "then" | .ELSE => "else"
  | .PRINCIPAL => "principal" | .ACTION => "action" | .RESOURCE => "resource"
  | .CONTEXT => "context"
  | .PRINCIPAL_SLOT => "?principal" | .RESOURCE_SLOT => "?resource"
  | .OTHER_SLOT s => s
  | .IDENTIFIER s => s.val
  | .NUMBER n => toString n
  | .STRINGLIT s => "\"" ++ s ++ "\""
  | .AT => "@" | .DOT => "." | .COMMA => "," | .SEMICOLON => ";"
  | .COLON => ":" | .COLONCOLON => "::"
  | .LPAREN => "(" | .RPAREN => ")" | .LBRACE => "{" | .RBRACE => "}"
  | .LBRACKET => "[" | .RBRACKET => "]"
  | .EQ => "==" | .NEQ => "!=" | .LT => "<" | .LEQ => "<=" | .GEQ => ">=" | .GT => ">"
  | .OR => "||" | .AND => "&&"
  | .PLUS => "+" | .MINUS => "-" | .STAR => "*" | .SLASH => "/" | .PERCENT => "%"
  | .BANG => "!" | .SINGLE_EQ => "="
  | .EOF => ""

/-- Build an `IDENTIFIER` token from a string, guarding the `∉ keywords` subtype
    proof decidably. A keyword string falls back to `principal` (not a faithful
    roundtrip for that string, but total; faithful witnesses use non-keyword
    identifiers, which is exactly the lexer's reachable sublanguage). -/
def identTok (s : String) : Tok :=
  if h : s ∉ keywords then .IDENTIFIER ⟨s, h⟩ else .PRINCIPAL

/-- Tokens for a scope variable name (keyword scope variables only). -/
def unparseVar (v : VariableDef) : List Tok :=
  match v.variableName with
  | .principal => [.PRINCIPAL] | .action => [.ACTION] | .resource => [.RESOURCE]
  | .context => [.CONTEXT]
  | _ => [.PRINCIPAL]

/-- Tokens for one annotation `@key` or `@key("value")`. -/
def unparseAnnotation (a : Annotation) : List Tok :=
  let key : Tok := match a.key with
    | .ident s => identTok s
    | _ => identTok "ann"
  match a.value with
  | none => [.AT, key]
  | some (.string s) => [.AT, key, .LPAREN, .STRINGLIT s, .RPAREN]
  | some (.invalid s) => [.AT, key, .LPAREN, .STRINGLIT s, .RPAREN]

/-- Tokens for a scope-only policy: annotations, effect, parenthesized scope
    variables, and the trailing `;`. The condition sublanguage is covered by a
    `when { true }` form. -/
def unparsePolicy : Policy → List Tok
  | .policy ⟨annotations, effect, vars, conds⟩ =>
      let eff : Tok := match effect with
        | .permit => .PERMIT | .forbid => .FORBID
        | .ident s => identTok s
        | _ => .PERMIT
      let condToks := (conds.map (fun _ => [Tok.WHEN, .LBRACE, .TRUE, .RBRACE])).flatten
      (annotations.map unparseAnnotation).flatten ++
      [eff, .LPAREN] ++ List.intercalate [Tok.COMMA] (vars.map unparseVar) ++ [.RPAREN] ++
      condToks ++ [.SEMICOLON]

/-- Token generator for a `Policies` CST (parser roundtrip, DESIGN §16.5). -/
def unparsePolicies (p : Policies) : List Tok :=
  (p.policies.map unparsePolicy).flatten

/-! ### Roundtrip corpus (the specification)

`corpus` is the list of ASTs the generated `CedarParserRoundtrip` proves the
roundtrip for. It lives here, in the user's module, so regeneration never
overwrites it. Adding a witness here — and nothing else — extends every roundtrip
theorem to cover it. These are scope-only `permit`/`forbid` policies, annotations,
a custom-effect identifier, and a `when { true }` condition: the sublanguage
`unparsePolicies`/`renderTok` cover. -/

def scopeVar (name : Ident) : VariableDef := VariableDef.mk name none none none
def pol (effect : Ident) (vars : List VariableDef)
    (conds : List Cond := []) (annotations : List Annotation := []) : Policy :=
  .policy (PolicyImpl.mk annotations effect vars conds)

def corpus : List Policies :=
  [ ⟨[]⟩,
    ⟨[pol .permit [scopeVar .principal, scopeVar .action, scopeVar .resource]]⟩,
    ⟨[pol .forbid [scopeVar .principal]]⟩,
    ⟨[pol (.ident "custom") [scopeVar .principal]]⟩,
    ⟨[pol .permit [scopeVar .principal], pol .forbid [scopeVar .resource]]⟩,
    ⟨[pol .permit [scopeVar .principal]
        (annotations := [Annotation.mk (.ident "id") (some (.string "v"))])]⟩,
    ⟨[pol .permit [scopeVar .principal] [Cond.mk .when (Expr.fromPrimary (.literal .trueLit))]]⟩ ]

end CedarUnparse
