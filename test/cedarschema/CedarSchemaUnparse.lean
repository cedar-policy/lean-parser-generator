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
`test/cedarschema/CedarSchemaUnparse.lean` — the token generator and token renderer
for the Cedar-schema parser roundtrip (DESIGN §16.5).

As with `CedarUnparse`, these reference `Tok` (from the generated
`CedarSchemaLexer`), so they live here rather than in the AST or the shared
`%header`. `unparseSchema` is the parser-roundtrip primitive
(`%option roundtrip_parser unparseSchema`); `renderTok` is the formatter's complete
token renderer (`%option roundtrip_format renderTok`). Both cover the type- and
entity-declaration sublanguage the roundtrip corpus exercises.
-/
public import cedarschema.CedarSchemaLexer
public import cedarschema.CedarSchemaAst


@[expose] public section

namespace CedarSchemaUnparse

open CedarSchema

/-- A complete token renderer: every token maps to surface text that re-lexes to it. -/
def renderTok : Tok → String
  | .NAMESPACE => "namespace" | .ENTITY => "entity" | .IN => "in" | .TYPE => "type"
  | .SET => "Set" | .APPLIESTO => "appliesTo"
  | .PRINCIPAL => "principal" | .ACTION => "action" | .RESOURCE => "resource"
  | .CONTEXT => "context" | .ATTRIBUTES => "attributes" | .TAGS => "tags"
  | .LONG => "Long" | .STRING => "String" | .BOOL => "Bool" | .ENUM => "enum"
  | .IDENTIFIER s => s
  | .NUMBER n => toString n
  | .STRINGLIT s => "\"" ++ s ++ "\""
  | .COMMA => "," | .SEMICOLON => ";" | .COLON => ":" | .COLONCOLON => "::"
  | .LBRACE => "{" | .RBRACE => "}" | .LBRACKET => "[" | .RBRACKET => "]"
  | .LANGLE => "<" | .RANGLE => ">" | .EQUALS => "=" | .QUESTION => "?"
  | .AT => "@" | .LPAREN => "(" | .RPAREN => ")"
  | .EOF => ""

/-- An identifier's token: a keyword constructor renders to its keyword token, a
    free identifier to `IDENTIFIER`. This mirrors the lexer's keyword folding, so the
    token re-lexes to itself. -/
def identTok : Ident → Tok
  | .namespaceKw => .NAMESPACE | .entityKw => .ENTITY | .setKw => .SET
  | .appliesToKw => .APPLIESTO | .principalKw => .PRINCIPAL | .actionKw => .ACTION
  | .resourceKw => .RESOURCE | .contextKw => .CONTEXT | .attributesKw => .ATTRIBUTES
  | .tagsKw => .TAGS | .boolKw => .BOOL | .longKw => .LONG | .stringKw => .STRING
  | .typeKw => .TYPE | .inKw => .IN | .enumKw => .ENUM
  | .ident s => .IDENTIFIER s

/-- Tokens for a `::`-separated path. -/
def unparsePath (p : Path) : List Tok :=
  List.intercalate [Tok.COLONCOLON] ((p.prefixPath ++ [p.basename]).map (fun i => [identTok i]))

mutual
/-- Tokens for a schema type: a path, `Set < Type >`, or a record. -/
partial def unparseType : SType → List Tok
  | .ident p => unparsePath p
  | .set t => [.SET, .LANGLE] ++ unparseType t ++ [.RANGLE]
  | .record attrs => [.LBRACE] ++ List.intercalate [Tok.COMMA] (attrs.map unparseAttr) ++ [.RBRACE]
/-- Tokens for one annotated attribute `name ['?'] ':' Type` (annotations omitted). -/
partial def unparseAttr : Annotated AttrDecl → List Tok
  | ⟨.mk name required ty, _⟩ =>
      [Tok.IDENTIFIER name] ++ (if required then [] else [Tok.QUESTION]) ++ [.COLON] ++ unparseType ty
end

/-- Tokens for a declaration: `type I = T ;` or `entity Is [in [..]] [{..}] ;`. -/
def unparseDecl : Declaration → List Tok
  | .type t => [.TYPE, identTok t.name, .EQUALS] ++ unparseType t.definition ++ [.SEMICOLON]
  | .entity (.standard e) =>
      [Tok.ENTITY] ++ List.intercalate [Tok.COMMA] (e.names.map (fun i => [identTok i])) ++
      (match e.memberOfTypes with
       | [] => []
       | ps => [Tok.IN, .LBRACKET] ++ List.intercalate [Tok.COMMA] (ps.map unparsePath) ++ [.RBRACKET]) ++
      (match e.attrs with
       | [] => []
       | attrs => [Tok.LBRACE] ++ List.intercalate [Tok.COMMA] (attrs.map unparseAttr) ++ [.RBRACE]) ++
      (match e.tags with
       | none => []
       | some t => [Tok.TAGS] ++ unparseType t) ++ [.SEMICOLON]
  | .entity (.enum e) =>
      [Tok.ENTITY] ++ List.intercalate [Tok.COMMA] (e.names.map (fun i => [identTok i])) ++
      [.ENUM, .LBRACKET] ++
      List.intercalate [Tok.COMMA] (e.choices.map (fun c => [Tok.STRINGLIT c.value])) ++
      [.RBRACKET, .SEMICOLON]
  | .action _ => [.ACTION, identTok (.ident "a"), .SEMICOLON]

/-- Tokens for a namespace: a named `namespace P { decls }` or a bare declaration. -/
def unparseNamespace : Annotated Namespace → List Tok
  | ⟨⟨none, [⟨d, _⟩]⟩, _⟩ => unparseDecl d
  | ⟨⟨none, _⟩, _⟩ => []
  | ⟨⟨some p, decls⟩, _⟩ =>
      [Tok.NAMESPACE] ++ unparsePath p ++ [.LBRACE] ++
      (decls.map (fun ⟨d, _⟩ => unparseDecl d)).flatten ++ [.RBRACE]

/-- Token generator for a `Schema` CST (parser roundtrip, DESIGN §16.5). -/
def unparseSchema (s : Schema) : List Tok :=
  (s.namespaces.map unparseNamespace).flatten

/-! ### Roundtrip corpus (the specification)

`corpus` is the list of schemas the generated `CedarSchemaParserRoundtrip` proves
the roundtrip for; it lives here so regeneration never overwrites it. Adding a
witness extends every roundtrip theorem to cover it. These are `type` and `entity`
declarations in named and anonymous namespaces, with `Set<…>` and record types —
the sublanguage `unparseSchema`/`renderTok` cover. -/

def ann (data : Declaration) : Annotated Declaration := ⟨data, []⟩
def ns (name : Option Path) (decls : List (Annotated Declaration)) : Annotated Namespace :=
  ⟨⟨name, decls⟩, []⟩

def corpus : List Schema :=
  [ ⟨[]⟩,
    ⟨[ns none [ann (.type (TypeDecl.mk (.ident "Age") (.ident (Path.single .longKw))))]]⟩,
    ⟨[ns (some (Path.single (.ident "NS")))
        [ann (.type (TypeDecl.mk (.ident "Names") (.set (.ident (Path.single .stringKw)))))]]⟩,
    ⟨[ns none [ann (.entity (.standard (StandardEntityDecl.mk [.ident "User"] []
        [⟨AttrDecl.mk "age" true (.ident (Path.single .longKw)), []⟩] none)))]]⟩,
    ⟨[ns none [ann (.entity (.standard (StandardEntityDecl.mk [.ident "Photo"]
        [Path.single (.ident "Album")] [] none)))]]⟩ ]

end CedarSchemaUnparse
