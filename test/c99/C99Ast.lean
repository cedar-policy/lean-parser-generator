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
`test/c99/C99Ast.lean` — token type and concrete syntax tree for an LR(1) C99
subset.

This follows the C99 grammar (ISO/IEC 9899:1999, Annex A) as used by CompCert's
`cparser` and the "Validating LR(1) Parsers" evaluation. Two constructs that are
not LR(1) in raw form are handled the way that development handles them:

* `typedef-name` vs `identifier` is resolved before parsing: the token stream
  carries distinct `TYPEDEF_NAME` and `IDENTIFIER` terminals (the "lexer hack" /
  first pass). The grammar over that stream is LR(1).
* the dangling `else` is resolved by splitting statements into matched and
  unmatched forms, so the grammar has no shift/reduce conflict.

Only the token type and CST types are provided here; a tokenizer is not part of
this fixture, which exists to exercise the generator at C-grammar scale.
-/


@[expose] public section

namespace C99

/-- C99 tokens: keywords, the three name/constant/string terminals, and the
punctuators. `TYPEDEF_NAME` is emitted by the pre-parsing pass for identifiers
that name a type; `IDENTIFIER` for all others. -/
inductive Tok where
  -- type specifiers / qualifiers / storage-class keywords
  | VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE | SIGNED | UNSIGNED | BOOL | COMPLEX
  | STRUCT | UNION | ENUM
  | CONST | RESTRICT | VOLATILE
  | TYPEDEF | EXTERN | STATIC | AUTO | REGISTER | INLINE
  -- statement keywords
  | CASE | DEFAULT | IF | ELSE | SWITCH | WHILE | DO | FOR
  | GOTO | CONTINUE | BREAK | RETURN
  | SIZEOF
  -- names and literals
  | IDENTIFIER : String → Tok
  | TYPEDEF_NAME : String → Tok
  | CONSTANT : String → Tok
  | STRING_LITERAL : String → Tok
  -- punctuators
  | LBRACKET | RBRACKET | LPAREN | RPAREN | LBRACE | RBRACE
  | DOT | ARROW
  | INC | DEC
  | AMP | STAR | PLUS | MINUS | TILDE | BANG
  | SLASH | PERCENT | LSHIFT | RSHIFT
  | LT | GT | LEQ | GEQ | EQEQ | NEQ
  | CARET | PIPE | ANDAND | OROR
  | QUESTION | COLON | SEMICOLON | ELLIPSIS
  | EQ | STAR_EQ | SLASH_EQ | PERCENT_EQ | PLUS_EQ | MINUS_EQ
  | LSHIFT_EQ | RSHIFT_EQ | AMP_EQ | CARET_EQ | PIPE_EQ
  | COMMA
  | EOF
  deriving Repr, BEq, Inhabited

/-! ## Concrete syntax tree

The tree keeps every precedence layer and grammar form rather than collapsing to
a semantic AST, mirroring the CST style used by the other fixtures. Payloads are
deliberately shallow: the fixture measures grammar scale, so most nodes carry the
minimum needed for the semantic actions to type-check. -/

/-- Assignment / unary / binary operators, kept as source-level tokens. -/
inductive UnaryOp where
  | addr | deref | plus | minus | bnot | lnot
  deriving Repr, BEq, Inhabited

inductive AssignOp where
  | eq | mulEq | divEq | modEq | addEq | subEq
  | shlEq | shrEq | andEq | xorEq | orEq
  deriving Repr, BEq, Inhabited

/-- A type name string, either a keyword specifier or a typedef name. -/
inductive TypeSpec where
  | void | char | short | int | long | float | double
  | signed | unsigned | bool | complex
  | structOrUnion : String → TypeSpec        -- struct/union tag or body marker
  | enumSpec : String → TypeSpec
  | typedefName : String → TypeSpec
  deriving Repr, BEq, Inhabited

/-- A type name (a specifier list with an optional abstract declarator). -/
inductive CTypeName where
  | mk : List TypeSpec → Nat → CTypeName        -- specifiers, pointer depth
  deriving Repr, BEq, Inhabited

/-- Expressions, one constructor family per precedence level. -/
inductive Expr where
  | ident : String → Expr
  | constant : String → Expr
  | stringLit : String → Expr
  | paren : Expr → Expr
  | index : Expr → Expr → Expr
  | call : Expr → List Expr → Expr
  | field : Expr → String → Expr
  | arrow : Expr → String → Expr
  | postInc : Expr → Expr
  | postDec : Expr → Expr
  | preInc : Expr → Expr
  | preDec : Expr → Expr
  | unary : UnaryOp → Expr → Expr
  | sizeofExpr : Expr → Expr
  | sizeofType : CTypeName → Expr
  | cast : CTypeName → Expr → Expr
  | binop : String → Expr → Expr → Expr
  | cond : Expr → Expr → Expr → Expr
  | assign : AssignOp → Expr → Expr → Expr
  | comma : Expr → Expr → Expr
  deriving Repr, BEq

mutual
/-- A C declarator (name plus pointer/array/function modifiers). -/
inductive Declarator where
  | name : String → Declarator
  | pointer : Declarator → Declarator
  | array : Declarator → Option Expr → Declarator
  | func : Declarator → List Param → Declarator
  | paren : Declarator → Declarator
  deriving Repr, BEq

/-- One function parameter. -/
inductive Param where
  | mk : List TypeSpec → Option Declarator → Param
  | ellipsis : Param
  deriving Repr, BEq
end

/-- One declaration: specifiers plus a list of init-declarators. `isTypedef`
records whether the storage class was `typedef`. -/
structure InitDeclarator where
  decl : Declarator
  init : Option Expr
  deriving Repr, BEq

structure Declaration where
  isTypedef : Bool
  specs : List TypeSpec
  declarators : List InitDeclarator
  deriving Repr, BEq

mutual

/-- Statements. The matched/unmatched split lives in the grammar; the CST keeps a
single `Stmt` type. -/
inductive Stmt where
  | labeled : String → Stmt → Stmt
  | case : Expr → Stmt → Stmt
  | default : Stmt → Stmt
  | compound : List BlockItem → Stmt
  | expr : Option Expr → Stmt
  | ifThen : Expr → Stmt → Stmt
  | ifElse : Expr → Stmt → Stmt → Stmt
  | switch : Expr → Stmt → Stmt
  | whileDo : Expr → Stmt → Stmt
  | doWhile : Stmt → Expr → Stmt
  | forLoop : Option Expr → Option Expr → Option Expr → Stmt → Stmt
  | goto : String → Stmt
  | continueStmt : Stmt
  | breakStmt : Stmt
  | returnStmt : Option Expr → Stmt
  deriving Repr, BEq

/-- An item inside a compound statement: a declaration or a statement. -/
inductive BlockItem where
  | decl : Declaration → BlockItem
  | stmt : Stmt → BlockItem
  deriving Repr, BEq

end

/-- A function definition: specifiers, declarator, body. -/
structure FunctionDef where
  specs : List TypeSpec
  decl : Declarator
  body : Stmt
  deriving Repr, BEq

/-- A top-level external declaration. -/
inductive ExternalDecl where
  | function : FunctionDef → ExternalDecl
  | decl : Declaration → ExternalDecl
  deriving Repr, BEq

/-- A translation unit: a nonempty list of external declarations. -/
structure TranslationUnit where
  decls : List ExternalDecl
  deriving Repr, BEq

end C99
