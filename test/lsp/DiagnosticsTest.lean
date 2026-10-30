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
`test/lsp/DiagnosticsTest.lean` — unit tests for the `.lig` diagnostics engine
(`Frontend.collectDiagnostics` and helpers) that powers the language server.

Run with:  `lake env lean test/lsp/DiagnosticsTest.lean`

Each `#guard` is checked at elaboration time, so a regression fails the build.
-/
public import LeanParserGenerator.Frontend.Diagnostics
-- `#guard` evaluates at the meta phase, so the engine is also `meta`-imported.
meta import LeanParserGenerator.Frontend.Diagnostics


public section

open Frontend

/-- Does `s` contain `needle` as a substring? -/
def strContains (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

/-- Any error-severity diagnostic whose message contains `needle`. -/
def hasError (ds : Array LigDiagnostic) (needle : String) : Bool :=
  ds.any fun d => d.severity == .error && strContains d.message needle

/-- Any warning-severity diagnostic whose message contains `needle`. -/
def hasWarning (ds : Array LigDiagnostic) (needle : String) : Bool :=
  ds.any fun d => d.severity == .warning && strContains d.message needle

/-- Any information-severity diagnostic whose message contains `needle`. -/
def hasInfo (ds : Array LigDiagnostic) (needle : String) : Bool :=
  ds.any fun d => d.severity == .information && strContains d.message needle

def countErrors (ds : Array LigDiagnostic) : Nat :=
  (ds.filter (·.severity == .error)).size

/-! ### byteToLineCol -/

#guard byteToLineCol "ab\ncd" 0 == (0, 0)
#guard byteToLineCol "ab\ncd" 1 == (0, 1)
#guard byteToLineCol "ab\ncd" 2 == (0, 2)
#guard byteToLineCol "ab\ncd" 3 == (1, 0)
#guard byteToLineCol "ab\ncd" 4 == (1, 1)
-- Past-the-end clamps to the final position.
#guard byteToLineCol "ab\ncd" 100 == (1, 2)
-- Multi-byte (UTF-8) char: 'é' is 2 bytes but 1 UTF-16 unit; byte offset 3 is after it.
#guard byteToLineCol "é\nx" 3 == (1, 0)

/-! ### extractByteOffset -/

#guard extractByteOffset "expected identifier at byte 42" == some 42
#guard extractByteOffset "expected '%' directive at byte 7" == some 7
#guard extractByteOffset "missing `%%` separating directives from rules" == none

/-! ### Full grammars -/

def validGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | e=expr PLUS { 0 }
  | PLUS { 0 }
"

-- A well-formed, conflict-free grammar produces no error-severity diagnostics.
#guard countErrors (collectDiagnostics validGrammar) == 0

def undefinedSymbolGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | e=expr PLUS rhs=bogus { 0 }
  | PLUS { 0 }
"

#guard hasError (collectDiagnostics undefinedSymbolGrammar) "bogus"

-- The undefined-symbol diagnostic points at the offending element, not byte 0.
#guard (collectDiagnostics undefinedSymbolGrammar).any
  fun d => d.severity == .error && d.startByte > 0

def parseErrorGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
"  -- no `%%` and no rules

#guard countErrors (collectDiagnostics parseErrorGrammar) ≥ 1

def duplicateTokenGrammar : String :=
"%tokentype Tok
%token PLUS
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | PLUS { 0 }
"

#guard hasWarning (collectDiagnostics duplicateTokenGrammar) "declared more than once"

def startNotRuleGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start missing
%%
expr :: Nat
  | PLUS { 0 }
"

#guard hasError (collectDiagnostics startNotRuleGrammar) "start symbol"

def eofInProductionGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | PLUS EOF { 0 }
"

#guard hasError (collectDiagnostics eofInProductionGrammar) "end-of-input token"

def unusedNonterminalGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | PLUS { 0 }
dead :: Nat
  | PLUS { 0 }
"

#guard hasInfo (collectDiagnostics unusedNonterminalGrammar) "never used"

/-! ### %option validation -/

def unknownOptionGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%option bogus_option
%start expr
%%
expr :: Nat
  | PLUS { 0 }
"

-- An unknown `%option` is an error that names the accepted options, located at the
-- option name (not byte 0).
#guard hasError (collectDiagnostics unknownOptionGrammar) "unknown `%option bogus_option`"
#guard hasError (collectDiagnostics unknownOptionGrammar) "compress_tables"
#guard hasError (collectDiagnostics unknownOptionGrammar) "roundtrip_lexer"
#guard hasError (collectDiagnostics unknownOptionGrammar) "module_prefix"
#guard (collectDiagnostics unknownOptionGrammar).any
  fun d => d.severity == .error && d.startByte > 0

def knownOptionsGrammar : String :=
"%tokentype Tok
%token PLUS
%token EOF
%eof EOF
%option compress_tables
%option roundtrip_lexer
%option module_prefix my.project
%start expr
%%
expr :: Nat
  | PLUS { 0 }
"

-- The three known options (including the value-carrying `module_prefix`) parse
-- without any error diagnostics.
#guard countErrors (collectDiagnostics knownOptionsGrammar) == 0

/-! ### `gen_rust` and `!!rust{…}` -/

def rustGrammar : String :=
"%tokentype Tok
%token PLUS
%token <Nat> NUM
%token EOF
%eof EOF
%option gen_rust rust/src/generated.rs
%option rust_ctx crate::ast::Arena
%option rust_list crate::ast::lists
%option roundtrip_parser unparse
%option roundtrip_format renderTok
%lexer {
  | ['0'-'9']+ as s => { Tok.NUM (String.toNat! s) }
  | \"+\" => { Tok.PLUS }
  eof => { Tok.EOF }
}
%start expr
%%
expr :: Nat !!rust{u64}
  | a=expr PLUS n=NUM { a + n }
                      !!rust{ a + n }
  -- the Rust counterpart may follow a comment and contain braces
  | n=NUM { n }
    !!rust{ if n > 0 { n } else { 0 } }
  | { 0 } !!rust{ 0 }
list_of_nums :: List Nat !!rust{std::collections::VecDeque<u64>}
  | xs=list(NUM) { xs } !!rust{ xs }
"

-- The `gen_rust` option (with its path) and Rust actions, Rust types and macros in a
-- grammar with Rust text raise no diagnostics of any severity apart from the unused
-- nonterminal below.
#guard countErrors (collectDiagnostics rustGrammar) == 0
#guard !(collectDiagnostics rustGrammar).any (fun d => d.severity == .warning)
#guard (collectDiagnostics rustGrammar).all fun d => strContains d.message "never used"

-- An unclosed `!!rust{` is a located error from the frontend.
def unclosedRustGrammar : String :=
"%tokentype Tok
%token EOF
%eof EOF
%start s
%%
s :: Nat
  | { 0 } !!rust{ 0
"

#guard hasError (collectDiagnostics unclosedRustGrammar) "!!rust"

#eval IO.println "All diagnostics engine tests passed."
