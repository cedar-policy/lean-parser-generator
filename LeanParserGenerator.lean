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
     This file imports both the runtime and generator libraries.
     You may want to look only at LeanParserGenerator.Runtime if you only need to run
     the generated parsers.
-/
public import LeanParserGenerator.Runtime
public import LeanParserGenerator.IR.Grammar
public import LeanParserGenerator.Construct.Analysis
public import LeanParserGenerator.Construct.LR0
public import LeanParserGenerator.Construct.LR1
public import LeanParserGenerator.Construct.Tables
public import LeanParserGenerator.Construct.Annotate
public import LeanParserGenerator.Emit.Codegen
public import LeanParserGenerator.Emit.CodegenVerified
public import LeanParserGenerator.Emit.CodegenLexer
public import LeanParserGenerator.Emit.CodegenLexerRoundtrip
public import LeanParserGenerator.Emit.CodegenParserRoundtrip
public import LeanParserGenerator.Emit.ErrorList
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Frontend.Diagnostics
public import LeanParserGenerator.Frontend.LigLexer
public import LeanParserGenerator.Frontend.LigParse
public import LeanParserGenerator.Frontend.Generated.LigParser
public import LeanParserGenerator.Lexer.Regex
public import LeanParserGenerator.Lexer.Spec
public import LeanParserGenerator.Lexer.Tokenize
public import LeanParserGenerator.Lexer.FlatScan
public import LeanParserGenerator.Lexer.FlatValidator
public import LeanParserGenerator.LSP.Server
