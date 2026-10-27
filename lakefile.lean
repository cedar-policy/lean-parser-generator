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

import Lake
open Lake DSL

/-- Package-wide linter configuration.

`linter.unusedVariables` flags dead binders across the package.
`warn.classDefReducibility` is disabled because alphabet instances intentionally
expose semireducible class-field projections.

The `weak.` prefix is required because linter options are registered after Lake
startup. -/
package «LeanParserGenerator» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`weak.linter.unusedVariables, true⟩,
    ⟨`weak.warn.classDefReducibility, false⟩
  ]

/-- Generated parsers need to import that library. -/
@[default_target]
lean_lib «LeanParserGenerator» where
  globs := #[.one `LeanParserGenerator, .submodules `LeanParserGenerator]

@[default_target]
lean_exe «leanparsergenerator» where
  root := `Main
  -- The interpreter is required for our code generation.
  supportInterpreter := true


/-- Describes the targets of code generation (testing our generator itself). -/
structure GenTarget where
  /-- The `.lig` input file, relative to the package directory. -/
  lig : String
  /-- The generated files this target produces, relative to the package directory,
      used only for the staleness (mtime) check. Their names are what the CLI
      infers from `lig` and the grammar's `%option`s. -/
  outputs : Array String
  /-- When set, the explicit CLI arguments to pass instead of the single `lig`
      argument. Used for the bootstrap, whose outputs live in a `Generated/`
      directory under a dotted module prefix that cannot be recovered by path
      inference. -/
  explicitArgs : Option (Array String) := none


/-- Committed generated outputs. Each grammar produces two backends;
    output names and modules are inferred from the `.lig` stem and its `%option`s
    (`module_prefix`, `roundtrip_lexer`), so a normal target is just the input. -/
def genTargets : Array GenTarget := #[
  -- Our parser generator bootsraps itselfs by generating the parser for `.lig` files.
  -- Regenerating this needs a working generator; the committed `LigParser`/`LigVerified` keep a
  -- clean checkout building without bootstrapping. Its outputs live in
  -- `Generated/` under a dotted module prefix, so it uses the explicit CLI form.
  { lig := "LeanParserGenerator/Frontend/lig.lig"
    outputs := #["LeanParserGenerator/Frontend/Generated/LigVerified.lean",
      "LeanParserGenerator/Frontend/Generated/LigParser.lean"]
    explicitArgs := some #["LeanParserGenerator/Frontend/lig.lig",
      "LeanParserGenerator/Frontend/Generated/LigVerified.lean",
      "LeanParserGenerator/Frontend/Generated/LigParser.lean",
      "LeanParserGenerator.Frontend.Generated.LigVerified",
      "LeanParserGenerator.Frontend.Generated.LigParser",
      "LeanParserGenerator.Frontend.Generated.LigParser"] },
  -- Below are examples for testing.
  -- LIG
  { lig := "test/calc/calc.lig"
    outputs := #["test/calc/CalcVerified.lean", "test/calc/CalcParser.lean",
      "test/calc/CalcLexer.lean", "test/calc/CalcLexerRoundtrip.lean"] },
  -- IMP
  { lig := "test/imp/imp.lig"
    outputs := #["test/imp/ImpVerified.lean", "test/imp/ImpParser.lean"] },
  -- Cedar policies
  { lig := "test/cedar/cedar.lig"
    outputs := #["test/cedar/CedarVerified.lean", "test/cedar/CedarParser.lean",
      "test/cedar/CedarLexer.lean", "test/cedar/CedarLexerRoundtrip.lean",
      "test/cedar/CedarParserRoundtrip.lean"] },
  -- Cedar schema
  { lig := "test/cedarschema/CedarSchema.lig"
    outputs := #["test/cedarschema/CedarSchemaVerified.lean",
      "test/cedarschema/CedarSchemaParser.lean", "test/cedarschema/CedarSchemaLexer.lean",
      "test/cedarschema/CedarSchemaLexerRoundtrip.lean",
      "test/cedarschema/CedarSchemaParserRoundtrip.lean"] },
  -- Cedar entities
  { lig := "test/cedarentities/CedarEntities.lig"
    outputs := #["test/cedarentities/CedarEntitiesVerified.lean",
      "test/cedarentities/CedarEntitiesParser.lean",
      "test/cedarentities/CedarEntitiesLexer.lean",
      "test/cedarentities/CedarEntitiesLexerRoundtrip.lean"] },
  { lig := "test/spanuse/SpanUse.lig"
    outputs := #["test/spanuse/SpanUseVerified.lean", "test/spanuse/SpanUseParser.lean",
      "test/spanuse/SpanUseLexer.lean", "test/spanuse/SpanUseLexerRoundtrip.lean"] }
]

/-- The heaviest fixtures (`c99`) -/
def heavyGenTargets : Array GenTarget := #[
  { lig := "test/c99/c99.lig"
    outputs := #["test/c99/C99Verified.lean", "test/c99/C99Parser.lean"] },
]

/-- Regenerate one grammar (inferring outputs from its `.lig` and `%option`s, or
    using explicit CLI args for the bootstrap) if any output is stale. -/
def regenSpec (dir : System.FilePath) (exeFile : System.FilePath)
    (spec : GenTarget) : IO Unit := do
  let ligPath := dir / spec.lig
  -- Regenerate when any expected output is missing or older than the input or the
  -- generator executable.
  let mut regenerate := false
  let ligMtime := (← ligPath.metadata).modified
  let exeMtime := (← exeFile.metadata).modified
  for out in spec.outputs do
    let outPath := dir / out
    if !(← System.FilePath.pathExists outPath) then
      regenerate := true
    else
      let outMtime := (← outPath.metadata).modified
      if outMtime < ligMtime || outMtime < exeMtime then
        regenerate := true
  if regenerate then
    let args := spec.explicitArgs.getD #[spec.lig]
    let output ← IO.Process.output { cmd := exeFile.toString, args := args, cwd := dir }
    if output.exitCode != 0 && output.exitCode != 2 then
      error s!"leanparsergenerator failed on {spec.lig}:\n{output.stderr}"
    else
      IO.print output.stdout
      unless output.stderr.isEmpty do IO.eprint output.stderr

/-- Regenerate every non-heavy grammar. -/
target parsers (pkg : NPackage __name__) : Unit := do
  let exeJob ← «leanparsergenerator».fetch
  exeJob.bindM fun exeFile => do
    Job.async do
      for spec in genTargets do
        regenSpec pkg.dir exeFile spec

/-- Regenerate the heavy fixtures (`c99`); opt-in, not needed by default targets. -/
target heavyParsers (pkg : NPackage __name__) : Unit := do
  let exeJob ← «leanparsergenerator».fetch
  exeJob.bindM fun exeFile => do
    Job.async do
      for spec in heavyGenTargets do
        regenSpec pkg.dir exeFile spec

/-- Executable generated parsers and their hand-written token/AST modules. -/
lean_lib «Generated» where
  srcDir := "test"
  roots := #[`calc.CalcAst, `calc.CalcParser, `calc.CalcLexer, `imp.ImpAst, `imp.ImpParser,
    `cedar.CedarAst, `cedar.CedarLexer, `cedar.CedarParser,
    `cedarschema.CedarSchemaAst, `cedarschema.CedarSchemaLexer, `cedarschema.CedarSchemaParser,
    `cedarschema.ParserTestCedarSchema,
    `cedarentities.CedarEntitiesAst, `cedarentities.CedarEntitiesLexer, `cedarentities.CedarEntitiesParser,
  ]
  needs := #[parsers]

@[default_target]
lean_lib «VerifiedSmoke» where
  srcDir := "test"
  roots := #[`calc.CalcAst, `calc.CalcVerified, `calc.CompletenessValidatorTest,
    `calc.RefinementTest, `calc.GrammarViewTest,
    `calc.CalcLexer, `calc.CalcLexerRoundtripSupport, `calc.CalcLexerRoundtrip,
    `cedar.CedarAst, `cedar.CedarLexer, `cedar.CedarLexerRoundtripSupport,
    `cedar.CedarLexerRoundtrip,
    `cedar.CedarParser, `cedar.CedarUnparse, `cedar.CedarParserRoundtrip,
    `cedarschema.CedarSchemaAst, `cedarschema.CedarSchemaLexer,
    `cedarschema.CedarSchemaLexerRoundtripSupport, `cedarschema.CedarSchemaLexerRoundtrip,
    `cedarschema.CedarSchemaParser, `cedarschema.CedarSchemaUnparse,
    `cedarschema.CedarSchemaParserRoundtrip,
    `cedarentities.CedarEntitiesAst, `cedarentities.CedarEntitiesLexer,
    `cedarentities.CedarEntitiesLexerRoundtripSupport,
    `cedarentities.CedarEntitiesLexerRoundtrip,
    `spanuse.SpanUseLexer, `spanuse.SpanUseLexerRoundtripSupport,
    `spanuse.SpanUseLexerRoundtrip,
  ]
  needs := #[parsers]

/-- Verified modules without the C99 example. -/
lean_lib «VerifiedMid» where
  srcDir := "test"
  roots := #[
    -- Calc
    `calc.CalcAst, `calc.CalcLexer, `calc.CalcParser, `calc.CalcVerified,
    -- Imp
    `imp.ImpAst, `imp.ImpParser, `imp.ImpVerified,
    -- Cedar
    `cedar.CedarAst, `cedar.CedarLexer, `cedar.CedarParser, `cedar.CedarVerified,
    -- Cedar schema
    `cedarschema.CedarSchemaAst, `cedarschema.CedarSchemaLexer,
    `cedarschema.CedarSchemaParser, `cedarschema.CedarSchemaVerified,
    -- Cedar entities
    `cedarentities.CedarEntitiesAst, `cedarentities.CedarEntitiesLexer,
    `cedarentities.CedarEntitiesParser, `cedarentities.CedarEntitiesVerified,
  ]
  needs := #[parsers]

/-- The heaviest verified fixtures (`c99` only currently) -/
lean_lib «VerifiedHeavy» where
  srcDir := "test"
  roots := #[
    `c99.C99Ast, `c99.C99Parser, `c99.C99Verified,
  ]
  needs := #[heavyParsers]

/-- Throughput benchmark exe -/
lean_exe «cedar-bench» where
  srcDir := "test"
  root := `cedar.CedarBench
  needs := #[parsers]

/-- Cedar entities corpus test -/
lean_exe «cedarentities-corpus-test» where
  srcDir := "test"
  root := `cedarentities.CorpusTest
  needs := #[parsers]

lean_exe «lig-bootstrap-test» where
  srcDir := "test"
  root := `lig.BootstrapAgreementTest

/-- End-to-end functional parser tests (calc, imp). Light fixtures only; kept out
    of the heavy path. Builds the `#guard`/`native_decide` checks. -/
lean_lib «ParserTests» where
  srcDir := "test"
  roots := #[`calc.CalcAst, `calc.CalcLexer, `calc.CalcParser, `calc.ParserTestCalc,
    `calc.PositionTest, `calc.ErrorMessageTest,
    `spanuse.SpanUseLexer, `spanuse.SpanUseParser, `spanuse.SpanUseTest,
    `imp.ImpAst, `imp.ImpParser, `imp.ParserTestImp]
  needs := #[parsers]

/-- LSP / Language server targets -/

@[default_target]
lean_exe «lig-language-server» where
  root := `LeanParserGenerator.LSP.Main

@[default_target]
lean_lib «LspDiagnosticsTest» where
  srcDir := "test"
  roots := #[`lsp.DiagnosticsTest]
