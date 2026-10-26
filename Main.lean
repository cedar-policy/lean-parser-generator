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
`Main.lean` — `leanparsergenerator` CLI.

Primary usage generates both backends from one parse and one Pager construction:

```
leanparsergenerator grammar.lig GrammarVerified.lean GrammarParser.lean
```

Explicit `--backend verified|executable` retains single-output generation, while
`--print-grammar bnf|markdown` renders the inspectable augmented view without
writing files. Exit code 2 reports Pager conflicts after still writing or
rendering the requested output.
-/
public import LeanParserGenerator.Emit.Codegen
public import LeanParserGenerator.Emit.CodegenVerified
public import LeanParserGenerator.Emit.CodegenLexer
public import LeanParserGenerator.Emit.CodegenLexerRoundtrip
public import LeanParserGenerator.Emit.CodegenParserRoundtrip
public import LeanParserGenerator.Frontend.File


public section

open Frontend Emit Construct

inductive Backend where
  | verified
  | executable
  deriving BEq

inductive GrammarViewFormat where
  | bnf
  | markdown

private def parseGrammarViewFormat : String → Option GrammarViewFormat
  | "bnf" => some .bnf
  | "markdown" => some .markdown
  | _ => none

/-- Derive a Lean module name from an output path's file stem. -/
def moduleOfPath (p : String) : String :=
  let base := (p.splitOn "/").getLast!
  if base.endsWith ".lean" then (base.dropEnd 5).toString else base

/-- The directory of a path (everything up to and including the last `/`), or the
    empty string when the path has no directory component. -/
def dirOfPath (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => ""
  | parts => String.intercalate "/" parts ++ "/"

/-- The base name inferred from a `.lig` path: its file stem with the first
    character upper-cased (`calc.lig` → `Calc`, `imp.lig` → `Imp`). The stem is used
    verbatim otherwise, so a `.lig` already named in CamelCase
    (`CedarSchema.lig` → `CedarSchema`) infers the CamelCase modules directly. -/
def baseOfLig (ligPath : String) : String :=
  let file := (ligPath.splitOn "/").getLast!
  let stem := if file.endsWith ".lig" then (file.dropEnd 4).toString else file
  match stem.toList with
  | [] => stem
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- Prefix a module name with a dotted module prefix, e.g. `calc` + `CalcParser` →
    `calc.CalcParser`. An empty prefix leaves the name top-level. -/
def qualify (prefix_ modName : String) : String :=
  if prefix_.isEmpty then modName else prefix_ ++ "." ++ modName

private def conflictExitCode (ligPath : String) (tables : Tables) : IO UInt32 := do
  unless tables.conflicts.isEmpty do
    IO.eprintln s!"warning: [{ligPath}] {tables.conflicts.length} Pager LR(1) conflict(s):"
    for conflict in tables.conflicts do
      IO.eprintln s!"    {conflict}"
  return if tables.conflicts.isEmpty then 0 else 2

private def prepareFile (ligPath : String) : IO (Except String (Surface × PreparedGrammar)) := do
  let input ← IO.FS.readFile ligPath
  match parseLig input with
  | .error error => return .error s!"parse error: {error}"
  | .ok surface0 =>
    match Frontend.Macros.expandMacros surface0 with
    | .error error => return .error s!"macro expansion error: {error}"
    | .ok surface =>
      match prepareGrammar surface with
      | .error error => return .error error
      | .ok prepared => return .ok (surface, prepared)

/-- Generate one explicitly selected backend. -/
def generateFile (backend : Backend) (ligPath outPath moduleName : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      let source ← if backend == .verified then
        generateVerifiedFrom surface prepared moduleName
      else
        generateFrom surface prepared moduleName
      match source with
      | .error error =>
          IO.eprintln s!"error: [{ligPath}] generation failed: {error}"
          return 1
      | .ok source =>
          IO.FS.writeFile outPath source
          IO.println s!"wrote {outPath} (module {moduleName})"
          conflictExitCode ligPath prepared.tables

/-- Generate verified and executable modules from one prepared grammar, and
    optionally the lexer module when the `.lig` has a `%lexer` block and a lexer
    output path is given. -/
def generateBothFiles (ligPath verifiedOut executableOut verifiedModule executableModule : String)
    (executableImport : Option String := none)
    (lexerOut : Option String := none) (lexerModule : Option String := none)
    (lexerImport : Option String := none) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      -- In the `%lexer` regime the lexer module owns the token type, so the parser
      -- modules import it. Determine the lexer module name up front (when a lexer
      -- output is requested and the grammar has a `%lexer` block) and thread its
      -- dotted import path into parser generation.
      let genLexer := lexerOut.isSome && surface.lexer.isSome
      let lexShortName : Option String :=
        if genLexer then some (lexerModule.getD (moduleOfPath lexerOut.get!)) else none
      let lexImportPath : Option String :=
        if genLexer then some (lexerImport.getD (lexShortName.getD "")) else none
      match ← generateBothFrom surface prepared verifiedModule executableModule executableImport lexImportPath with
      | .error error =>
          IO.eprintln s!"error: [{ligPath}] generation failed: {error}"
          return 1
      | .ok (verifiedSource, executableSource) =>
          -- Generate the lexer module first (it defines the token type the parser
          -- modules import), then the parser modules.
          match lexerOut with
          | none => pure ()
          | some lexPath =>
            if surface.lexer.isNone then
              IO.eprintln s!"warning: [{ligPath}] a lexer output was requested but the \
grammar has no `%lexer` block; skipping {lexPath}"
            else
              let lexMod := lexShortName.getD (moduleOfPath lexPath)
              match Emit.generateLexerFrom surface lexMod with
              | .error e =>
                  IO.eprintln s!"error: [{ligPath}] lexer generation failed: {e}"
                  return 1
              | .ok lexSource =>
                  IO.FS.writeFile lexPath lexSource
                  IO.println s!"wrote {lexPath} (module {lexMod})"
          IO.FS.writeFile verifiedOut verifiedSource
          IO.FS.writeFile executableOut executableSource
          IO.println s!"wrote {verifiedOut} (module {verifiedModule})"
          IO.println s!"wrote {executableOut} (module {executableModule})"
          conflictExitCode ligPath prepared.tables

/-- Generate every module for a `.lig` from the input path alone. Output paths and
    module names are inferred from the `.lig` stem (`baseOfLig`) and written next to
    the input; `%option module_prefix` supplies the dotted import prefix; a `%lexer`
    block adds the lexer module, and `%option roundtrip_lexer` adds the roundtrip
    module. This is the primary CLI form. -/
def generateInferred (ligPath : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      let dir := dirOfPath ligPath
      let base := baseOfLig ligPath
      let prefix_ := surface.options.modulePrefix
      let verifiedModule := base ++ "Verified"
      let executableModule := base ++ "Parser"
      let verifiedOut := dir ++ verifiedModule ++ ".lean"
      let executableOut := dir ++ executableModule ++ ".lean"
      let executableImport := qualify prefix_ executableModule
      -- Lexer only in the `%lexer` regime; roundtrip only when also asked for it.
      let genLexer := surface.lexer.isSome
      let lexerModule := base ++ "Lexer"
      let lexerImport := qualify prefix_ lexerModule
      let lexImportPath : Option String := if genLexer then some lexerImport else none
      match ← generateBothFrom surface prepared verifiedModule executableModule
              (some executableImport) lexImportPath with
      | .error error =>
          IO.eprintln s!"error: [{ligPath}] generation failed: {error}"
          return 1
      | .ok (verifiedSource, executableSource) =>
          -- Lexer first: it owns the token type the parser modules import.
          if genLexer then
            match Emit.generateLexerFrom surface lexerModule with
            | .error e =>
                IO.eprintln s!"error: [{ligPath}] lexer generation failed: {e}"
                return 1
            | .ok lexSource =>
                let lexPath := dir ++ lexerModule ++ ".lean"
                IO.FS.writeFile lexPath lexSource
                IO.println s!"wrote {lexPath} (module {lexerModule})"
          IO.FS.writeFile verifiedOut verifiedSource
          IO.FS.writeFile executableOut executableSource
          IO.println s!"wrote {verifiedOut} (module {verifiedModule})"
          IO.println s!"wrote {executableOut} (module {executableModule})"
          -- Roundtrip module, opt-in via `%option roundtrip_lexer`.
          if genLexer && surface.options.roundtripLexer then
            let rtModule := lexerModule ++ "Roundtrip"
            match Emit.generateRoundtripFrom surface lexerImport lexerModule rtModule with
            | .error e =>
                IO.eprintln s!"error: [{ligPath}] roundtrip generation failed: {e}"
                return 1
            | .ok rtSource =>
                let rtPath := dir ++ rtModule ++ ".lean"
                IO.FS.writeFile rtPath rtSource
                IO.println s!"wrote {rtPath} (module {rtModule})"
          -- Parser roundtrip module, opt-in via `%option roundtrip_parser <printer>`.
          -- Parser roundtrip module, opt-in via `%option roundtrip_parser <unparse>`.
          -- Needs the generated lexer (the formatter re-lexes through it) and a
          -- user module `<Base>Unparse` defining `unparse` (and `renderTok` for the
          -- formatter), which the roundtrip module imports.
          if genLexer && surface.options.roundtripParser.isSome then
            let prtModule := executableModule ++ "Roundtrip"
            let unparseModule := base ++ "Unparse"
            let unparseImport := qualify prefix_ unparseModule
            match Emit.generateParserRoundtripFrom surface lexerImport lexerModule
                    executableImport executableModule unparseImport prtModule with
            | .error e =>
                IO.eprintln s!"error: [{ligPath}] parser roundtrip generation failed: {e}"
                return 1
            | .ok prtSource =>
                let prtPath := dir ++ prtModule ++ ".lean"
                IO.FS.writeFile prtPath prtSource
                IO.println s!"wrote {prtPath} (module {prtModule})"
          conflictExitCode ligPath prepared.tables

/-- Print an inspectable view built from the same augmented grammar data emitted
    into the dependent specification module. The generated module's
    `verifiedGrammarView_agrees` theorem is the checked proof boundary. -/
def printGrammarView (format : GrammarViewFormat) (ligPath : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      let view := buildVerifiedGrammarView surface prepared.augmented prepared.augProd
      let rendered := match format with
        | .bnf => view.renderBNF
        | .markdown => view.renderMarkdown
      IO.println rendered
      conflictExitCode ligPath prepared.tables

/-- Generate only the lexer module from a `.lig` `%lexer` block. -/
def generateLexerOnly (ligPath lexerOut lexerModule : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      if surface.lexer.isNone then
        IO.eprintln s!"error: [{ligPath}] no `%lexer` block in the grammar"
        return 1
      match Emit.generateLexerFrom surface lexerModule with
      | .error e =>
          IO.eprintln s!"error: [{ligPath}] lexer generation failed: {e}"
          return 1
      | .ok lexSource =>
          IO.FS.writeFile lexerOut lexSource
          IO.println s!"wrote {lexerOut} (module {lexerModule})"
          conflictExitCode ligPath prepared.tables

/-- Generate only the roundtrip module from a `.lig` `%lexer` block. `lexerImport`
    is the dotted module path of the generated lexer (which owns the token type). -/
def generateRoundtripOnly (ligPath roundtripOut lexerImport roundtripModule : String) :
    IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      if surface.lexer.isNone then
        IO.eprintln s!"error: [{ligPath}] no `%lexer` block in the grammar"
        return 1
      -- The lexer's declaration namespace is the last dotted component of its
      -- import path (`calc.CalcLexer` → `CalcLexer`); that is what qualifies
      -- `tokenize` in term position.
      let lexerName := (lexerImport.splitOn ".").getLastD lexerImport
      match Emit.generateRoundtripFrom surface lexerImport lexerName roundtripModule with
      | .error e =>
          IO.eprintln s!"error: [{ligPath}] roundtrip generation failed: {e}"
          return 1
      | .ok rtSource =>
          IO.FS.writeFile roundtripOut rtSource
          IO.println s!"wrote {roundtripOut} (module {roundtripModule})"
          conflictExitCode ligPath prepared.tables

/-- Generate only the parser roundtrip module from a `.lig` with `%option
    roundtrip_parser`. `lexerImport`/`parserImport`/`unparseImport` are the dotted
    module paths of the generated lexer (token type), parser (`parse`), and the user
    module defining `unparse` (and `renderTok`). -/
def generateParserRoundtripOnly (ligPath roundtripOut lexerImport parserImport unparseImport
    roundtripModule : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error =>
      IO.eprintln s!"error: [{ligPath}] {error}"
      return 1
  | .ok (surface, prepared) =>
      let lexerName := (lexerImport.splitOn ".").getLastD lexerImport
      let parserName := (parserImport.splitOn ".").getLastD parserImport
      match Emit.generateParserRoundtripFrom surface lexerImport lexerName parserImport parserName
              unparseImport roundtripModule with
      | .error e =>
          IO.eprintln s!"error: [{ligPath}] parser roundtrip generation failed: {e}"
          return 1
      | .ok rtSource =>
          IO.FS.writeFile roundtripOut rtSource
          IO.println s!"wrote {roundtripOut} (module {roundtripModule})"
          conflictExitCode ligPath prepared.tables

private def usage : IO UInt32 := do
  IO.eprintln "usage:"
  IO.eprintln "  leanparsergenerator <input.lig>"
  IO.eprintln "      infer all outputs from the .lig stem (next to the input);"
  IO.eprintln "      %option module_prefix sets the import prefix, roundtrip_lexer adds the roundtrip module"
  IO.eprintln "  leanparsergenerator <input.lig> <verified-output.lean> <executable-output.lean>"
  IO.eprintln "  leanparsergenerator <input.lig> <verified-output.lean> <executable-output.lean> <lexer-output.lean>"
  IO.eprintln "  leanparsergenerator <input.lig> <verified-output.lean> <executable-output.lean> <verified-module> <executable-module> [executable-import]"
  IO.eprintln "  leanparsergenerator --lexer <input.lig> <lexer-output.lean> [LexerModule]"
  IO.eprintln "  leanparsergenerator --roundtrip <input.lig> <roundtrip-output.lean> <lexer-import> [RoundtripModule]"
  IO.eprintln "  leanparsergenerator --roundtrip-parser <input.lig> <roundtrip-output.lean> <lexer-import> <parser-import> <unparse-import> [RoundtripModule]"
  IO.eprintln "  leanparsergenerator --backend verified|executable <input.lig> <output.lean> [ModuleName]"
  IO.eprintln "  leanparsergenerator --print-grammar bnf|markdown <input.lig>"
  return 1

private def parseBackend : String → Option Backend
  | "verified" => some .verified
  | "executable" => some .executable
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--print-grammar", formatName, lig] =>
      match parseGrammarViewFormat formatName with
      | some format => printGrammarView format lig
      | none => usage
  | "--lexer" :: rest =>
      match rest with
      | [lig, lexerOut] => generateLexerOnly lig lexerOut (moduleOfPath lexerOut)
      | [lig, lexerOut, lexerModule] => generateLexerOnly lig lexerOut lexerModule
      | _ => usage
  | "--roundtrip" :: rest =>
      match rest with
      | [lig, rtOut, lexerImport] =>
          generateRoundtripOnly lig rtOut lexerImport (moduleOfPath rtOut)
      | [lig, rtOut, lexerImport, rtModule] =>
          generateRoundtripOnly lig rtOut lexerImport rtModule
      | _ => usage
  | "--roundtrip-parser" :: rest =>
      match rest with
      | [lig, rtOut, lexerImport, parserImport, unparseImport] =>
          generateParserRoundtripOnly lig rtOut lexerImport parserImport unparseImport (moduleOfPath rtOut)
      | [lig, rtOut, lexerImport, parserImport, unparseImport, rtModule] =>
          generateParserRoundtripOnly lig rtOut lexerImport parserImport unparseImport rtModule
      | _ => usage
  | "--backend" :: backendName :: rest =>
      match parseBackend backendName, rest with
      | some backend, [lig, out] => generateFile backend lig out (moduleOfPath out)
      | some backend, [lig, out, moduleName] => generateFile backend lig out moduleName
      | _, _ => usage
  | [lig] =>
      -- Primary form: infer all outputs from the `.lig` path and `%option`s.
      generateInferred lig
  | [lig, verifiedOut, executableOut] =>
      generateBothFiles lig verifiedOut executableOut
        (moduleOfPath verifiedOut) (moduleOfPath executableOut)
  | [lig, verifiedOut, executableOut, lexerOut] =>
      -- Fourth path is the lexer module output (distinct from the 5-arg
      -- module-name form).
      generateBothFiles lig verifiedOut executableOut
        (moduleOfPath verifiedOut) (moduleOfPath executableOut)
        (lexerOut := some lexerOut)
  | [lig, verifiedOut, executableOut, verifiedModule, executableModule] =>
      generateBothFiles lig verifiedOut executableOut verifiedModule executableModule
  | [lig, verifiedOut, executableOut, verifiedModule, executableModule, executableImport] =>
      generateBothFiles lig verifiedOut executableOut verifiedModule executableModule
        (some executableImport)
  | [lig, verifiedOut, executableOut, verifiedModule, executableModule, executableImport,
      lexerOut, lexerModule, lexerImport] =>
      -- Full form with explicit modules and a generated lexer (the `%lexer`
      -- regime): the parser modules import `lexerImport` for the token type.
      generateBothFiles lig verifiedOut executableOut verifiedModule executableModule
        (some executableImport) (some lexerOut) (some lexerModule) (some lexerImport)
  | _ => usage
