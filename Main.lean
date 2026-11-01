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

```
leanparsergenerator [options] <input.lig>
```

One invocation generates every module for the grammar from one parse and one Pager
construction. Output names come from the `.lig` stem, and the `.lig`'s `%option`s
decide which optional modules are written. The flags below adjust the defaults.
`--print-grammar` and `--rust-report` inspect a grammar without writing files.

Exit codes: 0 on success, 1 on any error (bad arguments, unreadable input, `.lig`
parse or generation error), 2 when Pager reports LR(1) conflicts. With exit code 2
the requested output is still written or rendered.
-/
public import LeanParserGenerator.Emit.Codegen
public import LeanParserGenerator.Emit.CodegenVerified
public import LeanParserGenerator.Emit.CodegenLexer
public import LeanParserGenerator.Emit.CodegenRust
public import LeanParserGenerator.Emit.Rust.BridgeIO
public import LeanParserGenerator.Emit.Rust.Report
public import LeanParserGenerator.Emit.CodegenLexerRoundtrip
public import LeanParserGenerator.Emit.CodegenParserRoundtrip
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Frontend.Diagnostics


public section

open Frontend Emit Construct

/-- The release version. Keep in sync with `version` in `lakefile.lean`. -/
def toolVersion : String := "0.1.0-alpha.1"

inductive GrammarViewFormat where
  | bnf
  | markdown

private def parseGrammarViewFormat : String → Option GrammarViewFormat
  | "bnf" => some .bnf
  | "markdown" => some .markdown
  | _ => none

/-- The outputs `--only` can select. -/
inductive OutputKind where
  | verified
  | parser
  | lexer
  | rust
  deriving BEq

private def parseOutputKind : String → Option OutputKind
  | "verified" => some .verified
  | "parser" => some .parser
  | "lexer" => some .lexer
  | "rust" => some .rust
  | _ => none

/-- The directory of a path (everything up to and including the last `/`), or the
    empty string when the path has no directory component. -/
def dirOfPath (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => ""
  | parts => String.intercalate "/" parts ++ "/"

/-- A directory name as a path prefix: empty stays empty, otherwise ends in `/`. -/
def asDirPrefix (d : String) : String :=
  if d.isEmpty || d.endsWith "/" then d else d ++ "/"

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

/-- Is `s` usable as one component of a Lean module name? It must be non-empty, use
    only ASCII letters, digits and underscores, and not start with a digit. -/
def isModuleComponent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
      (c.isAlpha || c == '_') && c.toNat < 128 && rest.all fun d => (d.isAlphanum || d == '_') && d.toNat < 128

/-- `s` with every character that `isModuleComponent` rejects replaced by `_`, and a
    leading `_` when it would start with a digit. Used to suggest a file name. -/
def sanitizeComponent (s : String) : String :=
  let mapped := String.ofList (s.toList.map fun c =>
    if (c.isAlphanum || c == '_') && c.toNat < 128 then c else '_')
  if mapped.isEmpty then "grammar"
  else if mapped.front.isDigit then "_" ++ mapped else mapped

/-- The error for a `.lig` file name that cannot give valid module names, or `none`.
    The generated modules are named `<Base>Parser`, `<Base>Verified` and
    `<Base>Lexer`, where `<Base>` is `baseOfLig`, so the stem has to be an identifier. -/
def ligNameError (ligPath : String) : Option String :=
  let file := (ligPath.splitOn "/").getLast!
  let stem := if file.endsWith ".lig" then (file.dropEnd 4).toString else file
  if isModuleComponent stem then none
  else
    let hint := s!"{sanitizeComponent stem}.lig"
    some s!"cannot infer module names from the file name `{file}`: the generated modules are named after the part before `.lig`, which must contain only ASCII letters, digits and underscores and not start with a digit. Rename the file, for example to `{hint}`."

/-- The error for a module prefix that is not a dotted list of identifiers, or `none`.
    The empty prefix is allowed. `source` says where the prefix came from. -/
def modulePrefixError (source prefix_ : String) : Option String :=
  if prefix_.isEmpty || (prefix_.splitOn ".").all isModuleComponent then none
  else some s!"invalid module prefix `{prefix_}` (from {source}): expected identifiers separated by `.`, each made of ASCII letters, digits and underscores and not starting with a digit"

/-- Prefix a module name with a dotted module prefix, e.g. `calc` + `CalcParser` →
    `calc.CalcParser`. An empty prefix leaves the name top-level. -/
def qualify (prefix_ modName : String) : String :=
  if prefix_.isEmpty then modName else prefix_ ++ "." ++ modName

/-- Print a message to stderr as `error: <message>`. -/
private def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  return 1

private def conflictExitCode (ligPath : String) (tables : Tables) : IO UInt32 := do
  unless tables.conflicts.isEmpty do
    IO.eprintln s!"warning: [{ligPath}] {tables.conflicts.length} Pager LR(1) conflict(s):"
    for conflict in tables.conflicts do
      IO.eprintln s!"    {conflict}"
  return if tables.conflicts.isEmpty then 0 else 2

/-- Format a `.lig` parse error as `file:line:col: message` when the scanner
    embedded a byte offset (`… at byte N`), dropping that suffix. Otherwise the
    message is only prefixed with the file name. Lines and columns start at 1. -/
private def locateParseError (ligPath input msg : String) : String :=
  match extractByteOffset msg with
  | none => s!"{ligPath}: parse error: {msg}"
  | some off =>
      let (line, col) := byteToLineCol input off
      let suffix := s!" at byte {off}"
      let msg := if msg.endsWith suffix then (msg.dropEnd suffix.length).toString else msg
      s!"{ligPath}:{line + 1}:{col + 1}: parse error: {msg}"

private def prepareFile (ligPath : String) : IO (Except String (Surface × PreparedGrammar)) := do
  unless ← System.FilePath.pathExists ligPath do
    return .error s!"cannot read `{ligPath}`: no such file"
  if ← System.FilePath.isDir ligPath then
    return .error s!"cannot read `{ligPath}`: it is a directory"
  let input ← IO.FS.readFile ligPath
  match parseLig input with
  | .error error => return .error (locateParseError ligPath input error)
  | .ok surface0 =>
    match Frontend.Macros.expandMacros surface0 with
    | .error error => return .error s!"{ligPath}: macro expansion error: {error}"
    | .ok surface =>
      -- The checks that the language server runs. Errors stop the generation, and
      -- warnings are printed.
      let ds := semanticDiagnostics surface
      let place (d : LigDiagnostic) : String :=
        -- A diagnostic without a span (start and end both 0) has no position.
        if d.startByte == 0 && d.endByte == 0 then ligPath
        else
          let (line, col) := byteToLineCol input d.startByte
          s!"{ligPath}:{line + 1}:{col + 1}"
      for d in ds do
        if d.severity == .warning then
          IO.eprintln s!"warning: {place d}: {d.message}"
      let errors := ds.filter (·.severity == .error)
      unless errors.isEmpty do
        return .error ("\nerror: ".intercalate (errors.toList.map fun d => s!"{place d}: {d.message}"))
      match prepareGrammar surface with
      | .error error => return .error s!"{ligPath}: {error}"
      | .ok prepared => return .ok (surface, prepared)

/-- Write a generated file, creating its directory, and report it. -/
private def writeOutput (path : String) (contents : String) (what : String) : IO Unit := do
  if let some parent := (System.FilePath.mk path).parent then
    unless parent.toString.isEmpty do IO.FS.createDirAll parent
  IO.FS.writeFile path contents
  IO.println s!"wrote {path} ({what})"

/-- What a generation run was asked to do. -/
structure GenConfig where
  ligPath : String
  /-- Directory for the generated Lean modules. Defaults to the `.lig`'s directory. -/
  outDir : Option String := none
  /-- Dotted module prefix. Overrides `%option module_prefix`. -/
  modulePrefix : Option String := none
  /-- Rust output path. Overrides `%option gen_rust`. -/
  rustOut : Option String := none
  /-- When non-empty, only these outputs are written. -/
  only : List OutputKind := []
  /-- Do not write the proof package of the Rust code (`%option gen_rust_verif`). -/
  skipRustVerif : Bool := false

/-- Generate the modules for a `.lig`. Output paths and module names are inferred
    from the `.lig` stem (`baseOfLig`); the `%lexer` block adds the lexer module,
    `%option roundtrip_lexer` and `%option roundtrip_parser` the roundtrip modules
    and `%option gen_rust` (or `--rust-out`) the Rust file. -/
def generate (cfg : GenConfig) : IO UInt32 := do
  let ligPath := cfg.ligPath
  match ← prepareFile ligPath with
  | .error error => fail error
  | .ok (surface, prepared) =>
    let wants (k : OutputKind) : Bool := cfg.only.isEmpty || cfg.only.contains k
    let dir := asDirPrefix (cfg.outDir.getD (dirOfPath ligPath))
    let base := baseOfLig ligPath
    let prefix_ := cfg.modulePrefix.getD surface.options.modulePrefix
    -- The names matter only when Lean modules are written. `--only rust` skips them.
    if wants .verified || wants .parser || wants .lexer then
      if let some e := ligNameError ligPath then return ← fail e
      let source := if cfg.modulePrefix.isSome then "`--module-prefix`" else "`%option module_prefix`"
      if let some e := modulePrefixError source prefix_ then return ← fail s!"{ligPath}: {e}"
    let verifiedModule := base ++ "Verified"
    let executableModule := base ++ "Parser"
    let executableImport := qualify prefix_ executableModule
    let lexerModule := base ++ "Lexer"
    let lexerImport := qualify prefix_ lexerModule
    let genLexer := surface.lexer.isSome
    if cfg.only.contains .lexer && !genLexer then
      return ← fail s!"{ligPath}: `--only lexer` needs a `%lexer` block in the grammar"
    -- The Rust path from `--rust-out` is relative to the working directory; the one
    -- from `%option gen_rust` is relative to the `.lig`.
    let rustPath : Option String :=
      cfg.rustOut <|> surface.options.genRust.map (dirOfPath ligPath ++ ·)
    if cfg.only.contains .rust && rustPath.isNone then
      return ← fail s!"{ligPath}: no Rust output path; set `%option gen_rust <path>` in the grammar or pass `--rust-out <path>`"
    -- Lean parser modules.
    if wants .verified || wants .parser then
      let lexImportPath : Option String := if genLexer then some lexerImport else none
      match ← generateBothFrom surface prepared verifiedModule executableModule
              (some executableImport) lexImportPath with
      | .error error => return ← fail s!"{ligPath}: generation failed: {error}"
      | .ok (verifiedSource, executableSource) =>
          -- Lexer first: it owns the token type the parser modules import.
          if genLexer && wants .lexer then
            match Emit.generateLexerFrom surface lexerModule with
            | .error e => return ← fail s!"{ligPath}: lexer generation failed: {e}"
            | .ok lexSource =>
                writeOutput (dir ++ lexerModule ++ ".lean") lexSource s!"module {lexerModule}"
          if wants .verified then
            writeOutput (dir ++ verifiedModule ++ ".lean") verifiedSource s!"module {verifiedModule}"
          if wants .parser then
            writeOutput (dir ++ executableModule ++ ".lean") executableSource s!"module {executableModule}"
    else if genLexer && wants .lexer then
      match Emit.generateLexerFrom surface lexerModule with
      | .error e => return ← fail s!"{ligPath}: lexer generation failed: {e}"
      | .ok lexSource =>
          writeOutput (dir ++ lexerModule ++ ".lean") lexSource s!"module {lexerModule}"
    -- Rust.
    if wants .rust then
      if let some rp := rustPath then
        match Emit.Rust.generateRustFrom surface prepared ligPath with
        | .error e => return ← fail s!"{ligPath}: Rust generation failed: {e}"
        | .ok rustSource => writeOutput rp rustSource "Rust"
    -- The proof package of the Rust code, via `%option gen_rust_verif <dir>` (experimental).
    -- Its directory is relative to the `.lig`, like the one of `%option gen_rust`.
    if wants .rust then
      if let some rel := surface.options.genRustVerif then
        let ligDir := dirOfPath ligPath
        if surface.options.genRust.isNone then
          return ← fail s!"{ligPath}: `%option gen_rust_verif` needs `%option gen_rust`"
        if cfg.skipRustVerif then
          IO.println s!"skipped {ligDir ++ rel} (--skip-rust-verif)"
        else if let .error e := Emit.RustBridge.coverage surface then
          if surface.options.rustVerifOptional then
            IO.eprintln s!"warning: {ligPath}: no Rust proof package: {e}"
          else
            return ← fail s!"{ligPath}: {e} (`%option rust_verif_optional` skips the proof package instead)"
        else
          match ← Emit.RustBridge.writeBridge surface prepared ligDir base executableImport lexerImport with
          | .error e => return ← fail s!"{ligPath}: Rust proof package: {e}"
          | .ok files => for f in files do IO.println s!"wrote {f}"
    -- Roundtrip modules (experimental) are opt-in through `%option`s and are written
    -- only when no `--only` restriction is given.
    if cfg.only.isEmpty then
      if genLexer && surface.options.roundtripLexer then
        let rtModule := lexerModule ++ "Roundtrip"
        match Emit.generateRoundtripFrom surface lexerImport lexerModule rtModule with
        | .error e => return ← fail s!"{ligPath}: roundtrip generation failed: {e}"
        | .ok rtSource =>
            writeOutput (dir ++ rtModule ++ ".lean") rtSource s!"module {rtModule}"
      -- The handwritten `<Base>Unparse` module defines `unparse`; a generated lexer
      -- is needed only for `%option roundtrip_format`.
      if surface.options.roundtripParser.isSome then
        let prtModule := executableModule ++ "Roundtrip"
        let unparseImport := qualify prefix_ (base ++ "Unparse")
        match Emit.generateParserRoundtripFrom surface lexerImport lexerModule
                executableImport executableModule unparseImport prtModule with
        | .error e => return ← fail s!"{ligPath}: parser roundtrip generation failed: {e}"
        | .ok prtSource =>
            writeOutput (dir ++ prtModule ++ ".lean") prtSource s!"module {prtModule}"
    conflictExitCode ligPath prepared.tables

/-- Print an inspectable view built from the same augmented grammar data emitted
    into the dependent specification module. The generated module's
    `verifiedGrammarView_agrees` theorem is the checked proof boundary. -/
def printGrammarView (format : GrammarViewFormat) (ligPath : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error => fail error
  | .ok (surface, prepared) =>
      let view := buildVerifiedGrammarView surface prepared.augmented prepared.augProd
      let rendered := match format with
        | .bnf => view.renderBNF
        | .markdown => view.renderMarkdown
      IO.println rendered
      conflictExitCode ligPath prepared.tables

/-- Report which semantic actions the Rust backend could emit (docs/RUST_PARSER.md). The
    resolver imports the header's modules, so run this under `lake env` with those
    modules built. -/
def rustReport (verbose : Bool) (ligPath : String) : IO UInt32 := do
  match ← prepareFile ligPath with
  | .error error => fail error
  | .ok (surface, _) =>
      let mods := Emit.Rust.headerImports surface.header
      let (res, note) ← match ← Emit.Rust.Resolver.ofImports mods with
        | .ok r => pure (r, s!"environment of {mods}")
        | .error e => pure (Emit.Rust.Resolver.empty, s!"none (import of {mods} failed: {e})")
      IO.print (Emit.Rust.report surface res note verbose)
      return 0

private def usageText : String :=
"usage: leanparsergenerator [options] <input.lig>
       leanparsergenerator --print-grammar bnf|markdown <input.lig>
       leanparsergenerator --rust-report [-v] <input.lig>
       leanparsergenerator --help | --version

Generate the Lean modules for a grammar. Outputs are named after the `.lig` stem
(`Expr.lig` gives `ExprVerified.lean`, `ExprParser.lean`, and `ExprLexer.lean` when
the grammar has a `%lexer` block) and written next to it. `%option`s in the `.lig`
add the roundtrip modules and the Rust file.

options:
  --out-dir <dir>          write the Lean modules to <dir> instead of next to the `.lig`
  --module-prefix <path>   dotted module prefix of the generated modules; overrides
                           `%option module_prefix`
  --rust-out <file>        also write the Rust parser to <file>; overrides `%option gen_rust`
  --only <output>          write only this output; repeat to select several.
                           <output> is verified, parser, lexer, or rust.
  --print-grammar <fmt>    print the checked grammar as bnf or markdown; writes no files
  --rust-report [-v]       report which actions the Rust backend can emit; writes no files
  --skip-rust-verif        do not write the proof package of the Rust code
                           (`%option gen_rust_verif`)
  --rust-extract-kernel <lpg-kernel dir> <rust/verif/Kernel dir>
                           rewrite the proved translation of the Rust kernel; writes no
                           other files
  -h, --help               show this help
  --version                show the version

exit codes:
  0  success
  1  error: bad arguments, unreadable input, or a `.lig` or generation error
  2  the grammar has LR(1) conflicts; the requested output is still written
"

private def usageError (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  IO.eprintln "try `leanparsergenerator --help`"
  return 1

/-- What the command line asks for. -/
inductive Command where
  | help
  | version
  | generate (cfg : GenConfig)
  | printGrammar (format : GrammarViewFormat) (ligPath : String)
  | rustReport (verbose : Bool) (ligPath : String)
  | extractKernel (kernel verifKernel : String)

/-- Split `--flag=value` into `(flag, some value)`. -/
private def splitFlag (a : String) : String × Option String :=
  if a.startsWith "--" then
    match a.splitOn "=" with
    | [] => (a, none)
    | [f] => (f, none)
    | f :: rest => (f, some ("=".intercalate rest))
  else (a, none)

/-- Parse the command line. `Except` carries a usage error message. -/
private partial def parseArgs (args : List String) : Except String Command := do
  let mut rest := args
  let mut cfg : GenConfig := { ligPath := "" }
  let mut positional : Array String := #[]
  let mut view : Option GrammarViewFormat := none
  let mut report : Option Bool := none
  let mut verbose := false
  let mut extract : Option (String × String) := none
  let mut help := false
  let mut version := false
  while !rest.isEmpty do
    let a := rest.head!
    rest := rest.tail!
    let (flag, inline) := splitFlag a
    -- The value of a flag that takes one: `--flag=value` or the next argument.
    let value : Unit → Except String String := fun _ =>
      match inline with
      | some v => .ok v
      | none => match rest with
        | v :: _ => .ok v
        | [] => .error s!"`{flag}` needs a value"
    let consume : Bool := inline.isNone
    match flag with
    | "-h" | "--help" => help := true
    | "--version" => version := true
    | "-v" | "--verbose" => verbose := true
    | "--rust-report" => report := some true
    | "--skip-rust-verif" => cfg := { cfg with skipRustVerif := true }
    | "--rust-extract-kernel" =>
        match rest with
        | kernel :: verifKernel :: tl => extract := some (kernel, verifKernel); rest := tl
        | _ => throw "`--rust-extract-kernel` needs two directories: the lpg-kernel crate and the rust/verif/Kernel directory"
    | "--out-dir" =>
        cfg := { cfg with outDir := some (← value ()) }
        if consume then rest := rest.tail!
    | "--module-prefix" =>
        cfg := { cfg with modulePrefix := some (← value ()) }
        if consume then rest := rest.tail!
    | "--rust-out" =>
        cfg := { cfg with rustOut := some (← value ()) }
        if consume then rest := rest.tail!
    | "--only" =>
        let v ← value ()
        if consume then rest := rest.tail!
        match parseOutputKind v with
        | some k => cfg := { cfg with only := cfg.only ++ [k] }
        | none => throw s!"unknown output `{v}` for `--only` (expected verified, parser, lexer, or rust)"
    | "--print-grammar" =>
        let v ← value ()
        if consume then rest := rest.tail!
        match parseGrammarViewFormat v with
        | some f => view := some f
        | none => throw s!"unknown format `{v}` for `--print-grammar` (expected bnf or markdown)"
    | _ =>
        if a.startsWith "-" && a != "-" then throw s!"unknown option `{a}`"
        else positional := positional.push a
  if help then return .help
  if version then return .version
  if let some (kernel, verifKernel) := extract then return .extractKernel kernel verifKernel
  if positional.size > 1 then
    throw s!"expected one input file, got {positional.size}: {" ".intercalate positional.toList}"
  let some lig := positional[0]? | throw "missing input file"
  if verbose && report.isNone then throw "`-v` is only meaningful with `--rust-report`"
  match view, report with
  | some _, some _ => throw "`--print-grammar` and `--rust-report` cannot be combined"
  | some f, none => return .printGrammar f lig
  | none, some _ => return .rustReport verbose lig
  | none, none => return .generate { cfg with ligPath := lig }

def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg => usageError msg
  | .ok .help => IO.print usageText; return 0
  | .ok .version => IO.println s!"leanparsergenerator {toolVersion} (Lean {Lean.versionString})"; return 0
  | .ok (.generate cfg) => generate cfg
  | .ok (.printGrammar f lig) => printGrammarView f lig
  | .ok (.rustReport v lig) => rustReport v lig
  | .ok (.extractKernel kernel verifKernel) =>
      match ← Emit.RustBridge.extractKernel kernel verifKernel with
      | .ok () =>
          IO.println s!"wrote {verifKernel}/Types.lean and {verifKernel}/Funs.lean"
          return 0
      | .error e => fail e

def main (args : List String) : IO UInt32 := do
  try run args
  catch e => fail e.toString
