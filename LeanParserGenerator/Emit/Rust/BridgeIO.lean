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
Writing the proof package of `%option gen_rust_verif` (docs/RUST_VERIFICATION.md).

The generator finds the Rust crate of the generated file (the nearest `Cargo.toml`) and asks
Cargo where its `lpg_kernel` dependency is. The proved kernel is the one in `rust/verif/` next to
that kernel crate (`<kernel>/../verif`). Then it

1. translates the crate's kernel with Charon and Aeneas and checks that the translation is the
   one `rust/verif/Kernel/` holds, the one the generic proofs are about;
2. translates the grammar crate from `parse` and `lex`, with the kernel as an external
   dependency, into the package's `Types.lean` and `Funs.lean`;
3. writes the lexer certificate, the proofs, the root module, and, once, the lakefile.

`charon` and `aeneas` are looked up on `PATH`, then in `$AENEAS_DIR/charon/bin` and
`$AENEAS_DIR/bin`. `extractKernel` is also the `--rust-extract-kernel` command, which
regenerates `rust/verif/Kernel/` after a change to the kernel.
-/
public import LeanParserGenerator.Emit.Rust.Bridge
public import Lean.Data.Json

@[expose] public section

namespace Emit.RustBridge

open Frontend Lean

/-- `xs` with a separator. -/
private def joinPath (a b : System.FilePath) : System.FilePath := a / b

/-- A program on `PATH`, or in `$AENEAS_DIR`. -/
def findTool (name : String) : IO (Option String) := do
  let path := (← IO.getEnv "PATH").getD ""
  for dir in path.splitOn ":" do
    if !dir.isEmpty then
      let p := System.FilePath.mk dir / name
      if ← p.pathExists then return some p.toString
  if let some ad := ← IO.getEnv "AENEAS_DIR" then
    for sub in ["charon/bin", "bin"] do
      let p := System.FilePath.mk ad / sub / name
      if ← p.pathExists then return some p.toString
  return none

/-- Run a program; its output, or an error with its output. -/
def runTool (cmd : String) (args : Array String) (cwd : System.FilePath) :
    IO (Except String String) := do
  let out ← IO.Process.output { cmd, args, cwd := some cwd }
  if out.exitCode != 0 then
    return .error s!"`{cmd} {" ".intercalate args.toList}` failed ({out.exitCode}):\n{out.stdout}{out.stderr}"
  -- Aeneas reports a partial translation with exit code 0 and `[Error]` lines.
  let o := out.stdout ++ out.stderr
  if o.contains "[Error]" || o.contains "mError\x1b" then
    return .error s!"`{cmd}` reported errors:\n{out.stdout}{out.stderr}"
  return .ok out.stdout

/-- The nearest directory above `p` with a `Cargo.toml`. -/
partial def crateDirOf (p : System.FilePath) : IO (Option System.FilePath) := do
  match p.parent with
  | none => return none
  | some d =>
    if ← (d / "Cargo.toml").pathExists then return some d
    else if d.toString.isEmpty || d == p then return none
    else crateDirOf d

/-- What Cargo says about a crate: the name of its library (or, without one, of its binary),
    the Cargo arguments that select that target, and the directory of its `lpg_kernel`
    dependency. -/
def cargoInfo (crate : System.FilePath) :
    IO (Except String (String × Array String × System.FilePath)) := do
  let out ← IO.Process.output
    { cmd := "cargo", args := #["metadata", "--format-version", "1"], cwd := some crate }
  if out.exitCode != 0 then return .error s!"`cargo metadata` failed:\n{out.stderr}"
  match Json.parse out.stdout with
  | .error e => return .error s!"cannot read `cargo metadata`: {e}"
  | .ok j =>
    let some pkgs := (j.getObjValD "packages").getArr?.toOption
      | return .error "`cargo metadata` has no packages"
    let manifest := (← IO.FS.realPath (crate / "Cargo.toml")).toString
    let mut libName : Option String := none
    let mut binName : Option String := none
    let mut kernel : Option System.FilePath := none
    for p in pkgs do
      let mp := (p.getObjValD "manifest_path").getStr?.toOption.getD ""
      let name := (p.getObjValD "name").getStr?.toOption.getD ""
      if name == "lpg_kernel" then
        kernel := (System.FilePath.mk mp).parent
      if mp == manifest then
        for t in ((p.getObjValD "targets").getArr?.toOption.getD #[]) do
          let kinds := (t.getObjValD "kind").getArr?.toOption.getD #[]
          let tname := (t.getObjValD "name").getStr?.toOption
          if kinds.any (·.getStr?.toOption == some "lib") then
            libName := tname
          else if kinds.any (·.getStr?.toOption == some "bin") && binName.isNone then
            binName := tname
    let some k := kernel | return .error s!"the crate at {crate} does not depend on `lpg_kernel`"
    match libName, binName with
    | some l, _ => return .ok (l.replace "-" "_", #["--lib"], k)
    | none, some b => return .ok (b.replace "-" "_", #["--bin", b], k)
    | none, none => return .error s!"the crate at {crate} has no library or binary target"

/-- The part of an Aeneas file from its own first line on (without the header we add). -/
def aeneasBody (s : String) : String :=
  match s.splitOn "-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS" with
  | [_, rest] => "-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS" ++ rest
  | _ => s

/-- Translate the kernel crate at `kernel` into `out/{Types,Funs}.lean` (in a scratch
    directory `tmp`), with the names `Kernel.Types` and `Kernel.Funs`. Returns the two files
    and the names Aeneas lists as external. -/
def translateKernel (charon aeneas : String) (kernel tmp : System.FilePath) :
    IO (Except String (String × String × String)) := do
  IO.FS.createDirAll tmp
  let tmp ← IO.FS.realPath tmp
  let llbc := tmp / "Kernel.llbc"
  if let .error e ← runTool charon #["cargo", "--preset=aeneas", "--dest-file", llbc.toString] kernel then
    return .error e
  let out := tmp / "kernel-out"
  if let .error e ← runTool aeneas #["-backend", "lean", llbc.toString, "-split-files",
      "-dest", out.toString] kernel then
    return .error e
  let types ← IO.FS.readFile (out / "Types.lean")
  let funs ← IO.FS.readFile (out / "Funs.lean")
  let tmpl ← if ← (out / "FunsExternal_Template.lean").pathExists then
    IO.FS.readFile (out / "FunsExternal_Template.lean") else pure ""
  return .ok (types, funs, tmpl)

/-- The names of the axioms of an Aeneas `FunsExternal_Template.lean`. -/
def externalNames (tmpl : String) : List String :=
  (tmpl.splitOn "\n").filterMap fun l =>
    if l.startsWith "axiom " then ((l.drop 6).toString.splitOn " ").head? else none

/-- `--rust-extract-kernel`: translate the kernel crate into `rust/verif/Kernel/{Types,Funs}.lean`,
    and check that every function Aeneas has no model for is defined in
    `rust/verif/Kernel/FunsExternal.lean`. -/
def extractKernel (kernel verifKernel : System.FilePath) : IO (Except String Unit) := do
  let some charon ← findTool "charon" | return .error "`charon` not found (PATH, $AENEAS_DIR)"
  let some aeneas ← findTool "aeneas" | return .error "`aeneas` not found (PATH, $AENEAS_DIR)"
  let tmp := verifKernel / ".." / ".lake" / "extract"
  match ← translateKernel charon aeneas kernel tmp with
  | .error e => return .error e
  | .ok (types, funs, tmpl) =>
    let ext ← IO.FS.readFile (verifKernel / "FunsExternal.lean")
    for name in externalNames tmpl do
      unless ext.contains s!"def {name}" do
        return .error s!"rust/verif/Kernel/FunsExternal.lean has no definition of `{name}`"
    let h := header "the Charon and Aeneas translation of rust/lpg-kernel \
      (`leanparsergenerator --rust-extract-kernel`)"
    IO.FS.writeFile (verifKernel / "Types.lean") (h ++ aeneasBody types)
    IO.FS.writeFile (verifKernel / "Funs.lean") (h ++ aeneasBody funs)
    return .ok ()

/-- The Lean prefix of a Rust module from the path of its file in the crate: `src/generated.rs`
    is `generated.`. -/
def rustModOf (crate rustFile : System.FilePath) : IO (Except String (String × String)) := do
  let src := (← IO.FS.realPath (crate / "src")).toString ++ "/"
  let file := (← IO.FS.realPath rustFile).toString
  unless file.startsWith src && file.endsWith ".rs" do
    return .error s!"the generated Rust file {rustFile} is not under {crate}/src"
  let rel := ((file.drop src.length).toString.dropEnd 3).toString
  let segs := (rel.splitOn "/").filter (· != "mod")
  if segs == ["lib"] || segs == ["main"] then
    return .error "the generated Rust file must be a module of the crate, not its root"
  return .ok (".".intercalate segs ++ ".", "::".intercalate ("crate" :: segs))

/-- The path of `dst` relative to the directory `src` (both absolute). -/
def relPath (src dst : System.FilePath) : String :=
  let a := (src.toString.splitOn "/").filter (· != "")
  let b := (dst.toString.splitOn "/").filter (· != "")
  let common := (a.zip b).takeWhile (fun (x, y) => x == y) |>.length
  let ups := List.replicate (a.length - common) ".."
  "/".intercalate (ups ++ b.drop common)


/-- Write the proof package of a grammar. `ligDir` is the directory of the `.lig`; `base` its
    base name (`Cedar`); `parserImport` and `lexerImport` the modules of the generated Lean
    parser and lexer. -/
def writeBridge (s : Surface) (prepared : PreparedGrammar) (ligDir base parserImport lexerImport : String) :
    IO (Except String (List String)) := do
  let some rel := s.options.genRustVerif | return .ok []
  if let .error e := coverage s then return .error e
  let some rustRel := s.options.genRust | return .error "`gen_rust_verif` needs `gen_rust`"
  let some charon ← findTool "charon"
    | return .error "`%option gen_rust_verif` needs `charon` (PATH, $AENEAS_DIR)"
  let some aeneas ← findTool "aeneas"
    | return .error "`%option gen_rust_verif` needs `aeneas` (PATH, $AENEAS_DIR)"
  let rustFile := System.FilePath.mk (ligDir ++ rustRel)
  let some crate ← crateDirOf rustFile
    | return .error s!"no Cargo.toml above {rustFile}"
  let (crateNs, targetArgs, kernel) ← match ← cargoInfo crate with
    | .ok r => pure r
    | .error e => return .error e
  let verif ← IO.FS.realPath (kernel / ".." / "verif")
  unless ← (verif / "Kernel" / "Funs.lean").pathExists do
    return .error s!"no proved kernel at {verif}/Kernel (the `rust/verif` package next to {kernel})"
  let bridgeDir := System.FilePath.mk (ligDir ++ rel)
  let bridge := base ++ "RustBridge"
  IO.FS.createDirAll (bridgeDir / ".lake" / "extract")
  let tmp ← IO.FS.realPath (bridgeDir / ".lake" / "extract")
  -- 1. The crate's kernel is the proved one.
  match ← translateKernel charon aeneas kernel tmp with
  | .error e => return .error e
  | .ok (types, funs, _) =>
    let pt ← IO.FS.readFile (verif / "Kernel" / "Types.lean")
    let pf ← IO.FS.readFile (verif / "Kernel" / "Funs.lean")
    unless aeneasBody types == aeneasBody pt && aeneasBody funs == aeneasBody pf do
      return .error s!"the translation of the kernel at {kernel} is not the proved one in \
        {verif}/Kernel; after changing the kernel, run `leanparsergenerator --rust-extract-kernel` \
        and update the proofs"
  -- 2. The grammar crate.
  let (rustMod, rustPath) ← match ← rustModOf crate rustFile with
    | .ok r => pure r
    | .error e => return .error e
  let llbc := tmp / s!"{bridge}.llbc"
  let starts := #["--start-from", rustPath ++ "::parse"] ++
    (if s.lexer.isSome then #["--start-from", rustPath ++ "::lex"] else #[])
  if let .error e ← runTool charon (#["cargo", "--preset=aeneas", "--opaque", "lpg_kernel"] ++
      starts ++ #["--dest-file", llbc.toString, "--"] ++ targetArgs) crate then
    return .error e
  let out := tmp / "grammar-out"
  if let .error e ← runTool aeneas #["-backend", "lean", llbc.toString, "-split-files",
      "-max-heartbeats", "4000000", "-max-recdepth", "16384", "-dest", out.toString] crate then
    return .error e
  let modDir := bridgeDir / bridge
  IO.FS.createDirAll modDir
  let mut written : List String := []
  let tr := s!"the Charon and Aeneas translation of {rustPath}"
  for f in ["Types", "Funs"] do
    let txt ← IO.FS.readFile (out / s!"{f}.lean")
    IO.FS.writeFile (modDir / s!"{f}.lean") (header tr ++ aeneasBody txt)
    written := written ++ [(modDir / s!"{f}.lean").toString]
  IO.FS.writeFile (modDir / "TypesExternal.lean")
    (header "the kernel's types are those of the proved kernel" ++ "module\npublic import Kernel.Types\n")
  IO.FS.writeFile (modDir / "FunsExternal.lean")
    (header "the kernel's functions are those of the proved kernel" ++ "module\npublic import Kernel.Funs\n")
  -- 3. Certificate, proofs, root module, lakefile.
  let parserNs := (parserImport.splitOn ".").getLastD parserImport
  let lexerNs := (lexerImport.splitOn ".").getLastD lexerImport
  let n : Names := ⟨bridge, crateNs, rustMod, parserImport, parserNs, lexerImport, lexerNs⟩
  IO.FS.writeFile (modDir / "Proof.lean") (renderProof n s prepared)
  written := written ++ [(modDir / "Proof.lean").toString]
  if let some spec := s.lexer then
    let augEof := prepared.augmented.numTerminals - 1
    match lexData s augEof spec with
    | .error e => return .error e
    | .ok d =>
      IO.FS.writeFile (modDir / "LexCert.lean") (renderLexCert n d)
      IO.FS.writeFile (modDir / "LexProof.lean") (renderLexProof n s d)
      written := written ++ [(modDir / "LexCert.lean").toString, (modDir / "LexProof.lean").toString]
  IO.FS.writeFile (bridgeDir / s!"{bridge}.lean") (renderRoot n s.lexer.isSome)
  -- The verif package, relative to the bridge.
  let bridgeAbs ← IO.FS.realPath bridgeDir
  let relVerif := relPath bridgeAbs verif
  unless ← (bridgeDir / "lakefile.lean").pathExists do
    IO.FS.writeFile (bridgeDir / "lakefile.lean") (renderLakefile n relVerif)
  unless ← (bridgeDir / "lean-toolchain").pathExists do
    IO.FS.writeFile (bridgeDir / "lean-toolchain") (← IO.FS.readFile (verif / "lean-toolchain"))
  return .ok written

end Emit.RustBridge
