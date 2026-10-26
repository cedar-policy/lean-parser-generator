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
The offline lexer backend.

Given a `.lig` `%lexer { … }` block (parsed into `Frontend.LexerSpec`), this
renders an inspectable `FooLexer.lean` module: the tokenizer with its DFA tables
and validator certificate as literal data, the a-posteriori validation theorem
(`native_decide`), the maximal-munch soundness corollary, and a `tokenize` entry
point. The DFA and certificate are built here, at generation time, by ordinary
compiled code (`Lexer.DFA.build?WithVecs`) — the same place Pager construction runs
for the parser — so no elaboration-time macro is involved and the emitted source is
what a reader audits.

This mirrors the parser backends (`Emit/Codegen.lean`, `Emit/CodegenVerified.lean`):
untrusted construction + emission, with the emitted `native_decide` validation the
checked boundary (docs/DESIGN.md §9.7).
-/
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Lexer.Validator
public import LeanParserGenerator.Emit.Builder


@[expose] public section

namespace Emit

open Frontend Lexer

/-! ### String renderers for the compiled data

These produce Lean source text (not `Syntax`), mirroring the constructors so the
generated module reads like hand-written data. -/

/-- A `(lo, hi)` pair. -/
def rangeStr (r : Nat × Nat) : String := s!"({r.1}, {r.2})"

/-- A `CharClass` as source (ranges-only, per docs/DESIGN.md §9.7 step 0). -/
def charClassStr (k : CharClass) : String :=
  let elems := String.intercalate ", " (k.rs.map rangeStr)
  s!"(Lexer.CharClass.ranges {k.neg} [{elems}])"

/-- A `Regex` as source. -/
partial def regexStr : Regex → String
  | .never => "Lexer.Regex.never"
  | .epsilon => "Lexer.Regex.epsilon"
  | .cls k => s!"(Lexer.Regex.cls {charClassStr k})"
  | .cat a b => s!"(Lexer.Regex.cat {regexStr a} {regexStr b})"
  | .alt a b => s!"(Lexer.Regex.alt {regexStr a} {regexStr b})"
  | .star a => s!"(Lexer.Regex.star {regexStr a})"

/-- A `DTrans` as source. -/
def dtransStr (t : DTrans) : String :=
  s!"(Lexer.DTrans.mk {charClassStr t.cls} {t.target})"

/-- A `DState` as source. -/
def dstateStr (s : DState) : String :=
  let trans := String.intercalate ", " (s.trans.toList.map dtransStr)
  let accept := match s.accept with
    | none => "none"
    | some r => s!"(some {r})"
  s!"(Lexer.DState.mk #[{trans}] {accept})"

/-- A `DFA` as source. -/
def dfaStr (d : DFA) : String :=
  let states := String.intercalate ",\n    " (d.states.toList.map dstateStr)
  s!"(Lexer.DFA.mk #[\n    {states}])"

/-- A `LexCert` as source. -/
def certStr (vecs : Array (Array Regex)) : String :=
  let vs := vecs.toList.map fun vec =>
    let rs := String.intercalate ", " (vec.toList.map regexStr)
    s!"#[{rs}]"
  s!"(Lexer.LexCert.mk #[\n    {String.intercalate ",\n    " vs}])"

/-! ### Token type

In the generated regime the lexer module owns the token type: it is emitted from
the `%token` declarations (the single source of truth), and the parser modules
import this module for it (docs/DESIGN.md §8, §9). -/

/-- Render `inductive <tokenType>` from the `%token` declarations: valueless tokens
    are nullary, `%token <T> NAME` becomes `NAME : T → <tokenType>`. Derives the
    instances the parser codegen and runtime need. -/
def tokInductiveStr (tokTy : String) (tokens : Array TokenDecl) : String :=
  let ctors := tokens.toList.map fun t =>
    if t.hasVal then s!"  | {t.name} : {t.ty} → {tokTy}"
    else s!"  | {t.name}"
  s!"inductive {tokTy} where\n" ++
  String.intercalate "\n" ctors ++ "\n" ++
  s!"  deriving Repr, BEq, Inhabited, DecidableEq\n"

/-! ### Action closures -/

/-- Render a `LexerTrans` as a `Lexer.Trans` source term, resolving mode names to
    indices via `modeIdx`. -/
def transStr (modeIdx : String → Option Nat) : LexerTrans → Except String String
  | .stay => .ok "Lexer.Trans.stay"
  | .pop => .ok "Lexer.Trans.pop"
  | .push m =>
      match modeIdx m with
      | some i => .ok s!"(Lexer.Trans.push {i})"
      | none => .error s!"lexer rule enters unknown mode `{m}`"

/-- Render a rule's action closure `String → Lexer.Act Tok`. -/
def actionStr (tokTy : String) (modeIdx : String → Option Nat)
    (r : LexerRule) : Except String String := do
  let tr ← transStr modeIdx r.trans
  let body := match r.emit with
    | none => s!"(Lexer.Act.mk none {tr})"
    | some e => s!"(Lexer.Act.mk (some ({e})) {tr})"
  -- Bind the matched text if the rule uses it; otherwise ignore it.
  let binder := match r.binder with
    | some x => if r.emit.isSome then x else "_"
    | none => "_"
  return s!"(fun ({binder} : String) => ({body} : Lexer.Act {tokTy}))"

/-! ### Module assembly -/

/-- Generate the `FooLexer.lean` source from a `.lig` surface with a `%lexer`
    block. `moduleName` is used only for the leading comment. Fails if the surface
    has no lexer, if DFA construction runs out of fuel, or if a rule enters an
    unknown mode. -/
def generateLexerFrom (surface : Surface) (moduleName : String) :
    Except String String := do
  let some spec := surface.lexer
    | .error "no `%lexer` block in the grammar; nothing to generate"
  let tokTy := surface.tokenType
  let modeNames := spec.modes.map (·.name)
  let modeIdx : String → Option Nat := fun s => modeNames.findIdx? (· == s)
  -- Build each mode's DFA + certificate now (generation time).
  let mut modeData : Array (LexerMode × DFA × Array (Array Regex)) := #[]
  for mode in spec.modes do
    let regexes := mode.rules.map (·.regex)
    match DFA.build?WithVecs regexes with
    | some (dfa, vecs) => modeData := modeData.push (mode, dfa, vecs)
    | none => .error s!"DFA construction for mode `{mode.name}` ran out of fuel"
  -- Render the tokenizer (rule regexes + action closures), per mode.
  let mut modeStrs : Array String := #[]
  for mode in spec.modes do
    let mut ruleStrs : Array String := #[]
    for r in mode.rules do
      let act ← actionStr tokTy modeIdx r
      ruleStrs := ruleStrs.push
        s!"    (Lexer.Rule.mk {regexStr r.regex} {act})"
    modeStrs := modeStrs.push ("[\n" ++ String.intercalate ",\n" ruleStrs.toList ++ "]")
  let eofStr := match spec.eof with
    | none => "none"
    | some e => s!"(some ({e}))"
  let tokenizerVal :=
    "{ modes := #[\n" ++ String.intercalate ",\n" modeStrs.toList ++ "]\n" ++
    s!"  , start := 0\n  , eofToken := {eofStr} }"
  let mut proofBlocks : Array String := #[]
  for h : m in [0:modeData.size] do
    let (mode, dfa, vecs) := modeData[m]
    let rulesStr := String.intercalate ", " (mode.rules.toList.map (fun r => regexStr r.regex))
    let block :=
      s!"def {moduleName}.rules{m} : Array Lexer.Regex := #[{rulesStr}]\n\n" ++
      s!"def {moduleName}.dfa{m} : Lexer.DFA :=\n  {dfaStr dfa}\n\n" ++
      s!"def {moduleName}.cert{m} : Lexer.LexCert :=\n  {certStr vecs}\n\n"
    let proofs :=
      s!"theorem {moduleName}.validated{m} :\n" ++
      s!"    Lexer.validate {moduleName}.rules{m} {moduleName}.dfa{m} {moduleName}.cert{m} = true := by\n" ++
      s!"  native_decide\n\n" ++
      s!"theorem {moduleName}.scanSound{m} (cs : List Char) :\n" ++
      s!"    Lexer.DFA.scan {moduleName}.dfa{m} cs = Lexer.fusedScan {moduleName}.rules{m} cs 0 none :=\n" ++
      s!"  Lexer.scan_sound {moduleName}.validated{m} cs\n\n"
    proofBlocks := proofBlocks.push (block ++ proofs)
  let header := surface.header
  let dfaRefs := String.intercalate ", " ((List.range modeData.size).map (fun m => s!"{moduleName}.dfa{m}"))
  let flatRefs := String.intercalate ", "
    ((List.range modeData.size).map (fun m => s!"Lexer.DFA.flatOfDFA {moduleName}.dfa{m}"))
  let textDepRefs := String.intercalate ", " (spec.modes.toList.map (fun mode =>
    let flags := mode.rules.toList.map (fun r =>
      if r.binder.isSome && r.emit.isSome then "true" else "false")
    "#[" ++ String.intercalate ", " flags ++ "]"))
  -- Per-mode a-posteriori validation of the flat tables against the DFAs, so
  -- `tokenizeFlatStr` (the emitted `tokenize`) is provably equal to the spec
  -- `tokenize`. Discharged by `native_decide` like the derivative-vector validator.
  let flatProofs := String.intercalate "" ((List.range modeData.size).map (fun m =>
    s!"theorem {moduleName}.flatValidated{m} :\n" ++
    s!"    Lexer.flatValidate ({moduleName}.cflat.flats.getD {m} default)\n" ++
    s!"      ({moduleName}.cflat.base.dfas.getD {m} default) = true := by native_decide\n\n"))
  let lexerHeaderBlock := if surface.lexerHeader.isEmpty then "" else surface.lexerHeader ++ "\n\n"
  let byteProofs := String.intercalate "" ((List.range modeData.size).map (fun m =>
    s!"theorem {moduleName}.byteValidated{m} :\n" ++
    s!"    Lexer.byteValidate ({moduleName}.cbyte.bytes.getD {m} default)\n" ++
    s!"      ({moduleName}.cflat.flats.getD {m} default) = true := by native_decide\n\n"))
  let out :=
    s!"module\n" ++
    s!"-- Generated by leanparsergenerator from a .lig `%lexer` block. Do not edit.\n" ++
    s!"-- Module: {moduleName}\n" ++
    "public import LeanParserGenerator.Lexer.Engine\n" ++
    "public import LeanParserGenerator.Lexer.Validator\n" ++
    "public import LeanParserGenerator.Lexer.StringScan\n" ++
    "public import LeanParserGenerator.Lexer.FlatTokenize\n" ++
    "public import LeanParserGenerator.Lexer.ByteTokenize\n" ++
    "public import LeanParserGenerator.Lexer.ByteValidator\n" ++
    "public import LeanParserGenerator.Lexer.DFA\n" ++
    "public import LeanParserGenerator.Lexer.ByteScan\n" ++
    -- `native_decide` evaluates the DFA/flat/byte tables and the validators at the
    -- meta phase, so the modules it reduces are also `meta`-imported. The plain
    -- `public import`s above keep them available to the ordinary `cflat`/`cbyte`
    -- definitions (module system: a module used in both phases is imported twice).
    "meta import LeanParserGenerator.Lexer.Validator\n" ++
    "meta import LeanParserGenerator.Lexer.ByteTokenize\n" ++
    "meta import LeanParserGenerator.Lexer.ByteValidator\n" ++
    "meta import LeanParserGenerator.Lexer.DFA\n" ++
    "meta import LeanParserGenerator.Lexer.ByteScan\n" ++
    "meta import LeanParserGenerator.Lexer.FlatTokenize\n\n" ++
    Builder.publicizeImports header ++ "\n\n" ++
    -- Large lexers (many-rule lexers) need a raised heartbeat/recursion budget for
    -- the `native_decide` validations and the big literal certificate to elaborate.
    -- Emitting these unconditionally is harmless for small lexers and removes the
    -- previously hand-added set_options that regeneration used to drop.
    "set_option maxHeartbeats 4000000\n" ++
    "set_option maxRecDepth 1000000\n\n" ++
    -- The lexer's public API is the token type and `tokenize`/`tokenizeByte`. The
    -- DFA/flat/byte tables and validator certificates are implementation detail;
    -- `public section` (not `@[expose]`) keeps their bodies in the private scope.
    -- The lexer's own `native_decide` validations reduce them via the `meta`
    -- imports above; downstream consumers use only the public API (module system).
    "public section\n\n" ++
    -- The lexer module owns the token type (generated from `%token`).
    tokInductiveStr tokTy surface.tokens ++ "\n" ++
    -- Lexer-only helpers (keyword folding, string stripping, …).
    lexerHeaderBlock ++
    String.intercalate "" proofBlocks.toList ++
    s!"def {moduleName}.tokenizer : Lexer.Tokenizer {tokTy} :=\n  {tokenizerVal}\n\n" ++
    s!"def {moduleName}.lexer : Lexer.Compiled {tokTy} :=\n" ++
    s!"  \{ dfas := #[{dfaRefs}]\n" ++
    s!"  , acts := ({moduleName}.tokenizer).modes.map (fun rules => (rules.map (·.act)).toArray)\n" ++
    s!"  , start := ({moduleName}.tokenizer).start\n" ++
    s!"  , eofToken := ({moduleName}.tokenizer).eofToken }\n\n" ++
    s!"def {moduleName}.cflat : Lexer.CompiledFlat {tokTy} :=\n" ++
    s!"  \{ base := {moduleName}.lexer\n" ++
    s!"  , flats := #[{flatRefs}]\n" ++
    s!"  , textDep := #[{textDepRefs}] }\n\n" ++
    flatProofs ++
    s!"def {moduleName}.tokenize (input : String) : Except Lexer.LexError (List (Runtime.Positioned {tokTy})) :=\n" ++
    s!"  Lexer.tokenizeFlatStrPos {moduleName}.cflat input\n\n" ++
    s!"def {moduleName}.tokenizeBare (input : String) : Except Lexer.LexError (List {tokTy}) :=\n" ++
    s!"  Lexer.tokenizeFlatStr {moduleName}.cflat input\n\n" ++
    s!"def {moduleName}.cbyte : Lexer.CompiledByte {tokTy} :=\n" ++
    s!"  Lexer.CompiledByte.ofFlat {moduleName}.cflat\n\n" ++
    byteProofs ++
    s!"def {moduleName}.tokenizeByte (input : String) : Except Lexer.LexError (List {tokTy}) :=\n" ++
    s!"  Lexer.tokenizeByte {moduleName}.cbyte input\n"
  return out

end Emit
