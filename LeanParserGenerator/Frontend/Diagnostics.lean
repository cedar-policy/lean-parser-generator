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
This module implements diagnostics for language servers, so that editing a `.lig`
file reports precise errors.

See also `LeanParserGenerator/LSP/Server.lean` for the server implementation.
The functionality in this module is independent of the LSP details, so it can be
unit-tested without any LSP plumbing:

    collectDiagnostics : String → Array LigDiagnostic

One difference from the code generation path is that this module uses the
untrusted parser (`Frontend.parseLig`). It allows more flexible error reporting
for rejected inputs. As the error reporting in LPG improves, we may switch to the
generated verified parser everywhere; maintaining the untrusted parser is
cumbersome.

Every diagnostic carries a half-open byte range into the
source, a severity, and a human-readable message. Byte ranges are derived from
the source `Span`s that the frontend already threads through `Surface`, or, for
scanner errors, from the `… at byte N` offset embedded in the parser's message.

The server layer converts byte ranges to LSP line/character positions with
`byteToLineCol` below (UTF-16 code units, per the LSP specification).
-/
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Emit.Codegen


@[expose] public section

namespace Frontend

/-- Severity of a `.lig` diagnostic. Mirrors the LSP severities the server
    emits; kept independent of `Lean.Lsp` so the engine stays pure and testable. -/
inductive DiagSeverity where
  | error
  | warning
  | information
  deriving Repr, DecidableEq, Inhabited

/-- A single diagnostic over a half-open byte range `[startByte, endByte)` of the
    `.lig` source. -/
structure LigDiagnostic where
  startByte : Nat
  endByte : Nat
  severity : DiagSeverity
  message : String
  deriving Repr, Inhabited

namespace LigDiagnostic

/-- Build a diagnostic from a source `Span`. -/
def ofSpan (sp : Span) (severity : DiagSeverity) (message : String) : LigDiagnostic :=
  { startByte := sp.startPos.byteIdx, endByte := sp.endPos.byteIdx, severity, message }

end LigDiagnostic

/-! ### Byte-offset → LSP position conversion -/

/-- The UTF-16 code-unit width of a character: astral-plane code points
    (`> 0xFFFF`) occupy a surrogate pair. -/
def utf16Width (c : Char) : Nat :=
  if c.val.toNat ≥ 0x10000 then 2 else 1

/-- Convert a byte offset into a zero-based `(line, character)` position, where
    `character` is measured in UTF-16 code units as the LSP specification
    requires. Offsets past the end clamp to the final position. -/
def byteToLineCol (text : String) (target : Nat) : Nat × Nat := Id.run do
  let mut line := 0
  let mut col := 0
  let mut b := 0
  for c in text.toList do
    if b ≥ target then
      return (line, col)
    if c == '\n' then
      line := line + 1
      col := 0
    else
      col := col + utf16Width c
    b := b + (String.singleton c).utf8ByteSize
  return (line, col)

/-! ### Scanner-error offset extraction -/

/-- Parse the leading run of decimal digits of a string, if any. -/
def leadingNat? (s : String) : Option Nat :=
  let digits := s.takeWhile Char.isDigit
  if digits.isEmpty then none else digits.toNat?

/-- The frontend's scanner errors embed a byte offset as `… at byte N`. Recover
    that offset so the diagnostic can be placed precisely. Returns `none` for
    structural errors that carry no offset (e.g. a missing `%%`). -/
def extractByteOffset (msg : String) : Option Nat :=
  let parts := msg.splitOn "byte "
  match parts.reverse with
  | tail :: _ :: _ => leadingNat? tail
  | _ => none

/-! ### Semantic checks over a parsed `Surface`

These reuse the spans the frontend already records, so a problem is highlighted
at the exact grammar symbol, token, or rule that caused it. -/

/-- Is `name` a declared token or a rule head (nonterminal)? -/
def knownSymbol (s : Surface) (name : String) : Bool :=
  (s.termIdx name).isSome || (s.ntIdx name).isSome

/-- Collect semantic diagnostics from a successfully parsed `Surface`. -/
def semanticDiagnostics (s : Surface) : Array LigDiagnostic := Id.run do
  let mut ds : Array LigDiagnostic := #[]

  -- Start symbol must be a rule head.
  if (s.ntIdx s.start).isNone then
    ds := ds.push {
      startByte := 0, endByte := 0, severity := .error,
      message := s!"start symbol `{s.start}` is not a rule head (no `{s.start} :: …` rule)" }

  -- Duplicate `%token` declarations.
  let mut seenTok : Array String := #[]
  for t in s.tokens do
    if seenTok.contains t.name then
      ds := ds.push (LigDiagnostic.ofSpan t.span .warning
        s!"token `{t.name}` is declared more than once")
    else
      seenTok := seenTok.push t.name

  -- Conflicting result types for the same nonterminal across its rules.
  let mut ntTy : Array (String × String) := #[]
  for r in s.rules do
    match ntTy.find? (·.1 == r.lhs) with
    | some (_, ty0) =>
      if ty0 != r.ty then
        ds := ds.push (LigDiagnostic.ofSpan r.span .warning
          s!"nonterminal `{r.lhs}` is given two result types: `{ty0}` and `{r.ty}`")
    | none => ntTy := ntTy.push (r.lhs, r.ty)

  -- Per-element checks: undefined symbols and misuse of the EOF token.
  for r in s.rules do
    for alt in r.alts do
      for e in alt.elems do
        if !knownSymbol s e.sym then
          ds := ds.push (LigDiagnostic.ofSpan e.span .error
            s!"symbol `{e.sym}` in rule `{r.lhs}` is neither a declared token nor a nonterminal")
        else if e.sym == s.eof then
          ds := ds.push (LigDiagnostic.ofSpan e.span .error
            s!"the end-of-input token `{e.sym}` must not appear inside a production")

  -- Nonterminals that are defined but never referenced (and are not the start
  -- symbol) — reported as low-severity information.
  let mut used : Array String := #[]
  for r in s.rules do
    for alt in r.alts do
      for e in alt.elems do
        unless used.contains e.sym do used := used.push e.sym
  for r in s.rules do
    if r.lhs != s.start && !used.contains r.lhs then
      -- Only report the first defining rule of the nonterminal.
      if (s.rules.find? (·.lhs == r.lhs)).map (·.span) == some r.span then
        ds := ds.push (LigDiagnostic.ofSpan r.span .information
          s!"nonterminal `{r.lhs}` is never used")
  return ds

/-! ### Top-level entry point -/

/-- Analyze a `.lig` document and return all diagnostics.

1. Run the frontend parser. A parse failure yields a single error diagnostic,
   located at the embedded `at byte N` offset when present.
2. On a successful parse, run the semantic checks above.
3. If the grammar is free of symbol errors, run grammar preparation / Pager
   construction and surface any LR(1) conflicts as warnings. -/
def collectDiagnostics (input : String) : Array LigDiagnostic :=
  match parseLig input with
  | .error msg =>
    let off := (extractByteOffset msg).getD 0
    -- Highlight from the offset to the end of its line (byte-accurate).
    let endByte : Nat := Id.run do
      let mut b := 0
      let mut endB := off
      let mut started := false
      for c in input.toList do
        if b ≥ off then started := true
        if started then
          if c == '\n' then return endB
          endB := endB + (String.singleton c).utf8ByteSize
        b := b + (String.singleton c).utf8ByteSize
      return endB
    #[{ startByte := off, endByte := max (off + 1) (min endByte input.utf8ByteSize),
        severity := .error, message := msg }]
  | .ok surface0 => Id.run do
    -- Expand parameterized-rule macros first, so the semantic checks (undefined
    -- symbols, unused nonterminals, LR conflicts) run on the same grammar the
    -- generator sees. Otherwise a `list(x)` element would be falsely reported as an
    -- undefined symbol.
    let surface ← match Frontend.Macros.expandMacros surface0 with
      | .error msg =>
          return #[{ startByte := 0, endByte := 0, severity := .error, message := s!"macro expansion error: {msg}" }]
      | .ok s => pure s
    let mut ds := semanticDiagnostics surface
    -- Only attempt Pager construction when symbols resolve; otherwise
    -- `prepareGrammar` would just re-report the symbol error without a span.
    let hasSymbolError := ds.any (fun d => d.severity == .error)
    unless hasSymbolError do
      match Emit.prepareGrammar surface with
      | .error msg =>
        ds := ds.push { startByte := 0, endByte := 0, severity := .error, message := msg }
      | .ok prepared =>
        for conflict in prepared.tables.conflicts do
          ds := ds.push { startByte := 0, endByte := 0, severity := .warning, message := s!"LR(1) conflict: {conflict}" }
    return ds

end Frontend
