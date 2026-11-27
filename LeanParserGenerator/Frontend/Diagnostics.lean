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
public import LeanParserGenerator.Lexer.DFA


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

/-! ### Lexer rule checks -/

/-- Does the class match no character? A positive class is empty when every range is
    reversed. A negated class is empty when its valid ranges cover every code point. -/
def classIsEmpty (k : Lexer.CharClass) : Bool :=
  let valid := k.rs.filter (fun r => r.1 ≤ r.2)
  if !k.neg then valid.isEmpty
  else
    -- Walk the ranges in order of their lower bound and track the first code point
    -- that is not yet covered.
    let sorted := valid.toArray.qsort (fun a b => a.1 < b.1)
    let next := sorted.foldl (fun next r => if r.1 ≤ next then max next (r.2 + 1) else next) 0
    next > Lexer.DFA.maxCodePoint

/-- Does the regex match no string at all? -/
def regexIsEmptyLang : Lexer.Regex → Bool
  | .never => true
  | .epsilon => false
  | .cls k => classIsEmpty k
  | .cat a b => regexIsEmptyLang a || regexIsEmptyLang b
  | .alt a b => regexIsEmptyLang a && regexIsEmptyLang b
  | .star _ => false

/-- The checks on the `%lexer` block that need no DFA:
    * a rule whose pattern matches nothing is an error;
    * a rule that matches the empty string is a warning, because the lexer never emits
      a token for an empty match (a zero-length longest match is a lexing error). -/
def lexerRuleDiagnostics (s : Surface) : Array LigDiagnostic := Id.run do
  let some spec := s.lexer | return #[]
  let mut ds : Array LigDiagnostic := #[]
  for mode in spec.modes do
    for r in mode.rules do
      if regexIsEmptyLang r.regex then
        ds := ds.push (LigDiagnostic.ofSpan r.span .error
          "this lexer rule can never match: its pattern matches no string")
      else if Lexer.Regex.nullable r.regex then
        ds := ds.push (LigDiagnostic.ofSpan r.span .warning
          "this lexer rule matches the empty string. The lexer never emits a token for an empty match, so only the non-empty strings it matches have an effect")
  return ds

/-- Lexer rules that can never win. Rule `i` of a mode wins in a DFA state when it is
    the lowest-numbered rule that accepts there, so a rule that wins in no state other
    than the start state matches only strings that an earlier rule matches too. A
    common cause is a keyword rule placed after the identifier rule. -/
def deadLexerRuleDiagnostics (s : Surface) : Array LigDiagnostic := Id.run do
  let some spec := s.lexer | return #[]
  let mut ds : Array LigDiagnostic := #[]
  for mode in spec.modes do
    let regexes := mode.rules.map (·.regex)
    -- A rule with an empty language is already reported as an error.
    if regexes.any regexIsEmptyLang then continue
    let some dfa := Lexer.DFA.build? regexes | continue
    let mut wins : Array Bool := Array.replicate mode.rules.size false
    for h : i in [1:dfa.states.size] do
      if let some k := dfa.states[i].accept then
        wins := wins.set! k true
    for h : k in [0:mode.rules.size] do
      if !wins[k]! then
        let r := mode.rules[k]
        ds := ds.push (LigDiagnostic.ofSpan r.span .warning
          "this lexer rule can never win: every string it matches is also matched by an earlier rule of the same mode, so the earlier rule is used. Move this rule before the earlier one")
  return ds

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

  -- A binder name used twice in one alternative.
  for r in s.rules do
    for alt in r.alts do
      let mut seen : Array String := #[]
      for e in alt.elems do
        if let some b := e.binder then
          if seen.contains b then
            ds := ds.push (LigDiagnostic.ofSpan e.span .error
              s!"binder `{b}` is used more than once in this alternative of `{r.lhs}`")
          else
            seen := seen.push b

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
  return ds ++ lexerRuleDiagnostics s ++ deadLexerRuleDiagnostics s

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
