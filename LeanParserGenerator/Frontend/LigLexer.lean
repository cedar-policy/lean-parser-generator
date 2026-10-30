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
public import LeanParserGenerator.Frontend.File
/-
Hand-written lexer for the `.lig` structural language, the escape hatch half of
the bootstrap (DESIGN §15.4).

The `.lig` grammar-file language is context-free in its *structure* (the sequence
of `%`-directives, the rule/alternative/element shape), but its leaves are
brace-balanced embedded Lean: `%header { … }`, `%lexer { … }`, `{ action }`
bodies, and the rest-of-line `:: Type` annotation. A regular DFA cannot balance
braces, so those leaves cannot be tokens of a generated DFA lexer. This module is
the hand-written lexer that turns `.lig` text into a flat `List LigTok`, capturing
each embedded-Lean leaf verbatim into a single string-carrying token using the
same balanced-brace / rest-of-line logic the old monolithic scanner used. The
*structure* over that token stream is then parsed by the generated `LigParser`
(`lig.lig`), so the hand-written control flow is replaced by a declared grammar.

`LigTok` is the hand-written token type the generated parser imports (the
hand-written-lexer regime, like `imp`). Value-carrying tokens carry the
captured `String`.
-/


@[expose] public section

namespace Frontend

/-- Tokens of the `.lig` structural language. Directive keywords are nullary;
    the embedded-Lean leaves (`HEADER`, `LEXERHEADER`, `LEXER`, `ACTION`,
    `TYPELINE`) and identifiers carry their captured text. -/
inductive LigTok where
  /-- `%header { … }` — interior captured verbatim. -/
  | HEADER : String → LigTok
  /-- `%lexerheader { … }` — interior captured verbatim. -/
  | LEXERHEADER : String → LigTok
  /-- `%lexer { … }` — interior captured verbatim (parsed later by
      `scanLexerBlockBody`). -/
  | LEXER : String → LigTok
  /-- `%tokentype` keyword. -/
  | KW_TOKENTYPE
  /-- `%token` keyword. -/
  | KW_TOKEN
  /-- `%eof` keyword. -/
  | KW_EOF
  /-- `%start` keyword. -/
  | KW_START
  /-- `%option` keyword. -/
  | KW_OPTION
  /-- `%%` separator. -/
  | PCTPCT
  /-- `::` rule-head separator. -/
  | DCOLON
  /-- `|` alternative separator. -/
  | PIPE
  /-- `=` binder separator. -/
  | EQ
  /-- A `<Type>` token-value annotation on `%token`; interior captured verbatim. -/
  | TYVAL : String → LigTok
  /-- The rest-of-line Lean type after `::`; captured verbatim, trimmed. -/
  | TYPELINE : String → LigTok
  /-- A `{ … }` production action; interior captured verbatim, trimmed. -/
  | ACTION : String → LigTok
  /-- An identifier or parameterized symbol (`list(x)` captured whole). -/
  | IDENT : String → LigTok
  /-- End of input. -/
  | EOF
  deriving Repr, Inhabited, DecidableEq

namespace LigLexer

open Frontend (Cursor)

/-- Where the lexer is in the file, which decides how the next chunk is read:
    directives vs. rules, and (inside rules) whether the next token after `::`
    is the rest-of-line type. -/
inductive Phase where
  /-- Before `%%`: the directive section. -/
  | directives
  /-- After `%%`, at a position where a rule head or the next alternative starts. -/
  | rules
  /-- Just consumed `::`; the next chunk is the rest-of-line type. -/
  | afterDColon
  deriving BEq

/-- Skip whitespace and `--`/`/- -/` comments. Mirrors `Frontend.skipWs`. -/
partial def skipWs (c : Cursor) : Cursor :=
  if c.atEnd then c
  else
    let ch := c.peek
    if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' then skipWs c.next
    else if ch == '-' && c.next.peek == '-' then
      skipWs (Id.run do
        let mut cur := c.next.next
        while !cur.atEnd && cur.peek != '\n' do cur := cur.next
        return cur)
    else if ch == '/' && c.next.peek == '-' then
      skipWs (Id.run do
        let mut cur := c.next.next
        while !cur.atEnd && !(cur.peek == '-' && cur.next.peek == '/') do cur := cur.next
        if !cur.atEnd then cur := cur.next.next
        return cur)
    else c

/-- Capture a balanced `o … cl` block, returning the interior and the cursor past
    the closing delimiter. Assumes the cursor is at the opening delimiter. -/
def captureBalanced (c : Cursor) (o cl : Char) : Except String (String × Cursor) :=
  if c.peek != o then .error s!"expected '{o}' at byte {c.pos.byteIdx}"
  else Id.run do
    let afterOpen := c.next
    let interiorStart := afterOpen.pos
    let mut cur := afterOpen
    let mut depth := 1
    while !cur.atEnd && depth > 0 do
      let ch := cur.peek
      if ch == o then depth := depth + 1; cur := cur.next
      else if ch == cl then
        depth := depth - 1
        if depth == 0 then break else cur := cur.next
      else cur := cur.next
    if depth != 0 then return .error s!"unterminated '{o}…{cl}' block"
    let interior := interiorStart.extract c.input cur.pos
    return .ok (interior, cur.next)

/-- Take the longest run satisfying `p`. -/
def takeWhile (c : Cursor) (p : Char → Bool) : String × Cursor := Id.run do
  let startPos := c.pos
  let mut cur := c
  while !cur.atEnd && p cur.peek do cur := cur.next
  return (startPos.extract c.input cur.pos, cur)

/-- Read a symbol name, optionally followed by a balanced `( … )` argument list
    (`list(x)`), returned as one string. Mirrors `Frontend.scanSymbolWithArgs`. -/
def scanSymbol (c : Cursor) : Except String (String × Cursor) := Id.run do
  let (nm, c1) := takeWhile c Cursor.isIdentCont
  if c1.peek == '(' then
    let mut cur := c1
    let mut depth := 0
    let mut out := nm
    repeat
      if cur.atEnd then return .error "unterminated `(` in parameterized symbol"
      let ch := cur.peek
      out := out.push ch
      if ch == '(' then depth := depth + 1
      else if ch == ')' then depth := depth - 1
      cur := cur.next
      if depth == 0 then break
    return .ok (out, cur)
  else
    return .ok (nm, c1)

/-- Tokenize `.lig` source into `LigTok`s, ending with `EOF`. The phase state
    picks the right capture for the next chunk (directive keyword and its block,
    the rest-of-line type after `::`, an action body, or a symbol). -/
partial def tokenize (input : String) : Except String (List LigTok) := do
  let mut cur : Cursor := { input := input, pos := ⟨0⟩ }
  let mut toks : Array LigTok := #[]
  let mut phase : Phase := .directives
  repeat
    cur := skipWs cur
    if cur.atEnd then break
    let ch := cur.peek
    if phase == .afterDColon then
      -- rest-of-line type
      let (line, c1) := takeWhile cur (· != '\n')
      toks := toks.push (.TYPELINE line.trimAscii.toString)
      cur := c1
      phase := .rules
    else if ch == '%' then
      if cur.next.peek == '%' then
        toks := toks.push .PCTPCT; cur := cur.next.next; phase := .rules
      else
        let (kw, c1) := takeWhile cur.next Cursor.isIdentCont
        match kw with
        | "header" =>
          match captureBalanced (skipWs c1) '{' '}' with
          | .error e => throw e
          | .ok (interior, c2) => toks := toks.push (.HEADER interior); cur := c2
        | "lexerheader" =>
          match captureBalanced (skipWs c1) '{' '}' with
          | .error e => throw e
          | .ok (interior, c2) => toks := toks.push (.LEXERHEADER interior); cur := c2
        | "lexer" =>
          match captureBalanced (skipWs c1) '{' '}' with
          | .error e => throw e
          | .ok (interior, c2) => toks := toks.push (.LEXER interior); cur := c2
        | "tokentype" => toks := toks.push .KW_TOKENTYPE; cur := c1
        | "token" => toks := toks.push .KW_TOKEN; cur := c1
        | "eof" => toks := toks.push .KW_EOF; cur := c1
        | "start" => toks := toks.push .KW_START; cur := c1
        | "option" => toks := toks.push .KW_OPTION; cur := c1
        | other => throw s!"unknown directive `%{other}`"
    else if ch == ':' && cur.next.peek == ':' then
      toks := toks.push .DCOLON; cur := cur.next.next; phase := .afterDColon
    else if ch == '|' then
      toks := toks.push .PIPE; cur := cur.next
    else if ch == '=' then
      toks := toks.push .EQ; cur := cur.next
    else if ch == '<' then
      match captureBalanced cur '<' '>' with
      | .error e => throw e
      | .ok (interior, c1) => toks := toks.push (.TYVAL interior.trimAscii.toString); cur := c1
    else if ch == '{' then
      match captureBalanced cur '{' '}' with
      | .error e => throw e
      | .ok (interior, c1) => toks := toks.push (.ACTION interior.trimAscii.toString); cur := c1
    else if (match toks.toList.reverse with
        | .IDENT "gen_rust" :: .KW_OPTION :: _ => true
        | _ => false) then
      -- The value of `%option gen_rust` is a file path: a run of non-whitespace.
      let (path, c1) := takeWhile cur (fun c => !(c == ' ' || c == '\t' || c == '\n' || c == '\r'))
      toks := toks.push (.IDENT path); cur := c1
    else if Cursor.isIdentStart ch then
      match scanSymbol cur with
      | .error e => throw e
      | .ok (sym, c1) => toks := toks.push (.IDENT sym); cur := c1
    else
      throw s!"unexpected character '{ch}' at byte {cur.pos.byteIdx}"
  toks := toks.push .EOF
  return toks.toList

end LigLexer

/-! ### Surface assembly

The generated `LigParser`'s actions cannot easily reproduce the imperative
post-processing of the old `parseLig` (defaulting `%tokentype`, validating that
`%eof` names a declared token, parsing the `%lexer` interior with
`scanLexerBlockBody`). So the grammar builds a flat list of `Directive`s and a
list of `Rule`s, and this pure `assembleSurface` helper folds them into a
`Surface` exactly as `parseLig` did — the one place the two frontends must agree
on defaults and validation. -/

/-- A single parsed directive, before assembly into `Surface`. Mirrors the cases
    of the directive `match` in the old `parseLig`. -/
inductive Directive where
  | header : String → Directive
  | lexerHeader : String → Directive
  | tokenType : String → Directive
  | tokens : Array TokenDecl → Directive
  | eof : String → Directive
  | start : String → Directive
  | option : String → Option String → Directive
  | lexer : String → Directive
  deriving Repr, Inhabited

/-- Fold parsed directives + rules into a `Surface`, applying the same defaults
    and validation as the old `parseLig`. Kept in sync with `parseLig`. -/
def assembleSurface (directives : Array Directive) (rules : Array Rule) :
    Except String Surface := do
  let mut header := ""
  let mut lexerHeader := ""
  let mut tokens : Array TokenDecl := #[]
  let mut eof : Option String := none
  let mut start : Option String := none
  let mut tokenType := "Tok"
  let mut lexer : Option LexerSpec := none
  let mut options : Options := {}
  for d in directives do
    match d with
    | .header h => header := h
    | .lexerHeader h => lexerHeader := h
    | .tokenType nm => tokenType := nm
    | .tokens ds => tokens := tokens ++ ds
    | .eof nm => eof := some nm
    | .start nm => start := some nm
    | .option nm val =>
      match nm, val with
      | "compress_tables", _ => options := { options with compressTables := true }
      | "roundtrip_lexer", _ => options := { options with roundtripLexer := true }
      | "roundtrip_parser", some v => options := { options with roundtripParser := some v }
      | "roundtrip_parser", none => throw "`%option roundtrip_parser` needs a token-generator function name (e.g. `%option roundtrip_parser unparsePolicies`)"
      | "roundtrip_format", some v => options := { options with roundtripFormat := some v }
      | "roundtrip_format", none => throw "`%option roundtrip_format` needs a token renderer function name (e.g. `%option roundtrip_format renderTok`)"
      | "module_prefix", some v => options := { options with modulePrefix := v }
      | "module_prefix", none => throw "`%option module_prefix` needs a module path (e.g. `%option module_prefix calc`)"
      | "gen_rust", some v => options := { options with genRust := some v }
      | "gen_rust", none => throw "`%option gen_rust` needs a file path (e.g. `%option gen_rust rust/src/generated.rs`)"
      | other, _ => throw (unknownOptionMessage other)
    | .lexer interior =>
      let innerCur : Cursor := { input := interior, pos := ⟨0⟩ }
      match (scanLexerBlockBody Span.dummy).run innerCur |>.1 with
      | .error e => throw s!"in %lexer block: {e}"
      | .ok spec => lexer := some spec
  let some eofName := eof | throw "missing `%eof` directive"
  let some startName := start | throw "missing `%start` directive"
  unless tokens.any (·.name == eofName) do
    throw s!"`%eof {eofName}` names a terminal that was not declared with `%token`"
  if rules.isEmpty then throw "no grammar rules found after `%%`"
  return { header := header, lexerHeader := lexerHeader, tokenType := tokenType,
           tokens := tokens, eof := eofName, start := startName, rules := rules,
           lexer := lexer, options := options }

/-- Result of parsing a `.lig` file: the assembled `Surface`, or an assembly
    error. A single-token alias so it drops into the generated `Option _` result
    type without a parenthesization quirk. -/
abbrev LigResult := Except String Surface

end Frontend

