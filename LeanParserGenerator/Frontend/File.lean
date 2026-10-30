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
public import Lean
public import LeanParserGenerator.Lexer.Regex
/-
The untrusted `.lig` grammar-file parser.

A `.lig` file is the input to the build-time code generator (the Menhir model: a
separate tool reads the grammar file and *writes* a `.lean` file, which `lake`
then compiles). This module parses the text into a `Surface` grammar; the
emitter (`Emit/Codegen.lean`) turns that into Lean source.

The parser is built from **hand-assembled `Lean.Parser` combinators** run
programmatically (via `ParserFn.run` over the file string) — no
`declare_syntax_cat`/global-syntax registration. Action bodies and type
annotations are captured as **verbatim source** (balanced `{ … }` / `< … >`),
never elaborated: type-checking happens only on the generated `.lean`.

Every `Surface` node carries the originating `.lig` source span (`Span`). Nothing
consumes spans yet, but they are threaded through from the start so a future
`.lig` language server can resurface generated-`.lean` diagnostics at the right
`.lig` location (see docs/DESIGN.md §9.2).

Nothing here is trusted: a bug yields a generated parser that the (future)
validator refuses to certify, or that fails to type-check.

Grammar-file syntax (Menhir/`.vy`-like):

```
%header {
import Test.Generated.CalcAst
open Calc
}
%token PLUS TIMES LPAR RPAR
%token <Int> NUM
%eof EOF
%start expr
%%
expr :: Int
  | e=expr PLUS t=term    { e + t }
  | t=term                { t }
term :: Int
  | t=term TIMES f=factor { t * f }
  | f=factor              { f }
factor :: Int
  | LPAR e=expr RPAR      { e }
  | n=NUM                 { n }
```
-/


@[expose] public section

namespace Frontend

/-- A half-open source span in the `.lig` file, as raw byte offsets. Carried on
    every `Surface` node for future `.lig` LSP diagnostics (DESIGN §9.2). -/
structure Span where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Repr, Inhabited, DecidableEq

/-- The empty/placeholder span (byte 0..0). -/
def Span.dummy : Span := ⟨⟨0⟩, ⟨0⟩⟩

/-- A terminal declaration: its name and its semantic Lean type (`"Unit"` for a
    valueless token). -/
structure TokenDecl where
  name : String
  /-- Lean type carried by this terminal; `"Unit"` if valueless. -/
  ty : String
  /-- Whether the token carries a value (i.e. it was declared `%token <T> …`). -/
  hasVal : Bool
  /-- Span of this token's name in the `.lig` source. -/
  span : Span := Span.dummy
  deriving Repr, Inhabited

/-- One RHS element of a production: an optional binder name and the symbol. -/
structure Elem where
  binder : Option String
  sym : String
  span : Span := Span.dummy
  deriving Repr, Inhabited

/-- One alternative of a rule: its RHS elements and the action term (verbatim,
    without the surrounding braces). -/
structure Alt where
  elems : Array Elem
  action : String
  /-- Span of the action body (between the braces) in the `.lig` source. -/
  actionSpan : Span := Span.dummy
  /-- The Rust action, from `!!rust{ … }` after the Lean action, verbatim. The Rust
      backend pastes it into the reduction of this alternative (docs/RUST_PARSER.md). -/
  rustAction : Option String := none
  deriving Repr, Inhabited

/-- One rule: an LHS nonterminal, its declared Lean type, and its alternatives. -/
structure Rule where
  lhs : String
  ty : String
  alts : Array Alt
  span : Span := Span.dummy
  /-- The Rust type of the rule's value, from `!!rust{ … }` after the Lean type. -/
  rustTy : Option String := none
  deriving Repr, Inhabited

/-! ### Lexer surface (the `%lexer { … }` block)

The `.lig` file may carry a lexer definition, so one CLI invocation generates the
tokenizer alongside the parser (LALRPOP-style). Patterns are `Lexer.Regex` values
(the frontend parses the `lexre` sub-grammar into them); actions are captured
verbatim like production actions and reference `%header` Lean code. This mirrors
the ocamllex-style regex surface, scanned into data rather than elaborated. -/

/-- How a matched lexer rule moves the mode stack. `stay` is the common case;
    `push`/`pop` give ocamllex-style recursive modes. -/
inductive LexerTrans where
  /-- Stay in the current mode. -/
  | stay
  /-- Push a mode by name (resolved to an index at codegen). -/
  | push (mode : String)
  /-- Pop the current mode. -/
  | pop
  deriving Repr, Inhabited, DecidableEq

/-- One lexer rule: a pattern, an optional binder for the matched text, an action
    (verbatim Lean token expression, or `skip` = emit nothing), and a mode
    transition. -/
structure LexerRule where
  /-- The pattern this rule matches. -/
  regex : Lexer.Regex
  /-- Binder name for the matched text in the action, if any (`… as x`). -/
  binder : Option String
  /-- The action: `none` means `skip` (emit nothing); `some expr` emits the token
      that verbatim Lean expression computes. -/
  emit : Option String
  /-- The mode-stack transition. -/
  trans : LexerTrans
  span : Span := Span.dummy
  deriving Repr, Inhabited

/-- One named lexer mode: a name and its ordered rule list. Single-mode lexers have
    exactly one mode. -/
structure LexerMode where
  name : String
  rules : Array LexerRule
  span : Span := Span.dummy
  deriving Repr, Inhabited

/-- A parsed `%lexer { … }` block. Modes are in source order (the first is the
    start mode); `eof` is the optional token expression emitted at end of input. -/
structure LexerSpec where
  /-- The lexer modes, in source order (first = start). -/
  modes : Array LexerMode
  /-- The verbatim token expression to emit at end of input, if any (`eof => …`). -/
  eof : Option String := none
  /-- `rust <LeanName> => <rust::path>`: the Rust counterpart of a Lean function used in a
      lexer action. Read only by the Rust backend (docs/RUST_PARSER.md). -/
  rustFns : Array (String × String) := #[]
  span : Span := Span.dummy
  deriving Repr, Inhabited

/-- Code-generation options set by `%option <name>` directives in the `.lig`. These
    affect only *how* the modules are emitted (and which ones), never the grammar the
    proofs are about. Unknown option names are rejected by the parser. -/
structure Options where
  /-- The generated Rust file, relative to the `.lig`'s directory. Set by
      `%option gen_rust rust/src/generated.rs`; the default invocation then also writes
      it (docs/RUST_PARSER.md). -/
  genRust : Option String := none
  /-- The Rust type of a user context passed to `parse_values` as `ctx: &'a <type>` and
      visible in the `!!rust{…}` actions (for example an arena the actions allocate the
      AST from). Set by `%option rust_ctx crate::ast::Arena` (docs/RUST_PARSER.md). -/
  rustCtx : Option String := none
  /-- A Rust module path providing the list type of the macro rules (`list`,
      `separated_list`, …) in place of `VecDeque`: `<path>::List<'a, T>` with
      `<path>::nil(ctx)`, `<path>::one(ctx, x)` and `<path>::cons(ctx, x, xs)`. Needs
      `rust_ctx`. Set by `%option rust_list crate::ast::lists`. -/
  rustList : Option String := none
  /-- When true, the executable parser writes its `actionData`/`gotoData` arrays in
      compressed source form: only the non-default cells (`.error` for actions,
      `none` for goto) are spelled out as `(index, value)` pairs, and a `buildDense`
      call fills the rest. The arrays still hold the same dense values at runtime —
      this changes only how they are *written*, not what they are — so the generated
      specification module and its `native_decide` refinement checks are unchanged;
      only the size of the emitted literal (and thus the executable parser's compile
      time / `.olean`) shrinks. Set by `%option compress_tables`. Defaults to
      `false`. -/
  compressTables : Bool := false
  /-- When true, and the grammar has a `%lexer` block, the generator also emits
      `<Base>LexerRoundtrip.lean`. The handwritten
      `<Base>LexerRoundtripSupport.lean` module supplies `renderTok`; the generated
      `render_roundtrip` theorem covers arbitrary lists whose elements satisfy the
      decidable structural `RoundtrippableTok` predicate. The current backend
      accepts only one-mode, `.stay` lexers with a skipped space separator. Set by
      `%option roundtrip_lexer`. Ignored without a `%lexer` block. Defaults to
      `false`. -/
  roundtripLexer : Bool := false
  /-- When set to a token-generator function name, the generator emits
      `<Base>ParserRoundtrip.lean` and parse-tree helpers in `<Base>Verified.lean`.
      The named `<StartTy> → List <Tok>` function comes from handwritten
      `<Base>Unparse.lean`. The generated `parse_certificate` theorem proves any
      supplied start-tree certificate; a separate handwritten proof constructs
      certificates for its printable domain. Generated and handwritten lexers are
      both supported. `none` emits no parser roundtrip module or tree helpers. -/
  roundtripParser : Option String := none
  /-- When set alongside `roundtrip_parser`, names a token renderer
      `renderTok : <Tok> → String` imported from the handwritten
      `<Base>Unparse` module. The parser roundtrip module then also defines
      `format`, `relex`, and `fullRoundtrip`. It does not prove that the renderer
      or unparser is complete; those properties belong in handwritten universal
      theorems. Without this option, only `parseRoundtrip` is emitted. -/
  roundtripFormat : Option String := none
  /-- The dotted module prefix under which the generated modules live, e.g. `calc`
      so the parser imports its lexer as `calc.CalcLexer` and a caller imports
      `calc.CalcParser`. Set by `%option module_prefix calc`. When empty (the
      default) the modules are top-level: the parser imports the bare `FooLexer` and
      the emitted module names carry no prefix. -/
  modulePrefix : String := ""
  deriving Repr, Inhabited

/-- The `%option` names the frontend accepts. Shared by both `.lig` parsers and the
    diagnostics engine so validation and error text stay in sync. `module_prefix`,
    `roundtrip_parser`, `roundtrip_format`, `gen_rust`, `rust_ctx` and `rust_list` carry a value
    (`%option module_prefix calc`, `%option roundtrip_parser unparsePolicies`,
    `%option roundtrip_format renderTok`); the rest are flags. -/
def knownOptions : List String :=
  ["compress_tables", "roundtrip_lexer", "roundtrip_parser", "roundtrip_format",
   "module_prefix", "gen_rust", "rust_ctx", "rust_list"]

/-- The `unknown %option` message, listing the accepted names. -/
def unknownOptionMessage (name : String) : String :=
  s!"unknown `%option {name}` (known: {", ".intercalate knownOptions})"

/-- A parsed `.lig` file. -/
structure Surface where
  /-- Verbatim Lean header (imports / opens / aux defs), copied into every
      generated module (parser backends and, if present, the lexer). -/
  header : String
  /-- Verbatim Lean header copied only into the generated lexer module: lexer-only
      helpers (e.g. keyword-folding functions) that the `%lexer` actions call. In
      the generated regime the lexer module owns these; the parser modules import
      the lexer module and so do not need them. -/
  lexerHeader : String := ""
  /-- The name of the user's token inductive type (from `%tokentype`; default
      `"Tok"`). Its constructors must be named exactly like the `%token`s:
      valueless tokens are nullary, value-carrying ones take one argument of the
      declared type (Menhir's `%token <T> NAME` ⇒ constructor `NAME : T → Tok`). -/
  tokenType : String
  /-- Terminal declarations, in declaration order (fixes terminal indices). -/
  tokens : Array TokenDecl
  /-- The end-of-input terminal's name. -/
  eof : String
  /-- The start nonterminal's name. -/
  start : String
  /-- The grammar rules, in source order. -/
  rules : Array Rule
  /-- The optional `%lexer { … }` block, generating a tokenizer alongside the
      parser. `none` when the `.lig` declares no lexer. -/
  lexer : Option LexerSpec := none
  /-- Code-generation options from `%option` directives. -/
  options : Options := {}
  deriving Repr, Inhabited

namespace Surface

/-- Terminal index (declaration order) of a name, if it is a declared token. -/
def termIdx (s : Surface) (name : String) : Option Nat :=
  s.tokens.findIdx? (fun (t : TokenDecl) => t.name == name)

/-- Nonterminal names in first-appearance order among the rule heads. -/
def ntNames (s : Surface) : Array String := Id.run do
  let mut acc : Array String := #[]
  for r in s.rules do
    unless acc.contains r.lhs do acc := acc.push r.lhs
  return acc

/-- Nonterminal index (first-appearance order) of a name. -/
def ntIdx (s : Surface) (name : String) : Option Nat :=
  s.ntNames.findIdx? (· == name)

end Surface

/-! ### Scanner

We parse `.lig` with a small character cursor over the input `String`, tracking a
`String.Pos.Raw` position. `Lean.Parser`'s registered term machinery is awkward to
run standalone and — more importantly — we want action bodies and type
annotations captured as **verbatim source** with balanced-brace handling, which a
direct scanner does precisely. Identifiers and structure are tokenized with the
same character classes Lean uses. -/

/-- Scanner state: the input and the current byte position. -/
structure Cursor where
  input : String
  pos : String.Pos.Raw
  deriving Inhabited

namespace Cursor

/-- Are we at (or past) the end of input? -/
def atEnd (c : Cursor) : Bool := c.pos.atEnd c.input

/-- The character at the cursor (or `'\u0000'` at end). -/
def peek (c : Cursor) : Char := if c.atEnd then default else c.pos.get c.input

/-- Advance one character. -/
def next (c : Cursor) : Cursor := { c with pos := c.pos.next c.input }

/-- Does the input continue with `p` at the cursor? -/
def startsWith (c : Cursor) (p : String) : Bool :=
  (p.toList.foldl (fun (acc : Option Cursor) ch =>
    match acc with
    | some cur => if !cur.atEnd && cur.peek == ch then some cur.next else none
    | none => none) (some c)).isSome

/-- Skip `p`, which the input is known to continue with. -/
def skip (c : Cursor) (p : String) : Cursor :=
  p.toList.foldl (fun cur _ => cur.next) c

/-- Is `ch` a `.lig` identifier character? (Letters, digits, `_`, and `'`; we also
    allow `.` so qualified names like `Ast.Foo` scan as one token in symbol
    position — though grammar symbols are normally simple.) -/
def isIdentCont (ch : Char) : Bool :=
  ch.isAlphanum || ch == '_' || ch == '\''

/-- Is `ch` a valid identifier-start character? -/
def isIdentStart (ch : Char) : Bool := ch.isAlpha || ch == '_'

end Cursor

/-- A scanning step: transforms a cursor, possibly failing with a message. -/
abbrev ScanM := StateM Cursor

/-- Skip spaces, tabs, newlines, and `--` line comments and `/- … -/` block
    comments. -/
partial def skipWs : ScanM Unit := do
  let c ← get
  if c.atEnd then return
  let ch := c.peek
  if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' then
    set c.next; skipWs
  else if ch == '-' then
    let c2 := c.next
    if c2.peek == '-' then
      let mut cur := c2.next
      while !cur.atEnd && cur.peek != '\n' do cur := cur.next
      set cur; skipWs
    else
      return
  else if ch == '/' then
    let c2 := c.next
    if c2.peek == '-' then
      let mut cur := c2.next
      while !cur.atEnd && !(cur.peek == '-' && cur.next.peek == '/') do
        cur := cur.next
      if !cur.atEnd then cur := cur.next.next
      set cur; skipWs
    else
      return
  else
    return

/-- Take the longest run of characters satisfying `p`, returning it and its span.
    Assumes the cursor is positioned at the run's start. -/
def takeWhile (p : Char → Bool) : ScanM (String × Span) := do
  let c ← get
  let startPos := c.pos
  let mut cur := c
  while !cur.atEnd && p cur.peek do cur := cur.next
  set cur
  let s := startPos.extract c.input cur.pos
  return (s, ⟨startPos, cur.pos⟩)

/-- Scan an identifier (must start with an ident-start char). Fails if none. -/
def scanIdent : ScanM (Except String (String × Span)) := do
  skipWs
  let c ← get
  if c.atEnd || !Cursor.isIdentStart c.peek then
    return .error s!"expected identifier at byte {c.pos.byteIdx}"
  let (s, sp) ← takeWhile Cursor.isIdentCont
  return .ok (s, sp)

/-- Scan a dotted module path (`calc`, `My.Project`). Like `scanIdent` but also
    accepts `.` between components. Used for `%option module_prefix`. -/
def scanModulePath : ScanM (Except String (String × Span)) := do
  skipWs
  let c ← get
  if c.atEnd || !Cursor.isIdentStart c.peek then
    return .error s!"expected a module path at byte {c.pos.byteIdx}"
  let (s, sp) ← takeWhile (fun ch => Cursor.isIdentCont ch || ch == '.')
  return .ok (s, sp)

/-- Scan a file path: a run of non-whitespace characters. Used for `%option gen_rust`, `rust_ctx` and `rust_list`. -/
def scanPathWord : ScanM (Except String (String × Span)) := do
  skipWs
  let c ← get
  if c.atEnd then return .error s!"expected a file path at byte {c.pos.byteIdx}"
  let (s, sp) ← takeWhile (fun ch => !(ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r'))
  if s.isEmpty then return .error s!"expected a file path at byte {c.pos.byteIdx}"
  return .ok (s, sp)

/-- Peek the next non-whitespace character without consuming it. -/
def peekTok : ScanM Char := do
  skipWs
  return (← get).peek

/-- Capture a verbatim block delimited by `o`/`cl` characters, honoring nesting,
    returning the interior text (without the outer delimiters) and its span.
    Assumes the cursor is at (whitespace before) the opening delimiter. -/
def captureBalanced (o cl : Char) : ScanM (Except String (String × Span)) := do
  skipWs
  let c ← get
  if c.peek != o then
    return .error s!"expected '{o}' at byte {c.pos.byteIdx}"
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
  if depth != 0 then
    return .error s!"unterminated '{o}…{cl}' block"
  let interiorEnd := cur.pos
  let interior := interiorStart.extract c.input interiorEnd
  set cur.next  -- consume the closing delimiter
  return .ok (interior, ⟨interiorStart, interiorEnd⟩)

/-- Consume the rest of the current line (verbatim), returning it trimmed of the
    trailing newline, plus its span. -/
def restOfLine : ScanM (String × Span) := do
  let c ← get
  let startPos := c.pos
  let mut cur := c
  while !cur.atEnd && cur.peek != '\n' do cur := cur.next
  set cur
  let s := startPos.extract c.input cur.pos
  return (s, ⟨startPos, cur.pos⟩)

/-! ### Top-level `.lig` parser

The whole parser runs in `ScanM = StateM Cursor`, threading an error through an
`Except` return where needed. We drive it to completion and read the final state. -/

/-- Read `%` followed by a directive keyword; returns the keyword (without `%`).
    Assumes `peekTok = '%'`. -/
def scanDirectiveKw : ScanM (Except String String) := do
  skipWs
  let c ← get
  if c.peek != '%' then
    return .error s!"expected '%' directive at byte {c.pos.byteIdx}"
  set c.next
  match ← scanIdent with
  | .error e => return .error e
  | .ok (kw, _) => return .ok kw

/-- Scan one `%token` body: an optional `<Type>` then one or more names. -/
def scanTokenDecls : ScanM (Except String (Array TokenDecl)) := do
  skipWs
  let c ← get
  let mut ty := "Unit"
  let mut hasVal := false
  if c.peek == '<' then
    match ← captureBalanced '<' '>' with
    | .error e => return .error e
    | .ok (t, _) => ty := t.trimAscii.toString; hasVal := true
  let mut decls : Array TokenDecl := #[]
  let mut go := true
  while go do
    skipWs
    let cc ← get
    if cc.atEnd || !Cursor.isIdentStart cc.peek then
      go := false
    else
      match ← scanIdent with
      | .error e => return .error e
      | .ok (nm, sp) => decls := decls.push { name := nm, ty := ty, hasVal := hasVal, span := sp }
      let cc2 ← get
      if cc2.peek == '\n' then go := false
  if decls.isEmpty then return .error "%token with no names"
  return .ok decls

/-- Read a symbol name, optionally followed by a parenthesized macro-argument list,
    e.g. `list(brace)` or `separated_list(COMMA, expr)`. The whole application is
    returned as one string; `Frontend.Macros` expands it into a concrete nonterminal
    before grammar preparation. Nested applications (`list(option(x))`) are supported
    by consuming balanced parentheses verbatim. -/
def scanSymbolWithArgs : ScanM (Except String (String × Span)) := do
  match ← scanIdent with
  | .error e => return .error e
  | .ok (nm, sp) =>
    let c ← get
    if c.peek == '(' then
      -- consume a balanced parenthesized argument list verbatim into the symbol name
      let startPos := sp.startPos
      let mut cur := c
      let mut depth := 0
      let mut out := nm
      let mut endPos := c.pos
      repeat
        if cur.atEnd then return .error "unterminated `(` in parameterized symbol"
        let ch := cur.peek
        out := out.push ch
        if ch == '(' then depth := depth + 1
        else if ch == ')' then depth := depth - 1
        cur := cur.next
        endPos := cur.pos
        if depth == 0 then break
      set cur
      return .ok (out, ⟨startPos, endPos⟩)
    else
      return .ok (nm, sp)

/-- The marker that introduces a Rust counterpart: `!!rust{ … }`. -/
def rustMarker : String := "!!rust"

/-- Split `text!!rust{rust}` into `text` and `rust`. The braces after the marker
    are removed; `rust` is verbatim and trimmed. Text without a marker is returned
    unchanged. -/
def splitRust (text : String) : String × Option String :=
  match text.splitOn (rustMarker ++ "{") with
  | [only] => (only.trimAscii.toString, none)
  | before :: rest =>
    let body := (rustMarker ++ "{").intercalate rest
    let body := if body.endsWith "}" then (body.dropEnd 1).toString else body
    (before.trimAscii.toString, some body.trimAscii.toString)
  | [] => (text, none)

/-- Scan one production alternative starting just after a `|`. Reads elements
    until the `{`, then captures the balanced action body. -/
def scanAlt : ScanM (Except String Alt) := do
  let mut elems : Array Elem := #[]
  let mut go := true
  while go do
    skipWs
    let c ← get
    if c.atEnd then return .error "unexpected end of input in alternative (expected `{`)"
    if c.peek == '{' then
      go := false
    else if c.peek == '|' || c.peek == '%' then
      return .error s!"expected `\{` to start action at byte {c.pos.byteIdx}"
    else
      match ← scanSymbolWithArgs with
      | .error e => return .error e
      | .ok (first, sp1) =>
        skipWs
        let c2 ← get
        if c2.peek == '=' then
          set c2.next
          skipWs
          match ← scanSymbolWithArgs with
          | .error e => return .error e
          | .ok (symName, sp2) =>
            elems := elems.push { binder := some first, sym := symName, span := ⟨sp1.startPos, sp2.endPos⟩ }
        else
          elems := elems.push { binder := none, sym := first, span := sp1 }
  match ← captureBalanced '{' '}' with
  | .error e => return .error e
  | .ok (act, sp) =>
    -- An optional Rust action: `!!rust{ … }`.
    skipWs
    let c ← get
    if c.startsWith rustMarker then
      set (c.skip rustMarker)
      match ← captureBalanced '{' '}' with
      | .error e => return .error ("in `!!rust{…}`: " ++ e)
      | .ok (rustBody, _) =>
        return .ok { elems := elems, action := act.trimAscii.toString, actionSpan := sp,
                     rustAction := some rustBody.trimAscii.toString }
    return .ok { elems := elems, action := act.trimAscii.toString, actionSpan := sp }

/-- Scan a rule: a head `NT :: Type`, then one or more `|`-alternatives. -/
def scanRule : ScanM (Except String Rule) := do
  match ← scanIdent with
  | .error e => return .error s!"expected rule head: {e}"
  | .ok (lhs, sp) =>
    skipWs
    let c ← get
    if !(c.peek == ':' && c.next.peek == ':') then
      return .error s!"expected `::` after rule head `{lhs}` at byte {c.pos.byteIdx}"
    set c.next.next
    let (tyStr, _) ← restOfLine
    let (ty, rustTy) := splitRust tyStr
    let mut alts : Array Alt := #[]
    let mut go := true
    while go do
      skipWs
      let cc ← get
      if cc.peek == '|' then
        set cc.next
        match ← scanAlt with
        | .error e => return .error e
        | .ok a => alts := alts.push a
      else
        go := false
    if alts.isEmpty then return .error s!"rule `{lhs}` has no alternatives"
    return .ok { lhs := lhs, ty := ty, alts := alts, span := sp, rustTy := rustTy }

/-! ### Lexer block scanner (`%lexer { … }`)

Parses the ocamllex-style `lexre` regex sub-grammar into the hand-written scanner,
producing `Lexer.Regex` values. Precedence (tight → loose): postfix `* + ?` >
concatenation > alternation `|`. Atoms: `"str"`, `'c'`, `_` (any), `ε` (epsilon),
`( re )`, `[ … ]` / `[^ … ]` character classes, and a bare identifier that
references a `let`-bound definition. -/

/-- Decode a backslash escape (the cursor is just past the `\`). Returns the
    character and advances. Supports `n t r \ " ' 0` and `\uXXXX`. -/
def scanEscape : ScanM (Except String Char) := do
  let c ← get
  if c.atEnd then return .error "unterminated escape"
  let ch := c.peek
  set c.next
  match ch with
  | 'n' => return .ok '\n'
  | 't' => return .ok '\t'
  | 'r' => return .ok '\r'
  | '0' => return .ok (Char.ofNat 0)
  | '\\' => return .ok '\\'
  | '"' => return .ok '"'
  | '\'' => return .ok '\''
  | 'u' =>
      -- \uXXXX : exactly four hex digits
      let mut cur ← get
      let mut n := 0
      let mut count := 0
      while count < 4 && !cur.atEnd && cur.peek.isDigit || (count < 4 && !cur.atEnd && "abcdefABCDEF".contains cur.peek) do
        let d := cur.peek
        let v := if d.isDigit then d.toNat - '0'.toNat
                 else (d.toLower.toNat - 'a'.toNat) + 10
        n := n * 16 + v
        cur := cur.next
        count := count + 1
      set cur
      if count == 0 then return .error "malformed \\u escape"
      return .ok (Char.ofNat n)
  | other => return .ok other

/-- Scan a `'c'` character literal (cursor at the opening quote). -/
def scanCharLit : ScanM (Except String Char) := do
  skipWs
  let c ← get
  if c.peek != '\'' then return .error s!"expected char literal at byte {c.pos.byteIdx}"
  set c.next
  let c1 ← get
  if c1.atEnd then return .error "unterminated char literal"
  let result ←
    if c1.peek == '\\' then
      set c1.next
      match ← scanEscape with
      | .error e => return .error e
      | .ok ch => pure ch
    else
      set c1.next
      pure c1.peek
  let c2 ← get
  if c2.peek != '\'' then return .error s!"unterminated char literal at byte {c2.pos.byteIdx}"
  set c2.next
  return .ok result

/-- Scan a `"…"` string literal into its decoded characters (cursor at the opening
    quote). -/
def scanStrLit : ScanM (Except String String) := do
  skipWs
  let c ← get
  if c.peek != '"' then return .error s!"expected string literal at byte {c.pos.byteIdx}"
  set c.next
  let mut out : String := ""
  let mut cur ← get
  while !cur.atEnd && cur.peek != '"' do
    if cur.peek == '\\' then
      set cur.next
      match ← scanEscape with
      | .error e => return .error e
      | .ok ch => out := out.push ch
      cur ← get
    else
      out := out.push cur.peek
      cur := cur.next
      set cur
  cur ← get
  if cur.atEnd then return .error "unterminated string literal"
  set cur.next  -- consume closing quote
  return .ok out

/-- A character-class item: a single char `'a'` or a range `'a'-'z'`, as a
    `(lo, hi)` code-point pair. -/
def scanClsItem : ScanM (Except String (Nat × Nat)) := do
  match ← scanCharLit with
  | .error e => return .error e
  | .ok lo =>
    skipWs
    let c ← get
    if c.peek == '-' then
      set c.next
      match ← scanCharLit with
      | .error e => return .error e
      | .ok hi => return .ok (lo.toNat, hi.toNat)
    else
      return .ok (lo.toNat, lo.toNat)

/-- Lexer-definition environment: `let`-bound names to their regexes. -/
abbrev LexDefs := Array (String × Lexer.Regex)

/-- Look up a `let`-bound regex name. -/
def LexDefs.find? (ds : LexDefs) (name : String) : Option Lexer.Regex :=
  (Array.find? (fun p => p.1 == name) ds).map (·.2)

mutual
/-- Parse an alternation `re | re | …` (loosest). -/
partial def scanRegexAlt (ds : LexDefs) : ScanM (Except String Lexer.Regex) := do
  match ← scanRegexCat ds with
  | .error e => return .error e
  | .ok first =>
    let mut acc := first
    repeat
      let ch ← peekTok
      if ch == '|' then
        let c ← get; set c.next
        match ← scanRegexCat ds with
        | .error e => return .error e
        | .ok r => acc := .alt acc r
      else
        break
    return .ok acc

/-- Parse a concatenation `re re …` (tighter than `|`). Stops at `|`, `)`, `=>`,
    `as`, `}`, `|`-rule-start, or end. -/
partial def scanRegexCat (ds : LexDefs) : ScanM (Except String Lexer.Regex) := do
  match ← scanRegexPostfix ds with
  | .error e => return .error e
  | .ok first =>
    let mut acc := first
    repeat
      skipWs
      let c ← get
      let ch := c.peek
      -- Concatenation continues only if another atom can start here.
      if c.atEnd || ch == '|' || ch == ')' || ch == '}' || ch == '=' then
        break
      -- `as` keyword terminates the pattern.
      if ch == 'a' && c.next.peek == 's' && !Cursor.isIdentCont c.next.next.peek then
        break
      if ch == '"' || ch == '\'' || ch == '_' || ch == '(' || ch == '[' || ch == 'ε'
         || Cursor.isIdentStart ch then
        match ← scanRegexPostfix ds with
        | .error e => return .error e
        | .ok r => acc := .cat acc r
      else
        break
    return .ok acc

/-- Parse postfix `* + ?` applied to an atom. -/
partial def scanRegexPostfix (ds : LexDefs) : ScanM (Except String Lexer.Regex) := do
  match ← scanRegexAtom ds with
  | .error e => return .error e
  | .ok atom =>
    let mut acc := atom
    repeat
      skipWs
      let c ← get
      let ch := c.peek
      if ch == '*' then set c.next; acc := .star acc
      else if ch == '+' then set c.next; acc := Lexer.Regex.plus acc
      else if ch == '?' then set c.next; acc := Lexer.Regex.opt acc
      else break
    return .ok acc

/-- Parse a single atom. -/
partial def scanRegexAtom (ds : LexDefs) : ScanM (Except String Lexer.Regex) := do
  skipWs
  let c ← get
  let ch := c.peek
  if ch == '"' then
    match ← scanStrLit with
    | .error e => return .error e
    | .ok s => return .ok (Lexer.Regex.str s)
  else if ch == '\'' then
    match ← scanCharLit with
    | .error e => return .error e
    | .ok ch => return .ok (Lexer.Regex.char ch)
  else if ch == '_' && !Cursor.isIdentCont c.next.peek then
    set c.next; return .ok Lexer.Regex.any
  else if ch == 'ε' then
    set c.next; return .ok Lexer.Regex.epsilon
  else if ch == '(' then
    set c.next
    match ← scanRegexAlt ds with
    | .error e => return .error e
    | .ok r =>
      skipWs
      let c2 ← get
      if c2.peek != ')' then return .error s!"expected `)` at byte {c2.pos.byteIdx}"
      set c2.next
      return .ok r
  else if ch == '[' then
    set c.next
    skipWs
    let mut neg := false
    let c1 ← get
    if c1.peek == '^' then neg := true; set c1.next
    let mut items : Array (Nat × Nat) := #[]
    repeat
      skipWs
      let cc ← get
      if cc.peek == ']' then set cc.next; break
      if cc.atEnd then return .error "unterminated character class"
      match ← scanClsItem with
      | .error e => return .error e
      | .ok it => items := items.push it
    return .ok (.cls (.ranges neg items.toList))
  else if Cursor.isIdentStart ch then
    match ← scanIdent with
    | .error e => return .error e
    | .ok (nm, _) =>
      match ds.find? nm with
      | some r => return .ok r
      | none => return .error s!"unknown lexer definition `{nm}` (not introduced by `let`)"
  else
    return .error s!"expected a regex atom at byte {c.pos.byteIdx}"
end

/-- Scan an optional mode transition after a rule's action: `enter <mode>` /
    `↓ <mode>` (push), or `leave` / `↱` (pop). Returns `stay` when none is
    present. Assumes the cursor is positioned after the action. -/
def scanLexerTrans : ScanM (Except String LexerTrans) := do
  skipWs
  let c ← get
  let ch := c.peek
  if ch == '↓' then
    set c.next
    match ← scanIdent with
    | .error e => return .error e
    | .ok (m, _) => return .ok (.push m)
  else if ch == '↱' then
    set c.next; return .ok .pop
  else if ch == 'e' && c.next.peek == 'n' then
    -- `enter <mode>`
    match ← scanIdent with
    | .error _ => return .ok .stay
    | .ok (kw, _) =>
      if kw == "enter" then
        match ← scanIdent with
        | .error e => return .error e
        | .ok (m, _) => return .ok (.push m)
      else return .error s!"unexpected `{kw}` after lexer action (expected a transition)"
  else if ch == 'l' && c.next.peek == 'e' then
    match ← scanIdent with
    | .error _ => return .ok .stay
    | .ok (kw, _) =>
      if kw == "leave" then return .ok .pop
      else return .error s!"unexpected `{kw}` after lexer action (expected a transition)"
  else
    return .ok .stay

/-- Scan one lexer rule starting just after a `|`: `<lexre> [as x] => { <action> }
    [transition]`. The action body is captured verbatim between braces (like a
    production action); the emit is `skip` or a token expression. A trailing
    `enter m` / `↓ m` / `leave` / `↱` moves the mode stack. -/
def scanLexerRule (ds : LexDefs) : ScanM (Except String LexerRule) := do
  let startPos := (← get).pos
  match ← scanRegexAlt ds with
  | .error e => return .error e
  | .ok regex =>
    skipWs
    let c ← get
    -- optional `as <binder>`
    let mut binder : Option String := none
    if c.peek == 'a' && c.next.peek == 's' && !Cursor.isIdentCont c.next.next.peek then
      set c.next.next
      match ← scanIdent with
      | .error e => return .error e
      | .ok (b, _) => binder := some b
    skipWs
    let c2 ← get
    if !(c2.peek == '=' && c2.next.peek == '>') then
      return .error s!"expected `=>` in lexer rule at byte {c2.pos.byteIdx}"
    set c2.next.next
    -- action: `skip` keyword, or a `{ verbatim }` token expression
    skipWs
    let c3 ← get
    let mut emit : Option String := none
    let mut endPos := c3.pos
    if c3.peek == 's' && c3.next.peek == 'k' then
      match ← scanIdent with
      | .error e => return .error e
      | .ok (kw, sp) =>
        if kw != "skip" then return .error s!"expected `skip` or `\{action}`, got `{kw}`"
        emit := none; endPos := sp.endPos
    else
      match ← captureBalanced '{' '}' with
      | .error e => return .error e
      | .ok (act, sp) => emit := some act.trimAscii.toString; endPos := sp.endPos
    match ← scanLexerTrans with
    | .error e => return .error e
    | .ok trans =>
      return .ok { regex := regex, binder := binder, emit := emit, trans := trans,
                   span := ⟨startPos, endPos⟩ }

/-- Scan a `rule <name> { | rule … }` mode block (cursor at `rule`). -/
def scanLexerModeBlock (ds : LexDefs) : ScanM (Except String LexerMode) := do
  let startPos := (← get).pos
  match ← scanIdent with
  | .error e => return .error e
  | .ok (kw, _) =>
    if kw != "rule" then return .error s!"expected `rule`, got `{kw}`"
    match ← scanIdent with
    | .error e => return .error e
    | .ok (modeName, _) =>
      skipWs
      let c ← get
      if c.peek != '{' then return .error s!"expected `\{` after `rule {modeName}`"
      set c.next
      let mut rules : Array LexerRule := #[]
      repeat
        skipWs
        let cc ← get
        if cc.peek == '}' then set cc.next; break
        if cc.peek != '|' then return .error s!"expected `|` or `}` in mode `{modeName}` at byte {cc.pos.byteIdx}"
        set cc.next
        match ← scanLexerRule ds with
        | .error e => return .error e
        | .ok r => rules := rules.push r
      let endPos := (← get).pos
      return .ok { name := modeName, rules := rules, span := ⟨startPos, endPos⟩ }

/-- Parse the interior of a `%lexer { … }` block. Supports `let name = <lexre>`
    definitions, then either `rule <mode> { … }` blocks (multi-mode) or a flat list
    of `| …` rules (single mode), followed by an optional `eof => { … }` clause. -/
partial def scanLexerBlockBody (blockSpan : Span) : ScanM (Except String LexerSpec) := do
  let mut ds : LexDefs := #[]
  let mut rustFns : Array (String × String) := #[]
  -- 1. `let` definitions and `rust` declarations
  repeat
    skipWs
    let c ← get
    if c.peek == 'r' && c.next.peek == 'u' && c.next.next.peek == 's'
       && c.next.next.next.peek == 't' && c.next.next.next.next.peek == ' ' then
      -- `rust <LeanName> => <rust::path>`
      set c.next.next.next.next
      let (line, _) ← restOfLine
      match line.splitOn "=>" with
      | [lhs, rhs] =>
        let lean := lhs.trimAscii.toString
        let path := rhs.trimAscii.toString
        if lean.isEmpty || path.isEmpty || lean.any Char.isWhitespace then
          return .error s!"expected `rust <LeanName> => <rust::path>`, got `rust {line.trimAscii.toString}`"
        rustFns := rustFns.push (lean, path)
      | _ => return .error s!"expected `rust <LeanName> => <rust::path>`, got `rust {line.trimAscii.toString}`"
    else if c.peek == 'l' && c.next.peek == 'e' && c.next.next.peek == 't'
       && !Cursor.isIdentCont c.next.next.next.peek then
      -- `let name = <lexre>`
      let _ := c.next.next.next
      set c.next.next.next
      match ← scanIdent with
      | .error e => return .error e
      | .ok (nm, _) =>
        skipWs
        let ceq ← get
        if ceq.peek != '=' then return .error s!"expected `=` after `let {nm}`"
        set ceq.next
        -- Parse the definition body from the rest of the line, so a following
        -- `| rule` is not swallowed as an alternation.
        let (bodyStr, _) ← restOfLine
        let bodyCur : Cursor := { input := bodyStr.trimAscii.toString, pos := ⟨0⟩ }
        match (scanRegexAlt ds).run bodyCur |>.1 with
        | .error e => return .error s!"in `let {nm}`: {e}"
        | .ok r => ds := ds.push (nm, r)
    else
      break
  -- 2. modes: either `rule …` blocks, or a flat `| …` rule list (one implicit mode)
  let mut modes : Array LexerMode := #[]
  skipWs
  let c ← get
  if c.peek == 'r' && c.next.peek == 'u' then
    -- multi-mode: one or more `rule <name> { … }`
    repeat
      skipWs
      let cc ← get
      if cc.atEnd || cc.peek == 'e' then break  -- `eof` or end
      if cc.peek != 'r' then break
      match ← scanLexerModeBlock ds with
      | .error e => return .error e
      | .ok m => modes := modes.push m
  else if c.peek == '|' then
    -- single implicit mode: flat rule list
    let mut rules : Array LexerRule := #[]
    repeat
      skipWs
      let cc ← get
      if cc.peek != '|' then break
      set cc.next
      match ← scanLexerRule ds with
      | .error e => return .error e
      | .ok r => rules := rules.push r
    modes := #[{ name := "main", rules := rules }]
  -- 3. optional `eof => { … }`
  skipWs
  let mut eof : Option String := none
  let ce ← get
  if ce.peek == 'e' && ce.next.peek == 'o' then
    match ← scanIdent with
    | .error e => return .error e
    | .ok (kw, _) =>
      if kw != "eof" then return .error s!"expected `eof`, got `{kw}`"
      skipWs
      let carr ← get
      if !(carr.peek == '=' && carr.next.peek == '>') then
        return .error "expected `=>` after `eof`"
      set carr.next.next
      match ← captureBalanced '{' '}' with
      | .error e => return .error e
      | .ok (act, _) => eof := some act.trimAscii.toString
  if modes.isEmpty then return .error "empty `%lexer` block: no rules or modes"
  return .ok { modes := modes, eof := eof, rustFns := rustFns, span := blockSpan }

/-- Parse the whole `.lig` text into a `Surface`. -/
partial def parseLig (input : String) (_fileName : String := "<lig>") :
    Except String Surface := do
  let run {α} (m : ScanM (Except String α)) (c : Cursor) : Except String (α × Cursor) :=
    let (r, c') := m.run c
    r.map (·, c')
  let mut cur : Cursor := { input := input, pos := ⟨0⟩ }
  let mut header := ""
  let mut lexerHeader := ""
  let mut tokens : Array TokenDecl := #[]
  let mut eof : Option String := none
  let mut start : Option String := none
  let mut tokenType := "Tok"
  let mut lexer : Option LexerSpec := none
  let mut options : Options := {}
  let mut sawSep := false
  repeat
    let (_, c1) := skipWs.run cur; cur := c1
    if cur.atEnd then break
    if cur.peek != '%' then
      throw s!"expected a %-directive or `%%` at byte {cur.pos.byteIdx}"
    if cur.next.peek == '%' then
      cur := cur.next.next; sawSep := true; break
    let (kw, c2) ← run scanDirectiveKw cur; cur := c2
    match kw with
    | "header" =>
      let (h, c3) ← run (captureBalanced '{' '}') cur; cur := c3
      header := h.1
    | "lexerheader" =>
      let (h, c3) ← run (captureBalanced '{' '}') cur; cur := c3
      lexerHeader := h.1
    | "tokentype" =>
      let (nm, c3) ← run scanIdent cur; cur := c3
      tokenType := nm.1
    | "token" =>
      let (ds, c3) ← run scanTokenDecls cur; cur := c3
      tokens := tokens ++ ds
    | "eof" =>
      let (nm, c3) ← run scanIdent cur; cur := c3
      eof := some nm.1
    | "start" =>
      let (nm, c3) ← run scanIdent cur; cur := c3
      start := some nm.1
    | "option" =>
      let (nm, c3) ← run scanIdent cur; cur := c3
      match nm.1 with
      | "compress_tables" => options := { options with compressTables := true }
      | "roundtrip_lexer" => options := { options with roundtripLexer := true }
      | "roundtrip_parser" =>
        let (fn, c4) ← run scanIdent cur; cur := c4
        options := { options with roundtripParser := some fn.1 }
      | "roundtrip_format" =>
        let (fn, c4) ← run scanIdent cur; cur := c4
        options := { options with roundtripFormat := some fn.1 }
      | "module_prefix" =>
        let (val, c4) ← run scanModulePath cur; cur := c4
        options := { options with modulePrefix := val.1 }
      | "gen_rust" =>
        let (val, c4) ← run scanPathWord cur; cur := c4
        options := { options with genRust := some val.1 }
      | "rust_ctx" =>
        let (val, c4) ← run scanPathWord cur; cur := c4
        options := { options with rustCtx := some val.1 }
      | "rust_list" =>
        let (val, c4) ← run scanPathWord cur; cur := c4
        options := { options with rustList := some val.1 }
      | other => throw s!"{unknownOptionMessage other} at byte {nm.2.startPos.byteIdx}"
    | "lexer" =>
      let (blk, c3) ← run (captureBalanced '{' '}') cur; cur := c3
      let (interior, blockSpan) := blk
      -- Parse the block interior with a fresh cursor over its text.
      let innerCur : Cursor := { input := interior, pos := ⟨0⟩ }
      match (scanLexerBlockBody blockSpan).run innerCur |>.1 with
      | .error e => throw s!"in %lexer block: {e}"
      | .ok spec => lexer := some spec
    | other => throw s!"unknown directive `%{other}`"
  unless sawSep do throw "missing `%%` separating directives from rules"
  let some eofName := eof | throw "missing `%eof` directive"
  let some startName := start | throw "missing `%start` directive"
  unless tokens.any (·.name == eofName) do
    throw s!"`%eof {eofName}` names a terminal that was not declared with `%token`"
  let mut rules : Array Rule := #[]
  repeat
    let (_, c1) := skipWs.run cur; cur := c1
    if cur.atEnd then break
    let (r, c2) ← run scanRule cur; cur := c2
    rules := rules.push r
  if rules.isEmpty then throw "no grammar rules found after `%%`"
  return { header := header, lexerHeader := lexerHeader, tokenType := tokenType, tokens := tokens, eof := eofName, start := startName, rules := rules, lexer := lexer, options := options }

end Frontend
