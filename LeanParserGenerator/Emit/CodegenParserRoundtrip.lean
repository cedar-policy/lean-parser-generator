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
The offline parser *roundtrip* backend.

Separate from `Emit/Codegen.lean` for the same reason the lexer roundtrip backend
is separate from the lexer backend: the parser module (`FooParser.lean`) is emitted
for every grammar, but the parser roundtrip module (`FooParserRoundtrip.lean`) is
only emitted when the user asks for it (`%option roundtrip_parser <unparse>` / the
`--roundtrip-parser` CLI mode / the `parsers` Lake target's roundtrip step). The
opt-in generation lives in its own file so that boundary is explicit.

The parser roundtrip is a *token-generation* inverse: the user supplies
`unparse : StartTy → List Tok` (the inverse of what `parse` consumes), and the
module proves `parse (unparse t) = some t` for the ASTs in a `corpus` the user
lists. It is token-level and does not involve the lexer — it is the half of the
AST↔source story the parser owns (DESIGN §1: the parser theorem begins at tokens).

When the user also names a complete token renderer `renderTok : Tok → String`
(`%option roundtrip_format`), the module additionally proves *formatter idempotence*
(formatting the token stream with whitespace re-lexes to the same tokens) and the
*full* AST↔source roundtrip, which composes the token-level parser roundtrip with
the lexer roundtrip.

Every theorem the module emits is hole-free (`native_decide`, the parser/lexer axiom
budget). There is no `sorry`: the guarantee is quantified over the user's `corpus`,
not over all ASTs — the universal statement would have to invert the LR automaton and
is out of scope, exactly as the lexer roundtrip is stated over reachable tokens
(docs/LEXER.md). A `#eval guarantees` line prints what was proven. See docs/DESIGN.md
§16.5. -/
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Emit.Builder


@[expose] public section

namespace Emit

open Frontend

/-- The declared Lean result type of the start nonterminal (`Policies` for Cedar,
    `Schema` for CedarSchema, `Int` for calc). The parser produces this type, so it
    is what `unparse` consumes and the roundtrip compares. -/
def startResultType (surface : Surface) : Option String :=
  (surface.rules.find? (fun r => r.lhs == surface.start)).map (·.ty)

/-- Does the lexer's start mode have a `skip` rule? A whitespace separator between
    rendered tokens must be consumed by such a rule for formatter idempotence to
    hold; this is the necessary precondition, checked so the generated module can
    note it. -/
def lexerSkipsWhitespace (surface : Surface) : Bool := Id.run do
  let some spec := surface.lexer | return false
  let some mode0 := spec.modes[0]? | return false
  for r in mode0.rules do
    if r.emit.isNone then return true
  return false

/-- Generate `FooParserRoundtrip.lean`. Needs a token-generator named by
    `%option roundtrip_parser`. With `%option roundtrip_format` and a `%lexer` block
    it also emits formatter idempotence and the full roundtrip. `unparseImport` is the
    dotted module path that defines `unparse` (and `renderTok` for the formatter): a
    dedicated module importing the lexer (for `Tok`) and the AST, since those
    functions reference `Tok`, which the shared `%header` cannot (the lexer defines
    `Tok` after the header is spliced). Its last dotted component is `open`ed so the
    option may name the functions unqualified. -/
def generateParserRoundtripFrom (surface : Surface)
    (lexerImport lexerName parserImport parserName unparseImport roundtripModule : String) :
    Except String String := do
  let some unparse := surface.options.roundtripParser
    | .error "no `%option roundtrip_parser <unparse>` in the grammar; nothing to generate"
  let some startTy := startResultType surface
    | .error s!"the start nonterminal `{surface.start}` has no rule, so its result type \
is unknown"
  let tokTy := surface.tokenType
  let unparseNamespace := (unparseImport.splitOn ".").getLastD unparseImport
  let fuel := 30
  let formatName := surface.options.roundtripFormat
  let hasFormat := formatName.isSome && surface.lexer.isSome
  let eofName : Option String := match surface.lexer.bind (·.eof) with
    | some e => let en := e.trimAscii.toString
                if en.startsWith s!"{tokTy}." then some ((en.drop (tokTy.length + 1)).toString)
                else if en.startsWith "." then some ((en.drop 1).toString) else none
    | none => none
  let eofTok := match eofName with | some e => s!"{tokTy}.{e}" | none => "default"
  -- The "what is proven" summary string, printed by `#eval guarantees`.
  let guaranteeLines : List String :=
    ["  roundtrip_corpus       : parse (unparse t) = some t"]
    ++ (if hasFormat then
          ["  formatter_idempotence  : relex (format (unparse t)) = tokens ++ EOF  (space/newline/tab)",
           "  full_roundtrip_corpus  : parse (lex (format (unparse t))) = some t"]
        else [])
  let guaranteeBody := String.intercalate "\\n"
    ([s!"{roundtripModule}: proven hole-free for every t in `corpus`:"] ++ guaranteeLines)
  let header :=
    s!"module\n" ++
    s!"-- Generated by leanparsergenerator: parser roundtrip (token-generation inverse).\n" ++
    s!"--\n" ++
    s!"-- WHAT IS PROVEN (all hole-free, `native_decide`; see `#eval guarantees` below):\n" ++
    s!"--   roundtrip_corpus       : parse (unparse t) = some t, for every t in `corpus`.\n" ++
    (if hasFormat then
      s!"--   formatter_idempotence  : formatting unparse-tokens with space/newline/tab\n" ++
      s!"--                            re-lexes to the same tokens (+ EOF).\n" ++
      s!"--   full_roundtrip_corpus  : parse (lex (format (unparse t))) = t, for every t.\n"
     else "") ++
    s!"-- There are NO `sorry`s: the guarantee is over the ASTs you list in `corpus`,\n" ++
    s!"-- not all ASTs (a universal inverse would invert the LR automaton). To extend a\n" ++
    s!"-- guarantee, add witnesses to `corpus` — that is the whole specification.\n" ++
    s!"public import {lexerImport}\n" ++
    s!"public import {parserImport}\n" ++
    s!"public import {unparseImport}\n" ++
    s!"meta import {lexerImport}\n" ++
    s!"meta import {parserImport}\n" ++
    s!"meta import {unparseImport}\n" ++
    (if surface.header.isEmpty then "" else Builder.publicizeImports surface.header ++ "\n") ++ "\n" ++
    s!"@[expose] public section\n\n" ++
    s!"namespace {roundtripModule}\n\n" ++
    s!"open Lexer Runtime {unparseNamespace}\n\n"
  let parserPart :=
    s!"/-- Generate the token list of an AST with the user's `unparse`, then parse it\n" ++
    s!"    back. The roundtrip asks this to return `some t` on the AST `t`. The tokens\n" ++
    s!"    carry dummy spans (`parse` consumes `Positioned {tokTy}`). -/\n" ++
    s!"def parseRoundtrip (t : {startTy}) : Option {startTy} :=\n" ++
    s!"  {parserName}.parse (({unparse} t).map Positioned.dummy) {fuel}\n\n" ++
    s!"/-- The witness corpus. **This is the whole specification**: the ASTs the\n" ++
    s!"    roundtrip is proven for. It lives in your `{unparseNamespace}` module as\n" ++
    s!"    `corpus` (so regeneration never overwrites your witnesses); add ASTs there\n" ++
    s!"    and the theorems below cover them with no other change. Each entry is checked\n" ++
    s!"    by `native_decide`. -/\n" ++
    s!"abbrev corpus : List {startTy} := {unparseNamespace}.corpus\n\n" ++
    s!"/-- **Proven (hole-free).** Every AST in `corpus` generates-and-reparses to\n" ++
    s!"    itself: `parse (unparse t) = some t`. `native_decide`. -/\n" ++
    s!"theorem roundtrip_corpus :\n" ++
    s!"    corpus.all (fun t => parseRoundtrip t == some t) = true := by native_decide\n\n"
  let formatPart :=
    if !hasFormat then
      "-- No `%option roundtrip_format <renderTok>`: only the token-level parser\n" ++
      "-- roundtrip above is proven. Add a complete token renderer and the option to\n" ++
      "-- also prove formatter idempotence and the full AST↔source roundtrip.\n\n"
    else
      let renderTok := formatName.get!
      let wsNote := if lexerSkipsWhitespace surface then "" else
        "-- WARNING: no `skip` rule found in the lexer's start mode; the whitespace\n" ++
        "-- separator may not be consumed, and formatter idempotence below may fail.\n"
      wsNote ++
      s!"/-! ### Formatter idempotence and the full roundtrip\n\n" ++
      s!"`format sep` renders a token list with `{renderTok}` and a whitespace separator\n" ++
      s!"after each token. Formatter idempotence is that re-lexing the formatted stream\n" ++
      s!"recovers the tokens (+ EOF): adding whitespace does not change the roundtrip. It\n" ++
      s!"holds because `{renderTok}` is complete and the lexer skips whitespace. The full\n" ++
      s!"roundtrip composes it with the token-level parser roundtrip. -/\n\n" ++
      s!"/-- Format a token list: each token's rendered text followed by the separator. -/\n" ++
      s!"def format (sep : String) (ts : List {tokTy}) : String :=\n" ++
      s!"  ts.foldr (fun t acc => {renderTok} t ++ sep ++ acc) \"\"\n\n" ++
      s!"/-- Re-lex a formatted token stream back to tokens (dropping the lexer error). -/\n" ++
      s!"def relex (sep : String) (ts : List {tokTy}) : Option (List {tokTy}) :=\n" ++
      s!"  ({lexerName}.tokenizeBare (format sep ts)).toOption\n\n" ++
      s!"/-- **Proven (hole-free).** For every AST in `corpus`, formatting its token\n" ++
      s!"    stream with a space, a newline, or a tab all re-lex to the same tokens + EOF\n" ++
      s!"    — adding whitespace does not change what the lexer recovers. `native_decide`. -/\n" ++
      s!"theorem formatter_idempotence :\n" ++
      s!"    corpus.all (fun t =>\n" ++
      s!"      let toks := {unparse} t\n" ++
      s!"      (relex \" \" toks == some (toks ++ [{eofTok}]))\n" ++
      s!"        && (relex \"\\n\" toks == relex \" \" toks)\n" ++
      s!"        && (relex \"\\t\" toks == relex \" \" toks)) = true := by native_decide\n\n" ++
      s!"/-- Full AST↔source roundtrip: generate tokens, format them to source with the\n" ++
      s!"    separator, lex, and parse. The composition of the token-level parser\n" ++
      s!"    roundtrip with the lexer roundtrip (formatter idempotence). -/\n" ++
      s!"def fullRoundtrip (sep : String) (t : {startTy}) : Option {startTy} :=\n" ++
      s!"  (relex sep ({unparse} t)).bind (fun toks => {parserName}.parse (toks.map Positioned.dummy) {fuel})\n\n" ++
      s!"/-- **Proven (hole-free).** Every AST in `corpus` survives the full AST→tokens→\n" ++
      s!"    source→tokens→AST roundtrip, for a space and a newline separator.\n" ++
      s!"    `native_decide`. -/\n" ++
      s!"theorem full_roundtrip_corpus :\n" ++
      s!"    corpus.all (fun t =>\n" ++
      s!"      (fullRoundtrip \" \" t == some t) && (fullRoundtrip \"\\n\" t == some t)) = true := by\n" ++
      s!"  native_decide\n\n"
  -- A visible, runnable summary of exactly what the module proves.
  let guaranteesPart :=
    s!"/-- A human-readable summary of what this module proves, for the ASTs in\n" ++
    s!"    `corpus`. Run `#eval guarantees` to print it. -/\n" ++
    s!"def guarantees : String :=\n" ++
    s!"  \"{guaranteeBody}\"\n\n" ++
    s!"-- `#eval guarantees` prints the proven roundtrip facts; the corpus size is how\n" ++
    s!"-- many ASTs those facts currently cover.\n" ++
    s!"#eval guarantees\n" ++
    s!"#eval s!\"corpus size: \{corpus.length}\"\n\n"
  return header ++ parserPart ++ formatPart ++ guaranteesPart ++ s!"end {roundtripModule}\n"

end Emit
