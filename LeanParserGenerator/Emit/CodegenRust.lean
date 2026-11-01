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
The Rust backend (prototype). See docs/RUST_PARSER.md.

From the same `Surface` and `PreparedGrammar` that the Lean backends consume, this
renders one `.rs` file holding a byte-level DFA lexer and an LR(1) table-driven
parser. The tables are the Lean ones (`Construct.Tables`, `Lexer.ByteDFA`) written
as `static` arrays, with one change of representation: the byte DFA's columns are
merged into equivalence classes.

The parser has no semantic actions. It returns a postorder concrete-syntax trace
(`Vec<Node>`: one node per shifted token and one per reduction). The lexer is
`Emit/Rust/Lexer.lean`.
-/
public import LeanParserGenerator.Emit.Codegen
public import LeanParserGenerator.Emit.Rust.Lexer
public import LeanParserGenerator.Emit.Rust.Values


@[expose] public section

namespace Emit.Rust

open Frontend Lexer Construct

/-- Render the parser tables and the LR driver. -/
def renderParser (prepared : PreparedGrammar) : String := Id.run do
  let g := prepared.augmented
  let tables := prepared.tables
  let numT := g.numTerminals
  let numN := g.numNonterminals
  let numP := g.prods.size
  let numStates := tables.numStates
  -- Action cell: 0 error; `(target << 1) | 1` shift; `(prod + 1) << 1` reduce.
  let actCell (a : Act) : Nat :=
    match a with | .error => 0 | .shift j => (j <<< 1) ||| 1 | .reduce p => (p + 1) <<< 1
  let mut actRows : Array (Array String) := #[]
  for st in [0:numStates] do
    actRows := actRows.push <| (Array.range numT).map fun t =>
      toString (actCell ((tables.action.getD st #[]).getD t .error))
  let noGoto := 65535
  let mut gotoRows : Array (Array String) := #[]
  for st in [0:numStates] do
    gotoRows := gotoRows.push <| (Array.range numN).map fun n =>
      toString (((tables.goto.getD st #[]).getD n none).getD noGoto)
  let defRed := (List.range numStates).toArray.map fun st =>
    (tables.defaultReduce.getD st none).getD noGoto
  let lhs := g.prods.map (·.lhs)
  let len := g.prods.map (·.rhs.length)
  let nonterms := g.nontermNames
  let termNames := g.termNames
  return String.intercalate "\n\n" [
    s!"pub const NUM_TERMINALS: usize = {numT};\npub const NUM_NONTERMINALS: usize = {numN};\n" ++
    s!"pub const NUM_PRODUCTIONS: usize = {numP};\npub const NUM_STATES: usize = {numStates};\n" ++
    s!"const NONE: usize = {noGoto};\n/// The augmented start production.\npub const AUG_PROD: usize = {prepared.augProd};",
    "static TERM_NAMES: [&str; " ++ toString numT ++ "] = [\n" ++
      packLines (termNames.map reprStr) ++ "\n];",
    "static NONTERM_NAMES: [&str; " ++ toString numN ++ "] = [\n" ++
      packLines (nonterms.map reprStr) ++ "\n];",
    "pub fn term_name(t: u16) -> &'static str {\n    TERM_NAMES[t as usize]\n}",
    "pub fn nonterm_name(n: usize) -> &'static str {\n    NONTERM_NAMES[n]\n}",
    "/// The left-hand side nonterminal of production `p`.\npub fn prod_lhs(p: usize) -> usize {\n    LHS[p] as usize\n}",
    "/// The number of right-hand side symbols of production `p`.\npub fn prod_len(p: usize) -> usize {\n    RHS_LEN[p] as usize\n}",
    "/// `ACTION[state][terminal]`: 0 error, `(target << 1) | 1` shift,\n" ++
      "/// `(production + 1) << 1` reduce.\n" ++
      staticRows "ACTION" "u16" numT actRows,
    "/// `GOTO[state][nonterminal]`; `NONE` when absent.\n" ++
      staticRows "GOTO" "u16" numN gotoRows,
    "/// The production a state reduces regardless of lookahead, or `NONE`.\n" ++
      staticArr "DEFAULT_REDUCE" "u16" (defRed.map toString),
    staticArr "LHS" "u16" (lhs.map toString),
    staticArr "RHS_LEN" "u16" (len.map toString),
    String.intercalate "\n" [
      "/// Parse `tokens` (which end with the end-of-input token, or the parser reads `EOF`).",
      "/// `stack` and `nodes` are scratch and output buffers and are cleared first. On success",
      "/// `nodes` is the postorder trace and its last node is the augmented start production.",
      "/// The loop is `lpg_kernel::parse`, the same for every grammar (docs/RUST_PARSER.md).",
      "pub fn parse(",
      "    tokens: &[Token],",
      "    stack: &mut Vec<Entry>,",
      "    nodes: &mut Vec<Node>,",
      ") -> Result<(), ParseError> {",
      "    lpg_kernel::parse(tokens, stack, nodes, &ACTION, &GOTO, &DEFAULT_REDUCE, &LHS, &RHS_LEN, EOF, lpg_kernel::FUEL)",
      "}" ] ]

/-- The Rust source for a grammar's lexer (if it has a `%lexer` block) and parser. -/
def generateRustFrom (s : Surface) (prepared : PreparedGrammar) (source : String := "") :
    Except String String := do
  let g := prepared.augmented
  let augEof := g.numTerminals - 1
  if g.prods.size ≥ 0x8000 then throw "too many productions for the Rust node encoding"
  -- With a `%lexer` block the lexer produces the `Token`s and owns `Tok`, the tokens with
  -- their values; without one, the caller supplies the `Token`s (`rule` is not read).
  let lexer ← match s.lexer with
    | some spec => renderLexer s augEof spec
    | none => pure ""
  let parser := renderParser prepared
  -- With Rust actions in the `.lig`: the value stacks and `parse_values`.
  let values ← if hasRustActions s then do
      let plan ← planValues s
      let tokLt ← if s.lexer.isSome then do pure (← renderTok s augEof).1 else pure ""
      renderValueParser s plan s.lexer.isSome tokLt
    else pure ""
  -- Terminal constants. The `%eof` token's own declaration slot is unused (it is
  -- renamed to the augmented end terminal).
  let mut consts : Array String := #[]
  for (t, i) in s.tokens.zipIdx do
    let idx := if t.name == s.eof then augEof else i
    consts := consts.push s!"    pub const {t.name}: u16 = {idx};"
  let header := String.intercalate "\n" [
    "// Generated by LeanParserGenerator from a .lig grammar. DO NOT EDIT." ++
      (if source.isEmpty then "" else s!"\n// Source: {source}"),
    "// Backend: rust (prototype; see docs/RUST_PARSER.md).",
    "#![allow(dead_code)]" ]
  let common := String.intercalate "\n\n" [
    "#[allow(unused_imports)]\npub use lpg_kernel::{Entry, Node, ParseError, Token, PROD_FLAG};",
    s!"pub const EOF: u16 = {augEof};",
    "/// Terminal indices by token name.\npub mod term {\n" ++
      "\n".intercalate consts.toList ++ "\n}" ] ++ "\n"
  return String.intercalate "\n\n" (
    [header, common] ++ (if lexer.isEmpty then [] else [lexer]) ++ [parser ++ "\n"] ++ (if values.isEmpty then [] else [values]))

end Emit.Rust
