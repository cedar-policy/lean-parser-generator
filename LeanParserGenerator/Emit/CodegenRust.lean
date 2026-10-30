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
  let mut act : Array Nat := #[]
  for st in [0:numStates] do
    for t in [0:numT] do
      act := act.push (actCell ((tables.action.getD st #[]).getD t .error))
  let noGoto := 65535
  let mut gotoE : Array Nat := #[]
  for st in [0:numStates] do
    for n in [0:numN] do
      gotoE := gotoE.push (((tables.goto.getD st #[]).getD n none).getD noGoto)
  let defRed := (List.range numStates).toArray.map fun st =>
    (tables.defaultReduce.getD st none).getD noGoto
  let lhs := g.prods.map (·.lhs)
  let len := g.prods.map (·.rhs.length)
  let actMax := act.foldl max 0
  let nonterms := g.nontermNames
  let termNames := g.termNames
  return String.intercalate "\n\n" [
    s!"pub const NUM_TERMINALS: usize = {numT};\npub const NUM_NONTERMINALS: usize = {numN};\n" ++
    s!"pub const NUM_PRODUCTIONS: usize = {numP};\npub const NUM_STATES: usize = {numStates};\n" ++
    s!"const NONE: usize = {noGoto};\nconst AUG_PROD: usize = {prepared.augProd};",
    "static TERM_NAMES: [&str; " ++ toString numT ++ "] = [\n" ++
      packLines (termNames.map reprStr) ++ "\n];",
    "static NONTERM_NAMES: [&str; " ++ toString numN ++ "] = [\n" ++
      packLines (nonterms.map reprStr) ++ "\n];",
    "pub fn term_name(t: u16) -> &'static str {\n    TERM_NAMES[t as usize]\n}",
    "pub fn nonterm_name(n: usize) -> &'static str {\n    NONTERM_NAMES[n]\n}",
    "/// The left-hand side nonterminal of production `p`.\npub fn prod_lhs(p: usize) -> usize {\n    LHS[p] as usize\n}",
    "/// The number of right-hand side symbols of production `p`.\npub fn prod_len(p: usize) -> usize {\n    RHS_LEN[p] as usize\n}",
    "/// `ACTION[state * NUM_TERMINALS + terminal]`: 0 error, `(target << 1) | 1` shift,\n" ++
      "/// `(production + 1) << 1` reduce.\n" ++
      staticArr "ACTION" (uintTy actMax) (act.map toString),
    "/// `GOTO[state * NUM_NONTERMINALS + nonterminal]`; `NONE` when absent.\n" ++
      staticArr "GOTO" "u16" (gotoE.map toString),
    "/// The production a state reduces regardless of lookahead, or `NONE`.\n" ++
      staticArr "DEFAULT_REDUCE" "u16" (defRed.map toString),
    staticArr "LHS" (uintTy numN) (lhs.map toString),
    staticArr "RHS_LEN" "u8" (len.map toString),
    String.intercalate "\n" [
      "/// A node of the postorder trace: a shifted token or a reduction.",
      "#[derive(Clone, Copy, Debug, PartialEq, Eq)]",
      "pub struct Node {",
      "    /// A terminal index, or `PROD_FLAG | production`.",
      "    pub kind: u16,",
      "    pub start: u32,",
      "    pub end: u32,",
      "}",
      "",
      "pub const PROD_FLAG: u16 = 0x8000;",
      "",
      "#[derive(Clone, Copy, Debug, PartialEq, Eq)]",
      "pub struct Entry {",
      "    pub state: u16,",
      "    pub start: u32,",
      "}",
      "",
      "#[derive(Clone, Copy, Debug, PartialEq, Eq)]",
      "pub struct ParseError {",
      "    /// Index of the offending token.",
      "    pub token: usize,",
      "    pub state: usize,",
      "    pub term: u16,",
      "}",
      "",
      "/// Parse `tokens` (ending with the end-of-input terminal). `stack` and `nodes` are",
      "/// scratch/output buffers and are cleared first. On success `nodes` is the postorder",
      "/// trace and its last node is the augmented start production.",
      "pub fn parse<T: Terminal>(",
      "    tokens: &[Spanned<T>],",
      "    stack: &mut Vec<Entry>,",
      "    nodes: &mut Vec<Node>,",
      ") -> Result<(), ParseError> {",
      "    stack.clear();",
      "    nodes.clear();",
      "    stack.push(Entry { state: 0, start: 0 });",
      "    let mut ti = 0usize;",
      "    let mut prev_end = 0u32;",
      "    loop {",
      "        let state = stack[stack.len() - 1].state as usize;",
      "        let dr = DEFAULT_REDUCE[state] as usize;",
      "        let prod = if dr != NONE {",
      "            dr",
      "        } else {",
      "            let (term, tstart, tend) = if ti < tokens.len() {",
      "                (tokens[ti].tok.term(), tokens[ti].start, tokens[ti].end)",
      "            } else {",
      "                (EOF, prev_end, prev_end)",
      "            };",
      "            let a = ACTION[state * NUM_TERMINALS + term as usize] as usize;",
      "            if a == 0 {",
      "                return Err(ParseError { token: ti, state, term });",
      "            }",
      "            if a & 1 == 1 {",
      "                stack.push(Entry { state: (a >> 1) as u16, start: tstart });",
      "                nodes.push(Node { kind: term, start: tstart, end: tend });",
      "                prev_end = tend;",
      "                ti += 1;",
      "                continue;",
      "            }",
      "            (a >> 1) - 1",
      "        };",
      "        let n = RHS_LEN[prod] as usize;",
      "        if n >= stack.len() {",
      "            return Err(ParseError { token: ti, state, term: u16::MAX });",
      "        }",
      "        let base = stack.len() - n;",
      "        let start = if n > 0 { stack[base].start } else { prev_end };",
      "        stack.truncate(base);",
      "        let top = stack[base - 1].state as usize;",
      "        let g = GOTO[top * NUM_NONTERMINALS + LHS[prod] as usize] as usize;",
      "        nodes.push(Node { kind: PROD_FLAG | prod as u16, start, end: prev_end });",
      "        if g == NONE {",
      "            return if prod == AUG_PROD {",
      "                Ok(())",
      "            } else {",
      "                Err(ParseError { token: ti, state, term: u16::MAX })",
      "            };",
      "        }",
      "        stack.push(Entry { state: g as u16, start });",
      "    }",
      "}" ] ]

/-- The Rust source for a grammar's lexer (if it has a `%lexer` block) and parser. -/
def generateRustFrom (s : Surface) (prepared : PreparedGrammar) (source : String := "") :
    Except String String := do
  let g := prepared.augmented
  let augEof := g.numTerminals - 1
  if g.prods.size ≥ 0x8000 then throw "too many productions for the Rust node encoding"
  -- With a `%lexer` block the lexer owns `Tok`; without one, the caller supplies tokens
  -- by implementing `Terminal` (`Kind` is the plain terminal index).
  let lexer ← match s.lexer with
    | some spec => renderLexer s augEof spec
    | none => pure ""
  let parser := renderParser prepared
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
    s!"pub const EOF: u16 = {augEof};",
    "/// The terminal index of a token, as the parser reads it.\n" ++
      "pub trait Terminal {\n    fn term(&self) -> u16;\n}",
    "/// A token with its byte span in the source.\n" ++
      "#[derive(Clone, Debug, PartialEq, Eq)]\n" ++
      "pub struct Spanned<T> {\n    pub tok: T,\n    pub start: u32,\n    pub end: u32,\n}",
    "/// Terminal indices by token name.\npub mod term {\n" ++
      "\n".intercalate consts.toList ++ "\n}" ] ++ "\n"
  let kind := if s.lexer.isSome then [] else [
    "/// A token that is only its terminal index, for grammars without a lexer.\n" ++
    "#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n" ++
    "pub struct Kind(pub u16);\n\n" ++
    "impl Terminal for Kind {\n    fn term(&self) -> u16 {\n        self.0\n    }\n}"]
  return String.intercalate "\n\n" (
    [header, common] ++ kind ++ (if lexer.isEmpty then [] else [lexer]) ++ [parser ++ "\n"])

end Emit.Rust
