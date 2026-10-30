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
The Rust lexer (docs/RUST_PARSER.md, "Lexers").

The Rust backend accepts a lexer rule only if its action has one of five forms. With
`%token IDENT` valueless, `%token <T> NAME` carrying a value, and `s` the `as` binder:

    skip                      emit nothing
    Tok.IDENT                 a token without a value
    Tok.NAME s                a token whose value is the lexeme (type `String`, `&'a str` in Rust)
    Tok.NAME (f s)            a token whose value is `f` applied to the lexeme
    g s                       the token `g` computes from the lexeme

`f` and `g` are Lean functions. A function in `builtinFns` has a Rust counterpart in
the generated prelude; any other needs a declaration `rust f => path::to::f` in the
`%lexer` block, and the user writes it in Rust. The Rust counterpart of `f : String → T`
has type `fn(&str) -> Option<T'>` and that of `g : String → Tok` has type
`fn(&str) -> Option<Tok>`, where `T'` is the Rust type of `T`. `None` means the Lean
result is not representable in Rust (a numeral beyond `u64`); the lexer then fails at the
start of the lexeme. The Lean definition stays the
specification: the verification step relates the two (docs/RUST_PARSER.md).
Everything else is an error that names the rule.

The generated `Tok` enum has one variant per `%token`, with the Rust type of the
declared Lean type as payload (`rustTyOf`). Lean's dependent types have no Rust
counterpart: a subtype is its base type. A `String` payload is a slice of the source,
`&'a str`, so that lexing does not allocate (decision D13); `Tok` then has the lifetime
parameter `'a`, and only then.
-/
public import LeanParserGenerator.Emit.Rust.Action
public import LeanParserGenerator.Emit.Rust.Ty
public import LeanParserGenerator.Emit.Rust.Text
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Lexer.ByteScan
public import LeanParserGenerator.Lexer.DFA


@[expose] public section

namespace Emit.Rust

open Frontend Lexer

/-- The Rust type of a token value of Lean type `t` (decision D7: `Nat` is `u64`). -/
def rustTyOf : Ty → Except String String
  | .con "String" #[] => .ok "&'a str"
  | .con "Nat" #[] => .ok "u64"
  | .con "Int" #[] => .ok "i64"
  | .con "Bool" #[] => .ok "bool"
  | .con "Char" #[] => .ok "char"
  | .sub b => rustTyOf b
  | t => .error s!"no Rust type for the token value type `{repr t}`"

/-- The Lean library functions that the generated prelude (`lexrt`) implements. -/
def builtinFns : List (String × String) := [
  ("String.toNat!", "lexrt::to_nat"),
  ("String.toInt!", "lexrt::to_int"),
  ("String.length", "lexrt::length") ]

/-- The forms of lexer action the Rust backend accepts. -/
inductive LexAct where
  | skip
  /-- `Tok.NAME`: terminal index. -/
  | const (name : String)
  /-- `Tok.NAME s`. -/
  | lexeme (name : String)
  /-- `Tok.NAME (f s)`, with the Rust path of `f`. -/
  | transform (name : String) (fn : String)
  /-- `g s`, with the Rust path of `g`. -/
  | tokenFn (fn : String)
  deriving Repr, BEq, Inhabited

/-- The Rust path of a Lean function used in a lexer action. -/
def rustFnOf (spec : LexerSpec) (lean : String) : Except String String :=
  match spec.rustFns.find? (·.1 == lean) with
  | some (_, path) => .ok path
  | none =>
    match builtinFns.lookup lean with
    | some p => .ok p
    | none => .error s!"`{lean}` has no Rust counterpart; declare `rust {lean} => path::to::fn` in the %lexer block"

/-- The name of the Lean function if `e` is `f s` or `s.f` for the lexeme `s`. -/
def lexemeCall (b : String) : AExpr → Option String
  | .app (.global f) #[.var x] => if x == b then some f else none
  | .field (.var x) m => if x == b then some ("String." ++ m) else none
  | _ => none

/-- Classify the action of one lexer rule against the five forms. -/
def classifyLexAct (s : Surface) (spec : LexerSpec) (r : LexerRule) : Except String LexAct := do
  let some src := r.emit | return .skip
  let b := r.binder.getD ""
  let e := Action.parse (match r.binder with | some b => [b] | none => []) src
  let pre := s.tokenType ++ "."
  let tokName? (n : String) : Option String :=
    if n.startsWith pre then some (n.drop pre.length).toString else none
  let decl (name : String) : Except String TokenDecl :=
    match s.tokens.find? (·.name == name) with
    | some t => .ok t
    | none => .error s!"`{pre}{name}` is not a declared %token"
  let bad : Except String LexAct :=
    .error s!"lexer action `{src.trimAscii.toString}` is not one of: skip, {pre}T, {pre}T s, {pre}T (f s), g s"
  match e with
  | .global n =>
    match tokName? n with
    | some name =>
      let t ← decl name
      if t.hasVal then .error s!"`{n}` carries a value but the action gives none" else .ok (.const name)
    | none => bad
  | .app (.global n) #[arg] =>
    match tokName? n with
    | some name =>
      let t ← decl name
      if !t.hasVal then .error s!"`{n}` carries no value but the action gives one"
      else
        match arg with
        | .var x =>
          if x == b then
            match Ty.parse t.ty with
            | .con "String" #[] | .sub (.con "String" #[]) => .ok (.lexeme name)
            | _ => .error s!"`{n} {b}`: the lexeme is a String but `{n}` carries `{t.ty}`; apply a function"
          else bad
        | _ =>
          match lexemeCall b arg with
          | some f => return .transform name (← rustFnOf spec f)
          | none => .error s!"lexer action `{src.trimAscii.toString}`: the value must be the lexeme `{b}` or one function applied to it (declare a function for a composition)"
    | none =>
      match lexemeCall b e with
      | some f => return .tokenFn (← rustFnOf spec f)
      | none => bad
  | _ =>
    match lexemeCall b e with
    | some f => return .tokenFn (← rustFnOf spec f)
    | none => bad

/-- Merge byte columns that agree on every state: `(classOf, nClasses)`. -/
def byteClasses (bd : ByteDFA) : Array Nat × Nat := Id.run do
  let mut seen : Std.HashMap (Array Nat) Nat := {}
  let mut cls : Array Nat := #[]
  for b in [0:256] do
    let mut col : Array Nat := Array.mkEmpty bd.nStates
    for st in [0:bd.nStates] do
      col := col.push (bd.trans.getD (st * 256 + b) 0)
    match seen.get? col with
    | some c => cls := cls.push c
    | none =>
      let c := seen.size
      seen := seen.insert col c
      cls := cls.push c
  return (cls, seen.size)

/-- The Rust prelude: the Rust counterparts of `builtinFns`. -/
def prelude : String := String.intercalate "\n" [
  "/// Rust counterparts of the Lean library functions that lexer actions may call. Each",
  "/// returns `None` where the Lean result does not fit the Rust type, or where the Lean",
  "/// function is applied outside its domain.",
  "pub mod lexrt {",
  "    /// `String.toNat!` on a non-empty string of decimal digits, as a `u64`.",
  "    pub fn to_nat(s: &str) -> Option<u64> {",
  "        if s.is_empty() {",
  "            return None;",
  "        }",
  "        let mut n: u64 = 0;",
  "        for b in s.bytes() {",
  "            if !b.is_ascii_digit() {",
  "                return None;",
  "            }",
  "            n = n.checked_mul(10)?.checked_add((b - b'0') as u64)?;",
  "        }",
  "        Some(n)",
  "    }",
  "",
  "    /// `String.toInt!` on an optional `-` and decimal digits, as an `i64`.",
  "    pub fn to_int(s: &str) -> Option<i64> {",
  "        match s.strip_prefix('-') {",
  "            Some(rest) => {",
  "                let n = to_nat(rest)?;",
  "                if n <= i64::MAX as u64 {",
  "                    Some(-(n as i64))",
  "                } else if n == i64::MAX as u64 + 1 {",
  "                    Some(i64::MIN)",
  "                } else {",
  "                    None",
  "                }",
  "            }",
  "            None => i64::try_from(to_nat(s)?).ok(),",
  "        }",
  "    }",
  "",
  "    /// `String.length`: the number of characters.",
  "    pub fn length(s: &str) -> Option<u64> {",
  "        Some(s.chars().count() as u64)",
  "    }",
  "}" ]

/-- Render the `Tok` enum and its `Terminal` instance. -/
def renderTok (s : Surface) (augEof : Nat) : Except String (String × String) := do
  let mut variants : Array String := #[]
  let mut arms : Array String := #[]
  let mut borrows := false
  for (t, i) in s.tokens.zipIdx do
    let idx := if t.name == s.eof then augEof else i
    if t.hasVal then
      let ty ← rustTyOf (Ty.parse t.ty)
      if ty.contains '\'' then borrows := true
      variants := variants.push s!"    {t.name}({ty}),"
      arms := arms.push s!"            Tok::{t.name}(_) => {idx},"
    else
      variants := variants.push s!"    {t.name},"
      arms := arms.push s!"            Tok::{t.name} => {idx},"
  let lt := if borrows then "<'a>" else ""
  let impl_ := if borrows then "impl<'a>" else "impl"
  return (lt, String.intercalate "\n" [
    "#[derive(Clone, Debug, PartialEq, Eq)]",
    "#[allow(non_camel_case_types)]",
    s!"pub enum Tok{lt} \{",
    "\n".intercalate variants.toList,
    "}",
    "",
    s!"{impl_} Terminal for Tok{lt} \{",
    "    fn term(&self) -> u16 {",
    "        match self {",
    "\n".intercalate arms.toList,
    "        }",
    "    }",
    "}" ])

/-- The Rust statement that handles a rule's match: it pushes the token directly, so
    that the token is built in the output vector and not on the stack first. -/
def stepStmt : LexAct → String
  | .skip => "{}"
  | .const n => s!"out.push(Spanned \{ tok: Tok::{n}, start: pos as u32, end: end as u32 })"
  | .lexeme n =>
    s!"out.push(Spanned \{ tok: Tok::{n}(text), start: pos as u32, end: end as u32 })"
  | .transform n f =>
    s!"match {f}(text) \{ Some(v) => out.push(Spanned \{ tok: Tok::{n}(v), start: pos as u32, end: end as u32 }), None => return Err(lex_error(src, pos, LexErrorReason::Unrepresentable)) }"
  | .tokenFn f =>
    s!"match {f}(text) \{ Some(tok) => out.push(Spanned \{ tok, start: pos as u32, end: end as u32 }), None => return Err(lex_error(src, pos, LexErrorReason::Unrepresentable)) }"

/-- A mode's DFA in the layout the Rust scanner reads (decision D16).

State `s` of the byte DFA is renumbered so that the accepting states come last, and
state number `k` is the row at offset `(k + 1) * nc`; row 0 is the dead row. A table
entry is the offset of the target row (0 for dead), so a step is
`trans[off + class]` with no multiplication, and "this state accepts" is
`off >= acceptFrom`. `acceptAt[off]` is the accepting rule plus one at an accepting
row's offset. -/
structure EncodedMode where
  /-- The new number of each original state. -/
  newIdx : Array Nat
  /-- `trans[off + class]`. -/
  trans : Array Nat
  /-- The accepting rule plus one, by row offset (0 elsewhere). -/
  acceptAt : Array Nat
  /-- Offset of the start row. -/
  start : Nat
  /-- Rows at or above this offset accept. -/
  acceptFrom : Nat

/-- Re-encode a byte DFA with byte classes `cls`/`nc`. -/
def encodeMode (bd : ByteDFA) (cls : Array Nat) (nc : Nat) : EncodedMode := Id.run do
  let nonAcc := (List.range bd.nStates).filter fun s => bd.accept.getD s (-1) < 0
  let acc := (List.range bd.nStates).filter fun s => !(bd.accept.getD s (-1) < 0)
  let order := (nonAcc ++ acc).toArray
  let mut newIdx : Array Nat := Array.replicate bd.nStates 0
  for h : k in [0:order.size] do
    newIdx := newIdx.set! order[k] k
  -- One representative byte per class.
  let mut rep : Array Nat := Array.replicate nc 0
  for b in (List.range 256).reverse do
    rep := rep.set! cls[b]! b
  let size := (bd.nStates + 1) * nc
  let mut trans : Array Nat := Array.replicate size 0
  let mut acceptAt : Array Nat := Array.replicate size 0
  for k in [0:order.size] do
    let o := order[k]!
    for c in [0:nc] do
      let tg := bd.trans.getD (o * 256 + rep[c]!) 0
      if tg != 0 then
        trans := trans.set! ((k + 1) * nc + c) ((newIdx[tg - 1]! + 1) * nc)
    match bd.accept.getD o (-1) with
    | .ofNat r => acceptAt := acceptAt.set! ((k + 1) * nc) (r + 1)
    | _ => pure ()
  return { newIdx, trans, acceptAt, start := (newIdx[0]! + 1) * nc,
           acceptFrom := (nonAcc.length + 1) * nc }

/-- Does the encoding agree with the byte DFA on every state and byte, and on which
    states accept? The generator refuses to emit a table that fails this. -/
def EncodedMode.agrees (e : EncodedMode) (bd : ByteDFA) (cls : Array Nat) (nc : Nat) : Bool :=
  (List.range bd.nStates).all fun o =>
    let off := (e.newIdx[o]! + 1) * nc
    let acceptOk :=
      match bd.accept.getD o (-1) with
      | .ofNat r => off >= e.acceptFrom && e.acceptAt[off]! == r + 1
      | _ => off < e.acceptFrom
    acceptOk && (List.range 256).all fun b =>
      let tg := bd.trans.getD (o * 256 + b) 0
      let t := e.trans[off + cls[b]!]!
      if tg == 0 then t == 0 else t == (e.newIdx[tg - 1]! + 1) * nc

/-- Render the lexer: tables, then `tokenize`. Fails on an action outside the five
    forms. -/
def renderLexer (s : Surface) (augEof : Nat) (spec : LexerSpec) : Except String String := do
  -- The %eof token must be the `eof` action's constant (or absent).
  match spec.eof with
  | none => pure ()
  | some e =>
    let e := e.trimAscii.toString
    unless e == s.tokenType ++ "." ++ s.eof do
      throw s!"the `eof` action must be `{s.tokenType}.{s.eof}`, got `{e}`"
  let (lt, tokEnum) ← renderTok s augEof
  -- Build every mode's byte DFA.
  let mut dfas : Array (ByteDFA × Array Nat × Nat) := #[]
  for mode in spec.modes do
    let some (dfa, _) := DFA.build?WithVecs (mode.rules.map (·.regex))
      | throw s!"DFA construction for mode `{mode.name}` ran out of fuel"
    let bd := ByteDFA.byteOfFlat (DFA.flatOfDFA dfa)
    let (cls, nc) := byteClasses bd
    dfas := dfas.push (bd, cls, nc)
  let maxOff := dfas.foldl (fun m (bd, _, nc) => max m ((bd.nStates + 1) * nc)) 0
  let maxRules := spec.modes.foldl (fun m md => max m md.rules.size) 0
  let transTy := uintTy maxOff
  let acceptTy := uintTy maxRules
  let modeIdx (m : String) : Option Nat := spec.modes.findIdx? (·.name == m)
  let mut tables : Array String := #[]
  let mut modeRecs : Array String := #[]
  let mut modeArms : Array String := #[]
  let mut transArms : Array String := #[]
  let mut usesModes := false
  for h : mi in [0:spec.modes.size] do
    let mode := spec.modes[mi]
    let (bd, cls, nc) := dfas[mi]!
    let e := encodeMode bd cls nc
    unless e.agrees bd cls nc do
      throw s!"internal error: the re-encoded tables of mode `{mode.name}` disagree with the byte DFA"
    tables := tables.push (String.intercalate "\n" [
      s!"// Mode `{mode.name}`: {bd.nStates} states, {nc} byte classes.",
      staticArr s!"M{mi}_CLASS" "u8" (cls.map toString),
      staticArr s!"M{mi}_TRANS" transTy (e.trans.map toString),
      staticArr s!"M{mi}_ACCEPT" acceptTy (e.acceptAt.map toString) ])
    modeRecs := modeRecs.push
      (s!"    Mode \{ class: &M{mi}_CLASS, trans: &M{mi}_TRANS, accept: &M{mi}_ACCEPT, " ++
       s!"start: {e.start}, accept_from: {e.acceptFrom} },")
    -- Actions
    let mut arms : Array String := #[]
    let mut skips : Array String := #[]
    let mut tarms : Array String := #[]
    for h2 : ri in [0:mode.rules.size] do
      let r := mode.rules[ri]
      let act ← classifyLexAct s spec r
        |>.mapError fun e => s!"mode `{mode.name}`, rule {ri}: {e}"
      match act with
      | .skip => skips := skips.push (toString ri)
      | _ => arms := arms.push s!"                {ri} => {stepStmt act},"
      match r.trans with
      | .stay => pure ()
      | .push m =>
        match modeIdx m with
        | some j => tarms := tarms.push s!"                {ri} => stack.push({j}),"; usesModes := true
        | none => throw s!"lexer rule enters unknown mode `{m}`"
      | .pop =>
        tarms := tarms.push s!"                {ri} => \{ stack.pop(); }"; usesModes := true
    let skipArm := if skips.isEmpty then [] else
      [s!"                {" | ".intercalate skips.toList} => \{}"]
    modeArms := modeArms.push (String.intercalate "\n" (
      [s!"            {mi} => match r \{"] ++ arms.toList ++ skipArm ++
      ["                _ => {}", "            },"]))
    transArms := transArms.push (String.intercalate "\n" (
      [s!"            {mi} => match r \{"] ++ tarms.toList ++ ["                _ => {}", "            },"]))
  let modeVar := if usesModes then "stack.last().copied().unwrap_or(0)" else "0"
  let body := String.intercalate "\n" ([
    "/// Longest-match tokenization of `src`, appending to `out` (which is not cleared).",
    "/// The last token pushed is the end-of-input token.",
    (if lt.isEmpty then "pub fn tokenize(src: &str, out: &mut Vec<Spanned<Tok>>) -> Result<(), LexError> {"
     else "pub fn tokenize<'a>(src: &'a str, out: &mut Vec<Spanned<Tok<'a>>>) -> Result<(), LexError> {"),
    "    let bytes = src.as_bytes();",
    "    let n = bytes.len();",
    "    let mut pos = 0usize;" ] ++
    (if usesModes then ["    let mut stack: Vec<usize> = vec![0];"] else []) ++ [
    "    while pos < n {",
    s!"        let mode = {modeVar};",
    "        let (rule, end) = scan(&MODES[mode], bytes, pos);",
    "        if rule == 0 || end == pos {",
    "            return Err(lex_error(src, pos, LexErrorReason::NoMatch));",
    "        }",
    "        let r = rule - 1;",
    "        let text = &src[pos..end];" ] ++
    (if usesModes then [
      "        match mode {",
      "\n".intercalate transArms.toList,
      "            _ => {}",
      "        }" ] else []) ++ [
    "        match mode {",
    "\n".intercalate modeArms.toList,
    "            _ => {}",
    "        }",
    "        pos = end;",
    "    }" ] ++
    (if usesModes then [
      "    if stack.len() != 1 {",
      "        return Err(lex_error(src, n, LexErrorReason::EndInMode));",
      "    }" ] else []) ++ [
    "    out.push(Spanned { tok: Tok::" ++ s.eof ++ ", start: n as u32, end: n as u32 });",
    "    Ok(())",
    "}" ])
  return String.intercalate "\n\n" [
    tokEnum,
    prelude,
    "/// One lexer mode. A state is the offset of its row in `trans`; `trans[row + class]` is\n" ++
    "/// the offset of the next row, 0 for dead. Accepting states are the rows at or above\n" ++
    "/// `accept_from`, and `accept[row]` is their rule plus one (docs/RUST_PARSER.md, D16).\n" ++
    "struct Mode {\n    class: &'static [u8; 256],\n    trans: &'static [" ++ transTy ++ "],\n" ++
    "    accept: &'static [" ++ acceptTy ++ "],\n    start: usize,\n    accept_from: usize,\n}",
    String.intercalate "\n\n" tables.toList,
    s!"static MODES: [Mode; {spec.modes.size}] = [\n" ++ "\n".intercalate modeRecs.toList ++ "\n];",
    "/// What the lexer could not do at the error position.\n" ++
    "#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n" ++
    "pub enum LexErrorReason {\n    /// No rule matches.\n    NoMatch,\n" ++
    "    /// A rule matches, but its value does not fit the Rust type (a numeral beyond `u64`).\n" ++
    "    Unrepresentable,\n    /// End of input inside a nested mode.\n    EndInMode,\n}\n\n" ++
    "#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n" ++
    "pub struct LexError {\n" ++
    "    /// Character offset, as in Lean's `LexError.pos`.\n    pub pos: usize,\n" ++
    "    /// Byte offset.\n    pub byte_pos: usize,\n" ++
    "    /// The offending character; none at end of input.\n    pub ch: Option<char>,\n" ++
    "    pub reason: LexErrorReason,\n}",
    "fn lex_error(src: &str, byte_pos: usize, reason: LexErrorReason) -> LexError {\n" ++
    "    LexError {\n        pos: src[..byte_pos].chars().count(),\n        byte_pos,\n" ++
    "        ch: src[byte_pos..].chars().next(),\n        reason,\n    }\n}",
    String.intercalate "\n" [
      "/// The longest match from `pos`: the accepting rule plus one (0 for none) and its end.",
      "#[inline(always)]",
      "fn scan(mode: &Mode, src: &[u8], pos: usize) -> (usize, usize) {",
      "    let mut row = mode.start;",
      "    let mut i = pos;",
      "    let mut best = 0usize;",
      "    let mut end = pos;",
      "    loop {",
      "        if row >= mode.accept_from {",
      "            best = row;",
      "            end = i;",
      "        }",
      "        if i >= src.len() {",
      "            break;",
      "        }",
      "        let next = mode.trans[row + mode.class[src[i] as usize] as usize] as usize;",
      "        if next == 0 {",
      "            break;",
      "        }",
      "        i += 1;",
      "        if next == row {",
      "            // A self-loop (a run of identifier characters, of spaces, …): the loads of",
      "            // the following bytes do not depend on each other, so scan the run apart.",
      "            while i < src.len()",
      "                && mode.trans[row + mode.class[src[i] as usize] as usize] as usize == row",
      "            {",
      "                i += 1;",
      "            }",
      "        } else {",
      "            row = next;",
      "        }",
      "    }",
      "    (mode.accept[best] as usize, end)",
      "}" ],
    body ]

end Emit.Rust
