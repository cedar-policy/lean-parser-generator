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
The Rust parser with semantic actions (docs/RUST_PARSER.md, "Rust actions").

A `.lig` file may give, next to each Lean action, a Rust one:

    expr :: Expr !!rust{ast::Expr}
      | e=expr PLUS t=term { Expr.add e t } !!rust{ ast::Expr::Add(Box::new(e), Box::new(t)) }

The generator does not look at the Rust text. It pastes the body of each action into the
reduction of its production, with the binders as Rust locals, and uses the Rust type of
each rule only to name the stack its values live on. If the Rust does not compile, the user
fixes it. The Lean action and the Rust action are written separately; the correspondence
between the two parsers is stated on the parse tree (the trace that `parse` returns), not
on the values.

The driver keeps one `Vec` per distinct value type, so a value is moved only when it is
pushed, popped, or used by an action. The production being reduced knows statically which
stacks to pop.
-/
public import LeanParserGenerator.Emit.Rust.Lexer


@[expose] public section

namespace Emit.Rust

open Frontend

/-- Names that cannot be used as Rust identifiers without `r#`. -/
def rustKeywordList : List String :=
  ["as", "break", "const", "continue", "else", "enum", "extern", "false", "fn", "for", "if",
   "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
   "static", "struct", "trait", "true", "type", "unsafe", "use", "where", "while", "async",
   "await", "dyn", "abstract", "become", "box", "do", "final", "macro", "override", "priv",
   "typeof", "unsized", "virtual", "yield", "try"]

/-- A binder as the Rust local the user's action refers to. -/
def rustLocal (b : String) : String :=
  if rustKeywordList.contains b then "r#" ++ b else b

/-- Does any alternative or rule of `s` carry Rust text? -/
def hasRustActions (s : Surface) : Bool :=
  s.rules.any fun r => r.rustTy.isSome || r.alts.any (·.rustAction.isSome)

/-- Everything `renderValueParser` needs. -/
structure ValuePlan where
  /-- Distinct value types (Rust spelling); position 0 is `()`. -/
  variants : Array String
  /-- The `match` arm of each production, in production order. -/
  arms : Array String
  /-- The Rust type of the start symbol. -/
  startTy : String

def variantIdx (vs : Array String) (t : String) : Nat :=
  (vs.findIdx? (· == t)).getD 0

/-- Check that the Rust text is complete and build the arms. -/
def planValues (s : Surface) : Except String ValuePlan := do
  if s.lexer.isNone && s.tokens.any (·.hasVal) then
    throw "Rust actions need the token payloads, which come from a `%lexer` block"
  -- Every rule needs a Rust type and every alternative a Rust action.
  let mut missing : Array String := #[]
  for r in s.rules do
    if r.rustTy.isNone then missing := missing.push s!"rule `{r.lhs}` has no `!!rust\{type}`"
    for h : i in [0:r.alts.size] do
      if r.alts[i].rustAction.isNone then
        missing := missing.push s!"alternative {i + 1} of rule `{r.lhs}` has no `!!rust\{…}` action"
  unless missing.isEmpty do
    throw ("Rust actions must be given for every rule and alternative (rules and alternatives\n" ++
      "generated from macros such as `list(X)` cannot have any):\n  " ++ "\n  ".intercalate missing.toList)
  -- The type of each symbol's value.
  let ntTy (nt : String) : Option String :=
    (s.rules.find? (·.lhs == nt)).bind (·.rustTy)
  let symTy (sym : String) : Except String String :=
    match s.tokens.find? (·.name == sym) with
    | some t => if t.hasVal then rustTyOf (Ty.parse t.ty) else .ok "()"
    | none =>
      match ntTy sym with
      | some t => .ok t.trimAscii.toString
      | none => .error s!"symbol `{sym}` is neither a token nor a nonterminal"
  let mut variants : Array String := #["()"]
  for t in s.tokens do
    let ty ← symTy t.name
    unless variants.contains ty do variants := variants.push ty
  for nt in s.ntNames do
    let ty ← symTy nt
    unless variants.contains ty do variants := variants.push ty
  -- Arms.
  let mut arms : Array String := #[]
  let mut prodIdx := 0
  for r in s.rules do
    let lhsVariant := variantIdx variants (← symTy r.lhs)
    for h : ai in [0:r.alts.size] do
      let alt := r.alts[ai]
      let body := alt.rustAction.getD ""
      let n := alt.elems.size
      let mut lines : Array String := #[]
      -- Pop the RHS values, last symbol first, each from the stack of its type.
      for j in [0:n] do
        let i := n - 1 - j
        let el := alt.elems[i]!
        let k := variantIdx variants (← symTy el.sym)
        match el.binder with
        | some b =>
          lines := lines.push s!"            let {rustLocal b}_span = Span \{ start: __stack[__base + {i}].start, end: __stack[__base + {i}].end };"
          if k == 0 then lines := lines.push s!"            let {rustLocal b} = ();"
          else lines := lines.push s!"            let {rustLocal b} = __s{k}.pop().unwrap();"
        | none =>
          if k != 0 then lines := lines.push s!"            __s{k}.pop();"
      -- `{ x }` for the only symbol, with the same type as the rule: the value is already on
      -- the right stack, so the reduction has nothing to do. (Chains of such unit productions
      -- are common in layered expression grammars.)
      let firstVariant ← match alt.elems[0]? with
        | some el => pure (variantIdx variants (← symTy el.sym))
        | none => pure 0
      let isIdent : Bool :=
        match alt.elems[0]?, n with
        | some el, 1 => el.binder.isSome && body.trimAscii.toString == el.binder.getD "" &&
            lhsVariant != 0 && firstVariant == lhsVariant
        | _, _ => false
      let pushVal := cond (lhsVariant == 0)
        s!"            let _: () = \{\n{body}\n            };"
        s!"            __s{lhsVariant}.push(\{\n{body}\n            });"
      let push := cond isIdent "            // identity: the value stays where it is" pushVal
      arms := arms.push (String.intercalate "\n" (
        [s!"        {prodIdx} => \{", s!"            // {r.lhs}, alternative {ai + 1}"] ++
        (cond isIdent [] lines.toList) ++ [push, "        }"]))
      prodIdx := prodIdx + 1
  let start ← symTy s.start
  return { variants, arms, startTy := start }

/-- The Rust text of the value stacks and of `parse_values`. `tokLt` is the lifetime
    argument of `Tok` (`"<'a>"` or `""`). -/
def renderValueParser (s : Surface) (plan : ValuePlan) (tokName tokLt : String) : Except String String := do
  let lt := if tokLt.isEmpty && !(plan.variants.any (·.contains '\'')) then "" else "<'a>"
  let typed := plan.variants.toList.zipIdx.filter (·.2 != 0)
  let fields := typed.map fun (t, i) => s!"    pub v{i}: Vec<{t}>,"
  let destructure := ", ".intercalate (typed.map fun (_, i) => s!"v{i}: __s{i}")
  let clears := "\n".intercalate (typed.map fun (_, i) => s!"        self.v{i}.clear();")
  -- A token's payload goes on the stack of its type when the token is shifted.
  let tokArms := s.tokens.toList.filterMap fun t =>
    if t.hasVal then
      match rustTyOf (Ty.parse t.ty) with
      | .ok ty =>
        let k := variantIdx plan.variants ty
        if k == 0 then none else some s!"        Tok::{t.name}(v) => s.v{k}.push(*v),"
      | .error _ => none
    else none
  let startK := variantIdx plan.variants plan.startTy
  let augTake := if startK == 0 then "()" else s!"__s{startK}.pop().unwrap()"
  let body := String.intercalate "\n" [
    "/// A byte range of the source: the extent of a symbol, as `x_span` in an action.",
    "#[derive(Clone, Copy, Debug, PartialEq, Eq)]",
    "pub struct Span {",
    "    pub start: u32,",
    "    pub end: u32,",
    "}",
    "",
    "/// A parse stack entry. The value of its symbol is on the stack of its type in `Stacks`.",
    "#[derive(Clone, Copy, Debug)]",
    "pub struct ValueEntry {",
    "    pub state: u16,",
    "    pub start: u32,",
    "    pub end: u32,",
    "}",
    "",
    "/// The buffers of `parse_values`: the entry stack and one value stack per type.",
    "/// Reuse one across calls to avoid reallocating.",
    "#[derive(Default)]",
    s!"pub struct Stacks{lt} \{",
    "    pub entries: Vec<ValueEntry>,",
    "\n".intercalate fields,
    "}",
    "",
    s!"impl{lt} Stacks{lt} \{",
    "    pub fn new() -> Self {",
    "        Self::default()",
    "    }",
    "",
    "    fn clear(&mut self) {",
    "        self.entries.clear();",
    clears,
    "    }",
    "}",
    "",
    "/// Push the value a shifted token carries onto the stack of its type.",
    s!"#[inline(always)]\nfn push_payload{lt}(s: &mut Stacks{lt}, t: &{tokName}{tokLt}) \{",
    "    match t {",
    "\n".intercalate tokArms,
    "        #[allow(unreachable_patterns)]",
    "        _ => {}",
    "    }",
    "}",
    "",
    "/// Parse `tokens` and return the value of the start symbol, computed by the Rust actions",
    "/// of the grammar. `stacks` is cleared first.",
    "#[allow(unused_variables, unused_mut, unused_parens, non_snake_case, clippy::all)]",
    s!"pub fn parse_values{lt}(",
    s!"    tokens: &[Spanned<{tokName}{tokLt}>],",
    s!"    stacks: &mut Stacks{lt},",
    s!") -> Result<{plan.startTy}, ParseError> \{",
    "    stacks.clear();",
    "    stacks.entries.push(ValueEntry { state: 0, start: 0, end: 0 });",
    "    let mut ti = 0usize;",
    "    let mut prev_end = 0u32;",
    "    loop {",
    "        let state = stacks.entries[stacks.entries.len() - 1].state as usize;",
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
    "                if ti < tokens.len() {",
    "                    push_payload(stacks, &tokens[ti].tok);",
    "                }",
    "                stacks.entries.push(ValueEntry { state: (a >> 1) as u16, start: tstart, end: tend });",
    "                prev_end = tend;",
    "                ti += 1;",
    "                continue;",
    "            }",
    "            (a >> 1) - 1",
    "        };",
    "        let __n = RHS_LEN[prod] as usize;",
    "        if __n >= stacks.entries.len() {",
    "            return Err(ParseError { token: ti, state, term: u16::MAX });",
    "        }",
    "        let __base = stacks.entries.len() - __n;",
    "        let __start = if __n > 0 { stacks.entries[__base].start } else { prev_end };",
    s!"        let Stacks \{ entries: __stack, {destructure} } = &mut *stacks;",
    "        match prod {",
    "            AUG_PROD => {",
    s!"                return Ok({augTake});",
    "            }",
    "\n".intercalate plan.arms.toList,
    "            _ => unreachable!(),",
    "        }",
    "        __stack.truncate(__base);",
    "        let __top = __stack[__base - 1].state as usize;",
    "        let __g = GOTO[__top * NUM_NONTERMINALS + LHS[prod] as usize] as usize;",
    "        if __g == NONE {",
    "            return Err(ParseError { token: ti, state, term: u16::MAX });",
    "        }",
    "        __stack.push(ValueEntry { state: __g as u16, start: __start, end: prev_end });",
    "    }",
    "}" ]
  return body ++ "\n"

end Emit.Rust
