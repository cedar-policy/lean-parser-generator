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
Untrusted parser-backend source emitter.

A parsed `.lig` becomes a self-contained module targeting `Runtime.Exec`:
Pager tables, a generated universal semantic-value sum `V`, token decoding,
wrapped semantic actions, and a runnable `parse` entry. Generated modules are
committed and compiled as ordinary Lean source.
-/
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Frontend.Macros
public import LeanParserGenerator.Construct.Tables
public import LeanParserGenerator.Emit.Builder
public import LeanParserGenerator.Emit.Quote


@[expose] public section

namespace Emit

open Frontend Construct IR
open Emit.Builder
open Lean Emit.Quote

/-! ### Surface → IR grammar -/

/-- Build the untrusted `IR.Grammar` from a parsed surface: terminals are the
    `%token`s in declaration order, nonterminals the rule heads in first-
    appearance order, productions the alternatives in source order. -/
def irOfSurface (s : Surface) : Except String IR.Grammar := do
  let numT := s.tokens.size
  let ntNames := s.ntNames
  let numN := ntNames.size
  let some startI := s.ntIdx s.start
    | throw s!"start symbol `{s.start}` is not a rule head"
  let mut prods : Array IR.Prod := #[]
  for r in s.rules do
    let some lhsI := s.ntIdx r.lhs | throw s!"unknown nonterminal `{r.lhs}`"
    for alt in r.alts do
      let mut syms : Array IR.Sym := #[]
      for e in alt.elems do
        match s.termIdx e.sym with
        | some ti => syms := syms.push (.term ti)
        | none =>
          match s.ntIdx e.sym with
          | some ni => syms := syms.push (.nonterm ni)
          | none => throw s!"symbol `{e.sym}` in rule `{r.lhs}` is neither a declared token nor a nonterminal"
      prods := prods.push { lhs := lhsI, rhs := syms.toList }
  return {
    numTerminals := numT
    numNonterminals := numN
    prods := prods
    start := startI
    termNames := s.tokens.map (·.name)
    nontermNames := ntNames
  }

/-! ### String helpers

    Literal/join rendering shared with the verified emitter lives in `Emit.Builder`. -/

/-! ### Value-type synthesis

The executable engine stores one value type `V` on its stack. We synthesize `V`
as a sum with one constructor per distinct semantic Lean type occurring among the
nonterminals and value-carrying terminals, including `unit : Unit → V` for
valueless symbols. `TyEnv` maps a type string to its constructor name. -/

/-- The synthesized value type: the distinct semantic types (in first-appearance
    order) and a lookup from a type string to its constructor name. -/
structure TyEnv where
  /-- Distinct non-`Unit` semantic type strings, in first-appearance order. -/
  types : Array String
  deriving Inhabited

namespace TyEnv

/-- Constructor name for a semantic type; `Unit` uses `unit`. -/
def ctorFor (e : TyEnv) (ty : String) : String :=
  if ty == "Unit" then "unit"
  else match e.types.findIdx? (· == ty) with
    | some i => s!"v{i}"
    | none => "unit"  -- unreachable for well-formed input

end TyEnv

/-- Collect the distinct semantic types from a surface (nonterminal `%type`s and
    value-carrying `%token`s). `"Unit"` uses the dedicated `unit` constructor. -/
def collectTypes (s : Surface) : TyEnv := Id.run do
  let mut acc : Array String := #[]
  for r in s.rules do
    if r.ty != "Unit" && !acc.contains r.ty then acc := acc.push r.ty
  for t in s.tokens do
    if t.hasVal && t.ty != "Unit" && !acc.contains t.ty then acc := acc.push t.ty
  return { types := acc }

/-- The semantic type string of a grammar symbol name (terminal or nonterminal),
    for pattern/wrapping purposes. -/
def symTy (s : Surface) (name : String) : String :=
  match s.tokens.find? (·.name == name) with
  | some t => t.ty
  | none =>
    match s.rules.find? (·.lhs == name) with
    | some r => r.ty
    | none => "Unit"

/-! ### Emission -/

/-- Emit the `V` inductive definition (`inductive V | unit : Unit → V | vN : ty → V …`).
    The semantic type of each constructor is a verbatim leaf. -/
def emitValueType (e : TyEnv) : EmitM (TSyntax `command) := do
  let vId := mkIdent `V
  let unitId := mkIdent `unit
  let unitTy := mkIdent `Unit
  let mut ctors : Array (TSyntax `Lean.Parser.Command.ctor) :=
    #[← `(Lean.Parser.Command.ctor| | $unitId:ident : $unitTy → $vId)]
  for (ty, i) in e.types.zipIdx do
    let cn := mkIdent (Name.mkSimple s!"v{i}")
    let tyLeaf ← freshLeaf ty
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $cn:ident : $tyLeaf → $vId))
  `(command| inductive $vId where $ctors* deriving $(mkIdent `Inhabited):ident)

/-- Emit the token decoders `termOf : <Tok> → Nat`, `valOf : <Tok> → V`, and
    `decode : Positioned <Tok> → Nat × VP`, which pairs them with the token's span.
    Each `%token` name is a constructor of the user's token type; value-carrying
    ones bind one argument. The engine calls `termOf` and `valOf` separately, so
    that reading a lookahead allocates nothing.

    The `%eof` token maps to the **augmented** end terminal `$` at index
    `augEofIdx` (= the un-augmented terminal count), NOT its declaration index —
    the LR tables reduce/accept on `$`. Grammars therefore must not reference the
    eof token inside a production; the input list ends with it and it acts as `$`.
    Other tokens map to their declaration indices. -/
def emitDecoder (s : Surface) (e : TyEnv) (augEofIdx : Nat) :
    EmitM (Array (TSyntax `command)) := do
  let termId := mkIdent `termOf
  let valId := mkIdent `valOf
  let decodeId := mkIdent `decode
  let natId := mkIdent `Nat
  let vpId := mkIdent `VP
  let vId := mkIdent `V
  let tokTyLeaf ← freshLeaf s.tokenType
  let mut termArms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  let mut valArms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  for (t, i) in s.tokens.zipIdx do
    let idx := if t.name == s.eof then augEofIdx else i
    let idxLit := Syntax.mkNumLit (toString idx)
    let ctor := mkIdent (Name.mkSimple t.name)
    if t.hasVal then
      let valCtor := mkIdent (Name.mkSimple (e.ctorFor t.ty))
      let x := mkIdent `x
      termArms := termArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident _ => $idxLit))
      valArms := valArms.push (← `(Lean.Parser.Term.matchAltExpr|
        | .$ctor:ident $x => .$valCtor:ident $x))
    else
      termArms := termArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident => $idxLit))
      valArms := valArms.push (← `(Lean.Parser.Term.matchAltExpr|
        | .$ctor:ident => .$(mkIdent `unit):ident ()))
  let posTy ← `($(mkIdent `Runtime.Positioned) $tokTyLeaf)
  let termCmd ← `(command| def $termId : $tokTyLeaf → $natId $termArms:matchAlt*)
  let valCmd ← `(command| def $valId : $tokTyLeaf → $vId $valArms:matchAlt*)
  let decodeCmd ← `(command| def $decodeId : $posTy → $natId × $vpId :=
    $(mkIdent `Runtime.Exec.decodeWith) $termId $valId)
  return #[termCmd, valCmd, decodeCmd]

/-- Emit the semantic-action dispatcher `sem : Nat → List V → V`.

    Productions are numbered in surface order; the final production (index
    `augProd`) is the augmented `S' → S $` and returns the start value while
    ignoring the end marker.
    For each original production we emit an arm that pattern-matches the popped
    argument list (left-to-right RHS order), unwrapping bound elements to their
    typed values, then wraps the user's verbatim action body in the LHS type's
    constructor. -/
def emitSem (s : Surface) (e : TyEnv) (augProd : Nat) : EmitM (TSyntax `command) := do
  let semId := mkIdent `sem
  let natId := mkIdent `Nat
  let vpId := mkIdent `VP
  let listVP ← `($(mkIdent `List) $vpId)
  -- Span name for element `i`: the user's `<binder>_span` when bound, else a fresh
  -- `__s{i}` so the RHS span fold can still reference it.
  let spanName := fun (elem : Frontend.Elem) (i : Nat) =>
    match elem.binder with
    | some nm => s!"{nm}_span"
    | none => s!"__s{i}"
  -- The production's span: merge(first symbol span, last symbol span); a single
  -- symbol is its own span; an empty RHS gets the dummy span (Menhir uses the
  -- lookahead point for empties; the value dispatcher has no lookahead, so dummy).
  let foldSpan := fun (elems : Array Frontend.Elem) =>
    if elems.size == 0 then "Runtime.Span.dummy"
    else if elems.size == 1 then spanName elems[0]! 0
    else s!"Runtime.Span.merge {spanName elems[0]! 0} {spanName elems[elems.size-1]! (elems.size-1)}"
  let mut arms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  let mut p := 0
  for r in s.rules do
    let lhsCtor := e.ctorFor r.ty
    for alt in r.alts do
      -- Left-to-right RHS cell patterns: `(<span>, .<ctor> <binder>)` when bound,
      -- `(<span>, _)` when unbound (span still named for the fold).
      let cells := alt.elems.zipIdx.map (fun (elem, i) =>
        match elem.binder with
        | some nm => s!"({spanName elem i}, .{e.ctorFor (symTy s elem.sym)} {nm})"
        | none => s!"({spanName elem i}, _)")
      let pat := "[" ++ joinWith ", " cells.toList ++ "]"
      let body := s!"({foldSpan alt.elems}, .{lhsCtor} ({alt.action}))"
      let pLit := Syntax.mkNumLit (toString p)
      let patLeaf ← freshLeaf pat
      let bodyLeaf ← freshLeaf body
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $pLit, $patLeaf => $bodyLeaf))
      p := p + 1
  -- Augmented `S' → S $`: return the start value cell (with its span), drop `$`.
  let augLit := Syntax.mkNumLit (toString augProd)
  let augLeaf ← freshLeaf "[x, _]"
  let augBody ← freshLeaf "x"
  arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $augLit, $augLeaf => $augBody))
  let fallLeaf ← freshLeaf "(Runtime.Span.dummy, .unit ())"
  arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => $fallLeaf))
  `(command| def $semId : $natId → $listVP → $vpId $arms:matchAlt*)

/-- The `Stk` cell constructor for a `V` constructor: `cUnit` for `unit`, `c<i>` for
    `v<i>`. -/
def cellFor (ctor : String) : String :=
  if ctor == "unit" then "cUnit" else "c" ++ String.ofList (ctor.toList.drop 1)

/-- Emit the generated parser stack `Stk` and its `Runtime.Exec.StackOps`.

    `Stk` has one cell constructor per semantic type: `cUnit` for `Unit` (no value
    field) and `c<i>` for the type of `V.v<i>`. A cell holds the state, the span
    offsets, and the unwrapped value, so a stack cell is one allocation instead of a
    cons, two pairs, a `Span` and a `V` box. `Stk.toList` maps it to the
    specification stack `List (Nat × VP)`. Returns `(defs, lawful)`: `lawful`
    mentions `flat` and goes after it. -/
def emitStack (s : Surface) (e : TyEnv) : String × String :=
  let tyCtors : List (String × String × String) :=
    e.types.toList.zipIdx.map (fun (ty, i) => (s!"c{i}", s!"v{i}", ty))
  let ctorDecls := tyCtors.map (fun (c, _, ty) =>
    s!"  | {c} (st : Nat) (b e : String.Pos.Raw) (x : {ty}) (tl : Stk)")
  let toListArms := tyCtors.map (fun (c, v, _) =>
    s!"  | .{c} st b e x tl => (st, (⟨b, e⟩, .{v} x)) :: tl.toList")
  let ofListArms := tyCtors.map (fun (c, v, _) =>
    s!"  | (st, (sp, .{v} x)) :: tl => .{c} st sp.startPos sp.endPos x (Stk.ofList tl)")
  let topArms := tyCtors.map (fun (c, _, _) => s!"  | .{c} st _ _ _ _ => st")
  let acceptArms := tyCtors.map (fun (c, v, _) => s!"  | .{c} _ b e x _ => .ok (⟨b, e⟩, .{v} x)")
  let pushArms := s.tokens.toList.map (fun t =>
    if t.hasVal && e.ctorFor t.ty != "unit" then
      s!"  | ⟨.{t.name} x, sp⟩ => .{cellFor (e.ctorFor t.ty)} st sp.startPos sp.endPos x tl"
    else if t.hasVal then
      s!"  | ⟨.{t.name} _, sp⟩ => .cUnit st sp.startPos sp.endPos tl"
    else
      s!"  | ⟨.{t.name}, sp⟩ => .cUnit st sp.startPos sp.endPos tl")
  let defs := paras [
    lines ([
      "/-- The parser stack: one cell constructor per semantic type (`cUnit` for `Unit`),",
      "    each holding the state, the span offsets, and the unwrapped value. -/",
      "inductive Stk where",
      "  | nil",
      "  | fail (orig : Stk)",
      "  | cUnit (st : Nat) (b e : String.Pos.Raw) (tl : Stk)"] ++ ctorDecls),
    lines ([
      "/-- The specification stack this stack represents. -/",
      "def Stk.toList : Stk → Runtime.Exec.Stack VP",
      "  | .nil => []",
      "  | .fail _ => []",
      "  | .cUnit st b e tl => (st, (⟨b, e⟩, .unit ())) :: tl.toList"] ++ toListArms),
    lines ([
      "def Stk.ofList : Runtime.Exec.Stack VP → Stk",
      "  | [] => .nil",
      "  | (st, (sp, .unit _)) :: tl => .cUnit st sp.startPos sp.endPos (Stk.ofList tl)"] ++
      ofListArms),
    lines ([
      "theorem Stk.toList_ofList (l : Runtime.Exec.Stack VP) : (Stk.ofList l).toList = l := by",
      "  induction l with",
      "  | nil => rfl",
      "  | cons hd tl ih =>",
      "    obtain ⟨st, sp, v⟩ := hd",
      "    cases v <;> (simp only [Stk.ofList, Stk.toList, ih]; try rfl)"]),
    lines ([
      "@[inline] def Stk.top (start : Nat) : Stk → Nat",
      "  | .nil => start",
      "  | .fail _ => start",
      "  | .cUnit st _ _ _ => st"] ++ topArms),
    lines ([
      "@[inline] def Stk.isFail : Stk → Bool",
      "  | .fail _ => true",
      "  | _ => false"]),
    lines ([
      "@[inline] def Stk.unfail : Stk → Stk",
      "  | .fail s => s",
      "  | s => s"]),
    lines ([
      "def Stk.accept : Stk → Runtime.Exec.Result VP",
      "  | .nil => .err \"accept on empty stack\"",
      "  | .fail _ => .err \"accept on empty stack\"",
      "  | .cUnit _ b e _ => .ok (⟨b, e⟩, .unit ())"] ++ acceptArms),
    lines ([
      s!"@[inline] def Stk.pushTok (st : Nat) (tok : Runtime.Positioned {s.tokenType}) (tl : Stk) : Stk :=",
      "  match tok with"] ++ pushArms),
    lines ([
      "instance stackOps : Runtime.Exec.StackOps V " ++ s.tokenType ++ " Stk where",
      "  nil := .nil",
      "  fail := Stk.fail",
      "  isFail := Stk.isFail",
      "  unfail := Stk.unfail",
      "  top := Stk.top",
      "  pushTok := Stk.pushTok",
      s!"  pushEof := fun st tl => Stk.pushTok st ⟨.{s.eof}, Runtime.Span.dummy⟩ tl",
      "  accept := Stk.accept",
      "  toList := Stk.toList",
      "  ofList := Stk.ofList"])]
  let lawful := lines [
    "theorem stackLawful : stackOps.Lawful valOf flat.eof.2 where",
    "  toList_nil := rfl",
    "  isFail_fail := fun _ => rfl",
    "  unfail_fail := fun _ => rfl",
    "  top_eq := by intro start s; cases s <;> rfl",
    "  pushTok_eq := by intro st tok s; obtain ⟨v, sp⟩ := tok; cases v <;> rfl",
    "  pushEof_eq := by intro st s; rfl",
    "  accept_eq := by intro s; cases s <;> rfl",
    "  toList_ofList := Stk.toList_ofList"]
  (defs, lawful)

/-- Emit the fused reduces: one `fuse<p> : Stk V → Stk V` per production (as
    `Syntax`), and as raw text the dispatcher `fuse : Nat → Stk V → Stk V`, one
    correctness theorem per production, and their combination `fuseOK`.

    `fuse<p> stk` reduces by production `p` in one call. It matches the top RHS cells
    of the stack (the last RHS symbol is on top), binds and unwraps the operands,
    builds the semantic value, and pushes the goto cell with `pushGoto`, all without
    an intermediate `List` or `Option`. It returns `Stk.nil` when the stack shape
    does not match or the goto entry is missing; the augmented production uses
    `fuseNone`, which always returns `Stk.nil`. The engine then reduces through
    `reduceInline` (`Runtime/ExecFast.lean`).

    `fuse` reads the per-production function from an array. A `Nat`-literal `match`
    with one arm per production compiles to a chain of comparisons, one per earlier
    arm, so the array read is cheaper at run time. It also keeps the proofs per
    production: each `fuseOK<p>` unfolds only `fuse<p>`, and Lean elaborates them in
    parallel. The fresh tail binder `__tail` cannot collide with a grammar binder.

    Returns `(defs, dispatch, proofs)`: `dispatch` goes before `flat`, `proofs`
    after it. -/
def emitFuse (s : Surface) (e : TyEnv) (g' : IR.Grammar) (startState augProd : Nat) :
    EmitM (Array (TSyntax `command) × String × String) := do
  -- Span name for element `i` (original left-to-right index), matching `emitSem`.
  let spanName := fun (elem : Frontend.Elem) (i : Nat) =>
    match elem.binder with
    | some nm => s!"{nm}_span"
    | none => s!"__s{i}"
  -- A cell carries its span as two offsets `<span>__b`/`<span>__e`. The production
  -- span starts where the first symbol starts and ends where the last one ends
  -- (`Span.merge`); an empty RHS gets the dummy span `0..0`, as in `emitSem`.
  let foldSpan := fun (elems : Array Frontend.Elem) =>
    if elems.size == 0 then "⟨0⟩ ⟨0⟩"
    else s!"{spanName elems[0]! 0}__b {spanName elems[elems.size-1]! (elems.size-1)}__e"
  let numN := g'.numNonterminals
  let mut cmds : Array (TSyntax `command) := #[]
  let mut proofs : Array String := #[]
  let mut names : Array String := #[]
  let mut oks : Array String := #[]
  let mut p := 0
  for r in s.rules do
    let lhsCtor := e.ctorFor r.ty
    for alt in r.alts do
      let lhs := (g'.prods.getD p default).lhs
      -- Left-to-right: the first RHS element is the innermost cell, the last the top.
      -- Each cell is matched with the constructor of its symbol's semantic type.
      let mut pat := "__tail"
      -- An action may name `<binder>_span`; rebuild it from the offsets. The
      -- compiler drops the `let` when the action does not use it.
      let mut lets := ""
      for (elem, i) in alt.elems.zipIdx do
        let sn := spanName elem i
        let ctor := e.ctorFor (symTy s elem.sym)
        let cell := cellFor ctor
        match elem.binder with
        | some nm =>
          lets := lets ++ s!"let {sn} : Runtime.Span := ⟨{sn}__b, {sn}__e⟩; "
          if ctor == "unit" then
            pat := s!".{cell} _ {sn}__b {sn}__e ({pat})"
            lets := lets ++ s!"let {nm} : Unit := (); "
          else
            pat := s!".{cell} _ {sn}__b {sn}__e {nm} ({pat})"
        | none =>
          if ctor == "unit" then
            pat := s!".{cell} _ {sn}__b {sn}__e ({pat})"
          else
            pat := s!".{cell} _ {sn}__b {sn}__e _ ({pat})"
      let lhsCell := cellFor lhsCtor
      let mk :=
        if lhsCtor == "unit" then s!"(fun __st => .cUnit __st {foldSpan alt.elems} __tail)"
        else s!"(fun __st => .{lhsCell} __st {foldSpan alt.elems} ({alt.action}) __tail)"
      let failv := if alt.elems.isEmpty then "(fun _ => .fail __tail)" else "(fun _ => .fail stk)"
      let push :=
        lets ++
        s!"Runtime.Exec.pushGotoWith gotoData {numN} {lhs} (Stk.top {startState} __tail) " ++
        s!"{mk} {failv}"
      let body :=
        if alt.elems.isEmpty then
          s!"fun __tail => {push}"
        else
          s!"fun stk => match stk with\n    | {pat} => {push}\n    | _ => .fail stk"
      let name := s!"fuse{p}"
      let sigLeaf ← freshLeaf "Stk → Stk"
      let bodyLeaf ← freshLeaf body
      cmds := cmds.push (← `(command| def $(mkIdent (Name.mkSimple name)) : $sigLeaf := $bodyLeaf))
      names := names.push name
      oks := oks.push s!"fuseOK{p}"
      -- `apply` unifies the lemma's conclusion with the goal first, which fixes the
      -- stack, the cell, and `mk`; the remaining goals are closed by `rfl` (`hred`) or
      -- `fun _ => rfl` (`hmk`, `hmkf`). `dsimp only` removes the action's `let`s.
      let close := [
        s!"    apply Runtime.Exec.fuseOKAt_of_pop stackLawful flat {p}",
        "    all_goals first | exact fun _ => rfl | rfl"]
      let proof :=
        if alt.elems.isEmpty then
          lines ([
            s!"theorem fuseOK{p} : Runtime.Exec.FuseOKAt stackOps flat {p} fuse{p} := by",
            "  intro stk",
            s!"  unfold fuse{p}",
            "  · try dsimp only"] ++ close)
        else
          lines ([
            s!"theorem fuseOK{p} : Runtime.Exec.FuseOKAt stackOps flat {p} fuse{p} := by",
            "  intro stk",
            s!"  unfold fuse{p}",
            "  split",
            "  · try dsimp only"] ++ close ++ [
            "  · exact ⟨fun _ => rfl, fun h => by cases h⟩"])
      proofs := proofs.push proof
      p := p + 1
  -- A balanced tree of `fuseIf` over the leaves `fuseLeaf p fuse<p>`; the production
  -- index is below `names.size` for every real production. The augmented production
  -- and out-of-range indices reach the empty tree and decline.
  let rec tree (lo hi : Nat) (fuel : Nat) : String × String :=
    match fuel with
    | 0 => ("(Runtime.Exec.fuseLeaf stackOps 0 (Runtime.Exec.fuseNone stackOps))", "")
    | fuel + 1 =>
      if hi ≤ lo then
        (s!"(fun _ => Runtime.Exec.fuseNone stackOps)", "fun _ => Runtime.Exec.fuseOKAt_none stackLawful flat _")
      else if hi = lo + 1 then
        (s!"(Runtime.Exec.fuseLeaf stackOps {lo} fuse{lo})",
         s!"(Runtime.Exec.fuseOK_leaf stackLawful fuseOK{lo})")
      else
        let mid := (lo + hi) / 2
        let (a, pa) := tree lo mid fuel
        let (b, pb) := tree mid hi fuel
        (s!"(Runtime.Exec.fuseIf {mid} {a} {b})", s!"(Runtime.Exec.fuseOK_if {pa} {pb})")
  let (treeTerm, treeProof) := tree 0 names.size (names.size + 1)
  let _ := augProd
  let dispatch := lines [
    "def fuse : Nat → Stk → Stk :=",
    "  " ++ treeTerm ]
  let combine := lines [
    "theorem fuseOK : Runtime.Exec.FuseOK stackOps flat fuse :=",
    "  " ++ treeProof ]
  return (cmds, dispatch, paras (proofs.toList ++ [combine]))

/-- Emit the flat parser tables (action/goto/defRed/lhs/len) for the augmented
    grammar.

    They are **flat `Array` literals** (row-major, indexed `st * width + col`)
    rather than nested `match` functions: a match with thousands of arms blows up
    Lean's elaborator on large grammars (Cedar has ~213 states), whereas an array
    literal elaborates cheaply and indexes in O(1). Returns `(prefix, defs, tail)`:
    a raw `buildDense` prefix (only when compressing, since it precedes the data
    defs that call it), the data-array defs as `Syntax`, and the raw `flat`/`table`
    record tail. -/
def emitTable (g' : IR.Grammar) (tables : Tables) (startState : Nat)
    (eofToken : String) (compressTables : Bool := false) :
    EmitM (String × String × String) := do
  let numStates := tables.numStates
  let numT := g'.numTerminals
  let numN := g'.numNonterminals
  let nP := g'.prods.size
  -- The data arrays are literals of numbers and fixed nullary/unary constructors.
  -- They were previously emitted as `Syntax` and pretty-printed with `ppCommand`,
  -- whose parenthesizer is superlinear on a single array literal with tens of
  -- thousands of elements — the dominant cost of generating a large uncompressed
  -- parser (≈21 s for c99). Rendering the element text directly and laying it out
  -- with a greedy fill reproduces Lean's array-literal formatting exactly (verified
  -- byte-for-byte against the committed fixtures) at `O(total element text)`.
  let actStr (a : Act) : String :=
    match a with
    | .shift j => s!".shift {j}"
    | .reduce p => s!".reduce {p}"
    | .error => ".error"
  let optNatStr (o : Option Nat) : String :=
    match o with
    | none => "none"
    | some n => s!"some {n}"
  -- Greedy width-116 fill of `def name : ty := #[e₀, e₁, …]`, matching the layout
  -- `ppCommand` produces: `#[` opens on a 2-space-indented line, continuation lines
  -- are indented 4 spaces, each line packs as many comma-separated elements as fit
  -- within 116 columns, and the closing `]` follows the last element.
  let width := 116
  let arrDefRaw (name typeStr : String) (elems : Array String) : String := Id.run do
    let header := s!"def {name} : Array {typeStr} :="
    if elems.isEmpty then
      return header ++ "\n  #[]"
    let mut lines : Array String := #[]
    let mut cur := "  #["
    let mut lineHasElem := false
    for h : k in [0:elems.size] do
      let e := elems[k]
      let isLast := k + 1 == elems.size
      let sep := if isLast then "" else ","
      if !lineHasElem then
        cur := cur ++ e ++ sep
        lineHasElem := true
      else
        let candidate := cur ++ " " ++ e ++ sep
        if candidate.length ≤ width then
          cur := candidate
        else
          lines := lines.push cur
          cur := "    " ++ e ++ sep
    cur := cur ++ "]"
    lines := lines.push cur
    return header ++ "\n" ++ "\n".intercalate lines.toList
  let mut actElems : Array String := #[]
  for st in [0:numStates] do
    let row := tables.action.getD st #[]
    for t in [0:numT] do
      actElems := actElems.push (actStr (row.getD t Act.error))
  let mut gotoElems : Array String := #[]
  for st in [0:numStates] do
    let row := tables.goto.getD st #[]
    for n in [0:numN] do
      gotoElems := gotoElems.push (optNatStr (row.getD n none))
  let mut drElems : Array String := #[]
  for st in [0:numStates] do
    drElems := drElems.push (optNatStr (tables.defaultReduce.getD st none))
  let mut lhsElems : Array String := #[]
  let mut lenElems : Array String := #[]
  for p in [0:nP] do
    let prod := g'.prods.getD p default
    lhsElems := lhsElems.push (toString prod.lhs)
    lenElems := lenElems.push (toString prod.rhs.length)
  let optNatTy := "(Option Nat)"
  let natTy := "Nat"
  let tailDefs : Array String := #[
    arrDefRaw "defRedData" optNatTy drElems,
    arrDefRaw "lhsData" natTy lhsElems,
    arrDefRaw "lenData" natTy lenElems ]
  let dataStr : String ←
    if compressTables then
      -- Non-default `(index, value)` pairs; `buildDense` (raw tail) fills the rest.
      let mut actPairs : Array String := #[]
      for st in [0:numStates] do
        let row := tables.action.getD st #[]
        for t in [0:numT] do
          let i := st * numT + t
          match row.getD t Act.error with
          | .error => pure ()
          | a => actPairs := actPairs.push s!"({i}, {actStr a})"
      let mut gotoPairs : Array String := #[]
      for st in [0:numStates] do
        let row := tables.goto.getD st #[]
        for n in [0:numN] do
          let i := st * numN + n
          match row.getD n none with
          | none => pure ()
          | some j => gotoPairs := gotoPairs.push s!"({i}, some {j})"
      let actCellTy := "(Nat × Runtime.Exec.Act)"
      let gotoCellTy := "(Nat × Option Nat)"
      let actSz := actElems.size
      let gotoSz := gotoElems.size
      let defs : Array String := #[
        arrDefRaw "actionCells" actCellTy actPairs,
        s!"def actionData : Array Runtime.Exec.Act :=\n  buildDense {actSz} .error actionCells",
        arrDefRaw "gotoCells" gotoCellTy gotoPairs,
        s!"def gotoData : Array (Option Nat) :=\n  buildDense {gotoSz} none gotoCells" ]
        ++ tailDefs
      pure ("\n\n".intercalate defs.toList)
    else
      let defs : Array String := #[
        arrDefRaw "actionData" "Runtime.Exec.Act" actElems,
        arrDefRaw "gotoData" optNatTy gotoElems ]
        ++ tailDefs
      pure ("\n\n".intercalate defs.toList)
  -- `buildDense` (only when compressing) and the fixed `flat`/`table` record are
  -- generator-authored boilerplate over the `Runtime.Exec` API; kept as raw text.
  let buildDenseDef :=
    "def buildDense {α : Type} (n : Nat) (dflt : α) (cells : Array (Nat × α)) : Array α := Id.run do\n" ++
    "  let mut a : Array α := Array.replicate n dflt\n" ++
    "  for (i, v) in cells do a := a.set! i v\n" ++
    "  return a"
  let tableDef := lines [
    "def flat : Runtime.Exec.FlatTable VP := {",
    s!"  numStates := {numStates}",
    s!"  startState := {startState}",
    s!"  eof := decode ⟨.{eofToken}, Runtime.Span.dummy⟩",
    s!"  actWidth := {numT}",
    s!"  gotoWidth := {numN}",
    "  actionData := actionData",
    "  gotoData := gotoData",
    "  defRedData := defRedData",
    "  lhsData := lhsData",
    "  lenData := lenData",
    "  sem := sem",
    "}",
    "",
    "def table : Runtime.Exec.ExecTable VP := flat.toExecTable" ]
  -- Return: raw prefix (buildDense, when compressing — it must precede the data
  -- defs that call it), the data-array defs as raw text, and the raw flat/table tail.
  let prefixRaw := if compressTables then buildDenseDef else ""
  return (prefixRaw, dataStr, tableDef)

/-- Emit the Menhir-style diagnostics wrappers over `Runtime.Exec` diagnose:
    `terminalName`, `diagnose`, `diagnoseSpanned`, and `errorMessage`. The engine
    runs at `VP := Span × V`, so `diagnoseSpanned` projects each token's span with
    `fun (sp, _) => some sp`, and `errorMessage` renders `line:col` when given the
    source string. `augNumT` is the augmented terminal count (action-table width);
    `eofIdx` is the end-of-input terminal index. -/
def emitDiagnostics (s : Surface) (augNumT eofIdx : Nat) : String :=
  let nameArms := String.intercalate "\n" <|
    (List.range s.tokens.size).map (fun i =>
      s!"  | {i} => \"{(s.tokens[i]!).name}\"") ++
    [s!"  | {eofIdx} => \"end of input\"",
     "  | n => s!\"terminal {n}\""]
  lines [
    "/-- The readable name of a terminal index (EOF is \"end of input\"). -/",
    "def terminalName : Nat → String",
    nameArms,
    "",
    "/-- Diagnose a parse: on rejection, the offending token index and expected set. -/",
    s!"def diagnose (input : List (Runtime.Positioned {s.tokenType})) (logNSteps : Nat := 20) :",
    "    Runtime.Exec.Diagnostic VP :=",
    s!"  Runtime.Exec.diagnose table {augNumT} (input.map decode) logNSteps",
    "",
    "/-- Diagnose, also recovering the offending token's source span for line:col. -/",
    s!"def diagnoseSpanned (input : List (Runtime.Positioned {s.tokenType})) (logNSteps : Nat := 20) :",
    "    Runtime.Exec.Diagnostic VP × Option Runtime.Span :=",
    s!"  Runtime.Exec.diagnoseSpanned table {augNumT} (fun (sp, _) => some sp) (input.map decode) logNSteps",
    "",
    "/-- A human-readable syntax-error message, or `none` when the input parses.",
    "    Pass `source` to render `line:col`; `messages` overrides per-state text. -/",
    s!"def errorMessage (input : List (Runtime.Positioned {s.tokenType})) (source : String := \"\")",
    "    (messages : Nat → Option String := fun _ => none) (logNSteps : Nat := 20) : Option String :=",
    "  match diagnoseSpanned input logNSteps with",
    "  | (.error e, span) => some (e.formatWithSource span source terminalName messages)",
    "  | _ => none" ]

/-- Shared untrusted construction result consumed by both emitters. -/
structure PreparedGrammar where
  source : IR.Grammar
  augmented : IR.Grammar
  augProd : Nat
  collection : Collection
  tables : Tables

/-- Parse-independent grammar preparation: normalize and construct Pager tables once. -/
def prepareGrammar (s : Surface) : Except String PreparedGrammar := do
  let s ← Frontend.Macros.expandMacros s
  let source ← irOfSurface s
  let (augmented, augProd, collection, tables) := Construct.pager source
  return { source, augmented, augProd, collection, tables }

/-- Render the parser backend from shared prepared construction data.

    When `lexerModule` is `some M`, the token type is defined by the generated
    lexer module `M` (the `%lexer` regime), so an `import M` is emitted and the
    shared `%header` is expected not to redeclare the token type. When `none`, the
    token type is hand-written and pulled in by `%header` (the lexerless regime). -/
def generateFrom (s : Surface) (prepared : PreparedGrammar)
    (moduleName : String := "Generated") (lexerModule : Option String := none) :
    IO (Except String String) := do
  let g := prepared.source
  let g' := prepared.augmented
  let augProd := prepared.augProd
  let tables := prepared.tables
  let e := collectTypes s
  let some _startNt := s.ntIdx s.start
    | return .error s!"start `{s.start}` not a rule head"
  let startState := 0
  let startTy := (s.rules.find? (·.lhs == s.start)).map (·.ty) |>.getD "Unit"
  let startCtor := e.ctorFor startTy
  -- C symbol prefix so a compiled/FFI caller can link `run`/`parse` without Lean's
  -- module-name mangling.
  let exportPrefix :=
    String.ofList (moduleName.toList.map (fun c =>
      if c.isAlphanum then c.toLower else '_'))
  -- The module is assembled inside `EmitM`: the per-grammar, leaf-bearing
  -- definitions (`V`, the decoders, `sem`, the `fuse<p>`, the flat table arrays) are built as
  -- `Lean.Syntax` and pretty-printed, so a malformed emission fails against Lean's
  -- grammar here; the fixed scaffolding (imports, `%header`, options, `flat`
  -- record, `fuse` dispatch and `fuseOK<p>` proofs, entry points, namespace) stays as raw text.
  Quote.emitModule do
    let valueTypeCmd ← emitValueType e
    let decodeCmds ← emitDecoder s e g.numTerminals
    let semCmd ← emitSem s e augProd
    let (fuseCmds, fuseDispatch, fuseProofs) ← emitFuse s e g' startState augProd
    let (stackDefs, stackLawful) := emitStack s e
    let (tablePrefix, dataStr, tableTail) ← emitTable g' tables startState s.eof s.options.compressTables
    let valueTypeStr ← Quote.renderCmd valueTypeCmd
    let mut decodeStrs : Array String := #[]
    for (c, i) in decodeCmds.zipIdx do
      let str ← Quote.renderCmd c
      -- `termOf` (the first decoder) is inlined into the engine loop.
      decodeStrs := decodeStrs.push (if i == 0 then "@[inline] " ++ str else str)
    let semStr ← Quote.renderCmd semCmd
    let fuseStr ← Quote.renderCmds fuseCmds
    let importLine := match lexerModule with
      | some m => s!"public import {m}"
      | none => ""
    let header := paras [
      s!"module",
      s!"-- Generated by LeanParserGenerator from a .lig grammar. DO NOT EDIT.",
      s!"-- Module: {moduleName}. Backend: parser.",
      "public import LeanParserGenerator.Runtime.Exec",
      "public import LeanParserGenerator.Runtime.ExecFast",
      "public import LeanParserGenerator.Runtime.Span",
      "public import LeanParserGenerator.Runtime.Diagnostic",
      importLine,
      Builder.publicizeImports s.header,
      "-- Raised limits for the generated parse-table literals.\n"
        ++ "set_option maxRecDepth 1000000\n"
        ++ "set_option maxHeartbeats 40000000",
      -- The parser's public API is its value type, `run`, and `parse`. The parse
      -- tables, the decoders, `sem`, and `fuse` are implementation detail: `public
      -- section` (not `@[expose]`) keeps their bodies in the private scope. The
      -- paired verified spec reaches them for its refinement proofs via `import
      -- all` (same package) and `native_decide` via `meta import` (module system,
      -- docs/DESIGN.md §16.2).
      "public section",
      "namespace " ++ moduleName ]
    -- The executable engine runs at `VP := Span × V`: each stack value carries its
    -- source span alongside the semantic value `V`. `decode` attaches each token's
    -- span; `sem`/`fuse<p>` bind `<x>_span` per RHS symbol and fold the production
    -- span (Menhir's start..end). `V` and the dependent refinement stay value-only.
    -- Generated `sem`/`fuse<p>` bind spans an action may ignore, so silence the
    -- package-wide unused-variable linter here.
    let vpAbbrev := lines [
      "abbrev VP := Runtime.Span × V",
      "",
      "set_option linter.unusedVariables false" ]
    let entry := lines [
      s!"@[export {exportPrefix}_run]",
      s!"def run (input : List (Runtime.Positioned {s.tokenType})) (logNSteps : Nat := 20) : Runtime.Exec.Result VP :=",
      "  Runtime.Exec.runFast (ops := stackOps) flat fuse termOf input logNSteps",
      "",
      s!"@[export {exportPrefix}_parse]",
      s!"def parse (input : List (Runtime.Positioned {s.tokenType})) (logNSteps : Nat := 20) : Option {startTy} :=",
      "  match run input logNSteps with",
      s!"  | .ok (_, .{startCtor} r) => some r",
      s!"  | _ => none" ]
    -- Menhir-style diagnostics over the positioned engine: terminalName / diagnose
    -- / diagnoseSpanned / errorMessage. EOF terminal index is `g.numTerminals`; the
    -- augmented action-table width is `g.numTerminals + 1`.
    let diagnosticsStr := emitDiagnostics s (g.numTerminals + 1) g.numTerminals
    -- Order: data arrays and their `buildDense` prefix, then the `fuse<p>` (read
    -- `gotoData`) and their dispatch, then `flat`/`table`, then the `fuseOK<p>`
    -- proofs (mention `flat`).
    let body := (if tablePrefix.isEmpty then [] else [tablePrefix]) ++
      [stackDefs, dataStr, fuseStr, fuseDispatch, tableTail, stackLawful, fuseProofs]
    return paras <|
      [header, valueTypeStr, vpAbbrev] ++ decodeStrs.toList ++ [semStr] ++ body ++
      [entry, diagnosticsStr, "end " ++ moduleName, ""]

/-- Generate the parser backend, including grammar preparation. -/
def generate (s : Surface) (moduleName : String := "Generated") : IO (Except String String) := do
  match prepareGrammar s with
  | .error e => return .error e
  | .ok prepared => generateFrom s prepared moduleName

end Emit
