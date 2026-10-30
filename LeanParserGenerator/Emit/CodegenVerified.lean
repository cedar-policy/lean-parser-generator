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
This module implements the code generator for the verified parser code. This is
*not* verified code: the generator is untrusted, but the generated code can be
verified.

It emits a dependent `Grammar` and `Automaton`, validation proofs, derived `Safe`
and `Complete` properties, and a specification-level `parse` entry.
The semantic types in the grammar are verbatim user-specified code snippets: any
error from the user will be printed in the output of the code generator.

The generated parsing tables are dependently typed: the type of each action
depends on the state index. The action, goto, and item tables are emitted as packed
`Nat` literals with generic decoders that rebuild the dependent values (including the
`Shift`/goto equality proofs) at evaluation time; the validators and refinement checks
evaluate these decoders, so a wrong table is rejected. The symbol-to-type map `semT'`
is a table lookup (`emitSemTable`) rather than a `match`, which keeps `whnf` of the
refinement's encoder cheap. `Fin` supplies the generated `Numbered → Alphabet`
instances.
-/
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Construct.Annotate
public import LeanParserGenerator.Emit.Codegen
public import LeanParserGenerator.Runtime.GrammarView


@[expose] public section

namespace Emit

open Frontend Construct IR
open Emit.Builder
open Lean Emit.Quote

/-! ### Semantic-type lookups (the user's actual Lean types)

Unlike the (executable) parser backend, the dependent `semT` uses each symbol's declared
Lean type directly. Valueless terminals get `Unit`. -/

/-- The Lean type of terminal index `i` (from the surface `%token` declarations);
    `Unit` for a valueless token. -/
def termTy (s : Surface) (i : Nat) : String :=
  match s.tokens[i]? with
  | some t => if t.hasVal then t.ty else "Unit"
  | none => "Unit"

/-- The Lean type of nonterminal index `i` (its rule's `%type`). -/
def nontermTy (s : Surface) (ntNames : Array String) (i : Nat) : String :=
  match ntNames[i]? with
  | some nm =>
    match s.rules.find? (·.lhs == nm) with
    | some r => r.ty
    | none => "Unit"
  | none => "Unit"

/-! ### Emitting the dependent `Grammar` instance -/

/-- Render a grammar symbol in the IR (`IR.Sym`) as a `Symbol` literal over the
    augmented `Fin` index types.
    Uses `⟨i, of_decide_eq_true rfl⟩` (a proof term, not the `by decide` tactic) so the
    `Fin` bound proof is discharged cheaply at scale --- ~54k such literals in Cedar,
    where the tactic overhead per call dominated proof-module compile time. -/
def symLit (sym : IR.Sym) : String :=
  match sym with
  | .term i => s!"Symbol.T ⟨{i}, of_decide_eq_true rfl⟩"
  | .nonterm i => s!"Symbol.NT ⟨{i}, of_decide_eq_true rfl⟩"

/-- Stable generated declaration name for a production's semantic action. -/
def semanticActionName (production : Nat) : String := s!"semanticAction{production}"

/-- Build the presentation view from the same augmented IR consumed by the
    dependent grammar emitter. Compilation of the generated agreement theorem is
    what promotes this untrusted metadata to an inspectable verified view. -/
def buildVerifiedGrammarView (s : Surface) (g' : IR.Grammar) (augProd : Nat) :
    Runtime.VerifiedGrammarView :=
  let realStart := (s.ntIdx s.start).getD 0
  let eofTerminal := g'.numTerminals - 1
  let terminals := (List.range g'.numTerminals).map fun index =>
    let name := g'.termNames[index]?.getD s!"t{index}"
    let semanticType := if index == eofTerminal then "Unit" else termTy s index
    ({ index, name, semanticType } : Runtime.VerifiedTerminalView)
  let nonterminals := (List.range g'.numNonterminals).map fun index =>
    let name := g'.nontermNames[index]?.getD s!"N{index}"
    let semanticType := if index == g'.start then nontermTy s s.ntNames realStart
      else nontermTy s s.ntNames index
    ({ index, name, semanticType } : Runtime.VerifiedNonterminalView)
  let surfaceAlts := s.rules.toList.flatMap (·.alts.toList)
  let productions := (List.range g'.prods.size).map (λ index =>
    let production := g'.prods[index]!
    let rhs := production.rhs.map
      (λ symbol => match symbol with
      | .term terminal => Runtime.VerifiedGrammarSymbol.terminal terminal
      | .nonterm nonterminal => Runtime.VerifiedGrammarSymbol.nonterminal nonterminal)
    let (rhsBinders, actionSource) := match surfaceAlts[index]? with
      | some alternative =>
          (alternative.elems.toList.map (·.binder),
            alternative.action.trimAscii.toString)
      | none => if index == augProd then ([some "x", none], "x")
          else (List.replicate rhs.length none, "()")
    Runtime.VerifiedProductionView.mk index production.lhs rhs rhsBinders actionSource
      (semanticActionName index))
  let tokenMappings := s.tokens.toList.map fun token =>
    let terminal := if token.name == s.eof then eofTerminal else (s.termIdx token.name).getD 0
    ({ token := token.name, terminal } : Runtime.VerifiedTokenMappingView)
  { terminals
    nonterminals
    productions
    tokenMappings
    userStartNonterminal := realStart
    startNonterminal := g'.start
    eofToken := s.eof
    eofTerminal
    augmentedTerminal := eofTerminal
    augmentedNonterminal := g'.start
    augmentedProduction := augProd }

def emitViewList (entries : List String) : String :=
  if entries.isEmpty then "[]" else "[\n" ++ ",\n".intercalate entries ++ "\n  ]"

/-- Emit the inspectable grammar-view value stored in each specification module.
    Kept as string emission: it is pure metadata (no dependent types, no escaping
    beyond `strLit`), and rendering an anonymous structure instance through
    `ppCommand` daggers the field names (`index✝`), which is invalid source. So
    `Syntax` would not help here — there is nothing to grammar-check that the
    string form gets wrong, and the field-name hygiene actively breaks it. -/
def emitVerifiedGrammarView (view : Runtime.VerifiedGrammarView) : String :=
  let terminals := view.terminals.map fun terminal =>
    "    { index := " ++ toString terminal.index ++
      ", name := " ++ strLit terminal.name ++
      ", semanticType := " ++ strLit terminal.semanticType ++ " }"
  let nonterminals := view.nonterminals.map fun nonterminal =>
    "    { index := " ++ toString nonterminal.index ++
      ", name := " ++ strLit nonterminal.name ++
      ", semanticType := " ++ strLit nonterminal.semanticType ++ " }"
  let productions := view.productions.map fun production =>
    let rhs := production.rhs.map fun symbol => match symbol with
      | .terminal index => s!".terminal {index}"
      | .nonterminal index => s!".nonterminal {index}"
    let rhsBinders := production.rhsBinders.map fun binder => match binder with
      | some value => "some " ++ strLit value
      | none => "none"
    "    { index := " ++ toString production.index ++
      ", lhs := " ++ toString production.lhs ++
      ", rhs := " ++ listLit rhs ++
      ", rhsBinders := " ++ listLit rhsBinders ++
      ", actionSource := " ++ strLit production.actionSource ++
      ", semanticAction := " ++ strLit production.semanticAction ++ " }"
  let tokenMappings := view.tokenMappings.map fun mapping =>
    "    { token := " ++ strLit mapping.token ++
      ", terminal := " ++ toString mapping.terminal ++ " }"
  lines [
    "def verifiedGrammarView : Runtime.VerifiedGrammarView :=",
    "  { terminals := " ++ emitViewList terminals,
    "    nonterminals := " ++ emitViewList nonterminals,
    "    productions := " ++ emitViewList productions,
    "    tokenMappings := " ++ emitViewList tokenMappings,
    s!"    userStartNonterminal := {view.userStartNonterminal}",
    s!"    startNonterminal := {view.startNonterminal}",
    s!"    eofToken := {strLit view.eofToken}",
    s!"    eofTerminal := {view.eofTerminal}",
    s!"    augmentedTerminal := {view.augmentedTerminal}",
    s!"    augmentedNonterminal := {view.augmentedNonterminal}",
    "    augmentedProduction := " ++ toString view.augmentedProduction ++ " }"]

/-- Emit `semTbl`, `symIdx`, and `semT'`: the semantic type of every grammar symbol,
    read off one table indexed by symbol number (terminals first, then nonterminals).

    Each table entry pairs the symbol's declared Lean type with its encoder into the
    executable parser's value type `VP` (or into `Unit` when no executable module is
    paired with this specification). Both `semT'` and the refinement's
    `refinementEncodeValue` project from the same entry, so the encoder's argument
    type is `semT' s` by definition, with no cast.

    A `match` over every symbol is avoided because `whnf` of an n-arm matcher is
    linear in n and the refinement's encoder mentions `semT'` once per arm, so each
    reduction at a concrete symbol was quadratic (0.3 s on Cedar). `List.getD` at a
    literal index is linear with a small constant. -/
def emitSemTable (s : Surface) (g' : IR.Grammar) (ntNames : Array String)
    (execModule : Option String) : String :=
  let numT' := g'.numTerminals
  let numN' := g'.numNonterminals
  let e := collectTypes s
  let realStart := (s.ntIdx s.start).getD 0
  let target := match execModule with
    | some m => s!"{m}.VP"
    | none => "Unit"
  let enc := fun (ty : String) => match execModule with
    | some _ => s!"fun v => (Runtime.Span.dummy, .{e.ctorFor ty} v)"
    | none => "fun _ => ()"
  -- The ascription fixes the expected type: a bare user type name such as `And` can
  -- otherwise be ambiguous with a root-namespace `Prop` connective.
  let entry := fun (ty : String) => s!"⟨({ty} : Type), {enc ty}⟩"
  let termEntries := (List.range numT').map fun i =>
    entry (if i == numT' - 1 then "Unit" else termTy s i)
  let ntEntries := (List.range numN').map fun i =>
    entry (if i == g'.start then nontermTy s ntNames realStart else nontermTy s ntNames i)
  lines [
    s!"def semTbl : List (Σ T : Type, T → {target}) := [",
    ",\n".intercalate ((termEntries ++ ntEntries).map ("  " ++ ·)) ++ "]",
    "",
    s!"def semDefault : Σ T : Type, T → {target} := {entry "Unit"}",
    "",
    "def symIdx : Symbol Terminal NonTerminal → Nat",
    "  | .T t => t.val",
    s!"  | .NT n => {numT'} + n.val",
    "",
    "abbrev semT' (s : Symbol Terminal NonTerminal) : Type :=",
    "  (semTbl.getD (symIdx s) semDefault).1" ]

/-- Emit the dependent grammar defs: `box`, the named `semanticAction{n}`s, and
    `prodContents'` with its projections (the symbol → semantic type map `semT'` is
    `emitSemTable`). The `def`/`abbrev`/match skeleton is real `Syntax`; the
    dependent patterns, signatures, and action bodies (which the generator does not
    parse) are leaves. -/
def emitGrammar
    (s : Surface)
    (g' : IR.Grammar)
    (augProd : Nat)
    (ntNames : Array String)
    (_eofIdx : Nat) : EmitM (Array (TSyntax `command)) := do
  let numT' := g'.numTerminals   -- includes augmented `$`
  let nP' := g'.prods.size
  let pairTy := "NonTerminal × List (Symbol Terminal NonTerminal)"
  let sigmaTy := s!"(pr : {pairTy}) × arrowsRight (semT' (.NT pr.1)) (pr.2.map semT')"
  let boxSigLeaf ← freshLeaf s!"(pr : {pairTy}) → (act : arrowsRight (semT' (.NT pr.1)) (pr.2.map semT')) → ({sigmaTy})"
  let boxBodyLeaf ← freshLeaf "fun pr act => ⟨pr, act⟩"
  let boxDef ← `(command| def $(mkIdent `box) : $boxSigLeaf := $boxBodyLeaf)
  let mut cmds : Array (TSyntax `command) := #[boxDef]
  -- prodContents' match arms and the action defs.
  let eofTermIdx' := numT' - 1
  let elemTyOf := fun (e : Elem) =>
    match s.termIdx e.sym with
    | some ti => if ti == eofTermIdx' then "Unit" else termTy s ti
    | none => match s.ntIdx e.sym with
              | some ni => nontermTy s ntNames ni
              | none => "Unit"
  let mut surfAlts : Array (String × Array Elem) := #[]
  for r in s.rules do
    for alt in r.alts do
      surfAlts := surfAlts.push (alt.action, alt.elems)
  let mut prodArms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  let symLitStr := fun (sym : IR.Sym) => symLit sym
  for pi in [0:nP'] do
    let prod := g'.prods[pi]!
    let lhsLit := s!"(⟨{prod.lhs}, of_decide_eq_true rfl⟩ : NonTerminal)"
    let rev := prod.rhs.reverse
    let rhsLit := "[" ++ ", ".intercalate (rev.map symLitStr) ++ "]"
    let pairLit := s!"({lhsLit}, {rhsLit})"
    let actionName := semanticActionName pi
    let actionExpr : String := Id.run do
      if h : pi < surfAlts.size then
        let (action, elems) := surfAlts[pi]
        let revElems := elems.reverse
        let binders := (revElems.map (fun e =>
          let nm := match e.binder with | some b => b | none => "_"
          s!"({nm} : {elemTyOf e})")).toList
        let lam := if binders.isEmpty then "" else "fun " ++ " ".intercalate binders ++ " => "
        let lhsTy :=
          let realStart := (s.ntIdx s.start).getD 0
          if prod.lhs == g'.start then nontermTy s ntNames realStart
          else nontermTy s ntNames prod.lhs
        if binders.isEmpty then
          -- Empty RHS: ascribe to the LHS type so a bare literal action (e.g. `{ 1 }`)
          -- sees its real `OfNat`, not the stuck `arrowsRight (semT' NT) []` match.
          return s!"(({action}) : {lhsTy})"
        else
          return s!"{lam}({action})"
      else if pi == augProd then
        return "fun (_ : Unit) x => x"
      else
        return "()"
    let actNameId := mkIdent (Name.mkSimple actionName)
    let actSigLeaf ← freshLeaf s!"arrowsRight (semT' (.NT {lhsLit})) ({rhsLit}.map semT')"
    let actBodyLeaf ← freshLeaf actionExpr
    cmds := cmds.push (← `(command| def $actNameId : $actSigLeaf := $actBodyLeaf))
    let prodPat ← freshLeaf s!"⟨{pi}, _⟩"
    let prodRhs ← freshLeaf s!"box {pairLit} {actionName}"
    prodArms := prodArms.push (← `(Lean.Parser.Term.matchAltExpr| | $prodPat => $prodRhs))
  let lastPat ← freshLeaf s!"⟨n+{nP'}, h⟩"
  let lastRhs ← freshLeaf "absurd h (by omega)"
  prodArms := prodArms.push (← `(Lean.Parser.Term.matchAltExpr| | $lastPat => $lastRhs))
  let prodContentsSigLeaf ← freshLeaf s!"Production → {sigmaTy}"
  let prodContentsDef ← `(command| def $(mkIdent `prodContents') : $prodContentsSigLeaf $prodArms:matchAlt*)
  cmds := cmds.push prodContentsDef
  -- prodLhs'/prodRhsRev'/prodAction' are fixed projections; leaf their bodies.
  let prodLhsSig ← freshLeaf "Production → NonTerminal"
  let prodLhsBody ← freshLeaf "fun p => (prodContents' p).1.1"
  cmds := cmds.push (← `(command| def $(mkIdent `prodLhs') : $prodLhsSig := $prodLhsBody))
  let prodRhsSig ← freshLeaf "Production → List (Symbol Terminal NonTerminal)"
  let prodRhsBody ← freshLeaf "fun p => (prodContents' p).1.2"
  cmds := cmds.push (← `(command| def $(mkIdent `prodRhsRev') : $prodRhsSig := $prodRhsBody))
  let prodActSig ← freshLeaf "(p : Production) → arrowsRight (semT' (.NT (prodLhs' p))) ((prodRhsRev' p).map semT')"
  let prodActBody ← freshLeaf "fun p => (prodContents' p).2"
  cmds := cmds.push (← `(command| def $(mkIdent `prodAction') : $prodActSig := $prodActBody))
  return cmds

/-- Emit standalone `tokenTerm'`/`tokenSem'` defs over the user's token type.
    `tokenTerm'` returns the terminal `Fin` index; `tokenSem'` the carried value
    (or `()` for valueless / eof). The eof token maps to the augmented `$` index.
    Note `tokenSem'`'s dependent return type `semT' (.T (tokenTerm' tok))` must
    reduce, which it does since `tokenTerm'` and `semT'` are concrete defs. -/
def emitToken (s : Surface) (eofIdx : Nat) : EmitM (Array (TSyntax `command)) := do
  let tokTyLeaf ← freshLeaf s.tokenType
  let stringId := mkIdent `String
  let terminalId := mkIdent `Terminal
  let mut nameArms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  for t in s.tokens do
    let ctor := mkIdent (Name.mkSimple t.name)
    let nameLit := Syntax.mkStrLit t.name
    if t.hasVal then
      nameArms := nameArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident _ => $nameLit))
    else
      nameArms := nameArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident => $nameLit))
  let nameDef ← `(command| def $(mkIdent `tokenName') : $tokTyLeaf → $stringId $nameArms:matchAlt*)
  let mut termArms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  for (t, i) in s.tokens.zipIdx do
    let idx := if t.name == s.eof then eofIdx else i
    let ctor := mkIdent (Name.mkSimple t.name)
    let finLeaf ← freshLeaf s!"⟨{idx}, of_decide_eq_true rfl⟩"
    if t.hasVal then
      termArms := termArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident _ => $finLeaf))
    else
      termArms := termArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident => $finLeaf))
  let termDef ← `(command| def $(mkIdent `tokenTerm') : $tokTyLeaf → $terminalId $termArms:matchAlt*)
  let semRetLeaf ← freshLeaf "semT' (.T (tokenTerm' tok))"
  let tokBinder := mkIdent `tok
  let mut semArms : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
  for t in s.tokens do
    let ctor := mkIdent (Name.mkSimple t.name)
    if t.hasVal && t.name != s.eof then
      let x := mkIdent `x
      semArms := semArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident $x => $x))
    else if t.hasVal then
      semArms := semArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident _ => ()))
    else
      semArms := semArms.push (← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident => ()))
  let semDef ← `(command| def $(mkIdent `tokenSem') : ($tokBinder : $tokTyLeaf) → $semRetLeaf $semArms:matchAlt*)
  return #[nameDef, termDef, semDef]

/-! ### Emitting the dependent `Automaton` instance -/

/-- Emit an `Action` value for state `st` from the Pager tables. Either a
    `Default_reduce` (when the state has a default reduction) or a `Lookahead`
    function matching on the terminal index. Shift arms carry the `rfl` proof
    `Symbol.T term = lastSymb' target`; reduce arms name the production; `Fail`
    otherwise. -/
def emitActionValue (tables : Tables) (numT' : Nat) (st : Nat) : String := Id.run do
  match tables.defaultReduce.getD st none with
  | some p => s!"Action.DefaultReduce ⟨{p}, of_decide_eq_true rfl⟩"
  | none =>
    let row := tables.action.getD st #[]
    let mut arms : Array String := #[]
    for t in [0:numT'] do
      let arm := match row.getD t Act.error with
        | .shift j => s!"LookaheadAction.Shift ⟨{j-1}, of_decide_eq_true rfl⟩ (by rfl)"
        | .reduce p => s!"LookaheadAction.Reduce ⟨{p}, of_decide_eq_true rfl⟩"
        | .error => "LookaheadAction.Fail"
      arms := arms.push s!"      | ⟨{t}, _⟩ => {arm}"
    let body := "fun term => match term with\n" ++ "\n".intercalate arms.toList
      ++ "\n      | _ => LookaheadAction.Fail"
    "Action.Lookahead (" ++ body ++ ")"

/-- Number of bits needed to store every value in `0 … n`. -/
def bitWidth (n : Nat) : Nat := Nat.log2 n + 1

/-- Pack `fields` into one natural number, `width` bits per field, field 0 lowest. -/
def packFields (width : Nat) (fields : List Nat) : Nat :=
  (fields.zipIdx.foldl (fun acc (v, i) => acc ||| (v <<< (width * i))) 0)

/-- Emit automaton tables and certificate annotations.

    LR state 0 is represented only by `Init`; state `k + 1` is represented by
    `Ninit ⟨k⟩`. Keeping the initial and non-initial types disjoint is required by
    validation. Reducible `lastSymb'` makes shift/goto equalities `rfl`. -/
def emitAutomaton (g' : IR.Grammar) (tables : Tables) (ann : Annotations)
    (nul : Array Bool) (fst : Array (List Nat)) : EmitM String := do
  let numStates := tables.numStates
  let numNI := numStates - 1
  let numT' := g'.numTerminals
  let numN' := g'.numNonterminals
  let stateMember := fun (si : Nat) =>
    if si == 0 then "(match s with | .Init _ => true | _ => false)"
    else s!"(match s with | .Ninit ⟨{si-1}, _⟩ => true | _ => false)"
  let mut L : Array String := #[]
  -- Reducibility makes generated shift/goto equality proofs `rfl`.
  L := L.push "abbrev lastSymb' : NonInitState → Symbol Terminal NonTerminal"
  L := L.push "  | s => match s with"
  for k in [0:numNI] do
    let symStr := match ann.lastSymb[k+1]! with
      | some sym => symLit sym
      | none => "Symbol.NT ⟨0, of_decide_eq_true rfl⟩"
    L := L.push s!"    | ⟨{k}, _⟩ => {symStr}"
  L := L.push "    | _ => Symbol.NT ⟨0, of_decide_eq_true rfl⟩"
  L := L.push ""
  L := L.push "def startNt' : InitState → NonTerminal"
  L := L.push s!"  | _ => ⟨{g'.start}, of_decide_eq_true rfl⟩"
  L := L.push ""
  L := L.push "abbrev St := State InitState NonInitState"
  L := L.push ""
  -- `actionTable'`, `gotoTable'` and `items'` are packed `Nat` tables with generic
  -- decoders instead of one `match` arm per cell. A row is one literal holding
  -- fixed-width bit fields, so the elaborator sees one numeral per state. The
  -- decoders rebuild the dependent values, including the `Shift`/goto equality
  -- proofs. The tables are untrusted: the validators and refinement checks
  -- evaluate the decoders, so a wrong table is rejected. On Cedar the old forms cost
  -- 5 s (goto), 4 s (code arrays), 57 s (items) and 9 s (compiling `actionTable'`).
  --
  -- Action cell encoding: `0` = Fail, `2*p+1` = Reduce production p,
  -- `2*s+2` = Shift state s. Field `numT'` of an action row is the state's
  -- default reduction: `0` = none, `p+1` = reduce p.
  let actCode := fun (st : Nat) (t : Nat) =>
    match (tables.action.getD st #[]).getD t Act.error with
    | .shift j => 2 * (j - 1) + 2
    | .reduce p => 2 * p + 1
    | .error => 0
  let defCode := fun (st : Nat) =>
    match tables.defaultReduce.getD st none with
    | some p => p + 1
    | none => 0
  let actRowFields := fun (st : Nat) =>
    (List.range numT').map (actCode st) ++ [defCode st]
  let actWidth := bitWidth (((List.range numStates).map fun st =>
    (actRowFields st).foldl max 0).foldl max 0)
  let actRows := (List.range numStates).map fun st => packFields actWidth (actRowFields st)
  let gotoCode := fun (st : Nat) (n : Nat) =>
    match (tables.goto.getD st #[]).getD n none with
    | some j => j  -- `j` is a Pager state number ≥ 1, i.e. target index `j-1`, plus one
    | none => 0
  let gotoRowFields := fun (st : Nat) => (List.range numN').map (gotoCode st)
  let gotoWidth := bitWidth (((List.range numStates).map fun st =>
    (gotoRowFields st).foldl max 0).foldl max 0)
  let gotoRows := (List.range numStates).map fun st => packFields gotoWidth (gotoRowFields st)
  let natArray := fun (name : String) (xs : List Nat) =>
    s!"def {name} : Array Nat :=\n  #[" ++ ",\n    ".intercalate (xs.map toString) ++ "]"
  L := L.push "/-- Read the `width`-bit field number `i` of a packed table row. -/"
  L := L.push "def packedField (row width i : Nat) : Nat := (row >>> (width * i)) % (1 <<< width)"
  L := L.push ""
  L := L.push "def stateRow : St → Nat"
  L := L.push "  | .Init _ => 0"
  L := L.push "  | .Ninit s => s.val + 1"
  L := L.push ""
  L := L.push s!"def decodeLA (term : Terminal) (code : Nat) : LookaheadAction NonInitState lastSymb' term :="
  L := L.push "  if code = 0 then LookaheadAction.Fail"
  L := L.push "  else if code % 2 = 1 then"
  L := L.push s!"    (if hp : (code - 1) / 2 < {g'.prods.size} then LookaheadAction.Reduce ⟨(code - 1) / 2, hp⟩ else LookaheadAction.Fail)"
  L := L.push "  else"
  L := L.push s!"    (if hs : (code - 2) / 2 < {numNI} then"
  L := L.push "      (if h : Symbol.T term = lastSymb' ⟨(code - 2) / 2, hs⟩ then LookaheadAction.Shift ⟨(code - 2) / 2, hs⟩ h else LookaheadAction.Fail)"
  L := L.push "     else LookaheadAction.Fail)"
  L := L.push ""
  L := L.push (natArray "actionRows" actRows)
  L := L.push ""
  L := L.push "def actionTable' (s : St) : Action NonInitState lastSymb' :="
  L := L.push "  let row := actionRows.getD (stateRow s) 0"
  L := L.push s!"  match packedField row {actWidth} {numT'} with"
  L := L.push s!"  | 0 => Action.Lookahead (fun term => decodeLA term (packedField row {actWidth} term.val))"
  L := L.push s!"  | p + 1 =>"
  L := L.push s!"    if hp : p < {g'.prods.size} then Action.DefaultReduce ⟨p, hp⟩"
  L := L.push "    else Action.Lookahead (fun _ => LookaheadAction.Fail)"
  L := L.push ""
  L := L.push (natArray "gotoRows" gotoRows)
  L := L.push ""
  L := L.push "def gotoTable' (s : St) (nt : NonTerminal) :"
  L := L.push "    Option { s : NonInitState // Symbol.NT nt = lastSymb' s } :="
  L := L.push s!"  match packedField (gotoRows.getD (stateRow s) 0) {gotoWidth} nt.val with"
  L := L.push "  | 0 => none"
  L := L.push "  | c + 1 =>"
  L := L.push s!"    if hs : c < {numNI} then"
  L := L.push "      (if h : Symbol.NT nt = lastSymb' ⟨c, hs⟩ then some ⟨⟨c, hs⟩, h⟩ else none)"
  L := L.push "    else none"
  L := L.push ""
  for (setL, k) in ann.stateSets.zipIdx do
    L := L.push s!"def stateSet{k} : St → Bool"
    let checks := setL.map stateMember
    let body := if checks.isEmpty then "false" else " || ".intercalate checks
    L := L.push s!"  | s => {body}"
  L := L.push "def pastSymb' : NonInitState → List (Symbol Terminal NonTerminal)"
  L := L.push "  | s => match s with"
  for k in [0:numNI] do
    let lits := listLit ((ann.pastSymb[k+1]!).map symLit)
    L := L.push s!"    | ⟨{k}, _⟩ => {lits}"
  L := L.push "    | _ => []"
  L := L.push "def pastStates' : NonInitState → List (St → Bool)"
  L := L.push "  | s => match s with"
  for k in [0:numNI] do
    let refs := listLit ((ann.pastStates[k+1]!).map (fun i => s!"stateSet{i}"))
    L := L.push s!"    | ⟨{k}, _⟩ => {refs}"
  L := L.push "    | _ => []"
  -- Items: one literal per state. Field 0 is the item count; field `i+1` is item
  -- `i`, laid out as `prod | dot << prodWidth | lookahead-bitmask << (prodWidth + dotWidth)`.
  -- Every field uses the same stride. Lookaheads decode in ascending terminal order.
  -- `itemTable` decodes each row once; the validators read `items'` many times.
  let allItems := (List.range numStates).map fun st => ann.items[st]!
  let prodWidth := bitWidth g'.prods.size
  let dotWidth := bitWidth ((allItems.map fun its => (its.map (·.dot)).foldl max 0).foldl max 0)
  let itemStride := max (prodWidth + dotWidth + numT')
    (bitWidth ((allItems.map List.length).foldl max 0))
  let packItem := fun (it : AnnItem) =>
    it.prod ||| (it.dot <<< prodWidth) |||
      ((it.lookaheads.foldl (fun m t => m ||| (1 <<< t)) 0) <<< (prodWidth + dotWidth))
  let itemRows := allItems.map fun its =>
    packFields itemStride (its.length :: its.map packItem)
  L := L.push (natArray "itemRows" itemRows)
  L := L.push ""
  L := L.push "def decodeItems (row : Nat) : List Item :="
  L := L.push s!"  (List.range (packedField row {itemStride} 0)).map fun i =>"
  L := L.push s!"    let item := packedField row {itemStride} (i + 1)"
  L := L.push s!"    ⟨Fin.ofNat {g'.prods.size} (item % (1 <<< {prodWidth})),"
  L := L.push s!"     (item >>> {prodWidth}) % (1 <<< {dotWidth}),"
  L := L.push s!"     (List.range {numT'}).filterMap fun t =>"
  L := L.push s!"       if ((item >>> {prodWidth + dotWidth}) >>> t) % 2 = 1 then some (Fin.ofNat {numT'} t) else none⟩"
  L := L.push ""
  L := L.push "def itemTable : Array (List Item) := itemRows.map decodeItems"
  L := L.push ""
  L := L.push "def items' (s : St) : List Item := itemTable.getD (stateRow s) []"
  L := L.push "def nullableNt' : NonTerminal → Bool"
  L := L.push "  | nt => match nt with"
  for i in [0:numN'] do
    L := L.push s!"    | ⟨{i}, _⟩ => {nul.getD i false}"
  L := L.push "    | _ => false"
  L := L.push "def firstNt' : NonTerminal → List Terminal"
  L := L.push "  | nt => match nt with"
  for i in [0:numN'] do
    let lits := listLit ((fst.getD i []).map (fun t => s!"⟨{t}, of_decide_eq_true rfl⟩"))
    L := L.push s!"    | ⟨{i}, _⟩ => {lits}"
  L := L.push "    | _ => []"
  return "\n".intercalate L.toList

/-! ### Inspectable grammar agreement -/

/-- Emit checked structural and token-mapping agreement for the readable view. -/
def emitVerifiedGrammarViewAgreement (s : Surface) (eofTerminal numTerminals numNonterminals numProductions : Nat) : String :=
  let tokenNames := listLit (s.tokens.toList.map fun token =>
    strLit token.name)
  lines [
    "def verifiedGrammarViewStructuralCheck (candidate : Runtime.VerifiedGrammarView) : Bool :=",
    "  (@Runtime.VerifiedGrammarView.structurallyAgrees sigInst",
    s!"    (Runtime.instNumberedFin {numTerminals})",
    s!"    (Runtime.instNumberedFin {numNonterminals})",
    s!"    (Runtime.instNumberedFin {numProductions})) candidate",
    "    (startNt' (⟨0, of_decide_eq_true rfl⟩ : InitState))",
    s!"    (⟨{eofTerminal}, of_decide_eq_true rfl⟩ : Terminal)",
    "",
    "theorem verifiedGrammarView_agrees :",
    "    verifiedGrammarViewStructuralCheck verifiedGrammarView = true ∧",
    s!"    verifiedGrammarView.tokenMappings.map (·.token) = {tokenNames} ∧",
    s!"    (∀ token : {s.tokenType},",
    "      verifiedGrammarView.tokenTerminal (tokenName' token) =",
    "        some (tokenTerm' token).val) := by",
    "  constructor",
    "  · native_decide",
    "  · constructor",
    "    · native_decide",
    "    · intro token",
    "      cases token <;> rfl" ]

/-! ### Executable refinement obligations -/

/-- Emit the per-grammar obligations consumed by `Runtime.Refinement`. Structural
    table agreement is checked natively; semantic actions reduce definitionally. -/
def emitRefinement (s : Surface) (g' : IR.Grammar) (execModule : String) : String := Id.run do
  let numP := g'.prods.size
  let realStart := (s.ntIdx s.start).getD 0
  let encode := #[
    s!"def refinementEncodeValue (s : Symbol Terminal NonTerminal) (v : semT' s) : {execModule}.VP :=",
    "  (semTbl.getD (symIdx s) semDefault).2 v"]
  let valuesPattern := fun (length : Nat) =>
    (List.range length).foldr (fun _ rest => s!".cons _ ({rest})") ".nil"
  -- One theorem per production so Lean checks them as parallel jobs;
  -- `refinementSemanticAgrees` only dispatches. One theorem with an `rfl` arm per
  -- production ran sequentially (Cedar: 11 s).
  let mut semantic : Array String := #[]
  for p in [0:numP] do
    let prod := s!"(⟨{p}, of_decide_eq_true rfl⟩ : Production)"
    semantic := semantic ++ #[
      s!"theorem refinementSemanticAgrees{p} :",
      s!"    ∀ (values : Runtime.Refinement.Values (G := grammarInst) (prodRhsRev' {prod})),",
      s!"      {execModule}.table.sem {p} (values.encode refinementEncodeValue).reverse =",
      s!"        refinementEncodeValue (.NT (prodLhs' {prod}))",
      s!"          (values.apply (prodAction' {prod}))",
      s!"  | {valuesPattern (g'.prods[p]!).rhs.length} => rfl",
      ""]
  semantic := semantic ++ #[
    "theorem refinementSemanticAgrees :",
    "    ∀ (production : Production)",
    "      (values : Runtime.Refinement.Values (G := grammarInst) (prodRhsRev' production)),",
    s!"      {execModule}.table.sem production.val (values.encode refinementEncodeValue).reverse =",
    "        refinementEncodeValue (.NT (prodLhs' production))",
    "          (values.apply (prodAction' production))"]
  for p in [0:numP] do
    semantic := semantic.push s!"  | ⟨{p}, _⟩, values => refinementSemanticAgrees{p} values"
  semantic := semantic.push s!"  | ⟨n + {numP}, h⟩, _ => absurd h (by omega)"

  let fixed := lines [
    s!"def refinementStateIndex : St → Nat",
    "  | .Init _ => 0",
    "  | .Ninit state => state.val + 1",
    "",
    "def refinementTerminalIndex (terminal : Terminal) : Nat := terminal.val",
    "def refinementNonterminalIndex (nonterminal : NonTerminal) : Nat := nonterminal.val",
    "def refinementProductionIndex (production : Production) : Nat := production.val",
    "",
    "def refinementDefault : St → Option Nat",
    "  | state => match actionTable' state with",
    "    | .DefaultReduce production => some production.val",
    "    | .Lookahead _ => none",
    "",
    "def refinementLookahead (state : St) (terminal : Terminal) : Runtime.Exec.Act :=",
    "  match actionTable' state with",
    "  | .DefaultReduce production => .reduce production.val",
    "  | .Lookahead actions => match actions terminal with",
    "    | .Shift target _ => .shift (target.val + 1)",
    "    | .Reduce production => .reduce production.val",
    "    | .Fail => .error",
    "",
    "def refinementGoto (state : St) (nonterminal : NonTerminal) : Option Nat :=",
    "  (gotoTable' state nonterminal).map fun target => target.1.val + 1",
    "",
    "def refinementDefaultCheck : Bool :=",
    "  (Finite.all (α := St)).all fun state =>",
    s!"    decide ({execModule}.table.defaultReduce (refinementStateIndex state) = refinementDefault state)",
    "",
    "theorem refinementDefaultCheck_ok : refinementDefaultCheck = true := by native_decide",
    "",
    "theorem refinementDefaultAgrees (state : St) :",
    s!"    {execModule}.table.defaultReduce (refinementStateIndex state) = refinementDefault state := by",
    "  exact of_decide_eq_true ((List.all_eq_true.mp refinementDefaultCheck_ok) state (Finite.mem_all state))",
    "",
    "def refinementLookaheadCheck : Bool :=",
    "  (Finite.all (α := St)).all fun state => match actionTable' state with",
    "    | .DefaultReduce _ => true",
    "    | .Lookahead _ => (Finite.all (α := Terminal)).all fun terminal =>",
    s!"      decide ({execModule}.table.action (refinementStateIndex state) terminal.val =",
    "        refinementLookahead state terminal)",
    "",
    "theorem refinementLookaheadCheck_ok : refinementLookaheadCheck = true := by native_decide",
    "",
    "theorem refinementLookaheadAgrees (state : St)",
    "    (actions : (terminal : Terminal) → LookaheadAction NonInitState lastSymb' terminal)",
    "    (haction : actionTable' state = .Lookahead actions) (terminal : Terminal) :",
    s!"    {execModule}.table.action (refinementStateIndex state) terminal.val =",
    "      refinementLookahead state terminal := by",
    "  have states := (List.all_eq_true.mp refinementLookaheadCheck_ok) state (Finite.mem_all state)",
    "  rw [haction] at states",
    "  exact of_decide_eq_true ((List.all_eq_true.mp states) terminal (Finite.mem_all terminal))",
    "",
    "def refinementGotoCheck : Bool :=",
    "  (Finite.all (α := St)).all fun state =>",
    "    (Finite.all (α := NonTerminal)).all fun nonterminal =>",
    s!"      decide ({execModule}.table.goto (refinementStateIndex state) nonterminal.val =",
    "        refinementGoto state nonterminal)",
    "",
    "theorem refinementGotoCheck_ok : refinementGotoCheck = true := by native_decide",
    "",
    "theorem refinementGotoAgrees (state : St) (nonterminal : NonTerminal) :",
    s!"    {execModule}.table.goto (refinementStateIndex state) nonterminal.val =",
    "      refinementGoto state nonterminal := by",
    "  have states := (List.all_eq_true.mp refinementGotoCheck_ok) state (Finite.mem_all state)",
    "  exact of_decide_eq_true ((List.all_eq_true.mp states) nonterminal (Finite.mem_all nonterminal))",
    "",
    "def refinementProductionCheck : Bool :=",
    "  (Finite.all (α := Production)).all fun production =>",
    s!"    decide ({execModule}.table.prodLhs production.val = (prodLhs' production).val) &&",
    s!"    decide ({execModule}.table.prodRhsLen production.val = (prodRhsRev' production).length)",
    "",
    "theorem refinementProductionCheck_ok : refinementProductionCheck = true := by native_decide",
    "",
    s!"def refinementStructuralCheck (candidate : Runtime.Exec.ExecTable {execModule}.VP) : Bool :=",
    "  decide (candidate.startState = 0) &&",
    "  ((Finite.all (α := St)).all fun state =>",
    "    decide (candidate.defaultReduce (refinementStateIndex state) = refinementDefault state) &&",
    "    (match actionTable' state with",
    "     | .DefaultReduce _ => true",
    "     | .Lookahead _ => (Finite.all (α := Terminal)).all fun terminal =>",
    "       decide (candidate.action (refinementStateIndex state) terminal.val =",
    "         refinementLookahead state terminal))) &&",
    "  ((Finite.all (α := St)).all fun state =>",
    "    (Finite.all (α := NonTerminal)).all fun nonterminal =>",
    "      decide (candidate.goto (refinementStateIndex state) nonterminal.val =",
    "        refinementGoto state nonterminal)) &&",
    "  ((Finite.all (α := Production)).all fun production =>",
    "    decide (candidate.prodLhs production.val = (prodLhs' production).val) &&",
    "    decide (candidate.prodRhsLen production.val = (prodRhsRev' production).length))",
    "",
    s!"theorem refinementStructuralCheck_ok : refinementStructuralCheck {execModule}.table = true := by",
    "  native_decide",
    "",
    "theorem refinementProductionLhsAgrees (production : Production) :",
    s!"    {execModule}.table.prodLhs production.val = (prodLhs' production).val := by",
    "  have checked := (List.all_eq_true.mp refinementProductionCheck_ok) production (Finite.mem_all production)",
    "  simp only [Bool.and_eq_true] at checked",
    "  exact of_decide_eq_true checked.1",
    "",
    "theorem refinementProductionLengthAgrees (production : Production) :",
    s!"    {execModule}.table.prodRhsLen production.val = (prodRhsRev' production).length := by",
    "  have checked := (List.all_eq_true.mp refinementProductionCheck_ok) production (Finite.mem_all production)",
    "  simp only [Bool.and_eq_true] at checked",
    "  exact of_decide_eq_true checked.2",
    "",
    "theorem refinementDecodeAgrees (token : grammarInst.Token) :",
    s!"    {execModule}.decode ⟨token, Runtime.Span.dummy⟩ =",
    "      (refinementTerminalIndex (tokenTerm' token),",
    "        refinementEncodeValue (.T (tokenTerm' token)) (tokenSem' token)) := by",
    "  cases token <;> rfl",
    "",
    "def executableRefinement : Runtime.Refinement.ExecRefinement (G := grammarInst)",
    (s!"    (A := automatonInst) {execModule}.VP := " ++ "{"),
    s!"  table := {execModule}.table",
    s!"  decode := fun t => {execModule}.decode ⟨t, Runtime.Span.dummy⟩",
    s!"  eof := .{s.eof}",
    "  encodeValue := refinementEncodeValue",
    "  stateIndex := refinementStateIndex",
    "  terminalIndex := refinementTerminalIndex",
    "  nonterminalIndex := refinementNonterminalIndex",
    "  productionIndex := refinementProductionIndex",
    "  start_agrees := by intro init; rfl",
    s!"  eof_agrees := by rfl",
    "  decode_agrees := refinementDecodeAgrees",
    "  default_agrees := by",
    "    intro state",
    "    have actionDef : @Automaton.actionTable sigInst automatonInst state = actionTable' state := rfl",
    "    rw [actionDef, refinementDefaultAgrees]",
    "    cases h : actionTable' state <;>",
    "      simp [refinementDefault, h, refinementProductionIndex]",
    "  lookahead_agrees := by",
    "    intro state actions haction terminal",
    "    have actionDef : @Automaton.actionTable sigInst automatonInst state = actionTable' state := rfl",
    "    have hactionConcrete : actionTable' state = .Lookahead actions := by",
    "      rw [← actionDef]",
    "      exact haction",
    "    rw [show refinementTerminalIndex terminal = terminal.val from rfl]",
    "    rw [refinementLookaheadAgrees state actions hactionConcrete terminal]",
    "    simp [refinementLookahead, hactionConcrete, refinementStateIndex,",
    "      refinementProductionIndex]",
    "    cases actions terminal <;> rfl",
    "  goto_agrees := by",
    "    intro state nonterminal",
    "    have gotoDef : @Automaton.gotoTable sigInst automatonInst state nonterminal =",
    "        gotoTable' state nonterminal := rfl",
    "    rw [gotoDef]",
    "    rw [show refinementNonterminalIndex nonterminal = nonterminal.val from rfl]",
    "    rw [refinementGotoAgrees]",
    "    unfold refinementGoto",
    "    cases gotoTable' state nonterminal <;> rfl",
    "  production_lhs_agrees := by",
    "    intro production",
    "    have lhsDef : grammarInst.prodLhs production = prodLhs' production := rfl",
    "    simpa [refinementProductionIndex, refinementNonterminalIndex, lhsDef] using",
    "      refinementProductionLhsAgrees production",
    "  production_length_agrees := by",
    "    intro production",
    "    have rhsDef : grammarInst.prodRhsRev production = prodRhsRev' production := rfl",
    "    simpa [refinementProductionIndex, rhsDef] using",
    "      refinementProductionLengthAgrees production",
    "  semantic_agrees := by",
    "    intro production values",
    "    change Runtime.Refinement.Values (G := grammarInst) (prodRhsRev' production) at values",
    s!"    change {execModule}.table.sem production.val (values.encode refinementEncodeValue).reverse =",
    "      refinementEncodeValue (.NT (prodLhs' production))",
    "        (values.apply (prodAction' production))",
    "    exact refinementSemanticAgrees production values",
    "}",
    "",
    "theorem parserRunRefines (input : List grammarInst.Token) (logNSteps : Nat) :",
    "    Runtime.Refinement.ResultRel executableRefinement",
    "      (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "      (Runtime.parse (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "        (Runtime.Refinement.listStream executableRefinement input) logNSteps)",
    s!"      ({execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps) := by",
    s!"  have hrun : {execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps",
    s!"      = Runtime.Exec.run {execModule}.table (input.map executableRefinement.decode) logNSteps := by",
    s!"    simp only [{execModule}.run]",
    s!"    rw [Runtime.Exec.runFast_eq_run {execModule}.stackOps {execModule}.flat {execModule}.fuse",
    s!"      {execModule}.termOf {execModule}.valOf {execModule}.stackLawful {execModule}.fuseOK]",
    s!"    simp only [{execModule}.table, executableRefinement, List.map_map]",
    "    rfl",
    "  rw [hrun]",
    "  simpa [executableRefinement] using",
    "    Runtime.Refinement.run_refines executableRefinement safety",
    "      (⟨0, of_decide_eq_true rfl⟩ : InitState) input logNSteps",
    "",
    "theorem parse_eq_dependent (input : List grammarInst.Token) (logNSteps : Nat) :",
    s!"    {execModule}.parse (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps = parse input logNSteps := by",
    "  have related := parserRunRefines input logNSteps",
    s!"  unfold {execModule}.parse parse",
    "  have streamEq : Runtime.Refinement.listStream executableRefinement input = toStream input := rfl",
    "  rw [← streamEq]",
    "  generalize hDep : Runtime.parse (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "    (Runtime.Refinement.listStream executableRefinement input) logNSteps = dependent",
    "    at related ⊢",
    s!"  generalize hExec : {execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps = executable at related ⊢",
    "  cases related <;> rfl",
    "",
    "abbrev ParserStartTree (word : List grammarInst.Token) :=",
    "  Grammar.ParseTree (G := grammarInst)",
    "    (.NT (startNt' (⟨0, of_decide_eq_true rfl⟩ : InitState))) word",
    "",
    "theorem parser_sound (input : List grammarInst.Token) (logNSteps : Nat)",
    s!"    (semantic : {nontermTy s s.ntNames realStart})",
    s!"    (accepted : {execModule}.parse (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps = some semantic) :",
    "    ∃ (word : List grammarInst.Token) (tree : ParserStartTree word)",
    "      (rest : Runtime.NatStream grammarInst.Token),",
    "      toStream input = Runtime.NatStream.appList word rest ∧",
    "      Grammar.ptSem tree = semantic := by",
    "  rw [parse_eq_dependent] at accepted",
    "  unfold parse at accepted",
    "  generalize hResult : Runtime.parse (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "    (toStream input) logNSteps = result at accepted",
    "  cases result with",
    "  | Fail state token => cases accepted",
    "  | Timeout => cases accepted",
    "  | Err message => cases accepted",
    "  | Parsed value rest =>",
    "      have valueEq : value = semantic := Option.some.inj accepted",
    "      have sound := Runtime.parseCorrect (G := grammarInst) (A := automatonInst)",
    "        (S := Runtime.NatStream grammarInst.Token)",
    "        (⟨0, of_decide_eq_true rfl⟩ : InitState) (toStream input) logNSteps",
    "      rw [hResult] at sound",
    "      obtain ⟨word, tree, inputEq, semanticEq⟩ := sound",
    "      exact ⟨word, tree, rest, inputEq, semanticEq.trans valueEq⟩",
    "",
    "theorem parser_err_free (input : List grammarInst.Token) (logNSteps : Nat) :",
    s!"    Runtime.Exec.ResultErrFree ({execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps) := by",
    "  have related := parserRunRefines input logNSteps",
    "  change Runtime.Refinement.ResultRel executableRefinement",
    "    (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "    (Runtime.parse (⟨0, of_decide_eq_true rfl⟩ : InitState) (toStream input) logNSteps)",
    s!"    ({execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps) at related",
    "  have dependentFree := Runtime.parse_err_free (G := grammarInst) (A := automatonInst)",
    "    safety (⟨0, of_decide_eq_true rfl⟩ : InitState) (toStream input) logNSteps",
    "  generalize hDependent : Runtime.parse (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "    (toStream input) logNSteps = dependent at related dependentFree",
    s!"  generalize hParser : {execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps = result at related ⊢",
    "  cases related with",
    "  | fail state token => trivial",
    "  | parsed value stream => trivial",
    "  | timeout => trivial",
    "  | error message => exact dependentFree",
    "",
    "theorem parser_ne_err (input : List grammarInst.Token) (logNSteps : Nat)",
    "    (message : String) :",
    s!"    {execModule}.run (input.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps ≠ .err message := by",
    "  intro isError",
    "  have errorFree := parser_err_free input logNSteps",
    "  rw [isError] at errorFree",
    "  exact errorFree",
    "",
    "theorem toStream_eq_appList (input : List grammarInst.Token) :",
    "    toStream input = Runtime.AppStream.appList input (toStream []) := by",
    "  funext index",
    "  induction input generalizing index with",
    "  | nil => rfl",
    "  | cons token input ih =>",
    "      cases index with",
    "      | zero => rfl",
    "      | succ index => exact ih index",
    "",
    "theorem parser_complete {word : List grammarInst.Token}",
    "    (tree : ParserStartTree word) (logNSteps : Nat)",
    "    (fuel : Grammar.ptSize tree ≤ 2 ^ logNSteps) :",
    s!"    {execModule}.parse (word.map (fun t => ⟨t, Runtime.Span.dummy⟩)) logNSteps = some (Grammar.ptSem tree) := by",
    "  rw [parse_eq_dependent]",
    "  unfold parse",
    "  have complete := Runtime.parseComplete (G := grammarInst) (A := automatonInst)",
    "    (S := Runtime.NatStream grammarInst.Token) completeness",
    "    (⟨0, of_decide_eq_true rfl⟩ : InitState) logNSteps (toStream []) tree",
    "  rw [← toStream_eq_appList] at complete",
    "  generalize hResult : Runtime.parse (⟨0, of_decide_eq_true rfl⟩ : InitState)",
    "    (toStream word) logNSteps = result at complete ⊢",
    "  cases result with",
    "  | Fail state token => exact complete.elim",
    "  | Err message => exact complete.elim",
    "  | Timeout => omega",
    "  | Parsed semantic rest => exact congrArg some complete.1",
    "",
    "theorem parser_unambiguous {word : List grammarInst.Token}",
    "    (tree1 tree2 : ParserStartTree word) :",
    "    Grammar.ptSem tree1 = Grammar.ptSem tree2 := by",
    s!"  letI : Inhabited grammarInst.Token := ⟨.{s.eof}⟩",
    "  exact Runtime.unambiguity (G := grammarInst) (A := automatonInst)",
    "    completeness (⟨0, of_decide_eq_true rfl⟩ : InitState) tree1 tree2"
  ]
  paras [lines encode.toList, lines semantic.toList, fixed]

/-- Emit token leaves and one source-order parse-tree constructor per production,
    with a `ptSem` equation for each production. These helpers hide terminal and
    production `Fin` witnesses plus the reversed `ParseTreeList` representation
    from handwritten certificates. They are generated only when
    `%option roundtrip_parser` is enabled. -/
def emitParseTreeConstructors (s : Surface) (g' : IR.Grammar) (_augProd : Nat) : String :=
  if s.options.roundtripParser.isNone then "" else
  let eofTerm := g'.numTerminals - 1
  let tokTy := s.tokenType
  let tokenBlocks := s.tokens.toList.zipIdx.map fun (decl, index) =>
    let term := if decl.name == s.eof then eofTerm else index
    let args := if decl.hasVal then s!"\n    (value : {decl.ty})" else ""
    let token := if decl.hasVal then s!"{tokTy}.{decl.name} value" else s!"{tokTy}.{decl.name}"
    s!"/-- Terminal parse tree for `{decl.name}` with its concrete grammar index. -/\n" ++
    s!"noncomputable def parseTreeToken{decl.name}{args} :\n" ++
    s!"    Grammar.ParseTree (G := grammarInst)\n" ++
    s!"      (.T (⟨{term}, of_decide_eq_true rfl⟩ : Terminal)) [{token}] :=\n" ++
    s!"  Runtime.castPT (G := grammarInst) (by with_unfolding_all rfl)\n" ++
    s!"    (.terminal (G := grammarInst) ({token}))"
  let blocks := (List.range g'.prods.size).map fun pi => Id.run do
    let prod := g'.prods[pi]!
    let production := s!"(⟨{pi}, of_decide_eq_true rfl⟩ : Production)"
    let mut args : List String := []
    let mut callArgs : List String := []
    let mut words : List String := []
    let mut trees : List String := []
    let mut semantics : List String := []
    for (sym, i) in prod.rhs.zipIdx do
      match sym with
      | .nonterm nt =>
          let word := s!"word{i}"
          let tree := s!"tree{i}"
          args := args ++ ["{" ++ word ++ " : List " ++ tokTy ++ "}",
            s!"({tree} : Grammar.ParseTree (G := grammarInst)\n      (.NT (⟨{nt}, of_decide_eq_true rfl⟩ : NonTerminal)) {word})"]
          words := words ++ [word]
          trees := trees ++ [tree]
          callArgs := callArgs ++ [tree]
          semantics := semantics ++ [s!"Grammar.ptSem {tree}"]
      | .term term =>
          let tokenName := if term == eofTerm then s.eof else (s.tokens[term]!).name
          let tokenDecl := if term == eofTerm then none else s.tokens[term]?
          let value := s!"value{i}"
          match tokenDecl with
          | some decl =>
              if decl.hasVal then
                args := args ++ [s!"({value} : {decl.ty})"]
                callArgs := callArgs ++ [value]
                semantics := semantics ++ [value]
              else semantics := semantics ++ ["()"]
          | none => semantics := semantics ++ ["()"]
          let token := match tokenDecl with
            | some decl =>
                if decl.hasVal then s!"{tokTy}.{tokenName} {value}"
                else s!"{tokTy}.{tokenName}"
            | none => s!"{tokTy}.{tokenName}"
          let tokenTree := s!"parseTreeToken{tokenName}" ++
            (match tokenDecl with
             | some decl => if decl.hasVal then s!" {value}" else ""
             | none => "")
          words := words ++ [s!"[{token}]"]
          trees := trees ++ [s!"({tokenTree})"]
    let word := if words.isEmpty then "[]" else String.intercalate " ++ " words
    let treeList := trees.foldl (fun rest tree => s!".cons ({rest}) ({tree})") ".nil"
    let argsText := if args.isEmpty then "" else "\n    " ++ String.intercalate "\n    " args
    let call := if callArgs.isEmpty then s!"parseTreeProduction{pi}"
      else s!"parseTreeProduction{pi} " ++ String.intercalate " " callArgs
    let actionArgs := semantics.reverse.map fun value => "(" ++ value ++ ")"
    let action := String.intercalate " " ([s!"semanticAction{pi}"] ++ actionArgs)
    let reductions := String.intercalate ", " <|
      ["Grammar.ptSem_nonTerminal"] ++
      List.replicate prod.rhs.length "Grammar.ptlSem_cons" ++
      ["Grammar.ptlSem_nil"]
    return s!"/-- Parse-tree constructor for production {pi}, in source RHS order. -/\n" ++
    s!"noncomputable def parseTreeProduction{pi}{argsText} :\n" ++
    s!"    Grammar.ParseTree (G := grammarInst)\n" ++
    s!"      (.NT (⟨{prod.lhs}, of_decide_eq_true rfl⟩ : NonTerminal))\n" ++
    s!"      ({word}) :=\n" ++
    s!"  .nonTerminal (G := grammarInst) {production} ({treeList})\n\n" ++
    s!"@[simp] theorem parseTreeProduction{pi}_sem{argsText} :\n" ++
    s!"    Grammar.ptSem ({call}) = {action} := by\n" ++
    s!"  unfold parseTreeProduction{pi}\n" ++
    s!"  erw [{reductions}]\n" ++
    s!"  with_unfolding_all rfl"
  String.intercalate "\n\n" tokenBlocks ++ "\n\n" ++
    String.intercalate "\n\n" blocks ++ "\n"

/-- Render the dependent specification from shared prepared construction data. -/
def generateVerifiedFrom (s : Surface) (prepared : PreparedGrammar)
    (moduleName : String := "CalcVerified")
    (executable : Option (String × String) := none)
    (lexerModule : Option String := none) : IO (Except String String) := do
  let g := prepared.source
  let g' := prepared.augmented
  let augProd := prepared.augProd
  let col := prepared.collection
  let tables := prepared.tables
  let ann := Construct.annotate g' col
  let nul := Construct.nullable g'
  let fst := Construct.firstSets g'
  let ntNames := s.ntNames
  let eofIdx := g.numTerminals
  let numT' := g'.numTerminals
  let numN' := g'.numNonterminals
  let nP' := g'.prods.size
  let numStates := tables.numStates
  let grammarView := buildVerifiedGrammarView s g' augProd
  -- `GrammarSig` excludes `semT`, so both validators remain computable and their
  -- per-grammar validation proofs can be discharged by `native_decide`.
  -- `grammarInst` is built *from* `sigInst`, making
  -- `grammarInst.toGrammarSig` definitionally equal to `sigInst`; the interpreter
  -- and validator therefore refer to the same automaton signature.
  let sigWiring := lines [
    "@[instance_reducible] def sigInst : GrammarSig where",
    "  Terminal := Terminal",
    "  NonTerminal := NonTerminal",
    "  Production := Production",
    "  prodLhs := prodLhs'",
    "  prodRhsRev := prodRhsRev'" ]
  let grammarWiring := lines [
    "instance grammarInst : Grammar := { sigInst with",
    "  semT := semT'",
    "  prodAction := prodAction'",
    "  Token := " ++ s.tokenType,
    "  tokenTerm := tokenTerm'",
    "  tokenSem := tokenSem' }" ]
  let autWiring := lines [
    "instance automatonInst : Automaton (G := sigInst) where",
    "  InitState := InitState",
    "  NonInitState := NonInitState",
    "  lastSymb := lastSymb'",
    "  startNt := startNt'",
    "  actionTable := actionTable'",
    "  gotoTable := gotoTable'",
    "  pastSymb := pastSymb'",
    "  pastStates := pastStates'",
    "  items := items'",
    "  nullableNt := nullableNt'",
    "  firstNt := firstNt'" ]
  -- `native_decide` trusts compiled Boolean evaluation; invalid certificates fail
  -- to elaborate, and the linking theorems derive `Safe` and `Complete`.
  let validationProofs := lines [

    "theorem safetyValidation : safeValidator (A := automatonInst) = true := by native_decide",
    "",
    "theorem safety : Safe := safe_of_safeValidator safetyValidation",
    "",
    "theorem completenessValidation : completeValidator (A := automatonInst) = true := by native_decide",
    "",
    "theorem completeness : Complete := complete_of_completeValidator completenessValidation" ]
  let startTy := (s.rules.find? (·.lhs == s.start)).map (·.ty) |>.getD "Unit"
  let parseEntry := lines [
    s!"def toStream (input : List {s.tokenType}) : Runtime.NatStream {s.tokenType} :=",
    s!"  fun n => input.getD n .{s.eof}",
    s!"def parse (input : List {s.tokenType}) (logNSteps : Nat := 40) : Option {startTy} :=",
    "  match Runtime.parse (S := Runtime.NatStream _) (⟨0, of_decide_eq_true rfl⟩ : InitState) (toStream input) logNSteps with",
    "  | .Parsed r _ => some r",
    "  | _ => none" ]
  let refinementImports := match executable with
    | some (importName, _) =>
        -- The refinement witness unfolds the parser's `decode`/`sem`/`table` in
        -- `rfl` proofs and `native_decide`s over the flat tables. The parser keeps
        -- those internal (`public section`, not exposed), so the spec reaches them
        -- via `import all` (def-eq access, same package) and `meta import`
        -- (meta-phase reduction). Both are needed (module system).
        "public import LeanParserGenerator.Runtime.Refinement\npublic import LeanParserGenerator.Runtime.Span\npublic import " ++ importName
          ++ "\nimport all " ++ importName
          ++ "\nmeta import " ++ importName
    | none => ""
  let refinementProof := match executable with
    | some (_, execModule) => emitRefinement s g' execModule
    | none => ""
  -- Assembled inside `EmitM`: the per-grammar semantic defs (`semT'`, actions,
  -- `prodContents'`, the `token*'`s) and the `Nat` code tables build as `Syntax`;
  -- the dependent automaton matches and fixed proof scaffolding stay raw text.
  -- See DESIGN §16.1.
  Quote.emitModule do
    let tokenCmds ← emitToken s eofIdx
    let tokenStr ← Quote.renderCmds tokenCmds
    let semTableStr := emitSemTable s g' ntNames (executable.map (·.2))
    let grammarCmds ← emitGrammar s g' augProd ntNames eofIdx
    let grammarStr ← Quote.renderCmds grammarCmds
    let automatonStr ← emitAutomaton g' tables ann nul fst
    let parseTreeConstructors := emitParseTreeConstructors s g' augProd
    let parts : List String := [
      "module",
      "-- Generated by LeanParserGenerator (dependent specification backend). DO NOT EDIT.",
      "public import LeanParserGenerator.Runtime.Interpreter",
      "public import LeanParserGenerator.Runtime.Validator.Safe",
      "public import LeanParserGenerator.Runtime.Validator.Complete",
      "public import LeanParserGenerator.Runtime.Safety",
      "public import LeanParserGenerator.Runtime.Correct",
      "public import LeanParserGenerator.Runtime.Complete",
      "public import LeanParserGenerator.Runtime.GrammarView",
      -- `native_decide` reduces the validators, the grammar view, and the flat
      -- parser tables at the meta phase, so those modules are also `meta`-imported
      -- (the plain imports above keep them available to ordinary generated defs).
      "meta import LeanParserGenerator.Runtime.Validator.Safe",
      "meta import LeanParserGenerator.Runtime.Validator.Complete",
      "meta import LeanParserGenerator.Runtime.GrammarView",
      refinementImports,
      (match lexerModule with
       | some m => s!"public import {m}"
       | none => ""),
      Builder.publicizeImports s.header,
      -- The dependent spec is reasoned about throughout (validation/refinement
      -- proofs unfold the grammar, automaton, and semantic defs), so expose the
      -- whole module (module system, docs/DESIGN.md §16.2).
      "@[expose] public section",
      "open Runtime",
      "set_option maxRecDepth 1000000",
      "set_option maxHeartbeats 40000000",
      "namespace " ++ moduleName,
      s!"abbrev Terminal := Fin {numT'}",
      s!"abbrev NonTerminal := Fin {numN'}",
      s!"abbrev Production := Fin {nP'}",
      s!"abbrev InitState := Fin 1",
      s!"-- Non-initial states are Pager states 1 … {numStates-1} (state 0 is only ever `Init`).",
      s!"abbrev NonInitState := Fin {numStates - 1}",
      emitVerifiedGrammarView grammarView,
      semTableStr,
      grammarStr,
      tokenStr,
      sigWiring,
      grammarWiring ++ (if parseTreeConstructors.isEmpty then ""
        else "\n\n" ++ parseTreeConstructors),
      automatonStr,
      autWiring,
      emitVerifiedGrammarViewAgreement s eofIdx numT' numN' nP',
      validationProofs,
      parseEntry,
      refinementProof,
      "end " ++ moduleName,
      ""
    ]
    return paras parts

/-- Generate the dependent specification, including grammar preparation. -/
def generateVerified (s : Surface) (moduleName : String := "CalcVerified") :
    IO (Except String String) := do
  match prepareGrammar s with
  | .error e => return .error e
  | .ok prepared => generateVerifiedFrom s prepared moduleName

/-- Render verified and executable modules from one prepared Pager construction. -/
def generateBothFrom (s : Surface) (prepared : PreparedGrammar)
    (verifiedModule executableModule : String) (executableImport : Option String := none)
    (lexerModule : Option String := none) :
    IO (Except String (String × String)) := do
  let importName := executableImport.getD executableModule
  match ← generateVerifiedFrom s prepared verifiedModule (some (importName, executableModule)) lexerModule with
  | .error e => return .error e
  | .ok verified =>
    match ← generateFrom s prepared executableModule lexerModule with
    | .error e => return .error e
    | .ok executable => return .ok (verified, executable)

/-- Prepare a grammar once and generate both parser backends. -/
def generateBoth (s : Surface) (verifiedModule executableModule : String)
    (executableImport : Option String := none)
    (lexerModule : Option String := none) : IO (Except String (String × String)) := do
  match prepareGrammar s with
  | .error e => return .error e
  | .ok prepared => generateBothFrom s prepared verifiedModule executableModule executableImport lexerModule

end Emit
