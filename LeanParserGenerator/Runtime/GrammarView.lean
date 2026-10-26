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
Inspectable metadata for an emitted dependent grammar.

The view records names and source strings for presentation, while
`VerifiedGrammarView.structurallyAgrees` checks the index-level grammar shape
against the actual `GrammarSig`. Semantic type and action names are deliberately
not part of that proof boundary: the generated Lean definitions remain
authoritative.
-/
public import LeanParserGenerator.Runtime.Grammar


@[expose] public section

namespace Runtime

/-- A grammar symbol represented by its terminal or nonterminal index. -/
inductive VerifiedGrammarSymbol where
  | terminal (index : Nat)
  | nonterminal (index : Nat)
  deriving Repr, DecidableEq, BEq

/-- Readable metadata for one terminal in the emitted grammar. -/
structure VerifiedTerminalView where
  index : Nat
  name : String
  semanticType : String
  deriving Repr, DecidableEq, BEq

/-- Readable metadata for one nonterminal in the emitted grammar. -/
structure VerifiedNonterminalView where
  index : Nat
  name : String
  semanticType : String
  deriving Repr, DecidableEq, BEq

/-- One production in source order. The RHS is stored left-to-right for readers.
`rhsBinders`, `actionSource`, and `semanticAction` are presentation metadata. -/
structure VerifiedProductionView where
  index : Nat
  lhs : Nat
  rhs : List VerifiedGrammarSymbol
  rhsBinders : List (Option String)
  actionSource : String
  semanticAction : String
  deriving Repr, DecidableEq, BEq

/-- The terminal selected by one constructor of the user's token type. -/
structure VerifiedTokenMappingView where
  token : String
  terminal : Nat
  deriving Repr, DecidableEq, BEq

/-- An inspectable view of the exact augmented grammar emitted for verification. -/
structure VerifiedGrammarView where
  terminals : List VerifiedTerminalView
  nonterminals : List VerifiedNonterminalView
  productions : List VerifiedProductionView
  tokenMappings : List VerifiedTokenMappingView
  userStartNonterminal : Nat
  startNonterminal : Nat
  eofToken : String
  eofTerminal : Nat
  augmentedTerminal : Nat
  augmentedNonterminal : Nat
  augmentedProduction : Nat
  deriving Repr, DecidableEq, BEq

namespace VerifiedGrammarView

/-- Find the terminal index recorded for a token-constructor name. -/
def tokenTerminal (view : VerifiedGrammarView) (token : String) : Option Nat :=
  (view.tokenMappings.find? (fun mapping => mapping.token == token)).map (·.terminal)

def indexedSymbol [G : GrammarSig]
    [Numbered G.Terminal] [Numbered G.NonTerminal] :
    Symbol G.Terminal G.NonTerminal → VerifiedGrammarSymbol
  | .T terminal => .terminal (Numbered.toFin terminal).val
  | .NT nonterminal => .nonterminal (Numbered.toFin nonterminal).val

def actualProductions [G : GrammarSig]
    [Numbered G.Terminal] [Numbered G.NonTerminal] [Numbered G.Production] :
    List VerifiedProductionView :=
  (List.finRange (Numbered.card G.Production)).map fun index =>
    let production := Numbered.ofFin index
    { index := index.val
      lhs := (Numbered.toFin (G.prodLhs production)).val
      rhs := (G.prodRhsRev production).reverse.map indexedSymbol
      rhsBinders := []
      actionSource := ""
      semanticAction := "" }

def productionShape (production : VerifiedProductionView) : VerifiedProductionView :=
  { production with rhsBinders := [], actionSource := "", semanticAction := "" }

def augmentationAgrees (view : VerifiedGrammarView) : Bool :=
  view.augmentedTerminal + 1 == view.terminals.length &&
  view.augmentedNonterminal + 1 == view.nonterminals.length &&
  view.augmentedProduction + 1 == view.productions.length &&
  view.startNonterminal == view.augmentedNonterminal &&
  view.eofTerminal == view.augmentedTerminal &&
  match view.productions[view.augmentedProduction]? with
  | some production =>
      production.lhs == view.augmentedNonterminal &&
      production.rhs == [
        .nonterminal view.userStartNonterminal,
        .terminal view.eofTerminal]
  | none => false

/-- Check all structural data that can be reflected from the emitted
`GrammarSig`, together with the generated start/EOF and augmentation metadata.
Names, semantic type strings, and semantic-action names are presentation-only. -/
def structurallyAgrees [G : GrammarSig]
    [Numbered G.Terminal] [Numbered G.NonTerminal] [Numbered G.Production]
    (view : VerifiedGrammarView) (start : G.NonTerminal) (eof : G.Terminal) : Bool :=
  view.terminals.map (·.index) == List.range (Numbered.card G.Terminal) &&
  view.nonterminals.map (·.index) == List.range (Numbered.card G.NonTerminal) &&
  view.productions.map productionShape == actualProductions (G := G) &&
  view.productions.all (fun production =>
    production.rhsBinders.length == production.rhs.length) &&
  view.startNonterminal == (Numbered.toFin start).val &&
  view.eofTerminal == (Numbered.toFin eof).val &&
  view.tokenMappings.all (fun mapping => mapping.terminal < view.terminals.length) &&
  view.tokenTerminal view.eofToken == some view.eofTerminal &&
  augmentationAgrees view

def terminalName (view : VerifiedGrammarView) (index : Nat) : String :=
  match view.terminals[index]? with
  | some terminal => terminal.name
  | none => s!"<terminal {index}>"

def nonterminalName (view : VerifiedGrammarView) (index : Nat) : String :=
  match view.nonterminals[index]? with
  | some nonterminal => nonterminal.name
  | none => s!"<nonterminal {index}>"

def symbolName (view : VerifiedGrammarView) : VerifiedGrammarSymbol → String
  | .terminal index => view.terminalName index
  | .nonterminal index => view.nonterminalName index

def renderRhs (view : VerifiedGrammarView) (rhs : List VerifiedGrammarSymbol) : String :=
  if rhs.isEmpty then "ε" else " ".intercalate (rhs.map view.symbolName)

def renderBoundSymbols (view : VerifiedGrammarView) :
    List VerifiedGrammarSymbol → List (Option String) → List String
  | [], _ => []
  | symbol :: symbols, binder :: binders =>
      let name := view.symbolName symbol
      (binder.map (fun value => value ++ ":" ++ name)).getD name ::
        view.renderBoundSymbols symbols binders
  | symbol :: symbols, [] =>
      view.symbolName symbol :: view.renderBoundSymbols symbols []

def renderBoundRhs (view : VerifiedGrammarView) (production : VerifiedProductionView) : String :=
  if production.rhs.isEmpty then "ε"
  else " ".intercalate (view.renderBoundSymbols production.rhs production.rhsBinders)

def compactActionSource (source : String) : String :=
  ((((source.replace "\r" " ").replace "\n" " ").replace "\t" " ").trimAscii).toString

/-- Render the view as compact, index-annotated BNF. The expression is readable
presentation metadata; the comment names the authoritative generated Lean action. -/
def renderBNF (view : VerifiedGrammarView) : String :=
  let terminalLines := view.terminals.map fun terminal =>
    s!"%terminal [{terminal.index}] {terminal.name} : {terminal.semanticType}"
  let nonterminalLines := view.nonterminals.map fun nonterminal =>
    s!"%nonterminal [{nonterminal.index}] {nonterminal.name} : {nonterminal.semanticType}"
  let header := [
    s!"%start [{view.startNonterminal}] {view.nonterminalName view.startNonterminal}",
    s!"%user-start [{view.userStartNonterminal}] {view.nonterminalName view.userStartNonterminal}",
    s!"%eof-token {view.eofToken} -> [{view.eofTerminal}] {view.terminalName view.eofTerminal}"]
  let productionLines := view.productions.map fun production =>
    s!"[{production.index}] {view.nonterminalName production.lhs} ::= " ++
      view.renderBoundRhs production ++ "    { " ++
      compactActionSource production.actionSource ++ " }  -- " ++ production.semanticAction
  "\n".intercalate (terminalLines ++ nonterminalLines ++ header ++ [""] ++ productionLines)

def markdownCell (value : String) : String :=
  (((value.replace "|" "\\|").replace "\n" " ").trimAscii).toString

/-- Render the view as Markdown tables suitable for generated documentation. -/
def renderMarkdown (view : VerifiedGrammarView) : String :=
  let terminalRows := view.terminals.map fun terminal =>
    s!"| {terminal.index} | {markdownCell terminal.name} | {markdownCell terminal.semanticType} |"
  let nonterminalRows := view.nonterminals.map fun nonterminal =>
    s!"| {nonterminal.index} | {markdownCell nonterminal.name} | {markdownCell nonterminal.semanticType} |"
  let productionRows := view.productions.map fun production =>
    s!"| {production.index} | {markdownCell (view.nonterminalName production.lhs)} | " ++
      s!"{markdownCell (view.renderRhs production.rhs)} | {markdownCell production.semanticAction} |"
  "\n".intercalate ([
    "# Verified grammar",
    "",
    s!"- Start: `[{view.startNonterminal}] {markdownCell (view.nonterminalName view.startNonterminal)}`",
    s!"- User start: `[{view.userStartNonterminal}] {markdownCell (view.nonterminalName view.userStartNonterminal)}`",
    s!"- EOF token: `{markdownCell view.eofToken}` → `[{view.eofTerminal}] {markdownCell (view.terminalName view.eofTerminal)}`",
    "",
    "## Terminals",
    "",
    "| Index | Name | Semantic type |",
    "| ---: | --- | --- |"] ++ terminalRows ++ [
    "",
    "## Nonterminals",
    "",
    "| Index | Name | Semantic type |",
    "| ---: | --- | --- |"] ++ nonterminalRows ++ [
    "",
    "## Productions",
    "",
    "| Index | LHS | RHS | Semantic action |",
    "| ---: | --- | --- | --- |"] ++ productionRows)

end VerifiedGrammarView

end Runtime
