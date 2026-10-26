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
This module defines the intermediate representation of the grammar: the grammar
in the DSL is parsed into an `IR.Grammar`, then the `IR.Grammar` is used to
generate code.

Building the IR requires deciding how to index the various constructs of the grammar:
  * terminals are `0 .. numTerminals - 1`;
  * nonterminals are `0 .. numNonterminals - 1`;
  * productions are indexed by their position in `prods`;
  * `start` is the index of the start **nonterminal**.
All the code generation modules then use the same indexing. Names are carried
only for pretty-printing / diagnostics. Carrying the name also matters so that we
can generate code that "shows" what is being verified.
-/


@[expose] public section

namespace IR

/--
  A grammar symbol (terminal or non terminal).
  For functions that give information about what that specific symbol
  represents in the grammar, see `Grammar.prodsFor` and `Grammar.symName`.
 -/
inductive Sym where
  | term : Nat → Sym
  | nonterm : Nat → Sym
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Sym

/-- Is this symbol a terminal? -/
def isTerm : Sym → Bool
  | .term _ => true
  | .nonterm _ => false

/-- The underlying index, ignoring the terminal/nonterminal tag. -/
def idx : Sym → Nat
  | .term i => i
  | .nonterm i => i

end Sym

/-- A production `lhs → rhs`, with `rhs` in natural left-to-right order. -/
structure Prod where
  /-- Left-hand side: a nonterminal index. -/
  lhs : Nat
  /-- Right-hand side symbols, left to right. -/
  rhs : List Sym
  deriving DecidableEq, Repr, Inhabited

/-- A whole grammar as plain data. -/
structure Grammar where
  /-- Number of terminals; valid terminal indices are `0 .. numTerminals-1`. -/
  numTerminals : Nat
  /-- Number of nonterminals; valid indices are `0 .. numNonterminals-1`. -/
  numNonterminals : Nat
  /-- Productions, indexed by position. -/
  prods : Array Prod
  /-- The start nonterminal's index. -/
  start : Nat
  /-- Optional terminal names (for diagnostics); `termNames[i]` is the name of terminal
  with index `i`. -/
  termNames : Array String := #[]
  /-- Optional nonterminal names (for diagnostics). -/
  nontermNames : Array String := #[]
  deriving Repr, Inhabited

namespace Grammar

/-- All production indices `0 .. prods.size - 1`. -/
def prodIdxs (g : Grammar) : List Nat := (List.range g.prods.size)

/-- The productions whose left-hand side is nonterminal `nt`, as `(index, prod)`. -/
def prodsFor (g : Grammar) (nt : Nat) : List (Nat × Prod) :=
  g.prodIdxs.filterMap (fun i =>
    match g.prods[i]? with
    | some p => if p.lhs = nt then some (i, p) else none
    | none => none)

/-- Pretty-print a symbol using the grammar's name tables when available. -/
def symName (g : Grammar) : Sym → String
  | .term i => g.termNames[i]?.getD s!"t{i}"
  | .nonterm i => g.nontermNames[i]?.getD s!"N{i}"

end Grammar

end IR
