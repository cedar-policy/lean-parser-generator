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
A Menhir `--list-errors`-style enumeration of the error states of a generated
parser.

Menhir's `--list-errors` walks the automaton and, for every state in which a
syntax error can occur, prints the set of terminals that would have been accepted
there, producing a `.messages` template the user fills in with custom messages
(later compiled by `--compile-errors` into a `state → message` function). Our
generated parsers accept exactly such a `messages : Nat → Option String` override
in `errorMessage`, so this command produces the template that feeds it.

This is an untrusted convenience over the plain `Construct.Tables`: it reports,
for each reachable state that consults its lookahead (i.e. has no default
reduction) and has at least one rejecting terminal, the state number and the
terminals it accepts. The state numbers match the generated parser's LR states,
so an entry `## State 7` corresponds to `fun st => if st == 7 then some "…"`.
-/
public import LeanParserGenerator.Emit.Codegen


@[expose] public section

namespace Emit

open Frontend Construct IR

/-- The readable name of terminal index `i` for a grammar whose source terminal
    count is `sourceNumT`; the augmented end marker `$` sits at index
    `sourceNumT`. -/
def terminalNameOf (s : Surface) (sourceNumT i : Nat) : String :=
  if i < sourceNumT then (s.tokens[i]?.map (·.name)).getD s!"terminal {i}"
  else if i == sourceNumT then "end of input"
  else s!"terminal {i}"

/-- States reachable from state `0` following `shift` action edges and `goto`
    edges. Uses a fuel bound equal to the state count (each state is enqueued at
    most once). -/
def reachableStates (tables : Tables) : Array Bool := Id.run do
  let n := tables.numStates
  let mut seen : Array Bool := Array.replicate n false
  if n = 0 then return seen
  seen := seen.set! 0 true
  let mut frontier : Array Nat := #[0]
  let mut fuel := n
  while !frontier.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let mut next : Array Nat := #[]
    for s in frontier do
      for a in tables.action.getD s #[] do
        match a with
        | .shift s' => if s' < n && !(seen.getD s' false) then
            seen := seen.set! s' true; next := next.push s'
        | _ => pure ()
      for g in tables.goto.getD s #[] do
        match g with
        | some s' => if s' < n && !(seen.getD s' false) then
            seen := seen.set! s' true; next := next.push s'
        | none => pure ()
    frontier := next
  return seen

/-- One error-state entry: the state, the terminals it accepts, and the terminals
    on which it rejects. -/
structure ErrorState where
  state : Nat
  expected : Array String
  rejecting : Array String
  deriving Repr, Inhabited

/-- Enumerate the reachable error states (those with no default reduction that
    reject at least one terminal). -/
def errorStates (s : Surface) (prepared : PreparedGrammar) : Array ErrorState := Id.run do
  let tables := prepared.tables
  let augNumT := prepared.augmented.numTerminals
  let sourceNumT := prepared.source.numTerminals
  let reach := reachableStates tables
  let mut result : Array ErrorState := #[]
  for st in [0:tables.numStates] do
    if reach.getD st false && (tables.defaultReduce.getD st none).isNone then
      let row := tables.action.getD st #[]
      let mut expected : Array String := #[]
      let mut rejecting : Array String := #[]
      for t in [0:augNumT] do
        match row.getD t Act.error with
        | .error => rejecting := rejecting.push (terminalNameOf s sourceNumT t)
        | _ => expected := expected.push (terminalNameOf s sourceNumT t)
      if !expected.isEmpty && !rejecting.isEmpty then
        result := result.push { state := st, expected, rejecting }
  return result

/-- Render the error states as a Menhir `.messages`-style template. -/
def renderErrorList (s : Surface) (prepared : PreparedGrammar) : String := Id.run do
  let states := errorStates s prepared
  let mut lines : Array String := #[
    s!"# Syntax-error states for this grammar ({states.size} state(s) can reject).",
    "# Fill in a message under each state and pass it to the generated parser's",
    "# `errorMessage` via `messages := fun st => …` (cf. Menhir --compile-errors).",
    ""]
  for es in states do
    lines := lines.push s!"## State {es.state}"
    lines := lines.push s!"## expected one of: {", ".intercalate es.expected.toList}"
    lines := lines.push s!"## rejects: {", ".intercalate es.rejecting.toList}"
    lines := lines.push "<YOUR SYNTAX ERROR MESSAGE HERE>"
    lines := lines.push ""
  return "\n".intercalate lines.toList

end Emit
