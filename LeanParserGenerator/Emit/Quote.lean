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
Emit generated Lean source as `Syntax` and render it to text.

The backends build the module *structure* (defs, matches, table arrays) as
`Lean.Syntax` and pretty-print it, so a malformed emission fails against Lean's
grammar when the generator runs, not when the generated file is later compiled.

Two subtleties (see DESIGN §16.1):
* Every generated name must be built with `mkIdent`. A name written literally in a
  `` `(…) `` quotation carries a macro scope that `ppCommand` renders as `sem✝`,
  which is invalid source.
* Verbatim embedded-Lean leaves (action bodies, `%type` strings) are not parsed:
  `runParserCategory` only has builtin term parsers and fails on ordinary notation,
  and the generator cannot know a user `%header`'s notation. A leaf is spliced as a
  placeholder ident and substituted with its exact source text after printing.
  Because leaves are substituted, not parsed, the emission env only needs `Init`.
-/
public import Lean


@[expose] public section

namespace Emit.Quote

open Lean Elab Command PrettyPrinter

/-- Emission monad: `CommandElabM` threading a pool of verbatim leaf strings. -/
abbrev EmitM := StateT (Array String) CommandElabM

/-- Placeholder identifier for opaque leaf `n`. -/
def leafIdent (n : Nat) : Ident := mkIdent (Name.mkSimple s!"__ligLeaf{n}__")

/-- Record a verbatim leaf and return its placeholder identifier. -/
def freshLeaf (source : String) : EmitM Ident := do
  let pool ← get
  set (pool.push source)
  return leafIdent pool.size

def leafToken (n : Nat) : String := s!"__ligLeaf{n}__"

/-- Pretty-print one command to source text. -/
def renderCmd (stx : TSyntax `command) (width : Nat := 116) : CommandElabM String := do
  let fmt ← liftCoreM <| ppCommand stx
  return fmt.pretty (width := width)

/-- Pretty-print a sequence of commands, blank-line separated. -/
def renderCmds (stxs : Array (TSyntax `command)) (width : Nat := 116) : CommandElabM String := do
  let parts ← stxs.mapM (renderCmd · width)
  return "\n\n".intercalate parts.toList

/-- Replace each leaf placeholder with its verbatim source. Fails if a placeholder
    is missing or malformed.

    The previous implementation called `String.replace` once per leaf, each a full
    scan and rebuild of the whole rendered module — `O(leaves × moduleLength)`, the
    dominant cost of generating a large module (minutes for c99). This splits the
    rendered text once on the marker (`O(moduleLength)`), then reassembles the
    segments in one linear join. Every segment after the first begins with a decimal
    index and the closing `__`; its leaf source is spliced verbatim. Leaf text is
    never rescanned, matching the old replace-then-check behavior for well-formed
    emissions. -/
def substituteLeaves (rendered : String) (leaves : Array String) : Except String String := Id.run do
  let marker := "__ligLeaf"
  let segments := rendered.splitOn marker
  match segments with
  | [] => return .ok ""
  | first :: rest =>
    -- Accumulate output pieces in an array and `join` once (a single left fold of
    -- `String ++` on a growing accumulator would reintroduce the quadratic cost).
    let mut pieces : Array String := #[first]
    let mut seen : Array Bool := Array.replicate leaves.size false
    for seg in rest do
      -- `seg` is `<digits>__<tail>`. Read the decimal index, then the tail.
      let cs := seg.toList
      let mut i := 0
      let mut num := 0
      let mut sawDigit := false
      while h : i < cs.length do
        let c := cs[i]
        if c.isDigit then
          num := num * 10 + (c.toNat - '0'.toNat)
          sawDigit := true
          i := i + 1
        else
          break
      -- The digits must be followed immediately by the closing `__`.
      if !sawDigit || !((cs.drop i).take 2 == ['_', '_']) then
        return .error s!"malformed leaf placeholder near `{marker}{seg.take 12}`"
      match leaves[num]? with
      | none => return .error s!"leaf placeholder {marker}{num}__ has no recorded source"
      | some leaf =>
        seen := seen.set! num true
        pieces := pieces.push leaf
        pieces := pieces.push (String.ofList (cs.drop (i + 2)))
    for (_, n) in leaves.zipIdx do
      unless seen[n]! do
        return .error s!"leaf placeholder {leafToken n} was not emitted"
    return .ok (String.join pieces.toList)

/-- Boot an `Init`-only elaboration environment and run an `EmitM` action. -/
unsafe def runEmitUnsafe (act : EmitM String) : IO (Except String (String × Array String)) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {} (trustLevel := 1024)
  let ctx : Command.Context :=
    { fileName := "<lig-codegen>", fileMap := default, snap? := none, cancelTk? := none }
  let st : Command.State := Command.mkState env {} {}
  let res ← (act.run #[]).run ctx |>.run st |>.toIO'
  match res with
  | .ok ((rendered, leaves), _) => return .ok (rendered, leaves)
  | .error e => return .error (← e.toMessageData.toString)

@[implemented_by runEmitUnsafe]
opaque runEmit (act : EmitM String) : IO (Except String (String × Array String))

/-- Run an emission action and substitute the leaves into the rendered module. -/
def emitModule (act : EmitM String) : IO (Except String String) := do
  match ← runEmit act with
  | .error e => return .error e
  | .ok (rendered, leaves) => return substituteLeaves rendered leaves

end Emit.Quote
