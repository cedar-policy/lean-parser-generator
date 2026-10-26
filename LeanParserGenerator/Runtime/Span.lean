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
Source spans on tokens and semantic values.

A `Span` is a half-open byte range into the parsed input (the string the generated
lexer tokenized), kept as two `String.Pos.Raw` offsets. It is two machine words
with no allocation, because it rides on every stack cell and every token in the
executable parser (docs/DESIGN.md lexer and parser sections).

This is distinct from `Frontend.Span`, which denotes byte offsets into the `.lig`
grammar file. `Runtime.Span` is about the end user's input being parsed.

Line/column is not stored; it is computed from the source string at error-render
time (unverified), so nothing here costs anything unless position rendering is used.
-/


@[expose] public section

namespace Runtime

/-- A half-open byte range into the parsed input. Two `String.Pos.Raw` offsets;
    line/column is derived from the source on demand, never stored. -/
structure Span where
  /-- Byte offset of the first character of the span. -/
  startPos : String.Pos.Raw
  /-- Byte offset one past the last character of the span. -/
  endPos : String.Pos.Raw
  deriving Repr, Inhabited, DecidableEq

/-- The empty/placeholder span (byte 0..0), for callers with no real positions
    (e.g. a hand-built token list). -/
@[reducible] def Span.dummy : Span := ⟨⟨0⟩, ⟨0⟩⟩

/-- The span covering both `a` and `b`, assuming `a` precedes `b`: it starts where
    `a` starts and ends where `b` ends. Used to fold a production's RHS span from
    its first and last symbols (Menhir's `$startpos`/`$endpos` of the whole rule). -/
@[reducible] def Span.merge (a b : Span) : Span := ⟨a.startPos, b.endPos⟩

/-- A zero-width span at a byte offset, for an empty production reducing at the
    current input point (Menhir's "between the previous and next tokens"). -/
@[reducible] def Span.point (p : String.Pos.Raw) : Span := ⟨p, p⟩

/-- A value paired with its source span. The generated lexer emits
    `List (Positioned Tok)`; a caller that does not need positions drops them with
    `·.val`. -/
structure Positioned (α : Type) where
  /-- The underlying value (a token, for the lexer output). -/
  val : α
  /-- Its source span. -/
  span : Span
  deriving Repr, Inhabited

/-- Wrap a value with the dummy span, for a caller with no real positions. -/
@[reducible] def Positioned.dummy (x : α) : Positioned α := Positioned.mk x Span.dummy

/-- Convert a byte offset into a 1-based `(line, column)` in `source`, counting
    characters. Offsets past the end clamp to the final position. Unverified;
    used only for human-readable error rendering. -/
def lineColOf (source : String) (byte : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  let mut b := 0
  for c in source.toList do
    if b ≥ byte then
      return (line, col)
    if c == '\n' then
      line := line + 1
      col := 1
    else
      col := col + 1
    b := b + (String.singleton c).utf8ByteSize
  return (line, col)

/-- Render `span`'s start as `line:col` against `source` (1-based). -/
def Span.lineCol (span : Span) (source : String) : Nat × Nat :=
  lineColOf source span.startPos.byteIdx

end Runtime
