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
public import spanuse.SpanUseLexer
public import spanuse.SpanUseParser
meta import spanuse.SpanUseLexer
meta import spanuse.SpanUseParser

public section

open SpanUseParser Runtime

/-! An action that reads `x_span`. The `spanuse` grammar's first rule
    `start ::= w=WORD { w_span.endPos.byteIdx - w_span.startPos.byteIdx }` returns
    the byte width of the WORD token's span; the second rule `w=WORD DOT { w }`
    ignores the spans entirely. The generated `sem`/`redv` bind `w_span` (and the
    unused DOT span) with the unused-variable linter disabled, so the
    span-ignoring rule compiles without a warning — this module building is that
    check. -/

/-- Wrap a token with an explicit byte span. -/
private def tokAt (t : Tok) (a b : Nat) : Positioned Tok := ⟨t, ⟨⟨a⟩, ⟨b⟩⟩⟩

-- `WORD` spanning bytes 2..7 (width 5): the action returns the span width.
#guard SpanUseParser.parse [tokAt (.WORD 99) 2 7, tokAt .EOF 7 7] = some 5

-- `WORD DOT`: the span-ignoring rule returns the payload (here 3).
#guard SpanUseParser.parse [tokAt (.WORD 3) 0 4, tokAt .DOT 4 5, tokAt .EOF 5 5] = some 3

-- End-to-end through the generated lexer: `"hello"` is one 5-char WORD.
#guard (SpanUseLexer.tokenize "hello").toOption.bind SpanUseParser.parse = some 5

#eval IO.println "spanuse (x_span-in-action) tests passed."
