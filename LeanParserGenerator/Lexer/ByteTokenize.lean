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
The runtime byte tokenizer over `String.toUTF8`.

`Lexer/ByteScan.lean` gives the `ByteDFA` and `DFA.byteScan`. This file wraps a
`CompiledFlat` with per-mode `ByteDFA`s (`CompiledByte`) and runs the tokenizer over
`input.toUTF8` by byte index, slicing lexemes with `ByteArray.extract` +
`String.fromUTF8!`. It is the fast runtime path; `Lexer/ByteValidator.lean` carries
the equivalence to the flat/spec tokenizer (in progress).
-/
public import LeanParserGenerator.Lexer.ByteScan
public import LeanParserGenerator.Lexer.FlatTokenize


@[expose] public section

namespace Lexer

variable {Tok : Type}

/-- Per-mode byte tables plus the shared `CompiledFlat` base (for actions, start,
    eof, and the `needsText` lexeme-skip flags). -/
structure CompiledByte (Tok : Type) where
  /-- The flat compilation (base + flat tables + textDep). -/
  flat : CompiledFlat Tok
  /-- One byte table per mode, index-aligned with `flat.base.dfas`. -/
  bytes : Array ByteDFA

/-- Build a `CompiledByte` by byte-expanding each mode's flat table (untrusted). -/
def CompiledByte.ofFlat (cf : CompiledFlat Tok) : CompiledByte Tok :=
  { flat := cf, bytes := cf.flats.map ByteDFA.byteOfFlat }

/-- The byte tokenization loop over `bytes` (= `input.toUTF8`) by byte index.
    Mirrors `tokenizeFlatStrAux` but scans with `DFA.byteScan` and slices lexemes by
    byte range. `cpos` counts bytes for error reporting. -/
def tokenizeByteAux (cb : CompiledByte Tok) (bytes : ByteArray) :
    Nat → Nat → Nat → List Nat → List Tok → Except LexError (List Tok)
  | 0, _, cpos, _, _ => .error { pos := cpos, char := none }
  | fuel + 1, i, cpos, stack, acc =>
      if i ≥ bytes.size then
        match stack with
        | [_] =>
            match cb.flat.base.eofToken with
            | some tok => .ok (tok :: acc).reverse
            | none => .ok acc.reverse
        | _ => .error { pos := cpos, char := none }
      else
        let mode := stack.headD cb.flat.base.start
        let bdfa := cb.bytes.getD mode default
        match DFA.byteScan bdfa bytes i with
        | some (rule, endi) =>
            if endi ≤ i then .error { pos := cpos, char := none }
            else
              let matched :=
                bif cb.flat.needsText mode rule then
                  String.fromUTF8! (bytes.extract i endi)
                else ""
              let act := (cb.flat.base.acts.getD mode #[]).getD rule (fun _ => {})
              let a := act matched
              let acc := match a.emit with | some tok => tok :: acc | none => acc
              let stack := match a.trans with
                | .stay => stack | .push m => m :: stack | .pop => stack.tail
              tokenizeByteAux cb bytes fuel endi (endi) stack acc
        | none => .error { pos := cpos, char := none }

/-- The byte tokenizer entry point: scan `input.toUTF8` from byte 0. Fuel is the byte
    count (each token consumes ≥ 1 byte). -/
def tokenizeByte (cb : CompiledByte Tok) (input : String) : Except LexError (List Tok) :=
  let bytes := input.toUTF8
  tokenizeByteAux cb bytes (bytes.size + 1) 0 0 [cb.flat.base.start] []

end Lexer
