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
public import cedarschema.CedarSchemaParserRoundtrip
meta import cedarschema.CedarSchemaParserRoundtrip

public section

open CedarSchemaParserRoundtrip

/-! The Cedar-schema parser roundtrip is proven hole-free in
`CedarSchemaParserRoundtrip` over the user corpus `CedarSchemaUnparse.corpus`. This
test confirms the guarantees are non-vacuous and re-states the three proven facts. -/

/-- The corpus has witnesses, so the roundtrip theorems are not vacuous. -/
example : 0 < corpus.length := by native_decide

/-- Token-level parser roundtrip, over the whole corpus. -/
example : corpus.all (fun t => parseRoundtrip t == some t) = true := roundtrip_corpus

/-- Formatter idempotence (space/newline/tab), over the whole corpus. -/
example :
    corpus.all (fun t =>
      let toks := CedarSchemaUnparse.unparseSchema t
      (relex " " toks == some (toks ++ [Tok.EOF]))
        && (relex "\n" toks == relex " " toks)
        && (relex "\t" toks == relex " " toks)) = true := formatter_idempotence

/-- Full AST↔source roundtrip (space and newline), over the whole corpus. -/
example :
    corpus.all (fun t =>
      (fullRoundtrip " " t == some t) && (fullRoundtrip "\n" t == some t)) = true :=
  full_roundtrip_corpus
