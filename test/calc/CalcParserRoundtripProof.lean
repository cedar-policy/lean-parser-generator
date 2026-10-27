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
public import calc.CalcParserRoundtrip
public import calc.CalcLexerRoundtrip

@[expose] public section

namespace CalcParserRoundtripProof

open Calc Runtime
open CalcUnparse

/-- The generated production constructors build the canonical `NUM` derivation
    `NUM → factor → term → expr → S'`. -/
noncomputable def certificate (n : Int) :
    CalcParserRoundtrip.Certificate (unparseInt n) n := by
  let factor := CalcVerified.parseTreeProduction6 n
  let term := CalcVerified.parseTreeProduction4 factor
  let expr := CalcVerified.parseTreeProduction1 term
  let start := CalcVerified.parseTreeProduction7 expr
  refine { tree := ?_, semantics := ?_ }
  · with_unfolding_all exact start
  · with_unfolding_all rfl

/-- Token-level parser roundtrip for every calculator result. -/
theorem parse_roundtrip (n : Int) :
    CalcParserRoundtrip.parseRoundtrip n (certificate n).logFuel = some n :=
  CalcParserRoundtrip.parse_roundtrip n (certificate n)

/-- Calculator values whose `NUM` token can also pass through the lexer. The
    parser-only theorem above has no such restriction. -/
structure PrintableInt where
  value : Int
  token_roundtrippable : CalcLexerRoundtrip.RoundtrippableTok (.NUM value)

instance : Coe PrintableInt Int := ⟨PrintableInt.value⟩

def unparsePrintable (n : PrintableInt) : List Tok := unparseInt n.value

noncomputable def printableCertificate (n : PrintableInt) :
    CalcParserRoundtrip.Certificate (unparsePrintable n) n.value := by
  simpa [unparsePrintable] using certificate n.value

theorem unparse_roundtrippable (n : PrintableInt) :
    Lexer.Forall CalcLexerRoundtrip.RoundtrippableTok (unparsePrintable n) := by
  exact .cons n.token_roundtrippable .nil

/-- Full value → tokens → source → tokens → value roundtrip for every
    `PrintableInt`. -/
theorem full_roundtrip (n : PrintableInt) :
    CalcParserRoundtrip.fullRoundtrip " " n.value (printableCertificate n).logFuel =
      some n.value := by
  unfold CalcParserRoundtrip.fullRoundtrip CalcParserRoundtrip.relex
  have hlex := CalcLexerRoundtrip.render_roundtrip (unparsePrintable n)
    (unparse_roundtrippable n)
  change
    (CalcLexer.tokenizeBare (CalcLexerRoundtrip.render (unparsePrintable n))).toOption.bind
      (fun toks => CalcParser.parse (toks.map Positioned.dummy)
        (printableCertificate n).logFuel) = some n.value
  rw [hlex]
  exact CalcParserRoundtrip.parse_certificate (printableCertificate n)

end CalcParserRoundtripProof
