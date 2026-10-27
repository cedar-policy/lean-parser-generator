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
import all imp.ImpVerified
public import imp.ImpParserRoundtrip

@[expose] public section

namespace ImpParserRoundtripProof

open Imp ImpUnparse Runtime Runtime.Grammar

noncomputable def aexpTree : (expression : AExp) →
    ParseTree (G := ImpVerified.grammarInst)
      (.NT (⟨4, by omega⟩ : ImpVerified.NonTerminal)) (unparseAExp expression)
  | .num value =>
      ImpVerified.parseTreeProduction16
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction21 value))
  | .var name =>
      ImpVerified.parseTreeProduction16
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction20 name))
  | .add lhs rhs =>
      let inner := ImpVerified.parseTreeProduction14 (aexpTree lhs)
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction19 (aexpTree rhs)))
      ImpVerified.parseTreeProduction16
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction19 inner))
  | .sub lhs rhs =>
      let inner := ImpVerified.parseTreeProduction15 (aexpTree lhs)
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction19 (aexpTree rhs)))
      ImpVerified.parseTreeProduction16
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction19 inner))
  | .mul lhs rhs =>
      let inner := ImpVerified.parseTreeProduction17
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction19 (aexpTree lhs)))
        (ImpVerified.parseTreeProduction19 (aexpTree rhs))
      ImpVerified.parseTreeProduction16
        (ImpVerified.parseTreeProduction18
          (ImpVerified.parseTreeProduction19
            (ImpVerified.parseTreeProduction16 inner)))

noncomputable def bexpTree : (expression : BExp) →
    ParseTree (G := ImpVerified.grammarInst)
      (.NT (⟨2, by omega⟩ : ImpVerified.NonTerminal)) (unparseBExp expression)
  | .tru => ImpVerified.parseTreeProduction7 ImpVerified.parseTreeProduction8
  | .fls => ImpVerified.parseTreeProduction7 ImpVerified.parseTreeProduction9
  | .le lhs rhs =>
      ImpVerified.parseTreeProduction7
        (ImpVerified.parseTreeProduction13
          (ImpVerified.parseTreeProduction7
            (ImpVerified.parseTreeProduction11 (aexpTree lhs) (aexpTree rhs))))
  | .eq lhs rhs =>
      ImpVerified.parseTreeProduction7
        (ImpVerified.parseTreeProduction13
          (ImpVerified.parseTreeProduction7
            (ImpVerified.parseTreeProduction12 (aexpTree lhs) (aexpTree rhs))))
  | .not value =>
      let inner := ImpVerified.parseTreeProduction10
        (ImpVerified.parseTreeProduction13 (bexpTree value))
      ImpVerified.parseTreeProduction7
        (ImpVerified.parseTreeProduction13
          (ImpVerified.parseTreeProduction7 inner))
  | .and lhs rhs =>
      let inner := ImpVerified.parseTreeProduction6
        (ImpVerified.parseTreeProduction13 (bexpTree lhs))
        (ImpVerified.parseTreeProduction7
          (ImpVerified.parseTreeProduction13 (bexpTree rhs)))
      ImpVerified.parseTreeProduction7
        (ImpVerified.parseTreeProduction13 inner)

mutual

noncomputable def comTree : (command : PrintableCom) →
    ParseTree (G := ImpVerified.grammarInst)
      (.NT (⟨0, by omega⟩ : ImpVerified.NonTerminal)) (unparsePrintableCom command)
  | .last stmt => ImpVerified.parseTreeProduction1 (stmtTree stmt)
  | .seq stmt rest => ImpVerified.parseTreeProduction0 (stmtTree stmt) (comTree rest)

noncomputable def stmtTree : (statement : PrintableStmt) →
    ParseTree (G := ImpVerified.grammarInst)
      (.NT (⟨1, by omega⟩ : ImpVerified.NonTerminal)) (unparsePrintableStmt statement)
  | .skip => ImpVerified.parseTreeProduction2
  | .assign name value => ImpVerified.parseTreeProduction3 name (aexpTree value)
  | .ite cond thenBranch elseBranch =>
      ImpVerified.parseTreeProduction4 (bexpTree cond) (comTree thenBranch)
        (comTree elseBranch)
  | .while cond body =>
      ImpVerified.parseTreeProduction5 (bexpTree cond) (comTree body)

end

theorem aexpTree_sem (expression : AExp) : ptSem (aexpTree expression) = expression := by
  induction expression with
  | num value =>
      rw [show aexpTree (AExp.num value)
            = ImpVerified.parseTreeProduction16
                (ImpVerified.parseTreeProduction18
                  (ImpVerified.parseTreeProduction21 value)) from rfl]
      erw [ImpVerified.parseTreeProduction16_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction21_sem]
      rfl
  | var name =>
      rw [show aexpTree (AExp.var name)
            = ImpVerified.parseTreeProduction16
                (ImpVerified.parseTreeProduction18
                  (ImpVerified.parseTreeProduction20 name)) from rfl]
      erw [ImpVerified.parseTreeProduction16_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction20_sem]
      rfl
  | add lhs rhs ihl ihr =>
      rw [show aexpTree (AExp.add lhs rhs)
            = ImpVerified.parseTreeProduction16
                (ImpVerified.parseTreeProduction18
                  (ImpVerified.parseTreeProduction19
                    (ImpVerified.parseTreeProduction14 (aexpTree lhs)
                      (ImpVerified.parseTreeProduction18
                        (ImpVerified.parseTreeProduction19 (aexpTree rhs)))))) from rfl]
      erw [ImpVerified.parseTreeProduction16_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction19_sem, ImpVerified.parseTreeProduction14_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction19_sem,
        ihl, ihr]
      rfl
  | sub lhs rhs ihl ihr =>
      rw [show aexpTree (AExp.sub lhs rhs)
            = ImpVerified.parseTreeProduction16
                (ImpVerified.parseTreeProduction18
                  (ImpVerified.parseTreeProduction19
                    (ImpVerified.parseTreeProduction15 (aexpTree lhs)
                      (ImpVerified.parseTreeProduction18
                        (ImpVerified.parseTreeProduction19 (aexpTree rhs)))))) from rfl]
      erw [ImpVerified.parseTreeProduction16_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction19_sem, ImpVerified.parseTreeProduction15_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction19_sem,
        ihl, ihr]
      rfl
  | mul lhs rhs ihl ihr =>
      rw [show aexpTree (AExp.mul lhs rhs)
            = ImpVerified.parseTreeProduction16
                (ImpVerified.parseTreeProduction18
                  (ImpVerified.parseTreeProduction19
                    (ImpVerified.parseTreeProduction16
                      (ImpVerified.parseTreeProduction17
                        (ImpVerified.parseTreeProduction18
                          (ImpVerified.parseTreeProduction19 (aexpTree lhs)))
                        (ImpVerified.parseTreeProduction19 (aexpTree rhs)))))) from rfl]
      erw [ImpVerified.parseTreeProduction16_sem, ImpVerified.parseTreeProduction18_sem, ImpVerified.parseTreeProduction19_sem, ImpVerified.parseTreeProduction16_sem, ImpVerified.parseTreeProduction17_sem, ImpVerified.parseTreeProduction18_sem,
        ImpVerified.parseTreeProduction19_sem, ImpVerified.parseTreeProduction19_sem, ihl, ihr]
      rfl

theorem bexpTree_sem (expression : BExp) : ptSem (bexpTree expression) = expression := by
  induction expression with
  | tru =>
      rw [show bexpTree BExp.tru
            = ImpVerified.parseTreeProduction7 ImpVerified.parseTreeProduction8 from rfl]
      erw [ImpVerified.parseTreeProduction7_sem]
      with_unfolding_all rfl
  | fls =>
      rw [show bexpTree BExp.fls
            = ImpVerified.parseTreeProduction7 ImpVerified.parseTreeProduction9 from rfl]
      erw [ImpVerified.parseTreeProduction7_sem]
      with_unfolding_all rfl
  | le lhs rhs =>
      rw [show bexpTree (BExp.le lhs rhs)
            = ImpVerified.parseTreeProduction7
                (ImpVerified.parseTreeProduction13
                  (ImpVerified.parseTreeProduction7
                    (ImpVerified.parseTreeProduction11 (aexpTree lhs) (aexpTree rhs)))) from rfl]
      erw [ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction13_sem, ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction11_sem, aexpTree_sem, aexpTree_sem]
      rfl
  | eq lhs rhs =>
      rw [show bexpTree (BExp.eq lhs rhs)
            = ImpVerified.parseTreeProduction7
                (ImpVerified.parseTreeProduction13
                  (ImpVerified.parseTreeProduction7
                    (ImpVerified.parseTreeProduction12 (aexpTree lhs) (aexpTree rhs)))) from rfl]
      erw [ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction13_sem, ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction12_sem, aexpTree_sem, aexpTree_sem]
      rfl
  | not value ih =>
      rw [show bexpTree (BExp.not value)
            = ImpVerified.parseTreeProduction7
                (ImpVerified.parseTreeProduction13
                  (ImpVerified.parseTreeProduction7
                    (ImpVerified.parseTreeProduction10
                      (ImpVerified.parseTreeProduction13 (bexpTree value))))) from rfl]
      erw [ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction13_sem, ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction10_sem, ImpVerified.parseTreeProduction13_sem, ih]
      rfl
  | and lhs rhs ihl ihr =>
      rw [show bexpTree (BExp.and lhs rhs)
            = ImpVerified.parseTreeProduction7
                (ImpVerified.parseTreeProduction13
                  (ImpVerified.parseTreeProduction6
                    (ImpVerified.parseTreeProduction13 (bexpTree lhs))
                    (ImpVerified.parseTreeProduction7
                      (ImpVerified.parseTreeProduction13 (bexpTree rhs))))) from rfl]
      erw [ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction13_sem, ImpVerified.parseTreeProduction6_sem, ImpVerified.parseTreeProduction13_sem, ImpVerified.parseTreeProduction7_sem, ImpVerified.parseTreeProduction13_sem,
        ihl, ihr]
      rfl

mutual

theorem comTree_sem (command : PrintableCom) :
    ptSem (comTree command) = command.toCom := by
  cases command with
  | last stmt =>
      simp only [comTree, PrintableCom.toCom]
      erw [ImpVerified.parseTreeProduction1_sem]
      exact stmtTree_sem stmt
  | seq stmt rest =>
      simp only [comTree, PrintableCom.toCom]
      erw [ImpVerified.parseTreeProduction0_sem, stmtTree_sem, comTree_sem]
      rfl

theorem stmtTree_sem (statement : PrintableStmt) :
    ptSem (stmtTree statement) = statement.toCom := by
  cases statement with
  | skip =>
      simp only [stmtTree, PrintableStmt.toCom]
      erw [ImpVerified.parseTreeProduction2_sem]
      rfl
  | assign name value =>
      simp only [stmtTree, PrintableStmt.toCom]
      erw [ImpVerified.parseTreeProduction3_sem, aexpTree_sem]
      rfl
  | ite cond thenBranch elseBranch =>
      simp only [stmtTree, PrintableStmt.toCom]
      erw [ImpVerified.parseTreeProduction4_sem, bexpTree_sem, comTree_sem, comTree_sem]
      rfl
  | «while» cond body =>
      simp only [stmtTree, PrintableStmt.toCom]
      erw [ImpVerified.parseTreeProduction5_sem, bexpTree_sem, comTree_sem]
      rfl

end

noncomputable def certificate (command : PrintableCom) :
    ImpParserRoundtrip.Certificate (unparsePrintableCom command) command.toCom := by
  refine { tree := ?_, semantics := ?_ }
  · with_unfolding_all exact ImpVerified.parseTreeProduction22 (comTree command)
  · show ptSem (ImpVerified.parseTreeProduction22 (comTree command)) = command.toCom
    erw [ImpVerified.parseTreeProduction22_sem]
    exact comTree_sem command

/-- Universal token-level parser roundtrip for the grammar-shaped IMP command type. -/
theorem parse_roundtrip (command : PrintableCom) :
    ImpParser.parse
      ((unparsePrintableCom command ++ [Tok.EOF]).map Positioned.dummy)
      (certificate command).logFuel = some command.toCom :=
  ImpParserRoundtrip.parse_certificate (certificate command)

end ImpParserRoundtripProof
