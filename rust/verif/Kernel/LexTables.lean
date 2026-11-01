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

import Kernel.LexBody
import Kernel.Tables
import Spec.LexCheck

/-!
The kernel's `lex`, called with tables that simulate a Lean lexer DFA, runs that DFA.

`lex_run` combines `lex_spec` (the Aeneas translation is `Spec.llex`) with `Spec.llex_rules`
(`Spec.llex` reports the rule-level run `Spec.ruleRun` of the Lean DFA). The conditions are
checked per grammar by the kernel: `lwfCheck` gives `LWf`, `packCheck` says that numbers packed
from the tables are the Aeneas arrays (so that `Spec.lexSimCheck` reads them fast), and
`Spec.lexSimCheck` gives `LexSim`.
-/

open Aeneas Aeneas.Std Result
open lpg_kernel

namespace lpg_kernel.Proof

/-- The bounds that `LWf` asks for, as a computation over the Aeneas arrays. -/
def lwfCheck {NC R NR : Usize} (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R)
    (accept : Array U16 R) (start : Usize) : Bool :=
  decide (start.val < R.val) && cls.val.all (fun x => decide (x.val < NC.val)) &&
  trans.val.all (fun r => r.val.all (fun x => decide (x.val < R.val))) &&
  accept.val.all (fun x => decide (x.val ≤ NR.val))

theorem lwf_of_check {NC R NR : Usize} (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (accept : Array U16 R) (start : Usize)
    (h : lwfCheck (NR := NR) cls trans accept start = true) :
    LWf (NR := NR) cls trans accept start := by
  simp only [lwfCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun b x hx => h2 x (List.mem_of_getElem? hx),
    fun s c r x hr hx => h3 r (List.mem_of_getElem? hr) x (List.mem_of_getElem? hx),
    fun s x hx => h4 x (List.mem_of_getElem? hx)⟩

/-- The packed numbers are the Aeneas arrays. -/
def packCheck {NC R : Usize} (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R)
    (accept : Array U16 R) (clsP : Nat) (transP : List Nat) (accP : Nat) : Bool :=
  cls.val.map (·.val) == (List.range 256).map (fun b => (clsP >>> (8 * b)) % 256) &&
  trans.val.map (fun r => r.val.map (·.val)) ==
    (List.range R.val).map (fun s =>
      (List.range NC.val).map (fun c => (transP.getD s 0 >>> (16 * c)) % 65536)) &&
  accept.val.map (·.val) == (List.range R.val).map (fun s => (accP >>> (16 * s)) % 65536)

theorem getD_range_map (f : Nat → Nat) (n i : Nat) :
    (((List.range n).map f)[i]?).getD 0 = if i < n then f i else 0 := by
  by_cases h : i < n
  · simp [h]
  · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)]; simp [h]

theorem lexDfaOf_eq_packed {NC R : Usize} (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (accept : Array U16 R) (start accept_from : Usize)
    (clsP : Nat) (transP : List Nat) (accP : Nat)
    (h : packCheck cls trans accept clsP transP accP = true) :
    lexDfaOf cls trans accept start accept_from =
      Spec.packedDfa NC.val R.val clsP transP accP start.val accept_from.val := by
  simp only [packCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold lexDfaOf Spec.packedDfa
  congr 1
  · funext b
    have : cellB cls b 0 = (((cls.val.map (·.val))[b]?).getD 0) := by
      unfold cellB; rw [List.getElem?_map]
    rw [this, h1, getD_range_map]
  · funext s c
    rw [cell2_eq, h2]
    unfold Spec.rowCell
    by_cases hs : s < R.val
    · rw [List.getElem?_map, List.getElem?_range hs]
      simp only [Option.map_some, Option.bind_some]
      rw [getD_range_map]
      by_cases hc : c < NC.val <;> simp [hs, hc]
    · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)]
      simp [hs]
  · funext s
    rw [cell1_eq, h3, getD_range_map]

/-- The dead state of packed tables is dead. -/
def deadCheck (nc : Nat) (transP : List Nat) : Bool :=
  (List.range nc).all (fun c => (transP.getD 0 0 >>> (16 * c)) % 65536 == 0)

theorem packed_dead (nc nr clsP : Nat) (transP : List Nat) (accP start acceptFrom : Nat)
    (h : deadCheck nc transP = true) :
    ∀ c, (Spec.packedDfa nc nr clsP transP accP start acceptFrom).trans 0 c = 0 := by
  intro c
  simp only [Spec.packedDfa]
  split
  · rename_i hc
    simp only [deadCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    simpa using h c hc.2
  · rfl

/-- **The kernel's `lex` runs the Lean DFA.** For tables that satisfy `LWf` and simulate the
    Lean DFA `dfa` (`LexSim`), on the UTF-8 bytes of the characters `cs` (at most `u32::MAX` of
    them), `lex` ends as the Rust report of the rule-level run `Spec.ruleRun dfa` reads it
    (`Spec.rustOut`): the tokens of the rules that are not skipped, with their byte spans, and
    then the end-of-input token, or the byte position of the first error. -/
theorem lex_run {NC R NR : Usize} (src : Slice U8) (out : alloc.vec.Vec Token)
    (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R) (accept : Array U16 R)
    (start accept_from : Usize) (rule_term : Array U16 NR) (eof : U16)
    (hw : LWf (NR := NR) cls trans accept start)
    (dfa : Lexer.DFA) (φ : Nat → Nat)
    (hsim : Spec.LexSim (lexDfaOf cls trans accept start accept_from) dfa φ)
    (cs : List Char) (hsrc : bytesOf src = Spec.encChars cs)
    (hlen : src.val.length ≤ 2 ^ 32 - 1)
    (hroom : out.val.length + src.val.length < Usize.max) :
    lex src out cls trans accept start accept_from rule_term eof ⦃ res out' =>
      LexRel (Spec.rustOut (lexTablesOf cls trans accept start accept_from rule_term eof)
          src.val.length (out.val.map ltokNat) (Spec.ruleRun dfa (cs.length + 1) cs 0)).1 res ∧
      out'.val.map ltokNat = (Spec.rustOut (lexTablesOf cls trans accept start accept_from
          rule_term eof) src.val.length (out.val.map ltokNat)
          (Spec.ruleRun dfa (cs.length + 1) cs 0)).2 ⦄ := by
  have hl : (bytesOf src).length = src.val.length := by simp [bytesOf]
  have hrun := Spec.llex_rules (lexTablesOf cls trans accept start accept_from rule_term eof) dfa
    φ hsim (bytesOf src) (cs.length + 1) cs 0 (out.val.map ltokNat) (Nat.le_refl _)
    (Nat.zero_le _) (by simpa using hsrc)
  have hllex : Spec.llex (lexTablesOf cls trans accept start accept_from rule_term eof)
      (bytesOf src) (out.val.map ltokNat) =
      Spec.rustOut (lexTablesOf cls trans accept start accept_from rule_term eof)
        src.val.length (out.val.map ltokNat) (Spec.ruleRun dfa (cs.length + 1) cs 0) := by
    unfold Spec.llex
    rw [hl, if_neg (by omega)]
    rw [← hl, ← hrun, Nat.sub_zero]
  rw [← hllex]
  exact lex_spec src out cls trans accept start accept_from rule_term eof hw hroom

end lpg_kernel.Proof
