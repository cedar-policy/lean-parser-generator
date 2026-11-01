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

import Kernel.ParseBody
import Spec.Lex

/-!
The Aeneas translation of `lpg_kernel::lex` is `Spec.llex`.

`lexTablesOf` reads the kernel's arguments as `Spec.LexTables`, and `LWf` is what they must
satisfy for the Rust not to panic: every state and class they name is in range, and every
accepting state names a rule. The inner loop of `scan` (`self_run`) skips a run of bytes that
leave the state unchanged; `Spec.lscan_run` says that the scan one byte at a time does the
same.
-/

open Aeneas Aeneas.Std Result ControlFlow
open lpg_kernel

namespace lpg_kernel.Proof

/-- A cell of a table of bytes, `d` out of range. -/
def cellB {n : Usize} (a : Array U8 n) (i d : Nat) : Nat :=
  ((a.val[i]?).map (·.val)).getD d

/-- The lexer DFA the kernel is called with, as numbers. -/
def lexDfaOf {NC R : Usize} (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R)
    (accept : Array U16 R) (start accept_from : Usize) : Spec.LexDFA where
  cls := fun b => cellB cls b 0
  trans := fun s c => cell2 trans s c 0
  accept := fun s => cell1 accept s 0
  start := start.val
  acceptFrom := accept_from.val

/-- The lexer tables the kernel is called with, as numbers. -/
def lexTablesOf {NC R NR : Usize} (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R)
    (accept : Array U16 R) (start accept_from : Usize) (rule_term : Array U16 NR) (eof : U16) :
    Spec.LexTables where
  dfa := lexDfaOf cls trans accept start accept_from
  ruleTerm := fun r => cell1 rule_term r 0
  eof := eof.val

def ltokNat (t : Token) : Spec.LTok := ⟨t.rule.val, t.term.val, t.start.val, t.«end».val⟩

/-- The bytes of the source as numbers. -/
def bytesOf (src : Slice U8) : List Nat := src.val.map (·.val)

/-- What the lexer tables must satisfy for `lex` to run without a panic. -/
structure LWf {NC R NR : Usize} (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R)
    (accept : Array U16 R) (start : Usize) : Prop where
  start : start.val < R.val
  cls : ∀ (b : Nat) (x : U8), cls.val[b]? = some x → x.val < NC.val
  trans : ∀ (s c : Nat) (r : Array U16 NC) (x : U16), trans.val[s]? = some r → r.val[c]? = some x →
    x.val < R.val
  accept : ∀ (s : Nat) (x : U16), accept.val[s]? = some x → x.val ≤ NR.val

/-- A Rust result of `lex` and the way `Spec.llex` ends correspond. -/
def LexRel : Spec.LStop → core.result.Result Unit LexFail → Prop
  | .ok, .Ok () => True
  | .noMatch p, .Err (.NoMatch q) => q.val = p
  | .tooLong, .Err .TooLong => True
  | _, _ => False

theorem cellB_of_get? {n : Usize} (a : Array U8 n) (i d : Nat) (x : U8)
    (h : a.val[i]? = some x) : cellB a i d = x.val := by
  simp [cellB, h]

theorem term_skip_val : TERM_SKIP.val = Spec.termSkip := by unfold TERM_SKIP; rfl

theorem rule_eof_val : RULE_EOF.val = Spec.ruleEof := by unfold RULE_EOF; rfl

/-! ### The helpers of `scan` -/

@[step]
theorem record_spec {R : Usize} (row i : Usize) (accept : Array U16 R) (accept_from : Usize)
    (best : U16) (e : Usize) (hrow : row.val < R.val) :
    record row i accept accept_from best e ⦃ r =>
      r.1.val = (if row.val ≥ accept_from.val then cell1 accept row.val 0 else best.val) ∧
      r.2.val = (if row.val ≥ accept_from.val then i.val else e.val) ⦄ := by
  unfold record
  by_cases h : row ≥ accept_from
  · have h' : row.val ≥ accept_from.val := by simpa using h
    simp only [h, ↓reduceIte]
    have hl : row.val < accept.val.length := by
      have := Array.property accept; omega
    step*
    simp only [h', ↓reduceIte, and_true]
    rw [cell1_of_get? _ _ _ i1 (by rw [i1_post]; exact List.getElem?_eq_getElem hl)]
  · have h' : ¬ row.val ≥ accept_from.val := by simpa using h
    simp [h, h']

/-- The transition the Rust computes from the byte at `k`. -/
theorem trans_cell {NC R : Usize} (src : Slice U8) (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (row k : Nat) (hk : k < (bytesOf src).length)
    (i2 : U8) (i3 : Usize) (i4 : U8) (i5 : Usize) (a : Array U16 NC) (i6 : U16) (next : Usize)
    (h2 : src.val[k]? = some i2) (h3 : i3 = UScalar.cast .Usize i2)
    (h4 : cls.val[i3.val]? = some i4)
    (h5 : i5 = UScalar.cast .Usize i4) (ha : trans.val[row]? = some a)
    (h6 : a.val[i5.val]? = some i6) (h7 : next = UScalar.cast .Usize i6) :
    next.val = cell2 trans row (cellB cls ((bytesOf src)[k]'hk) 0) 0 := by
  have hb : (bytesOf src)[k]'hk = i2.val := by
    have : (bytesOf src)[k]? = some i2.val := by simp [bytesOf, h2]
    rw [List.getElem?_eq_getElem hk] at this
    exact Option.some.inj this
  rw [hb]
  have h32 : i3.val = i2.val := by simp [h3]
  have hc : cellB cls i2.val 0 = i5.val := by
    rw [cellB_of_get? cls i2.val 0 i4 (by rw [← h32]; exact h4)]
    simp [h5]
  rw [hc, cell2_of_get? trans _ _ _ a i6 ha h6]
  simp [h7]

/-- The bytes from `i` to `j` leave the state `row` unchanged. -/
def RunOf {NC R : Usize} (src : Slice U8) (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (row i j : Nat) : Prop :=
  ∀ m (h : m < (bytesOf src).length), i ≤ m → m < j →
    cell2 trans row (cellB cls (bytesOf src)[m] 0) 0 = row

@[step]
theorem self_run_spec {NC R : Usize} (src : Slice U8) (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (row i : Usize) (hrow : row.val < R.val)
    (hi : i.val ≤ src.val.length)
    (hcls : ∀ (b : Nat) (x : U8), cls.val[b]? = some x → x.val < NC.val) :
    self_run src cls trans row i ⦃ j =>
      i.val ≤ j.val ∧ j.val ≤ src.val.length ∧ RunOf src cls trans row.val i.val j.val ⦄ := by
  unfold self_run self_run_loop
  apply Aeneas.Std.loop.spec_decr_nat (measure := fun k : Usize => src.val.length - k.val)
    (inv := fun k : Usize => i.val ≤ k.val ∧ k.val ≤ src.val.length ∧
      RunOf src cls trans row.val i.val k.val)
  · rintro k ⟨h1, h2, h3⟩
    unfold self_run_loop.body
    step*
    · -- the class is a column
      have hx : cls.val[i3.val]? = some i4 := by rw [i4_post]; exact List.getElem?_eq_getElem _
      have := hcls _ _ hx
      have h5 : i5.val = i4.val := by simp [i5_post]
      have : a.val.length = NC.val := Array.property a
      simp only [Array.length]; omega
    · -- one more byte of the run
      have hk : k.val < src.val.length := by simpa using ‹k < src.len›
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro m hm hm1 hm2
      by_cases hmk : m < k.val
      · exact h3 m hm hm1 hmk
      · have hmk' : m = k.val := by omega
        subst hmk'
        have := trans_cell src cls trans row.val k.val hm i2 i3 i4 i5 a i6 i7
          (by rw [i2_post]; exact List.getElem?_eq_getElem _) i3_post
          (by rw [i4_post]; exact List.getElem?_eq_getElem _) i5_post
          (by rw [a_post]; exact List.getElem?_eq_getElem _)
          (by rw [i6_post]; exact List.getElem?_eq_getElem _) i7_post
        rw [← this, ‹i7 = row›]
  · exact ⟨Nat.le_refl _, hi, fun m _ h1 h2 => absurd h2 (by omega)⟩

theorem scan_loop_spec {NC R NR : Usize} (src : Slice U8) (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (accept : Array U16 R) (start accept_from : Usize)
    (hw : LWf (NR := NR) cls trans accept start)
    (row i : Usize) (best : U16) (e : Usize) (hrow : row.val < R.val)
    (hi : i.val ≤ src.val.length) :
    scan_loop src cls trans accept accept_from row i best e ⦃ r =>
      (r.1.val, r.2.val) = Spec.lscan (lexDfaOf cls trans accept start accept_from)
        (bytesOf src) ((bytesOf src).length + 1 - i.val) row.val i.val best.val e.val ⦄ := by
  have hlen : (bytesOf src).length = src.val.length := by simp [bytesOf]
  unfold scan_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun x : Usize × Usize × U16 × Usize => src.val.length + 1 - x.2.1.val)
    (inv := fun x : Usize × Usize × U16 × Usize => x.1.val < R.val ∧ x.2.1.val ≤ src.val.length ∧
      Spec.lscan (lexDfaOf cls trans accept start accept_from) (bytesOf src)
        ((bytesOf src).length + 1 - x.2.1.val) x.1.val x.2.1.val x.2.2.1.val x.2.2.2.val =
      Spec.lscan (lexDfaOf cls trans accept start accept_from) (bytesOf src)
        ((bytesOf src).length + 1 - i.val) row.val i.val best.val e.val)
  · rintro ⟨row', i', best', e'⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    have hrec : ∀ (b1 : U16) (e1 : Usize),
        b1.val = (if row'.val ≥ accept_from.val then cell1 accept row'.val 0 else best'.val) →
        e1.val = (if row'.val ≥ accept_from.val then i'.val else e'.val) →
        Spec.lrecord (lexDfaOf cls trans accept start accept_from)
          row'.val i'.val best'.val e'.val = (b1.val, e1.val) := by
      intro b1 e1 hb he
      simp only [Spec.lrecord, lexDfaOf, hb, he]
      by_cases hc : row'.val ≥ accept_from.val <;> simp [hc]
    unfold scan_loop.body
    step*
    · -- the end of the source
      have hge : src.val.length ≤ i'.val := by simpa using ‹i' ≥ src.len›
      rw [← h3, Spec.lscan_end _ _ _ _ _ _ (by omega) (by omega), hrec _ _ best1_post best1_post1]
    · have hx : cls.val[i3.val]? = some i4 := by rw [i4_post]; exact List.getElem?_eq_getElem _
      have := hw.cls _ _ hx
      have h5 : i5.val = i4.val := by simp [i5_post]
      have : a.val.length = NC.val := Array.property a
      simp only [Array.length]; omega
    · -- a dead transition
      have hlt : i'.val < (bytesOf src).length := by
        have : ¬ src.val.length ≤ i'.val := by simpa using ‹¬i' ≥ src.len›
        omega
      have hn := trans_cell src cls trans row'.val i'.val hlt i2 i3 i4 i5 a i6 next
        (by rw [i2_post]; exact List.getElem?_eq_getElem _) i3_post
        (by rw [i4_post]; exact List.getElem?_eq_getElem _) i5_post
        (by rw [a_post]; exact List.getElem?_eq_getElem _)
        (by rw [i6_post]; exact List.getElem?_eq_getElem _) next_post
      have hn0 : next.val = 0 := by rw [‹next = 0#usize›]; rfl
      have hnT : (lexDfaOf cls trans accept start accept_from).trans row'.val
          ((lexDfaOf cls trans accept start accept_from).cls
            ((bytesOf src)[i'.val]'hlt)) = 0 := hn.symm.trans hn0
      rw [← h3, Spec.lscan_step _ _ _ _ _ _ hlt]
      simp only [hnT, ↓reduceIte, hrec _ _ best1_post best1_post1]
    · exact hw.cls
    · -- a run of bytes in the same state
      have hlt : i'.val < (bytesOf src).length := by
        have : ¬ src.val.length ≤ i'.val := by simpa using ‹¬i' ≥ src.len›
        omega
      have hn := trans_cell src cls trans row'.val i'.val hlt i2 i3 i4 i5 a i6 next
        (by rw [i2_post]; exact List.getElem?_eq_getElem _) i3_post
        (by rw [i4_post]; exact List.getElem?_eq_getElem _) i5_post
        (by rw [a_post]; exact List.getElem?_eq_getElem _)
        (by rw [i6_post]; exact List.getElem?_eq_getElem _) next_post
      have hn0 : next.val ≠ 0 := by
        intro h; apply ‹¬next = 0#usize›; apply UScalar.eq_of_val_eq; simpa using h
      have hnr : next.val = row'.val := by rw [‹next = row'›]
      refine ⟨h1, i8_post1, ?_, by omega⟩
      have hnT : (lexDfaOf cls trans accept start accept_from).trans row'.val
          ((lexDfaOf cls trans accept start accept_from).cls
            ((bytesOf src)[i'.val]'hlt)) = row'.val := hn.symm.trans hnr
      rw [← h3, Spec.lscan_step _ _ _ _ _ _ hlt]
      have hr0' : row'.val ≠ 0 := by rw [← hnr]; exact hn0
      simp only [hnT, hr0', ↓reduceIte, hrec _ _ best1_post best1_post1]
      have hr0 : row'.val ≠ 0 := by rw [← hnr]; exact hn0
      rw [show i'.val + 1 = i7.val by omega]
      refine (Spec.lscan_run _ _ _ _ _ _ _ i8_post (by omega) ?_ hr0).symm
      intro m hm hm1 hm2
      exact i8_post2 m hm hm1 hm2
    · -- a transition to another state
      have hlt : i'.val < (bytesOf src).length := by
        have : ¬ src.val.length ≤ i'.val := by simpa using ‹¬i' ≥ src.len›
        omega
      have hn := trans_cell src cls trans row'.val i'.val hlt i2 i3 i4 i5 a i6 next
        (by rw [i2_post]; exact List.getElem?_eq_getElem _) i3_post
        (by rw [i4_post]; exact List.getElem?_eq_getElem _) i5_post
        (by rw [a_post]; exact List.getElem?_eq_getElem _)
        (by rw [i6_post]; exact List.getElem?_eq_getElem _) next_post
      have hn0 : next.val ≠ 0 := by
        intro h; apply ‹¬next = 0#usize›; apply UScalar.eq_of_val_eq; simpa using h
      have hnR : next.val < R.val := by
        have hrA : trans.val[row'.val]? = some a := by
          rw [a_post]; exact List.getElem?_eq_getElem _
        have hcA : a.val[i5.val]? = some i6 := by
          rw [i6_post]; exact List.getElem?_eq_getElem _
        have := hw.trans _ _ a i6 hrA hcA
        have : next.val = i6.val := by simp [next_post]
        omega
      refine ⟨hnR, by omega, ?_, by omega⟩
      have hnT : (lexDfaOf cls trans accept start accept_from).trans row'.val
          ((lexDfaOf cls trans accept start accept_from).cls
            ((bytesOf src)[i'.val]'hlt)) = next.val := hn.symm
      rw [← h3, Spec.lscan_step _ _ _ _ _ _ hlt]
      simp only [hnT, hn0, ↓reduceIte, hrec _ _ best1_post best1_post1, i7_post]
  · exact ⟨hrow, hi, rfl⟩

@[step]
theorem scan_spec {NC R NR : Usize} (src : Slice U8) (pos : Usize) (cls : Array U8 256#usize)
    (trans : Array (Array U16 NC) R) (accept : Array U16 R) (start accept_from : Usize)
    (hw : LWf (NR := NR) cls trans accept start)
    (hpos : pos.val ≤ src.val.length) :
    scan src pos cls trans accept start accept_from ⦃ r =>
      (r.1.val, r.2.val) = Spec.lscanFrom
        (lexDfaOf cls trans accept start accept_from) (bytesOf src) pos.val ⦄ := by
  unfold scan
  exact scan_loop_spec src cls trans accept start accept_from hw start pos 0#u16 pos
    hw.start hpos

theorem lex_loop_spec {NC R NR : Usize} (src : Slice U8) (out : alloc.vec.Vec Token)
    (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R) (accept : Array U16 R)
    (start accept_from : Usize) (rule_term : Array U16 NR) (eof : U16)
    (hw : LWf (NR := NR) cls trans accept start)
    (n : Usize) (hn : n.val = src.val.length) (hn32 : n.val ≤ 2 ^ 32 - 1)
    (hroom : out.val.length + src.val.length < Usize.max) :
    lex_loop src out cls trans accept start accept_from rule_term eof n 0#usize ⦃ r =>
      LexRel (Spec.llexGo (lexTablesOf cls trans accept start accept_from rule_term eof)
          (bytesOf src) ((bytesOf src).length + 1) 0 (out.val.map ltokNat)).1 r.1 ∧
      r.2.val.map ltokNat = (Spec.llexGo (lexTablesOf cls trans accept start accept_from rule_term
          eof) (bytesOf src) ((bytesOf src).length + 1) 0 (out.val.map ltokNat)).2 ⦄ := by
  have hlen : (bytesOf src).length = src.val.length := by simp [bytesOf]
  unfold lex_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun x : alloc.vec.Vec Token × Usize => src.val.length + 1 - x.2.val)
    (inv := fun x : alloc.vec.Vec Token × Usize => x.2.val ≤ src.val.length ∧
      x.1.val.length ≤ out.val.length + x.2.val ∧
      Spec.llexGo (lexTablesOf cls trans accept start accept_from rule_term eof) (bytesOf src)
        ((bytesOf src).length + 1 - x.2.val) x.2.val (x.1.val.map ltokNat) =
      Spec.llexGo (lexTablesOf cls trans accept start accept_from rule_term eof) (bytesOf src)
        ((bytesOf src).length + 1) 0 (out.val.map ltokNat))
  · rintro ⟨out', pos⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    have hT : (lexTablesOf cls trans accept start accept_from rule_term eof).dfa =
        lexDfaOf cls trans accept start accept_from := rfl
    unfold lex_loop.body
    step*
    · -- the end of the source: the end-of-input token
      have hp : pos.val = (bytesOf src).length := by
        have : n.val ≤ pos.val := by simpa using ‹pos ≥ n›
        omega
      rw [← h3, Spec.llexGo_end _ _ _ _ hp]
      have hi : i.val = n.val := by simp [i_post]; omega
      have hi1 : i1.val = n.val := by simp [i1_post]; omega
      refine ⟨trivial, ?_⟩
      rw [out1_post]
      simp [ltokNat, hi, hi1, hn, hlen, rule_eof_val, lexTablesOf]
    all_goals
      have hlt : pos.val < (bytesOf src).length := by
        have : ¬ n.val ≤ pos.val := by simpa using ‹¬pos ≥ n›
        omega
      have hr1 : (Spec.lscanFrom (lexTablesOf cls trans accept start accept_from rule_term eof).dfa
          (bytesOf src) pos.val).1 = rule.val := by rw [hT, ← rule_post]
      have hr2 : (Spec.lscanFrom (lexTablesOf cls trans accept start accept_from rule_term eof).dfa
          (bytesOf src) pos.val).2 = «end».val := by rw [hT, ← rule_post]
      have hle : «end».val ≤ src.val.length := by
        have := Spec.lscanFrom_le (lexDfaOf cls trans accept start accept_from) (bytesOf src)
          pos.val (by omega)
        rw [← hT, hr2] at this; omega
    · -- no match
      rw [← h3, Spec.llexGo_step _ _ _ _ hlt, hr1]
      have : rule.val = 0 := by rw [‹rule = 0#u16›]; rfl
      simp [this, LexRel]
    · -- an empty match
      rw [← h3, Spec.llexGo_step _ _ _ _ hlt, hr2]
      have : «end».val ≤ pos.val := by simpa using ‹«end» ≤ pos›
      simp [this, LexRel]
    · -- the rule names a terminal
      have hle' : rule.val ≤ NR.val := by
        rw [← hr1, hT]
        apply Spec.lscan_rule_le
        · intro s'
          show cell1 accept s' 0 ≤ NR.val
          unfold cell1
          cases h : accept.val[s']? with
          | none => simp
          | some x => simpa using hw.accept s' x h
        · simp
      have : rule_term.val.length = NR.val := Array.property rule_term
      have : i.val = r.val := by simp [i_post]
      simp only [Array.length]; omega
    · -- a token
      have hgt : pos.val < «end».val := by
        have : ¬ «end».val ≤ pos.val := by simpa using ‹¬«end» ≤ pos›
        omega
      have hr0 : rule.val ≠ 0 := by
        intro h; apply ‹¬rule = 0#u16›; apply UScalar.eq_of_val_eq; simpa using h
      have hterm : cell1 rule_term (rule.val - 1) 0 = term.val := by
        rw [cell1_of_get? _ _ _ term]
        rw [term_post]
        have : i.val = rule.val - 1 := by simp [i_post, r_post]
        rw [← this]; exact List.getElem?_eq_getElem _
      have hskip : term.val ≠ Spec.termSkip := by
        intro h; apply (bne_iff_ne.mp ‹(term != TERM_SKIP) = true›)
        apply UScalar.eq_of_val_eq; rw [term_skip_val]; exact h
      refine ⟨hle, ?_, ?_, by omega⟩
      · rw [out1_post]; simp; omega
      · rw [← h3, Spec.llexGo_step _ _ _ _ hlt, hr1, hr2]
        have hi1 : i1.val = pos.val := by simp [i1_post]; omega
        have hi2 : i2.val = «end».val := by simp [i2_post]; omega
        simp only [hr0, false_or, show ¬ «end».val ≤ pos.val by omega, ↓reduceIte]
        simp only [lexTablesOf, hterm, ne_eq, hskip, not_false_eq_true, ↓reduceIte]
        rw [out1_post]
        simp [ltokNat, hi1, hi2, r_post]
    · -- a skipped rule
      have hgt : pos.val < «end».val := by
        have : ¬ «end».val ≤ pos.val := by simpa using ‹¬«end» ≤ pos›
        omega
      have hr0 : rule.val ≠ 0 := by
        intro h; apply ‹¬rule = 0#u16›; apply UScalar.eq_of_val_eq; simpa using h
      have hterm : cell1 rule_term (rule.val - 1) 0 = term.val := by
        rw [cell1_of_get? _ _ _ term]
        rw [term_post]
        have : i.val = rule.val - 1 := by simp [i_post, r_post]
        rw [← this]; exact List.getElem?_eq_getElem _
      have hskip : term.val = Spec.termSkip := by
        have : term.val = TERM_SKIP.val := by simpa using ‹¬(term != TERM_SKIP) = true›
        rw [this, term_skip_val]
      refine ⟨hle, by omega, ?_, by omega⟩
      rw [← h3, Spec.llexGo_step _ _ _ _ hlt, hr1, hr2]
      simp only [hr0, false_or, show ¬ «end».val ≤ pos.val by omega, ↓reduceIte]
      simp only [lexTablesOf, hterm, hskip, ne_eq, not_true_eq_false, ↓reduceIte]
  · exact ⟨by simp, by simp, by simp⟩

/-- **The kernel's `lex` is `Spec.llex`.** For tables that satisfy `LWf` and an output vector
    with room for a token per byte, `lex` returns what `Spec.llex` computes: how it ends, and the
    tokens after those already in `out`. -/
theorem lex_spec {NC R NR : Usize} (src : Slice U8) (out : alloc.vec.Vec Token)
    (cls : Array U8 256#usize) (trans : Array (Array U16 NC) R) (accept : Array U16 R)
    (start accept_from : Usize) (rule_term : Array U16 NR) (eof : U16)
    (hw : LWf (NR := NR) cls trans accept start)
    (hroom : out.val.length + src.val.length < Usize.max) :
    lex src out cls trans accept start accept_from rule_term eof ⦃ res out' =>
      LexRel (Spec.llex (lexTablesOf cls trans accept start accept_from rule_term eof)
          (bytesOf src) (out.val.map ltokNat)).1 res ∧
      out'.val.map ltokNat = (Spec.llex (lexTablesOf cls trans accept start accept_from rule_term
          eof) (bytesOf src) (out.val.map ltokNat)).2 ⦄ := by
  have hlen : (bytesOf src).length = src.val.length := by simp [bytesOf]
  unfold lex
  step*
  · -- too long
    have hgt : src.val.length > 2 ^ 32 - 1 := by
      have : i.val = 2 ^ 32 - 1 := by simp [i_post, core.num.U32.MAX]; rfl
      have := ‹Slice.len src > i›
      simp at this; omega
    have hgt' : 4294967295 < src.val.length := by omega
    simp [Spec.llex, hlen, hgt', LexRel]
  · -- the loop
    have hle : src.val.length ≤ 2 ^ 32 - 1 := by
      have : i.val = 2 ^ 32 - 1 := by simp [i_post, core.num.U32.MAX]; rfl
      have := ‹¬Slice.len src > i›
      simp at this; omega
    have := lex_loop_spec src out cls trans accept start accept_from rule_term eof hw
      (Slice.len src) (by simp) (by simp; omega) hroom
    refine Aeneas.Std.WP.spec_mono this ?_
    rintro ⟨res, out'⟩ ⟨h1, h2⟩
    simp only [Spec.llex, hlen, show ¬ src.val.length > 2 ^ 32 - 1 by omega, ↓reduceIte]
    rw [hlen] at h1 h2
    exact ⟨h1, h2⟩

end lpg_kernel.Proof
