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

import Spec.Utf8
import LeanParserGenerator.Lexer.FlatValidator

/-!
A check, run by the kernel, that the Rust lexer DFA simulates a Lean lexer DFA (`LexSim`).

The check is given the map `phi` from Lean states to Rust states and a list of intervals `ivs`
that cover the code points `[0, 0x10FFFF]`, on each of which every edge of every Lean state is
constant (`intervalConst`, from the Lean flat-table validator). For each Lean state and each
interval it walks the Rust DFA over the UTF-8 encodings of all the valid code points of the
interval (`segWalk`, five segments by encoding length) and requires that every walk ends in the
Rust state of the Lean step at the first valid code point of the interval, without an
accepting state in the middle of a character. `lexSim_of_check` derives `LexSim`.
-/

namespace Spec

open Lexer

/-- The valid code points, by encoding length: `(lo, hi, lead offset, bytes)`. -/
def segs : List (Nat × Nat × Nat × Nat) :=
  [(0, 0x7f, 0, 1), (0x80, 0x7ff, 0xc0, 2), (0x800, 0xd7ff, 0xe0, 3), (0xe000, 0xffff, 0xe0, 3),
   (0x10000, 0x10ffff, 0xf0, 4)]

/-- The walk over the valid code points of `[lo, hi]` in one segment. -/
def segPart (d : LexDFA) (Q : List Nat) (lo hi : Nat) : Nat × Nat × Nat × Nat → Option (List Nat)
  | (a, b, off, L) => if max lo a ≤ min hi b then walk d Q off L (max lo a) (min hi b) else some []

/-- The walk over all the valid code points of `[lo, hi]`. -/
def segWalk (d : LexDFA) (Q : List Nat) (lo hi : Nat) : Option (List Nat) :=
  segs.foldr (fun sg acc => match segPart d Q lo hi sg, acc with
    | some r, some rs => some (r ++ rs)
    | _, _ => none) (some [])

/-- A code point is valid: a scalar value. -/
def ValidCp (n : Nat) : Prop := n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

theorem validCp_toNat (c : Char) : ValidCp c.toNat := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  unfold ValidCp Char.toNat
  omega

theorem toNat_ofNat_valid (v : Nat) (h : ValidCp v) : (Char.ofNat v).toNat = v := by
  have hv : v.isValidChar := by simp [Nat.isValidChar]; unfold ValidCp at h; omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem segWalk_sound (d : LexDFA) (Q : List Nat) (lo hi : Nat) (R : List Nat)
    (h : segWalk d Q lo hi = some R) (q : Nat) (hq : q ∈ Q) (n : Nat) (hn : ValidCp n)
    (h1 : lo ≤ n) (h2 : n ≤ hi) : run d q (encN n) ∈ R ∧ Mids d q (encN n) := by
  have hseg : ∀ (sgs : List (Nat × Nat × Nat × Nat)) (R : List Nat),
      sgs.foldr (fun sg acc => match segPart d Q lo hi sg, acc with
        | some r, some rs => some (r ++ rs)
        | _, _ => none) (some []) = some R →
      ∀ a b off L, (a, b, off, L) ∈ sgs → a ≤ n → n ≤ b →
        ∃ r, walk d Q off L (max lo a) (min hi b) = some r ∧ r ⊆ R := by
    intro sgs
    induction sgs with
    | nil => intro R _ a b off L hm; simp at hm
    | cons sg sgs ih =>
      intro R hR a b off L hm ha hb
      simp only [List.foldr_cons] at hR
      split at hR
      · rename_i r rs hp hrs
        simp only [Option.some.injEq] at hR
        subst hR
        rcases List.mem_cons.mp hm with rfl | hm
        · simp only [segPart, show max lo a ≤ min hi b by omega, ↓reduceIte] at hp
          exact ⟨r, hp, List.subset_append_left _ _⟩
        · obtain ⟨r', h1', h2'⟩ := ih rs hrs a b off L hm ha hb
          exact ⟨r', h1', fun x hx => List.mem_append_right _ (h2' hx)⟩
      · cases hR
  have hn' : n < 0x110000 := by unfold ValidCp at hn; omega
  rw [encN_eq_bytesOf n hn']
  unfold segWalk at h
  -- the segment of `n`
  have go : ∀ a b off L, (a, b, off, L) ∈ segs → a ≤ n → n ≤ b →
      run d q (bytesOf off L n) ∈ R ∧ Mids d q (bytesOf off L n) := by
    intro a b off L hm ha hb
    obtain ⟨r, hw, hsub⟩ := hseg segs R h a b off L hm ha hb
    obtain ⟨x, y⟩ := walk_sound d L Q off _ _ r hw q hq n (by omega) (by omega)
    exact ⟨hsub x, y⟩
  unfold ValidCp at hn
  by_cases c1 : n ≤ 0x7f
  · simpa [c1] using go 0 0x7f 0 1 (by simp [segs]) (by omega) c1
  by_cases c2 : n ≤ 0x7ff
  · simpa [c1, c2] using go 0x80 0x7ff 0xc0 2 (by simp [segs]) (by omega) c2
  by_cases c3 : n ≤ 0xffff
  · by_cases c3' : n ≤ 0xd7ff
    · simpa [c1, c2, c3] using go 0x800 0xd7ff 0xe0 3 (by simp [segs]) (by omega) c3'
    · simpa [c1, c2, c3] using go 0xe000 0xffff 0xe0 3 (by simp [segs]) (by omega) c3
  · simpa [c1, c2, c3] using go 0x10000 0x10ffff 0xf0 4 (by simp [segs]) (by omega) (by omega)

/-- The first valid code point of `[lo, hi]`, if any (`lo ≤ 0x10FFFF`). -/
def firstValid (lo hi : Nat) : Option Nat :=
  if hi < lo then none
  else if 0xd800 ≤ lo ∧ lo ≤ 0xdfff then (if 0xe000 ≤ hi then some 0xe000 else none)
  else if lo < 0x110000 then some lo else none

theorem firstValid_of (lo hi n : Nat) (hn : ValidCp n) (h1 : lo ≤ n) (h2 : n ≤ hi) :
    ∃ v, firstValid lo hi = some v ∧ ValidCp v ∧ lo ≤ v ∧ v ≤ hi := by
  unfold ValidCp at hn
  unfold firstValid
  by_cases a : hi < lo
  · omega
  by_cases b : 0xd800 ≤ lo ∧ lo ≤ 0xdfff
  · exact ⟨0xe000, by simp [a, b]; omega, by unfold ValidCp; omega, by omega, by omega⟩
  · exact ⟨lo, by simp [a, b]; omega, by unfold ValidCp; omega, Nat.le_refl _, by omega⟩

/-- The Rust state of a Lean step. -/
def tgt (phi : List Nat) : Option Nat → Nat
  | some t => phi.getD t 0
  | none => 0

/-- The intervals follow each other from `next` to the last code point. -/
def ivsCover : List (Nat × Nat) → Nat → Bool
  | [], next => next == 0x110000
  | (lo, hi) :: rest, next => lo == next && decide (lo ≤ hi) && ivsCover rest (hi + 1)

theorem ivsCover_mem : ∀ (ivs : List (Nat × Nat)) (next : Nat), ivsCover ivs next = true →
    ∀ n, next ≤ n → n < 0x110000 → ∃ p ∈ ivs, p.1 ≤ n ∧ n ≤ p.2 := by
  intro ivs
  induction ivs with
  | nil => intro next h n h1 h2; simp [ivsCover] at h; omega
  | cons p rest ih =>
    intro next h n h1 h2
    obtain ⟨lo, hi⟩ := p
    simp only [ivsCover, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hle⟩, hr⟩ := h
    by_cases hn : n ≤ hi
    · exact ⟨(lo, hi), List.mem_cons_self .., h1, hn⟩
    · obtain ⟨p, hp, hp'⟩ := ih (hi + 1) hr n (by omega) h2
      exact ⟨p, List.mem_cons_of_mem _ hp, hp'⟩

/-- The check of one Lean state `st`, whose Rust state is `q`. -/
def stateCheck (d : LexDFA) (n : Nat) (phi : List Nat) (ivs : List (Nat × Nat)) (st : DState)
    (q : Nat) : Bool :=
  q != 0 &&
  (match st.accept with
    | some r => decide (d.acceptFrom ≤ q) && d.accept q == r + 1
    | none => decide (q < d.acceptFrom)) &&
  st.trans.all (fun e => decide (e.target < n)) &&
  ivs.all (fun (lo, hi) =>
    st.trans.all (fun e => intervalConst lo hi e.cls) &&
    match firstValid lo hi with
    | none => true
    | some v =>
      match segWalk d [q] lo hi with
      | some R => R.all (· == tgt phi (st.stepChar (Char.ofNat v)))
      | none => false)

/-- The check that `d` simulates `dfa` with `phi`, over the intervals `ivs`. The states are
    visited with their images in one pass, so that neither list is indexed. -/
def lexSimCheck (d : LexDFA) (dfa : DFA) (phi : List Nat) (ivs : List (Nat × Nat)) : Bool :=
  decide (0 < dfa.states.size) && phi.length == dfa.states.size && phi.getD 0 0 == d.start &&
  decide (0 < d.acceptFrom) && ivsCover ivs 0 &&
  (dfa.states.toList.zip phi).all (fun p => stateCheck d dfa.states.size phi ivs p.1 p.2)

theorem stepChar_target (st : DState) (c : Char) (t : Nat) (h : st.stepChar c = some t) :
    ∃ e ∈ st.trans, e.target = t := by
  unfold DState.stepChar at h
  obtain ⟨e, he, he'⟩ := Array.exists_of_findSome?_eq_some h
  refine ⟨e, he, ?_⟩
  split at he' <;> simp_all

/-- **The check is sound.** -/
theorem lexSim_of_check (d : LexDFA) (dfa : DFA) (phi : List Nat) (ivs : List (Nat × Nat))
    (h : lexSimCheck d dfa phi ivs = true) (hdead : ∀ c, d.trans 0 c = 0) :
    LexSim d dfa (fun s => phi.getD s 0) := by
  simp only [lexSimCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hsize, hlen⟩, hstart⟩, hna⟩, hcov⟩, hst⟩ := h
  have hs : ∀ s, s < dfa.states.size →
      stateCheck d dfa.states.size phi ivs (dfa.states[s]!) (phi.getD s 0) = true := by
    intro s hs'
    have hmem : (dfa.states.toList[s]'(by simpa using hs'), phi[s]'(by omega)) ∈
        dfa.states.toList.zip phi := by
      have hz : s < (dfa.states.toList.zip phi).length := by simp; omega
      rw [← List.getElem_zip (i := s) (h := hz)]
      exact List.getElem_mem _
    have := hst _ hmem
    have e1 : dfa.states[s]! = dfa.states.toList[s]'(by simpa using hs') := by
      simp [hs']
    have e2 : phi.getD s 0 = phi[s]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s < phi.length by omega)]
    rw [e1, e2]; exact this
  refine ⟨hstart, hsize, ?_, ?_, ?_, ?_, hdead, hna⟩
  · -- accept
    intro s hs' i b e
    have h := hs s hs'
    simp only [stateCheck, Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, hacc⟩, _⟩, _⟩ := h
    unfold lrecord
    generalize phi.getD s 0 = q at hacc ⊢
    cases ha : (dfa.states[s]!).accept with
    | none =>
      simp only [ha, decide_eq_true_eq] at hacc
      simp [show ¬ q ≥ d.acceptFrom by omega]
    | some r =>
      simp only [ha, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hacc
      simp [hacc.1, hacc.2]
  · -- step
    intro s hs' c
    have h := hs s hs'
    simp only [stateCheck, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨_, hiv⟩ := h
    obtain ⟨⟨lo, hi⟩, hmem, h1, h2⟩ :=
      ivsCover_mem ivs 0 hcov c.toNat (Nat.zero_le _) (by
        have := validCp_toNat c; unfold ValidCp at this; omega)
    have hc := hiv (lo, hi) hmem
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hconst, hwalk⟩ := hc
    obtain ⟨v, hv, hvv, hv1, hv2⟩ := firstValid_of lo hi c.toNat (validCp_toNat c) h1 h2
    simp only [hv] at hwalk
    have hstep : (dfa.states[s]!).stepChar c = (dfa.states[s]!).stepChar (Char.ofNat v) :=
      stepChar_congr_interval _ c (Char.ofNat v) lo hi h1 h2
        (by rw [toNat_ofNat_valid v hvv]; exact hv1) (by rw [toNat_ofNat_valid v hvv]; exact hv2)
        (fun e he => (Array.all_eq_true_iff_forall_mem.mp hconst) e he)
    split at hwalk
    · rename_i R hR
      obtain ⟨hrun, hmid⟩ := segWalk_sound d [phi.getD s 0] lo hi R hR _ (List.mem_singleton_self _)
        c.toNat (validCp_toNat c) h1 h2
      rw [enc_eq_encN]
      refine ⟨hmid, ?_⟩
      have := (List.all_eq_true.mp hwalk) _ hrun
      simp only [beq_iff_eq] at this
      rw [this, hstep]
      cases (dfa.states[s]!).stepChar (Char.ofNat v) <;> rfl
    · cases hwalk
  · -- target
    intro s hs' c t ht
    have h := hs s hs'
    simp only [stateCheck, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨_, _⟩, htg⟩, _⟩ := h
    obtain ⟨e, he, rfl⟩ := stepChar_target _ c t ht
    simpa using (Array.all_eq_true_iff_forall_mem.mp htg) e he
  · -- not dead
    intro s hs'
    have h := hs s hs'
    simp only [stateCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact h.1.1.1

/-! ### The check in blocks of states

The kernel keeps what it has reduced until the end of a declaration, so that one check over
all the states of a large DFA holds the reductions of all of them (for a DFA of 387 states,
more than 30 GB). `lexSimCheck_of_parts` splits the check into a check of the conditions that
do not depend on a state (`lexSimHead`) and checks of blocks of `k` states (`lexSimPart`),
each of which can be its own declaration. -/

/-- The part of `lexSimCheck` that does not depend on a state. -/
def lexSimHead (d : LexDFA) (dfa : DFA) (phi : List Nat) (ivs : List (Nat × Nat)) : Bool :=
  decide (0 < dfa.states.size) && phi.length == dfa.states.size && phi.getD 0 0 == d.start &&
  decide (0 < d.acceptFrom) && ivsCover ivs 0

/-- The check of the `k` states from state `lo`. -/
def lexSimPart (d : LexDFA) (dfa : DFA) (phi : List Nat) (ivs : List (Nat × Nat))
    (lo k : Nat) : Bool :=
  (((dfa.states.toList.zip phi).drop lo).take k).all
    (fun p => stateCheck d dfa.states.size phi ivs p.1 p.2)

theorem all_take_of_parts {α : Type} (f : α → Bool) (l : List α) (k : Nat) :
    ∀ m, (∀ i < m, ((l.drop (i * k)).take k).all f = true) → (l.take (m * k)).all f = true
  | 0, _ => by simp
  | m + 1, h => by
    rw [Nat.succ_mul, List.take_add, List.all_append, Bool.and_eq_true]
    exact ⟨all_take_of_parts f l k m (fun i hi => h i (by omega)), h m (by omega)⟩

/-- **The check in blocks.** If the head holds and the blocks of `k` states from `i * k`, for
    `i < m`, cover the states, `lexSimCheck` holds. -/
theorem lexSimCheck_of_parts (d : LexDFA) (dfa : DFA) (phi : List Nat)
    (ivs : List (Nat × Nat)) (k m : Nat) (hm : dfa.states.size ≤ m * k)
    (hh : lexSimHead d dfa phi ivs = true)
    (hp : ∀ i < m, lexSimPart d dfa phi ivs (i * k) k = true) :
    lexSimCheck d dfa phi ivs = true := by
  unfold lexSimCheck
  unfold lexSimHead at hh
  rw [hh, Bool.true_and]
  have h := all_take_of_parts (fun p => stateCheck d dfa.states.size phi ivs p.1 p.2)
    (dfa.states.toList.zip phi) k m (fun i hi => by
      have := hp i hi
      unfold lexSimPart at this
      exact this)
  rwa [List.take_of_length_le (by simp; omega)] at h

/-! ### Packed tables

The kernel reads an element of a list in one step per element before it, and a packed number
with one shift. `packedDfa` reads the Rust tables from numbers: the class of byte `b` is the 8
bits at `8 * b` of `clsP`, the transition of state `s` on class `c` the 16 bits at `16 * c` of
the row `s` of `transP`, the accept value of state `s` the 16 bits at `16 * s` of `accP`. The
transitions are one number per row, not one number: a shift allocates a number of the size of
the result, and with one number for all the rows every lookup allocates a copy of most of the
table (for 409 states and 66 classes, 54 KB). -/

/-- The DFA of packed tables of `nr` states and `nc` classes. -/
def packedDfa (nc nr clsP : Nat) (transP : List Nat) (accP start acceptFrom : Nat) : LexDFA where
  cls := fun b => if b < 256 then (clsP >>> (8 * b)) % 256 else 0
  trans := fun s c => if s < nr ∧ c < nc then (transP.getD s 0 >>> (16 * c)) % 65536 else 0
  accept := fun s => if s < nr then (accP >>> (16 * s)) % 65536 else 0
  start := start
  acceptFrom := acceptFrom

end Spec
