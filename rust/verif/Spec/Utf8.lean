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

import Spec.LexSim

/-!
Walking a byte DFA over the UTF-8 encodings of all the code points of an interval at once.

A code point of `L` bytes is written in base 64 after its lead byte: the lead byte is an offset
plus the high digit, and each following byte is `0x80` plus the next digit (`bytesOf`,
`encN_eq_bytesOf`). `walk d Q off j lo hi` follows the digits of every number of `[lo, hi]`
from every state of `Q`, one byte position at a time: the numbers of `[lo, hi]` whose digit at
that position is in a range of digits go, from a state `q`, to the states `trans q (cls b)` for
the bytes `b` of the range (`stepSet`). The interval is split on its first digit: the part with
the lowest digit, the part with the highest, and the full digits between. The result is the set
of states the walk can end in, or `none` if a state in the middle of a character accepts.
`walk_sound` says that this set contains the end of the walk for each number.
-/

namespace Spec

/-- The UTF-8 encoding of a code point, as `String.utf8EncodeChar` computes it. -/
def encN (v : Nat) : List Nat :=
  if v ≤ 0x7f then [v]
  else if v ≤ 0x7ff then [(v / 64) % 32 + 0xc0, v % 64 + 0x80]
  else if v ≤ 0xffff then [(v / 4096) % 16 + 0xe0, (v / 64) % 64 + 0x80, v % 64 + 0x80]
  else [(v / 262144) % 8 + 0xf0, (v / 4096) % 64 + 0x80, (v / 64) % 64 + 0x80, v % 64 + 0x80]

theorem enc_eq_encN (c : Char) : enc c = encN c.toNat := by
  have hc : c.toNat < 0x110000 := by
    have := c.valid
    simp only [UInt32.isValidChar, Nat.isValidChar] at this
    unfold Char.toNat
    omega
  unfold enc String.utf8EncodeChar encN
  simp only [Char.toNat] at hc ⊢
  split
  · rename_i h0
    simp
    unfold Char.toNat
    omega
  · split
    · simp
      omega
    · split
      · simp
        omega
      · simp
        omega

/-- The bytes of the `j` base-64 digits of `m`, the first with offset `off` and the others
    with `0x80`. -/
def bytesOf : Nat → Nat → Nat → List Nat
  | _, 0, _ => []
  | off, j + 1, m => (off + m / 64 ^ j) :: bytesOf 0x80 j (m % 64 ^ j)

theorem encN_eq_bytesOf (v : Nat) (hv : v < 0x110000) :
    encN v =
      if v ≤ 0x7f then bytesOf 0 1 v
      else if v ≤ 0x7ff then bytesOf 0xc0 2 v
      else if v ≤ 0xffff then bytesOf 0xe0 3 v
      else bytesOf 0xf0 4 v := by
  unfold encN
  simp only [bytesOf, Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.pow_succ, Nat.one_mul]
  split
  · simp
  · split
    · simp only [List.cons.injEq, and_true]
      omega
    · split
      · simp only [List.cons.injEq, and_true]
        refine ⟨by omega, ?_, by omega⟩
        rw [show (64 * 64 : Nat) = 64 * 64 from rfl, Nat.mod_mul_right_div_self]
        omega
      · simp only [List.cons.injEq, and_true]
        refine ⟨by omega, ?_, ?_, by omega⟩
        · rw [Nat.mod_mul_right_div_self]; omega
        · rw [Nat.mod_mod_of_dvd _ (by decide : 64 * 64 ∣ 64 * 64 * 64),
            Nat.mod_mul_right_div_self]
          omega

/-! ### Sets of states -/

/-- `x` added to `xs` unless it is there. -/
def addNew (xs : List Nat) (x : Nat) : List Nat := if x ∈ xs then xs else x :: xs

theorem mem_addNew {xs : List Nat} {x y : Nat} : y ∈ addNew xs x ↔ y = x ∨ y ∈ xs := by
  unfold addNew
  split
  · constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h) <;> assumption
  · simp

/-- The classes of the bytes from `blo` to `bhi`. -/
def classesIn (d : LexDFA) (blo bhi : Nat) : List Nat :=
  (List.range (bhi + 1 - blo)).foldl (fun acc k => addNew acc (d.cls (blo + k))) []

/-- The states `trans q (cls b)` for `q ∈ Q` and the bytes `b` from `blo` to `bhi`. The
    classes are computed first, so that a transition is read once per class, not per byte. -/
def stepSet (d : LexDFA) (Q : List Nat) (blo bhi : Nat) : List Nat :=
  let cs := classesIn d blo bhi
  Q.foldl (fun acc q => cs.foldl (fun acc c => addNew acc (d.trans q c)) acc) []

theorem foldl_addNew_mem (f : Nat → Nat) :
    ∀ (ks : List Nat) (acc : List Nat) (y : Nat),
      y ∈ ks.foldl (fun acc k => addNew acc (f k)) acc ↔ y ∈ acc ∨ ∃ k ∈ ks, y = f k := by
  intro ks
  induction ks with
  | nil => intro acc y; simp
  | cons k ks ih =>
    intro acc y
    simp only [List.foldl_cons, ih, mem_addNew, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨k', hk', rfl⟩)
      · exact Or.inr ⟨k, Or.inl rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨k', Or.inr hk', rfl⟩
    · rintro (h | ⟨k', (rfl | hk'), rfl⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨k', hk', rfl⟩

theorem mem_classesIn (d : LexDFA) (blo bhi b : Nat) (hb1 : blo ≤ b) (hb2 : b ≤ bhi) :
    d.cls b ∈ classesIn d blo bhi := by
  unfold classesIn
  refine (foldl_addNew_mem _ _ _ _).mpr (Or.inr ⟨b - blo, ?_, ?_⟩)
  · simp; omega
  · rw [show blo + (b - blo) = b by omega]

theorem mem_stepSet (d : LexDFA) (Q : List Nat) (blo bhi q b : Nat) (hq : q ∈ Q)
    (hb1 : blo ≤ b) (hb2 : b ≤ bhi) : d.trans q (d.cls b) ∈ stepSet d Q blo bhi := by
  unfold stepSet
  have hc := mem_classesIn d blo bhi b hb1 hb2
  generalize classesIn d blo bhi = cs at hc ⊢
  have key : ∀ (Q' : List Nat) (acc : List Nat),
      (d.trans q (d.cls b) ∈ acc ∨ q ∈ Q') →
      d.trans q (d.cls b) ∈ Q'.foldl (fun acc q =>
        cs.foldl (fun acc c => addNew acc (d.trans q c)) acc) acc := by
    intro Q'
    induction Q' with
    | nil => intro acc h; simpa using h
    | cons q' Q' ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | h
      · left; exact (foldl_addNew_mem _ _ _ _).mpr (Or.inl h)
      · rcases List.mem_cons.mp h with rfl | h
        · left
          exact (foldl_addNew_mem _ _ _ _).mpr (Or.inr ⟨d.cls b, hc, rfl⟩)
        · right; exact h
  exact key Q [] (Or.inr hq)

/-! ### The walk -/

/-- The walk over the digits of `[lo, hi]`: the states it can end in, or `none` if a state
    in the middle of a character accepts. `j` digits are left, the first with offset `off`. -/
def walk (d : LexDFA) : List Nat → Nat → Nat → Nat → Nat → Option (List Nat)
  | Q, _, 0, _, _ => some Q
  | Q, off, j + 1, lo, hi =>
    let D := 64 ^ j
    let part (a b l h : Nat) : Option (List Nat) :=
      let Q' := stepSet d Q (off + a) (off + b)
      if j ≠ 0 ∧ Q'.any (fun q => decide (d.acceptFrom ≤ q)) then none
      else walk d Q' 0x80 j l h
    if lo / D = hi / D then part (lo / D) (lo / D) (lo % D) (hi % D)
    else
      match part (lo / D) (lo / D) (lo % D) (D - 1),
          (if lo / D + 1 ≤ hi / D - 1 then part (lo / D + 1) (hi / D - 1) 0 (D - 1) else some []),
          part (hi / D) (hi / D) 0 (hi % D) with
      | some r1, some r2, some r3 => some (r1 ++ r2 ++ r3)
      | _, _, _ => none

theorem mids_cons (d : LexDFA) (q b : Nat) (bs : List Nat)
    (h1 : bs ≠ [] → d.trans q (d.cls b) < d.acceptFrom) (h2 : Mids d (d.trans q (d.cls b)) bs) :
    Mids d q (b :: bs) := by
  intro k hk hk'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [List.take_succ_cons, run]
  by_cases hk0 : k' = 0
  · subst hk0
    simp only [List.take_zero, run]
    exact h1 (by intro h; subst h; simp at hk')
  · exact h2 k' (by omega) (by simp at hk'; omega)

/-- One part of the walk: the numbers whose first digit is in `[a, b]`, and whose other digits
    are in `[l, h]`. -/
theorem part_sound (d : LexDFA) (Q : List Nat) (off j a b l h m : Nat) (R : List Nat)
    (ih : ∀ Q' R', walk d Q' 0x80 j l h = some R' → ∀ q ∈ Q', ∀ m', l ≤ m' → m' ≤ h →
      run d q (bytesOf 0x80 j m') ∈ R' ∧ Mids d q (bytesOf 0x80 j m'))
    (hpart : (let Q' := stepSet d Q (off + a) (off + b)
      if j ≠ 0 ∧ Q'.any (fun q => decide (d.acceptFrom ≤ q)) then none
      else walk d Q' 0x80 j l h) = some R)
    (hm1 : a ≤ m / 64 ^ j) (hm2 : m / 64 ^ j ≤ b) (hl : l ≤ m % 64 ^ j) (hh : m % 64 ^ j ≤ h) :
    ∀ q ∈ Q, run d q (bytesOf off (j + 1) m) ∈ R ∧ Mids d q (bytesOf off (j + 1) m) := by
  intro q hq
  simp only at hpart
  split at hpart
  · cases hpart
  · rename_i hacc
    have hmem := mem_stepSet d Q (off + a) (off + b) q (off + m / 64 ^ j) hq (by omega) (by omega)
    obtain ⟨h1, h2⟩ := ih _ R hpart _ hmem (m % 64 ^ j) hl hh
    refine ⟨by simpa [bytesOf, run] using h1, ?_⟩
    simp only [bytesOf]
    apply mids_cons _ _ _ _ _ h2
    intro hne
    have hj : j ≠ 0 := by
      intro hj; subst hj; simp [bytesOf] at hne
    have : ¬ (d.acceptFrom ≤ d.trans q (d.cls (off + m / 64 ^ j))) := by
      intro hle
      apply hacc
      refine ⟨hj, ?_⟩
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨_, hmem, hle⟩
    omega

/-- **The walk is sound**: every number of `[lo, hi]`, from every state of `Q`, ends in the
    result, through non-accepting states in the middle of the character. -/
theorem walk_sound (d : LexDFA) :
    ∀ (j : Nat) (Q : List Nat) (off lo hi : Nat) (R : List Nat), walk d Q off j lo hi = some R →
      ∀ q ∈ Q, ∀ m, lo ≤ m → m ≤ hi →
        run d q (bytesOf off j m) ∈ R ∧ Mids d q (bytesOf off j m) := by
  intro j
  induction j with
  | zero =>
    intro Q off lo hi R hw q hq m _ _
    simp only [walk, Option.some.injEq] at hw
    subst hw
    refine ⟨by simpa [bytesOf, run] using hq, ?_⟩
    intro k hk hk'; simp [bytesOf] at hk'
  | succ j ih =>
    intro Q off lo hi R hw q hq m hm1 hm2
    have ih' : ∀ l h, ∀ Q' R', walk d Q' 0x80 j l h = some R' → ∀ q ∈ Q', ∀ m', l ≤ m' →
        m' ≤ h → run d q (bytesOf 0x80 j m') ∈ R' ∧ Mids d q (bytesOf 0x80 j m') :=
      fun l h Q' R' hw' => ih Q' 0x80 l h R' hw'
    have hD : 0 < 64 ^ j := Nat.pos_of_neZero (64 ^ j)
    have hdiv1 : lo / 64 ^ j ≤ m / 64 ^ j := Nat.div_le_div_right hm1
    have hdiv2 : m / 64 ^ j ≤ hi / 64 ^ j := Nat.div_le_div_right hm2
    have hmod : m % 64 ^ j < 64 ^ j := Nat.mod_lt _ hD
    -- if `m` has the lowest digit, its rest is at least that of `lo`
    have hlo : m / 64 ^ j = lo / 64 ^ j → lo % 64 ^ j ≤ m % 64 ^ j := by
      intro he
      have h1 := Nat.div_add_mod m (64 ^ j)
      have h2 := Nat.div_add_mod lo (64 ^ j)
      rw [he] at h1
      omega
    have hhi : m / 64 ^ j = hi / 64 ^ j → m % 64 ^ j ≤ hi % 64 ^ j := by
      intro he
      have h1 := Nat.div_add_mod m (64 ^ j)
      have h2 := Nat.div_add_mod hi (64 ^ j)
      rw [he] at h1
      omega
    simp only [walk] at hw
    split at hw
    · rename_i heq
      exact part_sound d Q off j _ _ _ _ m R (ih' _ _) hw (by omega) (by omega)
        (hlo (by omega)) (hhi (by omega)) q hq
    · rename_i hne
      split at hw
      · rename_i r1 r2 r3 h1 h2 h3
        simp only [Option.some.injEq] at hw
        subst hw
        by_cases hA : m / 64 ^ j = lo / 64 ^ j
        · obtain ⟨a, b⟩ := part_sound d Q off j _ _ _ _ m r1 (ih' _ _) h1 (by omega) (by omega)
            (hlo hA) (by omega) q hq
          exact ⟨List.mem_append_left _ (List.mem_append_left _ a), b⟩
        · by_cases hB : m / 64 ^ j = hi / 64 ^ j
          · obtain ⟨a, b⟩ := part_sound d Q off j _ _ _ _ m r3 (ih' _ _) h3 (by omega) (by omega)
              (by omega) (hhi hB) q hq
            exact ⟨List.mem_append_right _ a, b⟩
          · have hmid : lo / 64 ^ j + 1 ≤ hi / 64 ^ j - 1 := by omega
            simp only [hmid, ↓reduceIte] at h2
            obtain ⟨a, b⟩ := part_sound d Q off j _ _ _ _ m r2 (ih' _ _) h2 (by omega) (by omega)
              (by omega) (by omega) q hq
            exact ⟨List.mem_append_left _ (List.mem_append_right _ a), b⟩
      · cases hw

end Spec
