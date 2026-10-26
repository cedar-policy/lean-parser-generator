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
A-posteriori Boolean validator for the flat scanner.

`Lexer/FlatScan.lean` proves the fast `FlatDFA` scanner equals the specification
`DFA.scan` *given* three agreements between the flat tables and the `DFA`
(`StepAgree`, `AcceptAgree`, `StatesInRange`). This file defines a Boolean
`flatValidate f dfa` that, when `true`, implies all three, and is discharged per
lexer with `native_decide` (docs/DESIGN.md §9.7 step 1, the a-posteriori route).

The alphabet cannot be enumerated (docs/DESIGN.md §9.3), so the step condition is
checked at one representative character per flat class, sound because within a flat
class every edge-class membership is constant (the flat boundaries refine every edge
class of every state). Constancy is an interval condition: each flat class interval
is inside-or-disjoint from every edge class, checked with the same interval
arithmetic as the derivative-vector validator (`Lexer/Validator.lean`).
-/
public import LeanParserGenerator.Lexer.FlatScan
public import LeanParserGenerator.Lexer.Validator


@[expose] public section

namespace Lexer

open DFA
open FlatDFA

/-! ### Flat-class representative and interval helpers -/

/-- `bsearch` spec: if `bounds[lo] ≤ n < bounds[hi]` and `lo < hi < size`, the result
    `ci` satisfies `bounds[ci] ≤ n < bounds[ci+1]` and `lo ≤ ci < hi`. By well-founded
    induction mirroring `bsearch`'s recursion. Sortedness is not needed: the bracket
    `bounds[lo] ≤ n < bounds[hi]` is threaded through the recursion explicitly. -/
theorem bsearch_spec (bounds : Array Nat) (n : Nat) :
    ∀ lo hi, lo < hi → hi < bounds.size →
      bounds.getD lo 0 ≤ n → n < bounds.getD hi 0 →
      bounds.getD (FlatDFA.bsearch bounds n lo hi) 0 ≤ n ∧
        n < bounds.getD (FlatDFA.bsearch bounds n lo hi + 1) 0 ∧
        lo ≤ FlatDFA.bsearch bounds n lo hi ∧ FlatDFA.bsearch bounds n lo hi < hi := by
  intro lo hi
  induction lo, hi using FlatDFA.bsearch.induct bounds n with
  | case1 lo hi hlt mid hmid ih =>
    intro _hlohi hhi hlon hnhi
    rw [FlatDFA.bsearch]
    have hmideq : (lo + hi) / 2 = mid := rfl
    simp only [hlt, hmideq, hmid, ite_eq_left]
    have hmidlo : lo < mid := by rw [← hmideq]; omega
    have hmidhi : mid < hi := by rw [← hmideq]; omega
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) hhi hmid hnhi
    have h3' : lo ≤ FlatDFA.bsearch bounds n mid hi := Nat.le_trans (Nat.le_of_lt hmidlo) h3
    exact ⟨h1, h2, h3', h4⟩
  | case2 lo hi hlt mid hmid ih =>
    intro _hlohi hhi hlon hnhi
    rw [FlatDFA.bsearch]
    have hmideq : (lo + hi) / 2 = mid := rfl
    have hmidn : ¬ bounds.getD mid 0 ≤ n := hmid
    simp only [hlt, hmideq, hmidn]
    have hmidlo : lo < mid := by rw [← hmideq]; omega
    have hmidhi : mid < hi := by rw [← hmideq]; omega
    have hmidsize : mid < bounds.size := by omega
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) hmidsize hlon (by simpa using Nat.lt_of_not_le hmidn)
    have h4' : FlatDFA.bsearch bounds n lo mid < hi := Nat.lt_trans h4 hmidhi
    exact ⟨h1, h2, h3, h4'⟩
  | case3 lo hi hlt =>
    intro hlohi hhi hlon hnhi
    rw [FlatDFA.bsearch]
    simp only [hlt, ite_false]
    have hhieq : hi = lo + 1 := by
      have h1 : lo < hi := hlohi
      have h2 : ¬ lo + 1 < hi := hlt
      omega
    subst hhieq
    exact ⟨hlon, hnhi, Nat.le_refl _, Nat.lt_succ_self _⟩

/-- The representative code point of flat class `ci`: its lower boundary, dodging
    the UTF-16 surrogate gap the same way `DFA.repOf` does. -/
def FlatDFA.repChar (f : FlatDFA) (ci : Nat) : Char :=
  DFA.repOf (f.bounds.getD ci 0)

/-- The inclusive code-point interval of flat class `ci`: `[bounds[ci], bounds[ci+1]-1]`. -/
def FlatDFA.classInterval (f : FlatDFA) (ci : Nat) : Nat × Nat :=
  (f.bounds.getD ci 0, f.bounds.getD (ci + 1) 0 - 1)

/-! ### The Boolean validator conditions -/

/-- Accept agreement, as a Boolean over all states. -/
def flatAcceptValid (f : FlatDFA) (dfa : DFA) : Bool :=
  (List.range dfa.states.size).all (fun sid =>
    acceptOf f sid == (dfa.states[sid]!).accept)

/-- Range validity: every flat transition target (minus the +1 encoding) is a valid
    state index. Checked over the whole flat transition array (by its actual size,
    so any nonzero entry — the only ones `step` can return — is covered). -/
def flatRangeValid (f : FlatDFA) (dfa : DFA) : Bool :=
  (List.range f.trans.size).all (fun idx =>
    let t := f.trans.getD idx 0
    t == 0 || (t - 1 < dfa.states.size))

/-! ### The easy agreements -/

theorem acceptAgree_of_valid (f : FlatDFA) (dfa : DFA)
    (h : flatAcceptValid f dfa = true) : AcceptAgree f dfa := by
  intro sid hsid
  have := (List.all_eq_true.mp h) sid (by simp [List.mem_range, hsid])
  simpa using (beq_iff_eq.mp this)

theorem statesInRange_of_valid (f : FlatDFA) (dfa : DFA)
    (h : flatRangeValid f dfa = true) : StatesInRange f dfa := by
  intro sid hsid c next hstep
  unfold FlatDFA.step at hstep
  simp only at hstep
  by_cases ht : (f.trans.getD (sid * f.nClasses + f.classOf c) 0 == 0) = true
  · simp only [ht, ite_true] at hstep; exact absurd hstep (by simp)
  · have htne : f.trans.getD (sid * f.nClasses + f.classOf c) 0 ≠ 0 := by
      simp only [beq_iff_eq] at ht; exact ht
    have hstep2 : f.trans.getD (sid * f.nClasses + f.classOf c) 0 - 1 = next := by
      simp only [ht, Bool.false_eq_true, ite_false] at hstep
      exact Option.some.injEq _ _ ▸ hstep
    have hidxlt : sid * f.nClasses + f.classOf c < f.trans.size := by
      rcases Nat.lt_or_ge (sid * f.nClasses + f.classOf c) f.trans.size with hlt | hge
      · exact hlt
      · exfalso; apply htne
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge]; rfl
    have hall := (List.all_eq_true.mp h) (sid * f.nClasses + f.classOf c)
      (by simp [List.mem_range, hidxlt])
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
    rcases hall with h0 | hlt
    · exact absurd h0 htne
    · rw [← hstep2]; exact hlt

/-! ### Step validator (the interval part) -/

/-- `[lo,hi]` is inside-or-disjoint from `k`: `memRanges k.rs` is constant on
    `[lo,hi]`, which holds iff no endpoint of `k` lies strictly in `(lo, hi]`. This
    is O(ranges), not O(points), so the Unicode-wide final flat class is cheap
    (docs/DESIGN.md §9.3, reusing `rangeEndpoints`/`memRanges_agree_of_noEndpointBetween`). -/
def intervalConst (lo hi : Nat) (k : CharClass) : Bool :=
  (rangeEndpoints k.rs).all (fun p => !(lo < p && p ≤ hi))

/-- Step validity: for each state and each flat class, the flat step agrees with the
    DFA step at the class representative, and `memRanges` of every edge class is
    constant on the flat class interval (so `stepChar` is constant on the class,
    making the one-representative check sound). -/
def flatStepValid (f : FlatDFA) (dfa : DFA) : Bool :=
  (List.range dfa.states.size).all (fun sid =>
    (List.range f.nClasses).all (fun ci =>
      let lo := f.bounds.getD ci 0
      let hi := f.bounds.getD (ci + 1) 0 - 1
      let rep := f.repChar ci
      (step f sid rep == (dfa.states[sid]!).stepChar rep) &&
      ((dfa.states[sid]!).trans.all (fun e => intervalConst lo hi e.cls))))

/-- Bounds shape: at least two boundaries, `bounds[0] = 0`, the last boundary is
    `maxCodePoint + 1`, `nClasses = bounds.size - 1`, and adjacent boundaries are
    strictly increasing (so every class interval is nonempty and the search brackets
    hold). -/
def flatBoundsValid (f : FlatDFA) : Bool :=
  (2 ≤ f.bounds.size) &&
  (f.bounds.getD 0 0 == 0) &&
  (f.bounds.getD (f.bounds.size - 1) 0 == DFA.maxCodePoint + 1) &&
  (f.nClasses == f.bounds.size - 1) &&
  ((List.range (f.bounds.size - 1)).all (fun i => f.bounds.getD i 0 < f.bounds.getD (i+1) 0))

/-- The ASCII fast-path table matches `classOfNat` on `0..127`, and every flat class
    representative round-trips its class (`classOf (repChar ci) = ci`). The latter is
    checked rather than derived, since `repChar` dodges the surrogate gap. -/
def flatClassValid (f : FlatDFA) : Bool :=
  ((List.range 128).all (fun b => f.ascii.getD b 0 == f.classOfNat b)) &&
  ((List.range f.nClasses).all (fun ci => f.classOf (f.repChar ci) == ci))

/-- The full flat validator: all conditions. When `true` (per lexer, `native_decide`),
    it implies `StepAgree`, `AcceptAgree`, and `StatesInRange`. -/
def flatValidate (f : FlatDFA) (dfa : DFA) : Bool :=
  flatAcceptValid f dfa && flatRangeValid f dfa && flatStepValid f dfa &&
  flatBoundsValid f && flatClassValid f

/-! ### Deriving `StepAgree` -/

/-- A character's code point is at most `maxCodePoint`. -/
theorem toNat_le_maxCodePoint (c : Char) : c.toNat ≤ DFA.maxCodePoint := by
  have hv := c.valid
  have he : c.val.toNat = c.toNat := Char.toNat_val
  unfold DFA.maxCodePoint
  rcases hv with h | h
  · rw [he] at h; omega
  · rw [he] at h; omega

/-- With a valid bounds shape, `classOfNat n` for `n ≤ maxCodePoint` brackets `n`:
    `bounds[ci] ≤ n < bounds[ci+1]`. -/
theorem classOfNat_bracket (f : FlatDFA) (hb : flatBoundsValid f = true)
    (n : Nat) (hn : n ≤ DFA.maxCodePoint) :
    f.bounds.getD (f.classOfNat n) 0 ≤ n ∧ n < f.bounds.getD (f.classOfNat n + 1) 0 := by
  unfold flatBoundsValid at hb
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hsize, h0⟩, hlast⟩, _hnc⟩, _hmono⟩ := hb
  unfold FlatDFA.classOfNat
  have hlo : f.bounds.getD 0 0 ≤ n := by rw [h0]; exact Nat.zero_le _
  have hhi : n < f.bounds.getD (f.bounds.size - 1) 0 := by
    rw [hlast]; unfold DFA.maxCodePoint at hn ⊢; omega
  have := bsearch_spec f.bounds n 0 (f.bounds.size - 1) (by omega) (by omega) hlo hhi
  exact ⟨this.1, this.2.1⟩

/-- `classOf c = classOfNat c.toNat` when the ASCII table is validated. -/
theorem classOf_eq_classOfNat (f : FlatDFA) (hc : flatClassValid f = true) (c : Char) :
    f.classOf c = f.classOfNat c.toNat := by
  unfold flatClassValid at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hascii, _⟩ := hc
  unfold FlatDFA.classOf
  by_cases h : c.toNat < 128
  · simp only [h, ite_true]
    have := (List.all_eq_true.mp hascii) c.toNat (by simp [List.mem_range, h])
    simpa using (beq_iff_eq.mp this)
  · simp only [h, ite_false]

/-- Two chars whose code points both lie in `[lo,hi]` and for which every edge class
    of the state has no endpoint strictly in `(lo,hi]` give the same `stepChar`. -/
theorem stepChar_congr_interval (st : DState) (c₁ c₂ : Char) (lo hi : Nat)
    (h1 : lo ≤ c₁.toNat) (h1' : c₁.toNat ≤ hi) (h2 : lo ≤ c₂.toNat) (h2' : c₂.toNat ≤ hi)
    (hedges : ∀ e ∈ st.trans, intervalConst lo hi e.cls = true) :
    st.stepChar c₁ = st.stepChar c₂ := by
  apply stepChar_congr
  intro e he
  -- both memberships equal memRanges lo, via constancy
  have hconst := hedges e he
  unfold intervalConst at hconst
  have hcut : ∀ p ∈ rangeEndpoints e.cls.rs, ¬ (lo < p ∧ p ≤ hi) := by
    intro p hp hpin
    have hpp := (List.all_eq_true.mp hconst) p hp
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at hpp
    obtain ⟨hlo, hle⟩ := hpin
    rcases hpp with h | h
    · simp only [decide_eq_false_iff_not] at h; exact h hlo
    · simp only [decide_eq_false_iff_not] at h; exact h hle
  -- membership of c₁ = memRanges lo (both endpoints have no cut between)
  have hm1 : memRanges e.cls.rs c₁.toNat = memRanges e.cls.rs lo :=
    (memRanges_agree_of_noEndpointBetween e.cls.rs h1 (by
      intro p hp ⟨hlo, hle⟩; exact hcut p hp ⟨hlo, Nat.le_trans hle h1'⟩)).symm
  have hm2 : memRanges e.cls.rs c₂.toNat = memRanges e.cls.rs lo :=
    (memRanges_agree_of_noEndpointBetween e.cls.rs h2 (by
      intro p hp ⟨hlo, hle⟩; exact hcut p hp ⟨hlo, Nat.le_trans hle h2'⟩)).symm
  rw [mem_eq_memRanges, mem_eq_memRanges, hm1, hm2]

/-- The main step-agreement derivation. -/
theorem stepAgree_of_valid (f : FlatDFA) (dfa : DFA)
    (hstepv : flatStepValid f dfa = true) (hb : flatBoundsValid f = true)
    (hc : flatClassValid f = true) : StepAgree f dfa := by
  intro sid hsid c
  -- ci = classOf c = classOfNat c.toNat, bracketed
  have hcls : f.classOf c = f.classOfNat c.toNat := classOf_eq_classOfNat f hc c
  obtain ⟨ci, hci⟩ : ∃ ci, f.classOfNat c.toNat = ci := ⟨_, rfl⟩
  have hbrack := classOfNat_bracket f hb c.toNat (toNat_le_maxCodePoint c)
  rw [hci] at hbrack hcls
  obtain ⟨hlo_c, hhi_c⟩ := hbrack
  -- ci < nClasses : from bracket and bounds shape (bounds sorted with size = nClasses+1)
  have hnc : f.nClasses = f.bounds.size - 1 := by
    unfold flatBoundsValid at hb
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    exact hb.1.2
  -- validator facts at this state and class
  unfold flatStepValid at hstepv
  have hsidmem : sid ∈ List.range dfa.states.size := by simp [List.mem_range, hsid]
  have hrow := (List.all_eq_true.mp hstepv) sid hsidmem
  -- need ci < nClasses to index the inner all
  have hci_lt : ci < f.nClasses := by
    unfold FlatDFA.classOfNat at hci
    unfold flatBoundsValid at hb
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨hsize, h0⟩, hlast⟩, _⟩, _⟩ := hb
    have hlo : f.bounds.getD 0 0 ≤ c.toNat := by rw [h0]; exact Nat.zero_le _
    have hhi : c.toNat < f.bounds.getD (f.bounds.size - 1) 0 := by
      rw [hlast]; have := toNat_le_maxCodePoint c; unfold DFA.maxCodePoint at this ⊢; omega
    have hspec := bsearch_spec f.bounds c.toNat 0 (f.bounds.size - 1) (by omega) (by omega) hlo hhi
    rw [hnc, ← hci]; exact hspec.2.2.2
  have hcimem : ci ∈ List.range f.nClasses := by simp [List.mem_range, hci_lt]
  have hcell := (List.all_eq_true.mp hrow) ci hcimem
  simp only [Bool.and_eq_true, beq_iff_eq] at hcell
  obtain ⟨hrep_eq, hedges_all⟩ := hcell
  -- rep and its class
  obtain ⟨rep, hrepdef⟩ : ∃ rep, f.repChar ci = rep := ⟨_, rfl⟩
  -- classOf rep = ci (validated)
  have hrep_cls : f.classOf rep = ci := by
    unfold flatClassValid at hc
    simp only [Bool.and_eq_true] at hc
    have hrt := (List.all_eq_true.mp hc.2) ci hcimem
    rw [← hrepdef]
    simpa using (beq_iff_eq.mp hrt)
  have hrep_clsN : f.classOfNat rep.toNat = ci := by
    have hcv : flatClassValid f = true := hc
    rw [← classOf_eq_classOfNat f hcv rep]; exact hrep_cls
  have hbrack_rep := classOfNat_bracket f hb rep.toNat (toNat_le_maxCodePoint rep)
  rw [hrep_clsN] at hbrack_rep
  obtain ⟨hlo_r, hhi_r⟩ := hbrack_rep
  -- fold rep into the validator's representative equality
  rw [hrepdef] at hrep_eq
  -- step f sid c = step f sid rep : same trans index (classOf c = ci = classOf rep)
  have hstep_eq : step f sid c = step f sid rep := by
    unfold FlatDFA.step
    rw [hcls, hrep_cls]
  -- stepChar sid c = stepChar sid rep via interval congruence
  have hedges : ∀ e ∈ (dfa.states[sid]!).trans,
      intervalConst (f.bounds.getD ci 0) (f.bounds.getD (ci + 1) 0 - 1) e.cls = true := by
    intro e he
    exact (Array.all_eq_true_iff_forall_mem.mp hedges_all) e he
  have hstepchar_eq : (dfa.states[sid]!).stepChar c = (dfa.states[sid]!).stepChar rep := by
    apply stepChar_congr_interval _ c rep (f.bounds.getD ci 0) (f.bounds.getD (ci + 1) 0 - 1)
    · exact hlo_c
    · omega
    · exact hlo_r
    · omega
    · exact hedges
  -- combine
  rw [hstep_eq, hrep_eq, hstepchar_eq]

/-- The validator implies all three agreements. -/
theorem agreements_of_flatValidate (f : FlatDFA) (dfa : DFA)
    (h : flatValidate f dfa = true) :
    StepAgree f dfa ∧ AcceptAgree f dfa ∧ StatesInRange f dfa := by
  unfold flatValidate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hacc, hrange⟩, hstepv⟩, hb⟩, hc⟩ := h
  exact ⟨stepAgree_of_valid f dfa hstepv hb hc,
         acceptAgree_of_valid f dfa hacc,
         statesInRange_of_valid f dfa hrange⟩

/-- Top-level: a validated flat table scans identically to the specification
    `DFA.scan`. This is the soundness of the fast scanner: the untrusted
    `DFA.flatOfDFA` constructor is not proved correct — its output is validated. -/
theorem flatScanArr_eq_scan_of_valid (f : FlatDFA) (dfa : DFA)
    (h : flatValidate f dfa = true) (hstart : 0 < dfa.states.size) (cs : Array Char) :
    DFA.flatScanArr f cs 0 = DFA.scan dfa cs.toList := by
  obtain ⟨hstep, hacc, hrange⟩ := agreements_of_flatValidate f dfa h
  exact flatScanArr_eq_scan f dfa hstep hacc hrange cs hstart

end Lexer
