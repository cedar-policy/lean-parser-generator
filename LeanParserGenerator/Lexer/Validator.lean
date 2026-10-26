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
The a-posteriori validator for generated lexer DFAs
(docs/DESIGN.md §9.7 steps 3–4).

Mirrors the parser's `Runtime/Validator/Safe.lean`: an untrusted construction
(`DFA.build?`) emits a certificate (per-state derivative vectors), a Boolean
validator checks it, and one generic theorem turns a successful check into the
maximal-munch / tokenization guarantees. Per-lexer the Boolean is discharged with
`native_decide`.

The structural difference from the parser (docs/DESIGN.md §9.3): the alphabet is
1.1M scalar values and cannot be enumerated, so every condition touching the
alphabet is interval arithmetic over `CharClass`, and the soundness of testing one
representative character per class rests on `deriv_congr`: `deriv` depends on a
character only through its membership in the classes syntactically present in the
regex.
-/
public import LeanParserGenerator.Lexer.DFA
public import LeanParserGenerator.Lexer.Spec


@[expose] public section

namespace Lexer

open Regex

/-! ### Derivative congruence

`deriv c r` inspects `c` only through `k.mem c` for each class `k` in
`classesOf r`. So two characters that agree on membership in every such class have
the same derivative. This is the lemma that makes it sound to probe one
representative character per edge class (docs/DESIGN.md §9.7, `V3`). -/

/-- Two characters agree on membership in every class syntactically present in
    `r`. -/
def agreeOn (r : Regex) (c₁ c₂ : Char) : Prop :=
  ∀ k ∈ DFA.classesOf r, k.mem c₁ = k.mem c₂

/-- If `c₁` and `c₂` agree on membership in every class of `r`, they have the same
    derivative. By induction on `r`. -/
theorem deriv_congr : ∀ (r : Regex) (c₁ c₂ : Char),
    agreeOn r c₁ c₂ → deriv c₁ r = deriv c₂ r
  | .never, _, _, _ => rfl
  | .epsilon, _, _, _ => rfl
  | .cls k, c₁, c₂, h => by
      have hk : k.mem c₁ = k.mem c₂ := h k (by simp [DFA.classesOf])
      simp only [deriv, hk]
  | .cat a b, c₁, c₂, h => by
      have ha : agreeOn a c₁ c₂ := fun k hk =>
        h k (by simp [DFA.classesOf]; exact Or.inl hk)
      have hb : agreeOn b c₁ c₂ := fun k hk =>
        h k (by simp [DFA.classesOf]; exact Or.inr hk)
      simp only [deriv, deriv_congr a c₁ c₂ ha, deriv_congr b c₁ c₂ hb]
  | .alt a b, c₁, c₂, h => by
      have ha : agreeOn a c₁ c₂ := fun k hk =>
        h k (by simp [DFA.classesOf]; exact Or.inl hk)
      have hb : agreeOn b c₁ c₂ := fun k hk =>
        h k (by simp [DFA.classesOf]; exact Or.inr hk)
      simp only [deriv, deriv_congr a c₁ c₂ ha, deriv_congr b c₁ c₂ hb]
  | .star a, c₁, c₂, h => by
      have ha : agreeOn a c₁ c₂ := fun k hk => h k (by simp [DFA.classesOf]; exact hk)
      simp only [deriv, deriv_congr a c₁ c₂ ha]

/-! ### Interval-set arithmetic over `CharClass`

Because the alphabet cannot be enumerated (docs/DESIGN.md §9.3), the validator
reasons about classes as interval sets. `Nat.memRanges` is membership in a raw
range list; `CharClass.mem` is defined from it. `subsetB`/`disjointB` are the
decidable containment/disjointness checks the validator uses, and the lemmas below
connect them to `CharClass.mem`. -/

/-- Membership of a code point in a raw inclusive-range list. -/
def memRanges (rs : List (Nat × Nat)) (n : Nat) : Bool :=
  rs.any (fun r => r.1 ≤ n && n ≤ r.2)

theorem mem_eq_memRanges (k : CharClass) (c : Char) :
    k.mem c = (if k.neg then !memRanges k.rs c.toNat else memRanges k.rs c.toNat) := by
  cases k with
  | mk neg rs => simp [CharClass.mem, memRanges]

/-- Interval-set containment used by `V3`: every code point of `a` is a code point
    of `b`. The validator checks a Boolean version; here is the semantic relation
    it must witness. `a ⊆ b` at the level of `CharClass.mem`. -/
def clsSubset (a b : CharClass) : Prop := ∀ c : Char, a.mem c = true → b.mem c = true

/-- Interval-set disjointness used by `V3`/`V4`: `a` and `b` share no code point. -/
def clsDisjoint (a b : CharClass) : Prop := ∀ c : Char, a.mem c = true → b.mem c = false

/-- `V3` per (edge class `a`, regex class `b`): the edge class is entirely inside
    the regex class or entirely outside it. This is exactly what makes probing one
    representative of `a` sound for `deriv` (via `deriv_congr`): all characters in
    `a` agree on membership in `b`. -/
def clsInOrOut (a b : CharClass) : Prop := clsSubset a b ∨ clsDisjoint a b

/-- If two characters are both in `a`, and `a` is in-or-out of every class of `r`,
    then they agree on membership in every class of `r`. Combined with
    `deriv_congr`, this is why one representative of an edge class determines the
    derivative of every character in that class. -/
theorem agreeOn_of_clsInOrOut {r : Regex} {a : CharClass} {c₁ c₂ : Char}
    (h₁ : a.mem c₁ = true) (h₂ : a.mem c₂ = true)
    (hio : ∀ k ∈ DFA.classesOf r, clsInOrOut a k) : agreeOn r c₁ c₂ := by
  intro k hk
  rcases hio k hk with hsub | hdis
  · rw [hsub c₁ h₁, hsub c₂ h₂]
  · rw [hdis c₁ h₁, hdis c₂ h₂]

/-! ### Leading classes and dead-complement

A character `c` can make `deriv c r` non-`never` only if it belongs to one of `r`'s
*leading* classes. `firstClasses` collects them; `deriv_never_of_not_firstClasses`
is the deadness lemma the validator's `V4` complement condition rests on: outside
the union of edge classes, every component is dead, so the DFA correctly has no
edge (docs/DESIGN.md §9.7, `V4`). -/

/-- The classes that can appear at the head of a match: a superset of the support
    of the first derivative. For `cat`, the leading classes of `b` count only when
    `a` is nullable. -/
def firstClasses : Regex → List CharClass
  | .never | .epsilon => []
  | .cls k => [k]
  | .cat a b => firstClasses a ++ (if a.nullable then firstClasses b else [])
  | .alt a b => firstClasses a ++ firstClasses b
  | .star a => firstClasses a

/-- If `c` is in none of `r`'s leading classes, the derivative is `never`. By
    induction on `r`, using the smart constructors' collapse of `never`. -/
theorem deriv_never_of_not_firstClasses : ∀ (r : Regex) (c : Char),
    (∀ k ∈ firstClasses r, k.mem c = false) → deriv c r = .never
  | .never, _, _ => rfl
  | .epsilon, _, _ => rfl
  | .cls k, c, h => by
      have hk : k.mem c = false := h k (by simp [firstClasses])
      simp [deriv, hk]
  | .cat a b, c, h => by
      have ha : deriv c a = .never :=
        deriv_never_of_not_firstClasses a c fun k hk =>
          h k (by simp [firstClasses]; exact Or.inl hk)
      simp only [deriv, ha, mkCat]
      by_cases hn : a.nullable
      · have hb : deriv c b = .never :=
          deriv_never_of_not_firstClasses b c fun k hk =>
            h k (by simp [firstClasses, hn]; exact Or.inr hk)
        simp [hn, hb, mkAlt]
      · simp [hn]
  | .alt a b, c, h => by
      have ha : deriv c a = .never :=
        deriv_never_of_not_firstClasses a c fun k hk =>
          h k (by simp [firstClasses]; exact Or.inl hk)
      have hb : deriv c b = .never :=
        deriv_never_of_not_firstClasses b c fun k hk =>
          h k (by simp [firstClasses]; exact Or.inr hk)
      simp [deriv, ha, hb, mkAlt]
  | .star a, c, h => by
      have ha : deriv c a = .never :=
        deriv_never_of_not_firstClasses a c fun k hk =>
          h k (by simp [firstClasses]; exact hk)
      simp [deriv, ha, mkCat]

/-! ### The certificate

`LexCert.vecs` holds one derivative vector per DFA state, in state-index order.
The construction (`DFA.build?`) already computes these vectors, so emitting them is
an annotation, not new work (docs/DESIGN.md §9.7 step 3). The validator checks the
vectors against the DFA edges and accepts; the generic theorem then reads scan
behaviour off the vectors. -/

/-- Per-state derivative-vector certificate for a built DFA. `vecs[s]` is the
    vector of per-rule derivatives at state `s`; `vecs[0]` is the start vector. -/
structure LexCert where
  /-- One derivative vector per DFA state, in state-index order. -/
  vecs : Array (Array Regex)
  deriving Inhabited

/-! ### Representatives of an edge class

`transitionsOf` only ever emits non-negated classes with a non-empty range list
(`ranges false ((lo,hi) :: _)`). `edgeRep` is a representative code point of such a
class; `edgeRep_mem` shows it is a member, so it is a legitimate probe point. -/

/-- A representative character of an edge class: `repOf` of its first range's low
    endpoint. Meaningful only for non-negated, non-empty classes (which is all
    `transitionsOf` emits). -/
def edgeRep (cls : CharClass) : Char :=
  match cls.rs with
  | [] => default
  | (lo, _) :: _ => DFA.repOf lo

/-! ### Boolean validator conditions (V0–V5)

All conditions are decidable; the alphabet-touching ones (`V2`, `V4`) are interval
arithmetic over `CharClass`, never enumeration (docs/DESIGN.md §9.3). -/

/-- Enumerate the code points of a non-negated, explicit range list. Retained for
    `V4` coverage of small leading classes and for the point-level lemmas; `V2` no
    longer enumerates (see `cellReps`). -/
def rangePoints (rs : List (Nat × Nat)) : List Nat :=
  rs.flatMap fun (lo, hi) => (List.range (hi + 1 - lo)).map (lo + ·)

/-! ### Interval refinement for `V2` (docs/DESIGN.md §9.3)

`V2` must check that `deriv c` maps the source vector `v` to the edge target for
*every* `c` in the edge class. Enumerating code points is intractable for
Unicode-wide edges (Cedar: 3.3M points). Instead we test one representative per
*cell*: a maximal sub-interval of the edge on which `deriv` is constant across `v`.

`deriv c r` depends on `c` only through `k.mem c` for `k ∈ classesOf r`
(`deriv_congr`), and `k.mem` is `memRanges k.rs` up to negation. `memRanges rs` is
constant between two code points with no endpoint of `rs` strictly between them.
So the cut points are the raw endpoints `lo` and `hi+1` of every class of every
component; the cells they induce on the edge intervals are where one representative
suffices. For Cedar this is 293 representatives instead of 3.3M points. -/

/-- Raw cut points of a range list: each interval contributes its low endpoint and
    one past its high endpoint. `memRanges rs` cannot change value except at one of
    these points. -/
def rangeEndpoints (rs : List (Nat × Nat)) : List Nat :=
  rs.flatMap fun (lo, hi) => [lo, hi + 1]

/-- All cut points relevant to a source vector `v`: the raw endpoints of every
    class syntactically present in any component. Testing one representative per
    cell delimited by these points is sound for `deriv` over all of `v`. -/
def vecEndpoints (v : Array Regex) : List Nat :=
  (v.toList.flatMap fun r => (DFA.classesOf r).flatMap fun k => rangeEndpoints k.rs)

/-- Split an interval `[lo, hi]` at sorted cut points into cells, returning each
    cell's `(cellLo, cellHi)` bounds: `[lo, c₁-1], [c₁, c₂-1], …, [cₖ, hi]`. Used by
    `cellReps`. -/
def splitCells (hi : Nat) : Nat → List Nat → List (Nat × Nat)
  | start, [] => [(start, hi)]
  | start, b :: bs => (start, b - 1) :: splitCells hi b bs

/-- Representatives of an edge's intervals against cut points `bs`: for each
    interval `(lo, hi)`, the `(cellLo, cellHi)` bounds of every cell delimited by
    the cut points strictly inside `(lo, hi]`. One representative per cell
    (docs/DESIGN.md §9.3); the rep character is `DFA.repOf cellLo`, dodging the
    surrogate gap like the DFA construction. -/
def cellReps (bs : List Nat) (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  rs.flatMap fun (lo, hi) =>
    let cuts := (bs.filter (fun b => lo < b && b ≤ hi)).mergeSort (· ≤ ·)
    splitCells hi lo cuts

/-- `memRanges rs` agrees on `n` and `m` (with `n ≤ m`) when no endpoint of `rs`
    lies strictly in `(n, m]`. Each range `(lo, hi)` contributes `lo` and `hi+1`;
    if neither is in `(n, m]` then `(lo ≤ n ≤ hi) = (lo ≤ m ≤ hi)`, so the `any`
    is unchanged. -/
theorem memRanges_agree_of_noEndpointBetween (rs : List (Nat × Nat)) {n m : Nat}
    (hnm : n ≤ m) (hcut : ∀ p ∈ rangeEndpoints rs, ¬ (n < p ∧ p ≤ m)) :
    memRanges rs n = memRanges rs m := by
  simp only [memRanges]
  induction rs with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨lo, hi⟩ := hd
      have hlo : ¬ (n < lo ∧ lo ≤ m) := hcut lo (by simp [rangeEndpoints])
      have hhi : ¬ (n < hi + 1 ∧ hi + 1 ≤ m) := hcut (hi + 1) (by simp [rangeEndpoints])
      have htl : ∀ p ∈ rangeEndpoints tl, ¬ (n < p ∧ p ≤ m) := by
        intro p hp
        exact hcut p (by
          simp only [rangeEndpoints, List.flatMap_cons, List.mem_append]
          exact Or.inr hp)
      have hhd : (lo ≤ n && n ≤ hi) = (lo ≤ m && m ≤ hi) := by
        -- Turn the two "no endpoint between" facts into omega-usable disjunctions.
        have hlo' : lo ≤ n ∨ m < lo := by
          rcases Nat.lt_or_ge n lo with h | h
          · exact Or.inr (Nat.lt_of_not_le fun hc => hlo ⟨h, hc⟩)
          · exact Or.inl h
        have hhi' : hi < n ∨ m ≤ hi := by
          rcases Nat.lt_or_ge hi m with h | h
          · exact Or.inl (Nat.lt_of_not_le fun hc => hhi ⟨Nat.lt_succ_of_le hc, h⟩)
          · exact Or.inr h
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      simp only [List.any_cons, hhd, ih htl]

/-- Two characters agree on every class of every component of `v` when no cut point
    of `v` lies strictly between their code points. This is the cell-soundness
    lemma behind `cellReps`: within a cell, `deriv` is constant across `v`. Stated
    on characters (not raw `Nat`) so no `Char.ofNat`/`toNat` round-trip is needed —
    the surrogate gap never appears because both sides are real characters. -/
theorem agreeOn_of_noEndpointBetween {v : Array Regex} {c₁ c₂ : Char}
    (hle : c₁.toNat ≤ c₂.toNat)
    (hcut : ∀ p ∈ vecEndpoints v, ¬ (c₁.toNat < p ∧ p ≤ c₂.toNat))
    (r : Regex) (hr : r ∈ v) : agreeOn r c₁ c₂ := by
  intro k hk
  have hk_endpoints : ∀ p ∈ rangeEndpoints k.rs, ¬ (c₁.toNat < p ∧ p ≤ c₂.toNat) := by
    intro p hp
    apply hcut p
    simp only [vecEndpoints, List.mem_flatMap]
    exact ⟨r, Array.mem_toList_iff.mpr hr, k, hk, hp⟩
  have hmr := memRanges_agree_of_noEndpointBetween k.rs hle hk_endpoints
  rw [mem_eq_memRanges, mem_eq_memRanges, hmr]

/-! ### `splitCells` coverage

For the representative check to be sound, every point of an edge interval must lie
in some produced cell whose low endpoint is a valid representative: no cut point
lies in `(cellLo, n]` for `n` in the cell. `splitCells_covers` is that invariant,
by induction on the cut list. Sorted cuts (from `mergeSort`) make the interior of
each cell cut-free; duplicate cuts only create empty cells, which are harmless. -/

/-- Every point `n ∈ [start, hi]` lies in a produced cell `(cLo, cHi)` with
    `start ≤ cLo ≤ n ≤ cHi` and no cut in `(cLo, cHi]` (so no cut lies strictly
    between any two points of the cell). Requires the cut list sorted ascending
    (`Pairwise (· ≤ ·)`, which `mergeSort` produces) and every cut `≥ start`. -/
theorem splitCells_covers (hi : Nat) :
    ∀ (cuts : List Nat) (start n : Nat),
      start ≤ n → n ≤ hi →
      (∀ b ∈ cuts, start ≤ b) →
      (∀ b ∈ cuts, b ≤ hi) →
      List.Pairwise (· ≤ ·) cuts →
      ∃ cLo cHi, (cLo, cHi) ∈ splitCells hi start cuts ∧
        cLo ≤ n ∧ n ≤ cHi ∧ start ≤ cLo ∧ cHi ≤ hi ∧
        (∀ b ∈ cuts, ¬ (cLo < b ∧ b ≤ cHi)) := by
  intro cuts
  induction cuts with
  | nil =>
      intro start n hsn hnhi _ _ _
      exact ⟨start, hi, by simp [splitCells], hsn, hnhi, Nat.le_refl _, Nat.le_refl _, by simp⟩
  | cons b bs ih =>
      intro start n hsn hnhi hge hle hsorted
      by_cases hnb : n < b
      · -- n is in the first cell [start, b-1]
        have hbhi : b ≤ hi := hle b (by simp)
        refine ⟨start, b - 1, by simp [splitCells], hsn, by omega, Nat.le_refl _, by omega, ?_⟩
        intro b' hb'
        rcases List.mem_cons.mp hb' with h | h
        · subst h; rintro ⟨_, hle'⟩; omega
        · have hbb' : b ≤ b' := List.rel_of_pairwise_cons hsorted h
          rintro ⟨_, hle'⟩; omega
      · -- n ≥ b: recurse into the tail with start := b.
        have hbn : b ≤ n := Nat.le_of_not_lt hnb
        have hge' : ∀ b' ∈ bs, b ≤ b' := fun b' hb' => List.rel_of_pairwise_cons hsorted hb'
        have hle' : ∀ b' ∈ bs, b' ≤ hi := fun b' hb' => hle b' (by simp [hb'])
        have hsorted' : List.Pairwise (· ≤ ·) bs := hsorted.of_cons
        obtain ⟨cLo, cHi, hcellMem, hcLo, hcHi, hbcLo, hcHihi, hcut⟩ :=
          ih b n hbn hnhi hge' hle' hsorted'
        have hsb : start ≤ b := hge b (by simp)
        refine ⟨cLo, cHi, ?_, hcLo, hcHi, by omega, hcHihi, ?_⟩
        · simp only [splitCells, List.mem_cons]; exact Or.inr hcellMem
        · intro b' hb'
          rcases List.mem_cons.mp hb' with h | h
          · subst h; exact fun hcon => absurd hcon.1 (Nat.not_lt.mpr hbcLo)
          · exact hcut b' h





/-- `a ⊆ b` for a non-negated edge class `a`: every code point enumerated from
    `a`'s ranges is in `b`. Directly reflects `clsSubset` (see
    `clsSubset_of_subsetB`). -/
def subsetB (a b : CharClass) : Bool :=
  (rangePoints a.rs).all fun n => b.mem (Char.ofNat n)

/-- `a` and `b` are disjoint for a non-negated edge class `a`: no code point
    enumerated from `a`'s ranges is in `b`. Directly reflects `clsDisjoint`. -/
def disjointB (a b : CharClass) : Bool :=
  (rangePoints a.rs).all fun n => b.mem (Char.ofNat n) == false

/-- For a non-negated class, membership means the code point is one of the
    enumerated `rangePoints`. -/
theorem toNat_mem_rangePoints {a : CharClass} (hneg : a.neg = false) {c : Char}
    (h : a.mem c = true) : c.toNat ∈ rangePoints a.rs := by
  simp only [CharClass.mem, hneg, Bool.false_eq_true, ite_false, List.any_eq_true] at h
  obtain ⟨r, hr, hmem⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  simp only [rangePoints, List.mem_flatMap]
  refine ⟨r, hr, ?_⟩
  simp only [List.mem_map, List.mem_range]
  exact ⟨c.toNat - r.1, by omega, by omega⟩

/-- `subsetB` soundly witnesses `clsSubset` for a non-negated edge class. -/
theorem clsSubset_of_subsetB {a b : CharClass} (hneg : a.neg = false)
    (h : subsetB a b = true) : clsSubset a b := by
  intro c hc
  have hn := toNat_mem_rangePoints hneg hc
  have := (List.all_eq_true.mp h) c.toNat hn
  rwa [Char.ofNat_toNat] at this

/-- `disjointB` soundly witnesses `clsDisjoint` for a non-negated edge class. -/
theorem clsDisjoint_of_disjointB {a b : CharClass} (hneg : a.neg = false)
    (h : disjointB a b = true) : clsDisjoint a b := by
  intro c hc
  have hn := toNat_mem_rangePoints hneg hc
  have hb := (List.all_eq_true.mp h) c.toNat hn
  rw [Char.ofNat_toNat] at hb
  simpa using hb

/-- Furthest point (exclusive) reachable from `cur` by a `lo`-sorted interval list:
    extend across each interval whose `lo ≤ cur`; stop at the first gap. -/
def sweep (cur : Nat) : List (Nat × Nat) → Nat
  | [] => cur
  | (lo, hi) :: rest => if lo ≤ cur then sweep (max cur (hi + 1)) rest else cur

/-- `sweep` never returns below its start point. -/
theorem sweep_ge_start : ∀ (ivs : List (Nat × Nat)) (cur : Nat), cur ≤ sweep cur ivs := by
  intro ivs
  induction ivs with
  | nil => intro cur; simp [sweep]
  | cons hd rest ih =>
      intro cur
      obtain ⟨lo, hi⟩ := hd
      simp only [sweep]
      by_cases h : lo ≤ cur
      · simp only [h, ite_true]
        have := ih (max cur (hi+1)); omega
      · simp only [h, ite_false]; exact Nat.le_refl _

/-- Core sweep soundness: for a `lo`-sorted interval list, if `start ≤ n` and
    `n < sweep start sorted`, then `n` is in some interval. -/
theorem mem_of_lt_sweep : ∀ (ivs : List (Nat × Nat)),
    List.Pairwise (fun a b => a.1 ≤ b.1) ivs →
    ∀ (start n : Nat), start ≤ n → n < sweep start ivs → memRanges ivs n = true := by
  intro ivs
  induction ivs with
  | nil => intro _ start n _ hn; simp only [sweep] at hn; omega
  | cons hd rest ih =>
      intro hsorted start n hstart hn
      obtain ⟨lo, hi⟩ := hd
      simp only [sweep] at hn
      simp only [memRanges, List.any_cons]
      by_cases hle : lo ≤ start
      · simp only [hle, ite_true] at hn
        by_cases hnhi : n ≤ hi
        · have : (lo ≤ n && n ≤ hi) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
          simp [this]
        · have hsorted' := hsorted.of_cons
          have hstart' : max start (hi+1) ≤ n := by omega
          have hrec := ih hsorted' (max start (hi+1)) n hstart' hn
          simp only [memRanges] at hrec
          simp [hrec]
      · simp only [hle, ite_false] at hn
        omega

/-! ### Edge coverage (`V4`), negation-aware interval version

A leading class `k` of a component is covered by the DFA's edges when every
*member* of `k` (accounting for `k.neg`) lies in some edge class. This is interval
coverage, not point enumeration: for a wide or negated leading class (Cedar's
string/comment rules have `[^"\]`, `[^\n]` leading classes) enumeration is
intractable and the old non-negated-only check was wrong. The `none` branch of
`validate_step` needs: a character in no edge class is in no leading class, hence
every component's derivative is `never`. -/

/-- `[lo, hi]` is covered by the union of `ivs`: sweeping from `lo` over the
    `lo`-sorted `ivs` reaches past `hi`. -/
def coversInterval (lo hi : Nat) (ivs : List (Nat × Nat)) : Bool :=
  decide (hi < sweep lo (ivs.mergeSort (fun a b => a.1 ≤ b.1)))

/-- Soundness of `coversInterval`: every point of `[lo, hi]` is in the union of
    `ivs`. -/
theorem memRanges_of_coversInterval {lo hi : Nat} {ivs : List (Nat × Nat)}
    (h : coversInterval lo hi ivs = true) {n : Nat} (h1 : lo ≤ n) (h2 : n ≤ hi) :
    memRanges ivs n = true := by
  simp only [coversInterval, decide_eq_true_eq] at h
  have hn : n < sweep lo (ivs.mergeSort (fun a b => a.1 ≤ b.1)) := by omega
  have hsorted : List.Pairwise (fun a b => a.1 ≤ b.1)
      (ivs.mergeSort (fun a b => a.1 ≤ b.1)) := by
    have hp := List.pairwise_mergeSort (le := fun a b => a.1 ≤ b.1)
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by rcases Nat.le_total a.1 b.1 with h | h <;> simp [h]) ivs
    exact hp.imp (by intro a b h; simpa using h)
  have hmem : memRanges (ivs.mergeSort (fun a b => a.1 ≤ b.1)) n = true :=
    mem_of_lt_sweep _ hsorted lo n h1 hn
  simpa [memRanges, List.mem_mergeSort] using hmem

/-- The union of edge classes' raw ranges (all edges are non-negated: V2 checks
    `e.cls.neg == false`). Membership in this union is `∃ edge, c ∈ edge.cls`. -/
def edgeUnion (es : Array DTrans) : List (Nat × Nat) :=
  es.toList.flatMap (·.cls.rs)

/-- V4 for one leading class `k`: every member of `k` is covered by the edge union.
    Negation-aware: for `k = [S]`, every interval of `S` is covered; for `k = [^S]`,
    `S ∪ edgeUnion` covers all of `[0, maxCodePoint]` (so the complement of `S` is
    covered). -/
def coveredByEdges (k : CharClass) (es : Array DTrans) : Bool :=
  if k.neg then
    coversInterval 0 DFA.maxCodePoint (k.rs ++ edgeUnion es)
  else
    k.rs.all fun r => coversInterval r.1 r.2 (edgeUnion es)

/-- Membership in `edgeUnion` gives a matching (non-negated) edge, provided every
    edge is non-negated. -/
theorem edge_of_memRanges_edgeUnion {es : Array DTrans}
    (hallneg : ∀ e ∈ es, e.cls.neg = false) {c : Char}
    (h : memRanges (edgeUnion es) c.toNat = true) : ∃ e ∈ es, e.cls.mem c = true := by
  simp only [edgeUnion, memRanges, List.any_eq_true, List.mem_flatMap, Array.mem_toList_iff] at h
  obtain ⟨r, ⟨e, he, hr⟩, hrmem⟩ := h
  refine ⟨e, he, ?_⟩
  rw [mem_eq_memRanges, hallneg e he, ite_eq_right (by simp)]
  simp only [memRanges, List.any_eq_true]
  exact ⟨r, hr, hrmem⟩

/-- If `k`'s members are covered by the edges (and all edges are non-negated), then
    any member of `k` is a member of some edge class. Negation-aware. `c` must be a
    valid scalar value (it is, being a `Char`) so its code point is `≤ maxCodePoint`. -/
theorem edge_of_coveredByEdges {k : CharClass} {es : Array DTrans}
    (hallneg : ∀ e ∈ es, e.cls.neg = false) (h : coveredByEdges k es = true) {c : Char}
    (hc : k.mem c = true) : ∃ e ∈ es, e.cls.mem c = true := by
  apply edge_of_memRanges_edgeUnion hallneg
  have hcmax : c.toNat ≤ DFA.maxCodePoint := by
    have hv := c.valid; have he : c.toNat = c.val.toNat := rfl
    unfold DFA.maxCodePoint; rw [he]; omega
  unfold coveredByEdges at h
  by_cases hkneg : k.neg = true
  · -- negated: k.rs ∪ edgeUnion covers [0, max]; c ∉ k.rs (since k.mem c); so c ∈ edgeUnion.
    simp only [hkneg, ite_true] at h
    have hcov := memRanges_of_coversInterval h (Nat.zero_le _) hcmax
    have hnotk : memRanges k.rs c.toNat = false := by
      rw [mem_eq_memRanges, hkneg, ite_eq_left rfl] at hc
      simpa using hc
    have happend : memRanges (k.rs ++ edgeUnion es) c.toNat
        = (memRanges k.rs c.toNat || memRanges (edgeUnion es) c.toNat) := by
      simp only [memRanges, List.any_append]
    rw [happend, hnotk] at hcov
    simpa using hcov
  · -- non-negated: some interval of k.rs contains c.toNat; that interval is covered.
    simp only [hkneg] at h
    have hkneg' : k.neg = false := by simpa using hkneg
    rw [mem_eq_memRanges, hkneg', ite_eq_right (by simp)] at hc
    simp only [memRanges, List.any_eq_true] at hc
    obtain ⟨r, hr, hrmem⟩ := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrmem
    have hcov := (List.all_eq_true.mp h) r hr
    exact memRanges_of_coversInterval hcov hrmem.1 hrmem.2

/-! ### The validator conditions (V0–V5)

`validate rules dfa cert` conjoins:

  * `V0`: `cert.vecs[0] = rules` (start vector is the mode's rule regexes);
  * `V1`: every state's `accept` is `vec.findIdx? nullable`;
  * `V2`: every edge is a non-negated class, its target is in range, and *every*
    code point of the edge class derives the source vector to the target vector.
    Enumerating the edge's code points and checking derivative-vector equality is
    sound and complete (no representative approximation): the merged edge classes
    that `transitionsOf` emits need not respect individual regex-class boundaries,
    so a membership-agreement condition would wrongly reject them. Cheap for the
    small edge classes of typical lexers; a Unicode-wide edge would be slow, which
    is the interval-arithmetic optimization left for large lexers (§9.3).
  * `V4`: every leading class of every component is covered by the edges (so a
    character in no edge is dead);
  * `V5`: `cert.vecs.size = dfa.states.size` (the build completed; every state has
    a vector). -/

/-- Check one edge `e` of a state with source vector `v`. `V2`: non-negated class,
    target in range, and for one representative per boundary cell of the edge (a
    `cellReps` cell low endpoint, mapped to a character by `DFA.repOf`), `deriv`
    maps `v` to the target vector. Testing one representative per cell is sound
    because `deriv` is constant across a cell (`agreeOn_of_noEndpointBetween`);
    this is the interval-refined `V2` (docs/DESIGN.md §9.3), 293 reps for Cedar. -/
def edgeValid (cert : LexCert) (v : Array Regex) (e : DTrans) : Bool :=
  (e.cls.neg == false) &&
  (e.target < cert.vecs.size) &&
  ((cellReps (vecEndpoints v) e.cls.rs).all fun cell =>
    decide (cert.vecs[e.target]! = v.map (deriv (DFA.repOf cell.1))))

/-- Check one state `s`. `V1`, `V2`, `V4`. -/
def stateValid (dfa : DFA) (cert : LexCert) (s : Nat) : Bool :=
  let v := cert.vecs[s]!
  let st := dfa.states[s]!
  (decide (st.accept = v.findIdx? nullable)) &&
  (st.trans.all fun e => edgeValid cert v e) &&
  (v.all fun r => (firstClasses r).all fun k => coveredByEdges k st.trans)

/-- The aggregate lexer-DFA validator. `V0`, `V5`, and every state's `stateValid`.
    `rules` is the mode's ordered rule regexes. -/
def validate (rules : Array Regex) (dfa : DFA) (cert : LexCert) : Bool :=
  (decide (cert.vecs.size = dfa.states.size)) &&
  (0 < cert.vecs.size) &&
  (decide (cert.vecs[0]! = rules)) &&
  ((List.range dfa.states.size).all fun s => stateValid dfa cert s)

/-! ### The step lemma

The certificate step lemma (docs/DESIGN.md §9.7 step 4): if validation succeeds
then, for every state `s` and character `c`, following the DFA edge for `c` lands
at a state whose vector is `vecs[s].map (deriv c)`, and if there is no edge then
every component's derivative is `never`. This is the invariant that makes
`DFA.scan` track the componentwise derivative — i.e. compute maximal munch. -/

/-- Extract the per-state check from a successful validation. -/
theorem stateValid_of_validate {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (h : validate rules dfa cert = true) {s : Nat} (hs : s < dfa.states.size) :
    stateValid dfa cert s = true := by
  simp only [validate, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, hstates⟩ := h
  have := (List.all_eq_true.mp hstates) s (by simp [List.mem_range, hs])
  exact this

/-- A character's code point avoids the surrogate gap and is below the max. This
    is `c.valid` transported to `Nat` for `omega`. -/
theorem toNat_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) :=
  c.valid

/-- `Char.ofNat n` round-trips through `toNat` for a valid scalar value `n`. -/
theorem toNat_ofNat_of_valid {n : Nat}
    (hn : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) : (Char.ofNat n).toNat = n := by
  have hvalid : n.isValidChar := hn
  have hlt : n < UInt32.size := by
    rcases hn with h | ⟨_, h⟩ <;> · unfold UInt32.size; omega
  show (Char.ofNat n).val.toNat = n
  simp only [Char.ofNat, dite_eq_left hvalid, Char.ofNatAux]
  simp [UInt32.toNat, BitVec.toNat_ofNatLT]

/-- `DFA.repOf cLo` for a valid, in-range low endpoint has `toNat = cLo`
    (non-surrogate) or `= 0xE000` (surrogate), and in both cases its `toNat` is a
    valid scalar value `≥ cLo`. -/
theorem repOf_toNat_cases (cLo : Nat) (hcLo : cLo < 0x110000) :
    (DFA.repOf cLo).toNat = cLo ∨ ((DFA.repOf cLo).toNat = 0xE000 ∧ 0xD800 ≤ cLo ∧ cLo ≤ 0xDFFF) := by
  unfold DFA.repOf
  by_cases hsur : 0xD800 ≤ cLo && cLo ≤ 0xDFFF
  · simp only [hsur, ite_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsur
    right; exact ⟨by decide, hsur.1, hsur.2⟩
  · simp only [hsur, Bool.false_eq_true, ite_false]
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le] at hsur
    left
    apply toNat_ofNat_of_valid
    by_cases hlt : cLo < 0xD800
    · exact Or.inl hlt
    · exact Or.inr ⟨by have := hsur (by omega); omega, hcLo⟩

/-- `edge_step` gives the target's vector as `c`'s derivative for every `c` in the
    edge class, via the interval-refined `V2`: `c.toNat` lies in some cell whose
    representative was tested, and `deriv` is constant across the cell
    (`agreeOn_of_noEndpointBetween` + `deriv_congr`). -/
theorem edge_step {cert : LexCert} {v : Array Regex} {e : DTrans}
    (h : edgeValid cert v e = true) {c : Char} (hc : e.cls.mem c = true) :
    e.target < cert.vecs.size ∧ cert.vecs[e.target]! = v.map (deriv c) := by
  simp only [edgeValid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hneg, htgt⟩, hcells⟩ := h
  have hneg : e.cls.neg = false := by simpa using hneg
  refine ⟨htgt, ?_⟩
  -- c.toNat lies in some interval (lo, hi) of the (non-negated) edge class.
  have hmemr : memRanges e.cls.rs c.toNat = true := by
    have hmm := mem_eq_memRanges e.cls c; rw [hneg, ite_eq_right (by simp)] at hmm
    rw [← hmm]; exact hc
  simp only [memRanges, List.any_eq_true] at hmemr
  obtain ⟨⟨lo, hi⟩, hr, hrmem⟩ := hmemr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrmem
  obtain ⟨hloc, hchi⟩ := hrmem
  -- Validity of c.toNat.
  have hcvalid := toNat_valid c
  -- The cut points for this interval: filter of vecEndpoints, sorted.
  let cuts := ((vecEndpoints v).filter (fun b => lo < b && b ≤ hi)).mergeSort (· ≤ ·)
  have hcuts : cuts = ((vecEndpoints v).filter (fun b => lo < b && b ≤ hi)).mergeSort (· ≤ ·) := rfl
  have hcuts_ge : ∀ b ∈ cuts, lo ≤ b := by
    intro b hb
    rw [hcuts, List.mem_mergeSort, List.mem_filter] at hb
    have h2 := hb.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    omega
  have hcuts_le : ∀ b ∈ cuts, b ≤ hi := by
    intro b hb
    rw [hcuts, List.mem_mergeSort, List.mem_filter] at hb
    have h2 := hb.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    omega
  have hcuts_sorted : List.Pairwise (· ≤ ·) cuts := by
    rw [hcuts]
    have hp := List.pairwise_mergeSort (le := fun a b => a ≤ b)
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by rcases Nat.le_total a b with h | h <;> simp [h])
      ((vecEndpoints v).filter (fun b => lo < b && b ≤ hi))
    exact hp.imp (by intro a b h; simpa using h)
  -- Locate the cell containing c.toNat.
  obtain ⟨cLo, cHi, hcellMem, hcLoLe, hLecHi, hloLe, hcHihi, hnocut⟩ :=
    splitCells_covers hi cuts lo c.toNat hloc hchi hcuts_ge hcuts_le hcuts_sorted
  -- This cell is in cellReps, so it was tested.
  have hcellReps : (cLo, cHi) ∈ cellReps (vecEndpoints v) e.cls.rs := by
    simp only [cellReps, List.mem_flatMap]
    exact ⟨(lo, hi), hr, by rw [← hcuts]; exact hcellMem⟩
  have htested := (List.all_eq_true.mp hcells) (cLo, cHi) hcellReps
  simp only [decide_eq_true_eq] at htested
  -- The representative character rep = repOf cLo; its toNat is in the cell.
  have hcLoMax : cLo < 0x110000 := by omega
  have hrepCases := repOf_toNat_cases cLo hcLoMax
  have hrepInCell : cLo ≤ (DFA.repOf cLo).toNat ∧ (DFA.repOf cLo).toNat ≤ cHi := by
    rcases hrepCases with heq | ⟨heq, hs1, hs2⟩
    · rw [heq]; exact ⟨Nat.le_refl _, Nat.le_trans hcLoLe hLecHi⟩
    · -- surrogate: c.toNat ∈ [cLo,cHi], c valid ⟹ c.toNat ≥ 0xE000 ⟹ cHi ≥ 0xE000.
      rw [heq]
      refine ⟨by omega, ?_⟩
      -- c.toNat ≥ cLo ≥ 0xD800; valid ⟹ c.toNat > 0xDFFF; and c.toNat ≤ cHi.
      rcases hcvalid with h | ⟨h1, _⟩
      · omega
      · omega
  -- No vecEndpoint lies strictly between rep.toNat and c.toNat (both in the cell).
  have hagree : ∀ (r : Regex), r ∈ v → agreeOn r (DFA.repOf cLo) c := by
    intro r hrmemv
    -- WLOG order by toNat; both in [cLo, cHi], cell has no cut.
    have hcutMem : ∀ p ∈ vecEndpoints v, lo < p → p ≤ hi → p ∈ cuts := by
      intro p hp hlp hph
      rw [hcuts, List.mem_mergeSort, List.mem_filter]
      exact ⟨hp, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hlp, hph⟩⟩
    -- The "no endpoint between x and y" fact for x,y ∈ [cLo,cHi].
    have hbetween : ∀ (x y : Nat), cLo ≤ x → x ≤ cHi → cLo ≤ y → y ≤ cHi →
        x ≤ y → (∀ p ∈ vecEndpoints v, ¬ (x < p ∧ p ≤ y)) := by
      intro x y hx1 hx2 hy1 hy2 hxy p hp
      rintro ⟨hpx, hpy⟩
      -- p ∈ (x, y] ⊆ (cLo, cHi] ⊆ (lo, hi]; so p is a cut in (cLo, cHi]: contra hnocut.
      have hlp : lo < p := by have := hloLe; omega
      have hph : p ≤ hi := by have := hcHihi; omega
      have hpcut : p ∈ cuts := hcutMem p hp hlp hph
      exact hnocut p hpcut ⟨by omega, by omega⟩
    rcases Nat.le_total (DFA.repOf cLo).toNat c.toNat with hle | hle
    · exact agreeOn_of_noEndpointBetween hle
        (hbetween _ _ hrepInCell.1 hrepInCell.2 hcLoLe hLecHi hle) r hrmemv
    · have hsymm := agreeOn_of_noEndpointBetween hle
        (hbetween _ _ hcLoLe hLecHi hrepInCell.1 hrepInCell.2 hle) r hrmemv
      exact fun k hk => (hsymm k hk).symm
  -- Conclude: deriv c agrees with deriv (repOf cLo) on every component of v.
  have hmapeq : v.map (deriv (DFA.repOf cLo)) = v.map (deriv c) := by
    apply Array.map_congr_left
    intro r hrmemv
    exact deriv_congr r _ _ (hagree r hrmemv)
  rw [htested, hmapeq]

/-! ### `stepChar` characterization

`stepChar st c` is `findSome?` over the edges; `some t` means some edge matches `c`
and yields `t`, and `none` means no edge matches `c`. -/

/-- If `stepChar` finds a target, some matching edge produced it. -/
theorem stepChar_some {st : DState} {c : Char} {t : Nat}
    (h : st.stepChar c = some t) : ∃ e ∈ st.trans, e.cls.mem c = true ∧ e.target = t := by
  simp only [DState.stepChar, Array.findSome?_eq_some_iff] at h
  obtain ⟨pre, x, post, hst, hx, _hpost⟩ := h
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [hst]; simp
  · by_cases hcm : x.cls.mem c = true <;> simp_all
  · by_cases hcm : x.cls.mem c = true <;> simp_all

/-- If `stepChar` finds nothing, no edge matches `c`. -/
theorem stepChar_none {st : DState} {c : Char}
    (h : st.stepChar c = none) : ∀ e ∈ st.trans, e.cls.mem c = false := by
  simp only [DState.stepChar, Array.findSome?_eq_none_iff] at h
  intro e he
  have hthis := h e he
  by_cases hcm : e.cls.mem c = true <;> simp_all

/-! ### The step lemma -/

/-- **Step lemma.** From a successful validation, following the DFA transition for
    `c` at any state `s` lands at a state whose vector is `vecs[s].map (deriv c)`;
    if there is no transition then every component's derivative is `never`. -/
theorem validate_step {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : validate rules dfa cert = true) {s : Nat} (hs : s < dfa.states.size)
    (c : Char) :
    (∀ t, (dfa.states[s]!).stepChar c = some t →
        t < cert.vecs.size ∧ cert.vecs[t]! = (cert.vecs[s]!).map (deriv c)) ∧
    ((dfa.states[s]!).stepChar c = none →
        ∀ r ∈ cert.vecs[s]!, deriv c r = .never) := by
  have hst := stateValid_of_validate hval hs
  simp only [stateValid, Bool.and_eq_true] at hst
  obtain ⟨⟨_hacc, hedges⟩, hcover⟩ := hst
  constructor
  · -- some case
    intro t hstep
    obtain ⟨e, he, hmem, htgt⟩ := stepChar_some hstep
    obtain ⟨i, hi, hei⟩ := Array.mem_iff_getElem.mp he
    have hev : edgeValid cert (cert.vecs[s]!) e = true := by
      have := (Array.all_eq_true.mp hedges) i hi; rwa [hei] at this
    have := edge_step hev hmem
    rw [htgt] at this
    exact this
  · -- none case
    intro hstep r hr
    have hnone := stepChar_none hstep
    -- Every edge is non-negated (from the V2 edge check).
    have hallneg : ∀ e ∈ (dfa.states[s]!).trans, e.cls.neg = false := by
      intro e he
      obtain ⟨i, hi, hei⟩ := Array.mem_iff_getElem.mp he
      have hev : edgeValid cert (cert.vecs[s]!) e = true := by
        have := (Array.all_eq_true.mp hedges) i hi; rwa [hei] at this
      simp only [edgeValid, Bool.and_eq_true] at hev
      have := hev.1.1; simpa using this
    -- r's leading classes are all covered by the edges; c matches no edge, so c is
    -- in none of r's leading classes; hence deriv c r = never.
    obtain ⟨i, hi, hri⟩ := Array.mem_iff_getElem.mp hr
    have hrcover : (firstClasses r).all (fun k =>
        coveredByEdges k (dfa.states[s]!).trans) = true := by
      have := (Array.all_eq_true.mp hcover) i hi; rwa [hri] at this
    apply deriv_never_of_not_firstClasses r c
    intro k hk
    have hkcov := (List.all_eq_true.mp hrcover) k hk
    by_cases hmemk : k.mem c = true
    · obtain ⟨e, he, hem⟩ := edge_of_coveredByEdges hallneg hkcov hmemk
      rw [hnone e he] at hem
      exact absurd hem (by simp)
    · simpa using hmemk

/-! ### Scan tracks the derivative vector

`fusedScan` is the spec-level maximal munch over a derivative *vector*: it accepts
by `findIdx? nullable`, steps by `map (deriv c)`, and mirrors `DFA.scan.go`'s
control flow. `scan_eq_fusedScan` proves the validated DFA scan equals it — this is
where `validate_step` and `V1` are used. `fusedScan_start_eq_bestMatch` (pure regex
reasoning, no DFA) then equates it with `bestMatch`. -/

/-- Spec-level fused maximal munch over a derivative vector, mirroring
    `DFA.scan.go`: accept via `findIdx? nullable`, step via `map (deriv c)`, and
    continue while the (abstract) transition is defined. Dead vectors never update
    `best` (nothing is nullable), so this matches `DFA.scan` and, separately,
    `bestMatch`. -/
def fusedScan (v : Array Regex) (cs : List Char) (pos : Nat)
    (best : Option (Nat × Nat)) : Option (Nat × Nat) :=
  let best := match v.findIdx? nullable with
    | some rule => some (rule, pos)
    | none => best
  match cs with
  | [] => best
  | c :: rest =>
      if (v.map (deriv c)).all isNever then best
      else fusedScan (v.map (deriv c)) rest (pos + 1) best
termination_by cs.length

/-- A dead derivative vector never updates `best`: `findIdx? nullable` is `none`
    (nothing is nullable) and stepping keeps it dead. So `fusedScan` returns `best`
    unchanged. -/
theorem fusedScan_dead_frozen (v : Array Regex) :
    ∀ (cs : List Char) (pos : Nat) (best : Option (Nat × Nat)),
      v.all isNever = true → fusedScan v cs pos best = best := by
  intro cs
  induction cs with
  | nil =>
      intro pos best hdead
      have hnn : v.findIdx? nullable = none := by
        rw [Array.findIdx?_eq_none_iff]
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Array.mem_iff_getElem.mp hx
        have hnv := (Array.all_eq_true.mp hdead) i hi
        rw [hxi] at hnv
        cases x <;> simp_all [isNever, nullable]
      simp [fusedScan, hnn]
  | cons c rest ih =>
      intro pos best hdead
      have hmapdead : (v.map (deriv c)).all isNever = true := by
        rw [Array.all_eq_true]
        intro i hi
        have hi' : i < v.size := by simpa using hi
        simp only [Array.getElem_map]
        have hv := (Array.all_eq_true.mp hdead) i hi'
        cases hvi : v[i] <;> simp_all [isNever, deriv]
      have hnull : v.findIdx? nullable = none := by
        rw [Array.findIdx?_eq_none_iff]
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Array.mem_iff_getElem.mp hx
        have hnv := (Array.all_eq_true.mp hdead) i hi
        rw [hxi] at hnv
        cases x <;> simp_all [isNever, nullable]
      simp only [fusedScan, hnull, hmapdead, ite_true]

/-- The validated DFA scan, started at any state, equals `fusedScan` on that
    state's derivative vector. By induction on the input. -/
theorem scan_eq_fusedScan {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : validate rules dfa cert = true) :
    ∀ (cs : List Char) (sid : Nat) (pos : Nat) (best : Option (Nat × Nat)),
      sid < dfa.states.size →
      DFA.scan.go dfa sid cs pos best = fusedScan (cert.vecs[sid]!) cs pos best := by
  have hsize : cert.vecs.size = dfa.states.size := by
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at hval
    exact hval.1.1.1
  intro cs
  induction cs with
  | nil =>
      intro sid pos best hsid
      have hst := stateValid_of_validate hval hsid
      simp only [stateValid, Bool.and_eq_true, decide_eq_true_eq] at hst
      have hacc : (dfa.states[sid]!).accept = (cert.vecs[sid]!).findIdx? nullable := hst.1.1
      simp only [DFA.scan.go, fusedScan, hacc]
      rfl
  | cons c rest ih =>
      intro sid pos best hsid
      have hst := stateValid_of_validate hval hsid
      simp only [stateValid, Bool.and_eq_true, decide_eq_true_eq] at hst
      have hacc : (dfa.states[sid]!).accept = (cert.vecs[sid]!).findIdx? nullable := hst.1.1
      have hstep := validate_step hval hsid c
      simp only [DFA.scan.go, fusedScan, hacc]
      -- align on whether there is an edge for c
      cases hsc : (dfa.states[sid]!).stepChar c with
      | none =>
          have hdead : ∀ r ∈ cert.vecs[sid]!, deriv c r = .never := hstep.2 hsc
          have hall : (cert.vecs[sid]!.map (deriv c)).all isNever = true := by
            rw [Array.all_eq_true]
            intro i hi
            simp only [Array.getElem_map]
            rw [hdead _ (Array.getElem_mem _)]
            rfl
          simp only [hall, ite_true]
          rfl
      | some next =>
          obtain ⟨hnext, hvec⟩ := hstep.1 next hsc
          have hnextlt : next < dfa.states.size := by rw [← hsize]; exact hnext
          simp only []
          by_cases hall : (cert.vecs[sid]!.map (deriv c)).all isNever = true
          · simp only [hall, ite_true]
            rw [ih next _ _ hnextlt, hvec]
            exact fusedScan_dead_frozen _ rest _ _ hall
          · have hallf : (cert.vecs[sid]!.map (deriv c)).all isNever = false := by
              simpa using hall
            simp only [hallf, Bool.false_eq_true, ite_false]
            have := ih next (pos+1) (match Array.findIdx? nullable cert.vecs[sid]! with
              | some rule => some (rule, pos) | none => best) hnextlt
            rw [hvec] at this
            exact this

/-- **Scan refines the pure-regex spec.** For a validated lexer, the executable
    `DFA.scan` on the whole input equals `fusedScan` on the mode's rule regexes —
    the derivative-defined maximal munch. Uses `V0` (`cert.vecs[0] = rules`). This
    is the maximal-munch correctness of the generated tables: the scanner computes
    exactly the specification, so the answer is unique (determinism gives
    unambiguity without a separate hypothesis, docs/DESIGN.md §9.7). -/
theorem scan_eq_fusedScan_start {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : validate rules dfa cert = true) (cs : List Char) :
    DFA.scan dfa cs = fusedScan rules cs 0 none := by
  have h0size : 0 < dfa.states.size := by
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at hval
    obtain ⟨⟨⟨hsz, hpos⟩, _⟩, _⟩ := hval
    omega
  have hv0 : cert.vecs[0]! = rules := by
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at hval
    exact hval.1.2
  have := scan_eq_fusedScan hval cs 0 0 none h0size
  rw [hv0] at this
  simpa [DFA.scan] using this

/-! ### Maximal-munch soundness and determinism

`fusedScan` is the derivative-defined maximal-munch specification (docs/DESIGN.md
§9.4): it walks the input taking derivatives of the whole rule vector, records the
earliest nullable rule at each position, and keeps the longest such position. The
theorems below are the lexer's soundness (the executable scanner computes exactly
this spec) and unambiguity (the spec is a function, so the result is unique). -/

/-- **Maximal-munch soundness.** For a validated lexer, the executable scanner's
    result on any input is exactly the derivative-defined maximal-munch winner
    (`fusedScan` over the rule regexes). Any two validated tables for the same
    rules therefore scan identically. -/
theorem scan_sound {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : validate rules dfa cert = true) (cs : List Char) :
    DFA.scan dfa cs = fusedScan rules cs 0 none :=
  scan_eq_fusedScan_start hval cs

/-- **Unambiguity / determinism.** Two validated DFAs for the same rule list scan
    every input to the same result. A direct consequence of `scan_sound`: the
    scanner is a function of the rules, not of the (untrusted) table shape. -/
theorem scan_deterministic {rules : Array Regex} {dfa₁ dfa₂ : DFA} {cert₁ cert₂ : LexCert}
    (h₁ : validate rules dfa₁ cert₁ = true) (h₂ : validate rules dfa₂ cert₂ = true)
    (cs : List Char) : DFA.scan dfa₁ cs = DFA.scan dfa₂ cs := by
  rw [scan_sound h₁, scan_sound h₂]

/-! ### Connecting `fusedScan` to the specification objects

`scan_sound` states the scanner against `fusedScan`, which is derivative
bookkeeping over a vector. `bestMatch`/`MatchStep` (`Lexer/Spec.lean`) are the
maximal-munch specification stated with `matchesFull`. This section closes the gap
`fusedScan rules cs 0 none = bestMatch rules cs` (docs/DESIGN.md §9.8) and derives
the `MatchStep` soundness of the scanner.

The proof has three parts:
  1. `fusedScan` equals `scanRec`, a version without the early dead-stop guard
     (the guard is a harmless optimization: a dead vector never becomes nullable);
  2. `scanRec` records exactly the longest prefix length matched by any component
     and the earliest component matching it, phrased with `matchesFull`;
  3. that characterization is the two directions of `MatchStep`, and equals
     `bestMatch`.

`nullable (derivs (cs.take l) r) = matchesFull r (cs.take l)`
(`Regex.matchesFull_eq_nullable_derivs`) is the bridge from the derivative vector
to `matchesFull`. -/

/-- `fusedScan` without the early dead-stop guard: always walks to the end of the
    input. Equal to `fusedScan` for validated inputs (`fusedScan_eq_scanRec`), but
    easier to characterize because it has no branch. -/
def scanRec (v : Array Regex) (cs : List Char) (pos : Nat)
    (best : Option (Nat × Nat)) : Option (Nat × Nat) :=
  let best := match v.findIdx? nullable with
    | some rule => some (rule, pos)
    | none => best
  match cs with
  | [] => best
  | c :: rest => scanRec (v.map (deriv c)) rest (pos + 1) best
termination_by cs.length

/-- A dead vector never updates `best` in `scanRec` either. -/
theorem scanRec_dead_frozen (v : Array Regex) :
    ∀ (cs : List Char) (pos : Nat) (best : Option (Nat × Nat)),
      v.all isNever = true → scanRec v cs pos best = best := by
  intro cs
  induction cs generalizing v with
  | nil =>
      intro pos best hdead
      have hnn : v.findIdx? nullable = none := by
        rw [Array.findIdx?_eq_none_iff]
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Array.mem_iff_getElem.mp hx
        have hnv := (Array.all_eq_true.mp hdead) i hi
        rw [hxi] at hnv
        cases x <;> simp_all [isNever, nullable]
      simp [scanRec, hnn]
  | cons c rest ih =>
      intro pos best hdead
      have hmapdead : (v.map (deriv c)).all isNever = true := by
        rw [Array.all_eq_true]
        intro i hi
        have hi' : i < v.size := by simpa using hi
        simp only [Array.getElem_map]
        have hv := (Array.all_eq_true.mp hdead) i hi'
        cases hvi : v[i] <;> simp_all [isNever, deriv]
      have hnull : v.findIdx? nullable = none := by
        rw [Array.findIdx?_eq_none_iff]
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Array.mem_iff_getElem.mp hx
        have hnv := (Array.all_eq_true.mp hdead) i hi
        rw [hxi] at hnv
        cases x <;> simp_all [isNever, nullable]
      simp only [scanRec, hnull]
      rw [ih (v.map (deriv c)) (pos+1) best hmapdead]

/-- The early dead-stop in `fusedScan` is harmless: it returns exactly what the
    unguarded `scanRec` returns. When the vector goes dead, `scanRec` continues but
    every later step is frozen (`scanRec_dead_frozen`), so both return the same
    accumulator. -/
theorem fusedScan_eq_scanRec (v : Array Regex) :
    ∀ (cs : List Char) (pos : Nat) (best : Option (Nat × Nat)),
      fusedScan v cs pos best = scanRec v cs pos best := by
  intro cs
  induction cs generalizing v with
  | nil => intro pos best; simp [fusedScan, scanRec]
  | cons c rest ih =>
      intro pos best
      simp only [fusedScan, scanRec]
      by_cases hall : (v.map (deriv c)).all isNever = true
      · simp only [hall, ite_true]
        rw [scanRec_dead_frozen _ rest _ _ hall]
      · have : (v.map (deriv c)).all isNever = false := by simpa using hall
        simp only [this, Bool.false_eq_true, ite_false]
        exact ih _ _ _

/-- The earliest component (by index) matching the length-`l` prefix of `cs`, or
    `none`. `nullable (derivs (cs.take l) r) = matchesFull r (cs.take l)`, so this
    is the earliest rule whose regex matches that prefix. -/
def winnerAt (v : Array Regex) (cs : List Char) (l : Nat) : Option Nat :=
  (v.map (fun r => Regex.derivs (cs.take l) r)).findIdx? nullable

/-- Stepping the vector by `deriv c` and shortening the input is the same as
    looking one position further into the original input: the vector after `d`
    steps of `deriv` is `v.map (derivs (cs.take d))`. -/
theorem winnerAt_cons (v : Array Regex) (c : Char) (rest : List Char) (l : Nat) :
    winnerAt (v.map (deriv c)) rest l = winnerAt v (c :: rest) (l + 1) := by
  have hmap : (v.map (deriv c)).map (fun r => Regex.derivs (List.take l rest) r)
      = v.map (fun r => Regex.derivs (List.take (l + 1) (c :: rest)) r) := by
    rw [Array.map_map]
    apply Array.map_congr_left
    intro r _
    simp only [Function.comp_apply, List.take_succ_cons, Regex.derivs_cons]
  simp only [winnerAt, hmap]

/-- `scanRec` is a left fold over positions `0 .. cs.length`: at each position it
    overwrites the accumulator with `(winnerAt, pos+l)` when some component is
    nullable there, keeping the last such position (earliest rule at it). This is
    the closed form used to read off the maximal-munch winner. -/
theorem scanRec_eq_foldl (v : Array Regex) :
    ∀ (cs : List Char) (pos : Nat) (best : Option (Nat × Nat)),
      scanRec v cs pos best =
        (List.range (cs.length + 1)).foldl
          (fun acc l => match winnerAt v cs l with
            | some r => some (r, pos + l)
            | none => acc)
          best := by
  intro cs
  induction cs generalizing v with
  | nil =>
      intro pos best
      have hmap : v.map (fun r => Regex.derivs [] r) = v := by
        simp [Regex.derivs_nil, Array.map_id']
      simp only [scanRec, List.length_nil, Nat.zero_add, List.range_one, List.foldl_cons,
        List.foldl_nil, winnerAt, List.take_zero, hmap, Nat.add_zero]
  | cons c rest ih =>
      intro pos best
      have hrange : List.range (rest.length + 1 + 1)
          = 0 :: (List.range (rest.length + 1)).map (· + 1) := by
        rw [List.range_succ_eq_map]
      simp only [List.length_cons]
      rw [hrange, List.foldl_cons, List.foldl_map]
      have h0 : winnerAt v (c :: rest) 0 = v.findIdx? nullable := by
        have hmap : v.map (fun r => Regex.derivs (List.take 0 (c :: rest)) r) = v := by
          simp [Regex.derivs_nil, Array.map_id']
        simp only [winnerAt, hmap]
      simp only [h0, Nat.add_zero]
      simp only [scanRec]
      rw [ih (v.map (deriv c)) (pos + 1)]
      have hfun : (fun (acc : Option (Nat × Nat)) l =>
            match winnerAt (v.map (deriv c)) rest l with
            | some r => some (r, pos + 1 + l)
            | none => acc)
          = (fun (acc : Option (Nat × Nat)) l =>
            match winnerAt v (c :: rest) (l + 1) with
            | some r => some (r, pos + (l + 1))
            | none => acc) := by
        funext acc l
        rw [winnerAt_cons]
        simp only [Nat.add_assoc, Nat.add_comm 1 l]
      rw [hfun]

/-! #### Reading the winner off the fold

`scanRec v cs 0 none` is a fold that overwrites the accumulator at every position
where some component matches, so it ends holding the *last* matching position and
the earliest rule there. The next two lemmas extract that: the `none` result means
no prefix matched, and a `some (rule, len)` result means `len` is a matching
position, it is maximal, and `rule` is the earliest match at it. -/

/-- One step of the "record last hit" fold: overwrite `acc` with `(r, l)` when
    `f l = some r`, else keep `acc`. Named (rather than an inline `match`) so the
    generic characterization lemmas and `fusedScan_eq_lastHit` refer to the same
    function and unify. -/
def hitStep {α : Type} (f : Nat → Option α) (acc : Option (α × Nat)) (l : Nat) : Option (α × Nat) :=
  match f l with
  | some r => some (r, l)
  | none => acc

/-- Generic "record the last hit" fold over `List.range n`, seeded with `none`:
    the result is `none` iff `f` is `none` on every index `< n`. -/
theorem foldl_lastHit_none {α : Type} (f : Nat → Option α) :
    ∀ (n : Nat),
      (List.range n).foldl (hitStep f) (none : Option (α × Nat)) = none
      ↔ ∀ l, l < n → f l = none := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      constructor
      · intro h
        have hfm : f m = none := by
          rcases hfm : f m with _ | r
          · rfl
          · rw [hitStep, hfm] at h; simp at h
        rw [hitStep, hfm] at h
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact (ih.mp h) l hlt
        · subst heq; exact hfm
      · intro h
        have hfm : f m = none := h m (Nat.lt_succ_self m)
        rw [hitStep, hfm]
        exact ih.mpr (fun l hl => h l (Nat.lt_succ_of_lt hl))

/-- Same fold, `some (r, k)` result: `k < n`, `f k = some r`, and `f` is `none`
    on every index strictly between `k` and `n` (so `k` is the last hit). -/
theorem foldl_lastHit_some {α : Type} (f : Nat → Option α) :
    ∀ (n : Nat) (r : α) (k : Nat),
      (List.range n).foldl (hitStep f) (none : Option (α × Nat)) = some (r, k)
      → k < n ∧ f k = some r ∧ ∀ l, k < l → l < n → f l = none := by
  intro n
  induction n with
  | zero => intro r k h; simp at h
  | succ m ih =>
      intro r k h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      rcases hfm : f m with _ | rm
      · rw [hitStep, hfm] at h
        obtain ⟨hk, hfk, hbetween⟩ := ih r k h
        refine ⟨Nat.lt_succ_of_lt hk, hfk, ?_⟩
        intro l hkl hlm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlm with hlt | heq
        · exact hbetween l hkl hlt
        · subst heq; exact hfm
      · rw [hitStep, hfm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hr, hkm⟩ := h
        subst hr
        subst hkm
        refine ⟨Nat.lt_succ_self m, hfm, ?_⟩
        intro l hkl hlk
        omega

/-- Completeness of the "record last hit" fold: if `f k = some r`, `k < n`, and `f`
    is `none` on every index strictly between `k` and `n`, the fold returns
    `some (r, k)`. -/
theorem foldl_lastHit_some_of {α : Type} (f : Nat → Option α) :
    ∀ (n : Nat) (r : α) (k : Nat), k < n → f k = some r →
      (∀ l, k < l → l < n → f l = none) →
      (List.range n).foldl (hitStep f) (none : Option (α × Nat)) = some (r, k) := by
  intro n
  induction n with
  | zero => intro r k hlt _ _; omega
  | succ m ih =>
      intro r k hlt hfk habove
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hkm | hkm
      · have hfm : f m = none := habove m hkm (Nat.lt_succ_self m)
        rw [hitStep, hfm]
        exact ih r k hkm hfk (fun l hkl hlm => habove l hkl (Nat.lt_succ_of_lt hlm))
      · subst hkm
        rw [hitStep, hfk]

/-! #### `winnerAt` in terms of `matchesFull`

`winnerAt v cs l` is the earliest component of `v` matching the length-`l` prefix
of `cs`, because `nullable (derivs (cs.take l) r) = matchesFull r (cs.take l)`. -/

/-- `winnerAt v cs l = some rule` picks the earliest component matching the
    length-`l` prefix, and that component does match. -/
theorem winnerAt_some {v : Array Regex} {cs : List Char} {l rule : Nat}
    (h : winnerAt v cs l = some rule) :
    rule < v.size ∧ Regex.matchesFull v[rule]! (cs.take l) = true
      ∧ ∀ j, j < rule → Regex.matchesFull v[j]! (cs.take l) = false := by
  simp only [winnerAt] at h
  obtain ⟨hlt, hnull, hbefore⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  have hsize : (v.map (fun r => Regex.derivs (cs.take l) r)).size = v.size := by simp
  have hrule : rule < v.size := by rw [hsize] at hlt; exact hlt
  refine ⟨hrule, ?_, ?_⟩
  · rw [Regex.matchesFull_eq_nullable_derivs, getElem!_pos v rule hrule]
    have hwget : (v.map (fun r => Regex.derivs (cs.take l) r))[rule] = Regex.derivs (cs.take l) v[rule] := by
      simp [Array.getElem_map]
    rw [hwget] at hnull
    exact hnull
  · intro j hj
    have hjlt : j < v.size := Nat.lt_trans hj hrule
    have hnn := hbefore j hj
    have hwgetj : (v.map (fun r => Regex.derivs (cs.take l) r))[j]'(by rw [hsize]; exact hjlt)
        = Regex.derivs (cs.take l) v[j] := by simp [Array.getElem_map]
    rw [hwgetj] at hnn
    rw [Regex.matchesFull_eq_nullable_derivs, getElem!_pos v j hjlt]
    simpa using hnn

/-- `winnerAt v cs l = none` means no component matches the length-`l` prefix. -/
theorem winnerAt_none {v : Array Regex} {cs : List Char} {l : Nat}
    (h : winnerAt v cs l = none) :
    ∀ j, j < v.size → Regex.matchesFull v[j]! (cs.take l) = false := by
  simp only [winnerAt] at h
  have hall := Array.findIdx?_eq_none_iff.mp h
  intro j hj
  have hjmap : j < (v.map (fun r => Regex.derivs (cs.take l) r)).size := by simpa using hj
  have hnn := hall (v.map (fun r => Regex.derivs (cs.take l) r))[j] (Array.getElem_mem hjmap)
  have hwgetj : (v.map (fun r => Regex.derivs (cs.take l) r))[j] = Regex.derivs (cs.take l) v[j] := by
    simp [Array.getElem_map]
  rw [hwgetj] at hnn
  rw [Regex.matchesFull_eq_nullable_derivs, getElem!_pos v j hj]
  simpa using hnn

/-! #### `fusedScan` characterized by `matchesFull`

Putting the pieces together: `fusedScan rules cs 0 none` returns the longest prefix
length matched by any rule, and the earliest rule matching it. This is the
statement of maximal munch in terms of the language `matchesFull`, i.e. the content
of `MatchStep`. -/

/-- `fusedScan rules cs 0 none` as a fold reading the last matching position. -/
theorem fusedScan_eq_lastHit (v : Array Regex) (cs : List Char) :
    fusedScan v cs 0 none =
      (List.range (cs.length + 1)).foldl (hitStep (winnerAt v cs)) none := by
  rw [fusedScan_eq_scanRec, scanRec_eq_foldl]
  congr 1
  funext acc l
  rw [hitStep]
  cases winnerAt v cs l with
  | none => rfl
  | some r => simp [Nat.zero_add]

/-- **`fusedScan` computes `MatchStep`.** If `fusedScan rules cs 0 none = some
    (rule, len)` with a non-empty match, then `(rule, len)` is the maximal-munch
    winner in the sense of `MatchStep`: the rule matches the length-`len` prefix,
    no rule matches longer, and no earlier rule matches the same length. This is
    the soundness of the derivative-defined maximal munch against the
    specification object (docs/DESIGN.md §9.4, §9.7 step 2). -/
theorem matchStep_of_fusedScan {rules : Array Regex} {cs : List Char} {rule len : Nat}
    (h : fusedScan rules cs 0 none = some (rule, len)) (hlen : 0 < len) :
    MatchStep rules cs rule len := by
  rw [fusedScan_eq_lastHit] at h
  obtain ⟨hlt, hfk, hbetween⟩ := foldl_lastHit_some (winnerAt rules cs) (cs.length + 1) rule len h
  have hlen_le : len ≤ cs.length := by omega
  obtain ⟨hrule, hmatch, hearlier⟩ := winnerAt_some hfk
  refine ⟨hrule, hmatch, hlen, ?_, ?_⟩
  · intro j hj l hl hjmatch
    rcases Nat.lt_or_ge len l with hlt' | hge
    · exfalso
      have hlrange : l < cs.length + 1 := by omega
      have hwn : winnerAt rules cs l = none := hbetween l hlt' hlrange
      have hfalse := winnerAt_none hwn j hj
      rw [hfalse] at hjmatch
      exact absurd hjmatch (by simp)
    · omega
  · intro j hj hjmatch
    have hfalse := hearlier j hj
    rw [hfalse] at hjmatch
    exact absurd hjmatch (by simp)

/-- **No match ⇒ `fusedScan` is `none`.** If no rule matches a positive-length
    prefix, `fusedScan` returns `none`. (The empty-string match at length 0, if
    any, does not count as a token — `bestMatch` filters it too.) -/
theorem fusedScan_none_of_no_match {rules : Array Regex} {cs : List Char}
    (h : ∀ l, 0 < l → l ≤ cs.length → ∀ j, j < rules.size →
      Regex.matchesFull rules[j]! (cs.take l) = false)
    (h0 : rules.findIdx? Regex.nullable = none) :
    fusedScan rules cs 0 none = none := by
  rw [fusedScan_eq_lastHit]
  refine (foldl_lastHit_none (winnerAt rules cs) (cs.length + 1)).mpr ?_
  intro l hl
  have hlle : l ≤ cs.length := by omega
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · subst hl0
    simp only [winnerAt, List.take_zero]
    have : (rules.map (fun r => Regex.derivs [] r)) = rules := by
      simp [Regex.derivs_nil, Array.map_id']
    rw [this]; exact h0
  · -- l > 0: no rule matches, so winnerAt is none
    rcases hw : winnerAt rules cs l with _ | rule
    · rfl
    · exfalso
      obtain ⟨hrule, hmatch, _⟩ := winnerAt_some hw
      have := h l hlpos hlle rule hrule
      rw [this] at hmatch
      exact absurd hmatch (by simp)

/-! ### Scanner soundness against the specification

Composing `scan_sound` (`DFA.scan = fusedScan`) with `matchStep_of_fusedScan`
(`fusedScan` computes a `MatchStep`) gives the lexer's maximal-munch soundness
stated against the specification object `MatchStep` (`Lexer/Spec.lean`), not merely
against `fusedScan`. This closes the connection docs/DESIGN.md §9.8 recorded as
missing. -/

/-- **Scanner maximal-munch soundness.** For a validated lexer, whenever the
    executable `DFA.scan` returns a non-empty match `(rule, len)`, that pair is the
    maximal-munch winner in the sense of the specification `MatchStep`: `rule`'s
    regex matches the length-`len` prefix, no rule matches a longer prefix, and no
    earlier rule matches the same length. This is `scan_sound` re-expressed against
    the specification object. -/
theorem scan_matchStep {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : validate rules dfa cert = true) {cs : List Char} {rule len : Nat}
    (hscan : DFA.scan dfa cs = some (rule, len)) (hlen : 0 < len) :
    MatchStep rules cs rule len := by
  have hfs : fusedScan rules cs 0 none = some (rule, len) := by
    rw [← scan_sound hval]; exact hscan
  exact matchStep_of_fusedScan hfs hlen

/-- **Completeness: a `MatchStep` winner is what `fusedScan` returns.** If
    `(rule, len)` is the maximal-munch winner in the sense of `MatchStep`, then
    `fusedScan rules cs 0 none = some (rule, len)`. Together with
    `matchStep_of_fusedScan` this gives the exact characterization
    `fusedScan rules cs 0 none = some (rule, len) ↔ MatchStep rules cs rule len`
    (for `0 < len`). -/
theorem fusedScan_of_matchStep {rules : Array Regex} {cs : List Char} {rule len : Nat}
    (hms : MatchStep rules cs rule len) (hlen_le : len ≤ cs.length) :
    fusedScan rules cs 0 none = some (rule, len) := by
  obtain ⟨hrule, hmatch, hlen, hmaximal, hearliest⟩ := hms
  rw [fusedScan_eq_lastHit]
  -- winnerAt rules cs len = some rule, and no hit strictly beyond len
  have hwin : winnerAt rules cs len = some rule := by
    rw [winnerAt]
    rw [Array.findIdx?_eq_some_iff_getElem]
    have hsize : (rules.map (fun r => Regex.derivs (cs.take len) r)).size = rules.size := by simp
    refine ⟨by rw [hsize]; exact hrule, ?_, ?_⟩
    · have hget : (rules.map (fun r => Regex.derivs (cs.take len) r))[rule]'(by rw [hsize]; exact hrule)
          = Regex.derivs (cs.take len) rules[rule] := by simp [Array.getElem_map]
      rw [hget, ← Regex.matchesFull_eq_nullable_derivs]
      rwa [getElem!_pos rules rule hrule] at hmatch
    · intro j hj
      have hjlt : j < rules.size := Nat.lt_trans hj hrule
      have hget : (rules.map (fun r => Regex.derivs (cs.take len) r))[j]'(by rw [hsize]; exact hjlt)
          = Regex.derivs (cs.take len) rules[j] := by simp [Array.getElem_map]
      rw [hget, ← Regex.matchesFull_eq_nullable_derivs, ← getElem!_pos rules j hjlt]
      -- earliest: rules[j]! does not match take len for j < rule
      intro hcontra
      exact hearliest j hj hcontra
  apply foldl_lastHit_some_of (winnerAt rules cs) (cs.length + 1) rule len
  · omega
  · exact hwin
  · intro l hll hlr
    -- l > len ⇒ no rule matches take l (else maximal gives l ≤ len)
    rcases hw : winnerAt rules cs l with _ | rule'
    · rfl
    · exfalso
      obtain ⟨hrule', hmatch', _⟩ := winnerAt_some hw
      have hlle : l ≤ cs.length := by omega
      have := hmaximal rule' hrule' l hlle hmatch'
      omega

/-- **Uniqueness of the maximal-munch winner.** `MatchStep` is functional: at most
    one `(rule, len)` satisfies it, so the tokenization derivation is unique. This
    is the lexer's unambiguity, a lemma rather than a separate obligation
    (docs/DESIGN.md §9.4). -/
theorem matchStep_unique {rules : Array Regex} {cs : List Char} {rule₁ len₁ rule₂ len₂ : Nat}
    (h₁ : MatchStep rules cs rule₁ len₁) (h₂ : MatchStep rules cs rule₂ len₂)
    (hle₁ : len₁ ≤ cs.length) (hle₂ : len₂ ≤ cs.length) :
    rule₁ = rule₂ ∧ len₁ = len₂ := by
  have he₁ := fusedScan_of_matchStep h₁ hle₁
  have he₂ := fusedScan_of_matchStep h₂ hle₂
  rw [he₁] at he₂
  simp only [Option.some.injEq, Prod.mk.injEq] at he₂
  exact ⟨he₂.1, he₂.2⟩

/-- **Exact characterization.** For `len ≤ cs.length` and `0 < len`, the
    derivative-defined scanner result and the specification `MatchStep` coincide.
    This is the pure-regex equivalence connecting `scan_sound` to the specification
    objects (docs/DESIGN.md §9.8), now proved. -/
theorem fusedScan_eq_some_iff_matchStep {rules : Array Regex} {cs : List Char}
    {rule len : Nat} (hlen : 0 < len) (hle : len ≤ cs.length) :
    fusedScan rules cs 0 none = some (rule, len) ↔ MatchStep rules cs rule len :=
  ⟨fun h => matchStep_of_fusedScan h hlen, fun h => fusedScan_of_matchStep h hle⟩

/-- **Scanner completeness.** For a validated lexer, `DFA.scan` returns the
    maximal-munch winner whenever one exists in the sense of `MatchStep`. The
    converse of `scan_matchStep`. -/
theorem scan_of_matchStep {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : validate rules dfa cert = true) {cs : List Char} {rule len : Nat}
    (hms : MatchStep rules cs rule len) (hle : len ≤ cs.length) :
    DFA.scan dfa cs = some (rule, len) := by
  rw [scan_sound hval]
  exact fusedScan_of_matchStep hms hle

end Lexer
