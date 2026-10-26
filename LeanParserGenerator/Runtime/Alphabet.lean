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
Finite, comparable index types: the foundation of the runtime core. Terminals,
non-terminals, states and productions are all `Alphabet`s. The classes here are
Mathlib-free and built on Lean's native `Ordering`/`DecidableEq`.

Design decisions (see docs/DESIGN.md §5.1):
  * `Comparable` gives a `cmp` with antisymmetry and transitivity laws.
  * `Finite` provides an enumeration `all` with a completeness proof.
  * `Numbered` is the cheap way to build all of the above: a bijection with
    `Fin n`. Generated index types get a `Numbered` instance and inherit the rest.
-/


@[expose] public section

namespace Runtime

/-- A type equipped with a comparison that induces a strict total order. -/
class Comparable (α : Type u) where
  cmp : α → α → Ordering
  /-- Comparison is antisymmetric: swapping arguments swaps the `Ordering`. -/
  cmp_swap : ∀ x y, (cmp x y).swap = cmp y x
  /-- Comparison is transitive within a fixed result. -/
  cmp_trans : ∀ {x y z : α} {c : Ordering}, cmp x y = c → cmp y z = c → cmp x z = c

namespace Comparable

variable {α : Type u} [Comparable α]

/-- Reflexivity of comparison: `cmp x x = .eq`. Follows from antisymmetry. -/
theorem cmp_refl (x : α) : cmp x x = Ordering.eq := by
  have h := cmp_swap x x
  cases hc : cmp x x <;> rw [hc] at h <;> simp_all

/-- Boolean equality derived from the comparison. -/
def eqb (x y : α) : Bool := (cmp x y).isEq

end Comparable

/-- A `Comparable` whose `eq` result coincides with propositional (Leibniz)
    equality. -/
class LawfulComparable (α : Type u) extends Comparable α where
  /-- `cmp x y = eq` implies `x = y`. -/
  cmp_eq : ∀ {x y : α}, cmp x y = Ordering.eq → x = y

/-- A finite type: an explicit enumeration together with a completeness proof. -/
class Finite (α : Type u) where
  all : List α
  mem_all : ∀ x, x ∈ all

/-- An alphabet is a finite type with a lawful comparison and decidable equality.
    This is the interface the trusted core requires of every index type.

    `DecidableEq` is a field (not `extends`) because it is a function type, not a
    structure, and so cannot be a class parent. -/
class Alphabet (α : Type u) extends LawfulComparable α, Finite α where
  decEq : DecidableEq α

attribute [instance] Alphabet.decEq

/-- The cheap constructor for alphabets: a bijection with `Fin n`.
    An instance of `Numbered` yields `Comparable`, `LawfulComparable`, `Finite`,
    `DecidableEq`, and hence `Alphabet`. -/
class Numbered (α : Type u) where
  card : Nat
  toFin : α → Fin card
  ofFin : Fin card → α
  toFin_ofFin : ∀ i, toFin (ofFin i) = i
  ofFin_toFin : ∀ x, ofFin (toFin x) = x

namespace Numbered

variable {α : Type u} [Numbered α]

/-- `toFin` is injective. -/
theorem toFin_inj {x y : α} (h : toFin x = toFin y) : x = y := by
  have := congrArg (ofFin (α := α)) h
  rwa [ofFin_toFin, ofFin_toFin] at this

/-- Comparison via the underlying `Fin` index. -/
instance instComparable : Comparable α where
  cmp x y := compare (toFin x).val (toFin y).val
  cmp_swap x y := Nat.compare_swap (toFin x).val (toFin y).val
  cmp_trans {x y z c} hxy hyz := by
    cases c with
    | eq =>
      have hxy' := Nat.compare_eq_eq.mp hxy
      have hyz' := Nat.compare_eq_eq.mp hyz
      exact Nat.compare_eq_eq.mpr (hxy'.trans hyz')
    | lt =>
      have hxy' := Nat.compare_eq_lt.mp hxy
      have hyz' := Nat.compare_eq_lt.mp hyz
      exact Nat.compare_eq_lt.mpr (Nat.lt_trans hxy' hyz')
    | gt =>
      have hxy' := Nat.compare_eq_gt.mp hxy
      have hyz' := Nat.compare_eq_gt.mp hyz
      exact Nat.compare_eq_gt.mpr (Nat.lt_trans hyz' hxy')

instance instLawfulComparable : LawfulComparable α where
  cmp_eq {x y} h := by
    have : (toFin x).val = (toFin y).val := Nat.compare_eq_eq.mp h
    exact toFin_inj (Fin.ext this)

instance instDecidableEq : DecidableEq α := fun x y =>
  if h : toFin x = toFin y then
    isTrue (toFin_inj h)
  else
    isFalse (fun he => h (he ▸ rfl))

/-- Enumeration: map every `Fin card` index back through `ofFin`. -/
instance instFinite : Finite α where
  all := (List.finRange (card α)).map ofFin
  mem_all x := by
    have hx : x = ofFin (toFin x) := (ofFin_toFin x).symm
    rw [hx]
    exact List.mem_map.mpr ⟨toFin x, List.mem_finRange _, rfl⟩

instance instAlphabet : Alphabet α := { decEq := instDecidableEq }

end Numbered

/-- `Fin n` is the canonical numbered type, hence an `Alphabet`. Generated index
    types (terminals, nonterminals, productions, states) are all `Fin`. -/
instance instNumberedFin (n : Nat) : Numbered (Fin n) where
  card := n
  toFin := id
  ofFin := id
  toFin_ofFin _ := rfl
  ofFin_toFin _ := rfl

end Runtime
