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
A small regular-expression language and a longest-match matcher over `List Char`.

The regex engine uses Brzozowski derivatives, so the matcher is a structural
recursion. `matchesFull` gives the language a `Regex` denotes and `longestMatch`
gives maximal munch for a single rule; the lemmas at the end of the file
characterize `longestMatch` in terms of `matchesFull`
(`longestMatch_some_iff`, `longestMatch_none_iff`). This is part of the lexer
track, whose end-to-end soundness (the emitted `tokenize` against the DFA, and
the bytes-to-characters layer) is not yet proved; see docs/DESIGN.md §9.
-/


@[expose] public section

namespace Lexer

/-- A character class: the comparison key *and* the matching semantics for a
    single-character pattern. A class is a (possibly negated) union of inclusive
    `(lo, hi)` code-point ranges. Keeping one first-order representation (rather
    than a `Char → Bool` predicate) makes `Regex` states comparable — which the
    DFA construction needs to keep its state set finite — gives it `DecidableEq`,
    and gives verification interval structure to reason about (docs/DESIGN.md
    §9.3). There is no opaque-predicate escape hatch: predicates like
    `Char.isWhitespace` must be written as explicit ranges. -/
structure CharClass where
  /-- When `true`, membership is complemented (`[^…]`). -/
  neg : Bool
  /-- A union of inclusive `(lo, hi)` code-point ranges. -/
  rs : List (Nat × Nat)
  deriving DecidableEq, Repr

namespace CharClass

/-- Build a (possibly negated) class from a range list. Retained so existing call
    sites that used the old `CharClass.ranges` constructor keep working. -/
def ranges (neg : Bool) (rs : List (Nat × Nat)) : CharClass := ⟨neg, rs⟩

/-- Does `c` fall in this class? -/
def mem (k : CharClass) (c : Char) : Bool :=
  let inside := k.rs.any (fun r => r.1 ≤ c.toNat && c.toNat ≤ r.2)
  if k.neg then !inside else inside

/-- Equality key: classes compare structurally on `(neg, rs)`. Agrees with
    `DecidableEq`; kept as a `Bool` for the construction code. -/
def beq (a b : CharClass) : Bool := a.neg == b.neg && a.rs == b.rs

instance : BEq CharClass := ⟨beq⟩

@[simp] theorem beq_eq (a b : CharClass) : (a == b) = (a.neg == b.neg && a.rs == b.rs) := rfl

/-- The empty class (matches nothing). -/
def none : CharClass := ⟨false, []⟩

/-- The full class (matches everything): the negation of the empty range set. -/
def all : CharClass := ⟨true, []⟩

instance : Inhabited CharClass := ⟨CharClass.none⟩

end CharClass

/-- A regular expression over characters. Classic constructors plus a character
    class (`cls`) so common classes like "digit" or "alphanumeric" can be written
    without enumerating every character. -/
inductive Regex where
  /-- Matches nothing (the empty language). -/
  | never : Regex
  /-- Matches the empty string only. -/
  | epsilon : Regex
  /-- Matches a single character in the given class. -/
  | cls : CharClass → Regex
  /-- Concatenation. -/
  | cat : Regex → Regex → Regex
  /-- Alternation. -/
  | alt : Regex → Regex → Regex
  /-- Kleene star. -/
  | star : Regex → Regex
  deriving DecidableEq, Repr

instance : Inhabited Regex := ⟨.never⟩

namespace Regex

/-- Match a single character in the ASCII/Unicode whitespace set that Lean's
    `Char.isWhitespace` recognizes, written as explicit ranges: tab (U+0009),
    line feed (U+000A), carriage return (U+000D), and space (U+0020). This
    replaces the old opaque `Char.isWhitespace` predicate (docs/DESIGN.md §9.7
    step 0): explicit ranges have `DecidableEq` and interval structure, which the
    validator needs. Note this is narrower than Rust's `char::is_whitespace`
    (which also includes U+0085, U+00A0, U+2028, U+3000); that fixture-fidelity
    gap is tracked separately in the design. -/
def asciiWhitespace : Regex :=
  .cls (.ranges false [(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)])

/-- Match a single specific character. -/
def char (c : Char) : Regex := .cls (.ranges false [(c.toNat, c.toNat)])

/-- Match any character. -/
def any : Regex := .cls .all

/-- Match any character in an inclusive range. -/
def range (lo hi : Char) : Regex :=
  .cls (.ranges false [(lo.toNat, hi.toNat)])

/-- Match any character in the given list. -/
def anyOf (cs : List Char) : Regex :=
  .cls (.ranges false (cs.map (fun c => (c.toNat, c.toNat))))

/-- A character class built from inclusive ranges (a single char `c` is the range
    `(c, c)`). When `neg` is true the class is complemented (`[^…]`). -/
def classOf (neg : Bool) (ranges : List (Char × Char)) : Regex :=
  .cls (.ranges neg (ranges.map (fun r => (r.1.toNat, r.2.toNat))))

/-- Match a literal string (as a concatenation of its characters). -/
def str (s : String) : Regex :=
  s.toList.foldr (fun c r => .cat (char c) r) .epsilon

/-- One-or-more repetition: `plus r = cat r (star r)`. -/
def plus (r : Regex) : Regex := .cat r (.star r)

/-- Optional: `opt r = alt r epsilon`. -/
def opt (r : Regex) : Regex := .alt r .epsilon

/-- Does the regex match the empty string? (The Brzozowski "nullable" predicate.) -/
def nullable : Regex → Bool
  | .never => false
  | .epsilon => true
  | .cls _ => false
  | .cat a b => nullable a && nullable b
  | .alt a b => nullable a || nullable b
  | .star _ => true

/-- Is this the empty language? Used to stop scanning once a derivative is dead.
    Only recognizes the syntactic `never`; smart constructors below keep dead
    subterms collapsed to `never`, so this stays cheap and effective. -/
def isNever : Regex → Bool
  | .never => true
  | _ => false

/-- Smart alternation: drop `never` alternatives. -/
def mkAlt (a b : Regex) : Regex :=
  match a, b with
  | .never, _ => b
  | _, .never => a
  | _, _ => .alt a b

/-- Smart concatenation: `never` on either side kills the whole thing, and a
    leading `epsilon` is dropped. -/
def mkCat (a b : Regex) : Regex :=
  match a, b with
  | .never, _ => .never
  | _, .never => .never
  | .epsilon, _ => b
  | _, _ => .cat a b

/-- Smart Kleene star: `star never` and `star epsilon` both match only the empty
    string, i.e. `epsilon`. -/
def mkStar (a : Regex) : Regex :=
  match a with
  | .never => .epsilon
  | .epsilon => .epsilon
  | _ => .star a

/-- Brzozowski derivative of a regex with respect to a character `c`: the language
    of strings `w` such that `c :: w` is in the language of the original regex.

    Uses the smart constructors so `never`/`epsilon` nodes collapse instead of
    accumulating; this keeps the derived term bounded as the scan proceeds. The
    language is unchanged from the naive derivative. -/
def deriv (c : Char) : Regex → Regex
  | .never => .never
  | .epsilon => .never
  | .cls k => if k.mem c then .epsilon else .never
  | .cat a b =>
      let da := mkCat (deriv c a) b
      if nullable a then mkAlt da (deriv c b) else da
  | .alt a b => mkAlt (deriv c a) (deriv c b)
  | .star a => mkCat (deriv c a) (.star a)

/-- Structural equality on regexes, comparing character classes structurally.
    Used to deduplicate DFA states so the state set stays finite. Agrees with the
    derived `DecidableEq Regex` (see `beq_iff_eq`). -/
def beq : Regex → Regex → Bool
  | .never, .never => true
  | .epsilon, .epsilon => true
  | .cls a, .cls b => a == b
  | .cat a1 b1, .cat a2 b2 => beq a1 a2 && beq b1 b2
  | .alt a1 b1, .alt a2 b2 => beq a1 a2 && beq b1 b2
  | .star a, .star b => beq a b
  | _, _ => false

instance : BEq Regex := ⟨beq⟩

/-- The structural `beq` agrees with propositional equality. This is what lets the
    validator reason about DFA state deduplication with `=` rather than `beq`. -/
theorem beq_iff_eq : ∀ {a b : Regex}, beq a b = true ↔ a = b
  | .never, .never => by simp [beq]
  | .epsilon, .epsilon => by simp [beq]
  | .cls a, .cls b => by
      simp only [beq, cls.injEq]
      constructor
      · intro h
        simp only [CharClass.beq_eq, Bool.and_eq_true] at h
        obtain ⟨hn, hr⟩ := h
        cases a; cases b; simp_all
      · rintro rfl; simp
  | .cat a1 b1, .cat a2 b2 => by
      simp only [beq, Bool.and_eq_true, cat.injEq]
      rw [beq_iff_eq, beq_iff_eq]
  | .alt a1 b1, .alt a2 b2 => by
      simp only [beq, Bool.and_eq_true, alt.injEq]
      rw [beq_iff_eq, beq_iff_eq]
  | .star a, .star b => by
      simp only [beq, star.injEq]; rw [beq_iff_eq]
  | .never, .epsilon | .never, .cls _ | .never, .cat _ _ | .never, .alt _ _ | .never, .star _
  | .epsilon, .never | .epsilon, .cls _ | .epsilon, .cat _ _ | .epsilon, .alt _ _ | .epsilon, .star _
  | .cls _, .never | .cls _, .epsilon | .cls _, .cat _ _ | .cls _, .alt _ _ | .cls _, .star _
  | .cat _ _, .never | .cat _ _, .epsilon | .cat _ _, .cls _ | .cat _ _, .alt _ _ | .cat _ _, .star _
  | .alt _ _, .never | .alt _ _, .epsilon | .alt _ _, .cls _ | .alt _ _, .cat _ _ | .alt _ _, .star _
  | .star _, .never | .star _, .epsilon | .star _, .cls _ | .star _, .cat _ _ | .star _, .alt _ _ => by
      simp [beq]

/-! ### Regex semantics

What a `Regex` denotes, defined directly by derivatives. These are the statements
the compiled tables are meant to satisfy (docs/DESIGN.md §9.4): language agreement
is `matchesFull`, maximal munch is `longestMatch`. Tokenizing does not go through
them — that is `Lexer/DFA.lean` — so they carry no performance requirement. -/

/-- Does the regex match the entire character list? The language a `Regex`
    denotes. -/
def matchesFull (r : Regex) (cs : List Char) : Bool :=
  match cs with
  | [] => nullable r
  | c :: rest => matchesFull (deriv c r) rest

/-- Longest-match prefix: the length of the longest prefix of `cs` that the regex
    matches, if any. The specification of maximal munch for a single rule;
    `DFA.scan` is this fused across a mode's rules.

    Walks the input left to right, taking derivatives, and records the most
    recent position at which the accumulated regex was nullable. Stops as soon as
    the derivative becomes the empty language (`never`): no longer prefix can
    match, so scanning the rest of the input is pointless. -/
def longestMatch (r : Regex) (cs : List Char) : Option Nat :=
  let rec go (r : Regex) (cs : List Char) (pos : Nat) (best : Option Nat) : Option Nat :=
    let best := if nullable r then some pos else best
    if isNever r then best
    else match cs with
      | [] => best
      | c :: rest => go (deriv c r) rest (pos + 1) best
  go r cs 0 none

/-! ### Semantics of `longestMatch`

The following lemmas characterize `longestMatch` purely in terms of `matchesFull`
(the language a `Regex` denotes), independent of the derivative bookkeeping the
scanner uses. They are what connects the derivative-defined maximal munch computed
by `DFA.scan`/`fusedScan` to the relational specification `MatchStep`
(docs/DESIGN.md §9.7 step 2).

The reading is: `longestMatch r cs = some len` iff `len` is the length of the
*longest* prefix of `cs` matched by `r`, and `= none` iff no prefix matches. The
early stop at `isNever` is only an optimization — a dead derivative is never again
nullable, so stopping does not lose any later match. -/

/-- A dead regex matches no string, in particular no prefix. -/
theorem matchesFull_never (cs : List Char) : matchesFull .never cs = false := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simpa [matchesFull, deriv] using ih

/-- `matchesFull` after one derivative: `r` matches `c :: rest` iff `deriv c r`
    matches `rest`. Definitional, stated for use in inductions on the input. -/
theorem matchesFull_cons (r : Regex) (c : Char) (rest : List Char) :
    matchesFull r (c :: rest) = matchesFull (deriv c r) rest := rfl

/-- `nullable r` is `matchesFull r []`. -/
@[simp] theorem matchesFull_nil (r : Regex) : matchesFull r [] = nullable r := rfl

/-- Iterated Brzozowski derivative: `derivs cs r` is `r` after consuming every
    character of `cs` in order. This is the state the scanner's derivative vector
    holds after reading `cs`. -/
def derivs (cs : List Char) (r : Regex) : Regex :=
  match cs with
  | [] => r
  | c :: rest => derivs rest (deriv c r)

@[simp] theorem derivs_nil (r : Regex) : derivs [] r = r := rfl

@[simp] theorem derivs_cons (c : Char) (cs : List Char) (r : Regex) :
    derivs (c :: cs) r = derivs cs (deriv c r) := rfl

/-- `matchesFull r cs` is exactly `nullable` of the derivative of `r` through all
    of `cs`. This is the bridge between the language `matchesFull` and the
    derivative bookkeeping that `longestMatch`/`fusedScan` do. -/
theorem matchesFull_eq_nullable_derivs (r : Regex) (cs : List Char) :
    matchesFull r cs = nullable (derivs cs r) := by
  induction cs generalizing r with
  | nil => rfl
  | cons c rest ih => simp [matchesFull, derivs, ih]

/-- A `never` derivative stays `never` under further derivatives. -/
theorem derivs_never (cs : List Char) : derivs cs .never = .never := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simpa [derivs, deriv] using ih

/-- `derivs` composes over concatenation of inputs. -/
theorem derivs_append (cs ds : List Char) (r : Regex) :
    derivs (cs ++ ds) r = derivs ds (derivs cs r) := by
  induction cs generalizing r with
  | nil => rfl
  | cons c rest ih => simp [derivs, ih]

/-- Once a derivative is dead (`never`), no longer prefix matches: for `l` past the
    point where `r` became `never`, `matchesFull r (take l)` is false. Concretely,
    if `derivs (cs.take k) r = never` then `matchesFull r (cs.take l) = false` for
    all `l ≥ k`. -/
theorem matchesFull_false_of_derivs_never {r : Regex} {cs : List Char} {k : Nat}
    (hk : derivs (cs.take k) r = .never) :
    ∀ l, k ≤ l → matchesFull r (cs.take l) = false := by
  intro l hl
  rw [matchesFull_eq_nullable_derivs]
  have htk : (cs.take l).take k = cs.take k := by
    rw [List.take_take, Nat.min_eq_left hl]
  have hsplit : cs.take l = cs.take k ++ (cs.take l).drop k := by
    rw [← htk, List.take_append_drop]
  rw [hsplit, derivs_append, hk, derivs_never]
  rfl

/-! #### `longestMatch` characterized by `matchesFull`

`longestMatch r cs` returns the length of the longest prefix of `cs` matched by
`r`. These lemmas state that in terms of `matchesFull`, mirroring the vector-level
`fusedScan` characterization in `Lexer/Validator.lean`. The single-regex early stop
at `isNever` is harmless: a `never` derivative is never again nullable
(`matchesFull_false_of_derivs_never`). -/

/-- `longestMatch.go` without the early `isNever` stop: always walks to the end. -/
def lmRec (r : Regex) (cs : List Char) (pos : Nat) (best : Option Nat) : Option Nat :=
  let best := if nullable r then some pos else best
  match cs with
  | [] => best
  | c :: rest => lmRec (deriv c r) rest (pos + 1) best
termination_by cs.length

/-- A dead regex never updates `best` in `lmRec`. -/
theorem lmRec_dead_frozen :
    ∀ (cs : List Char) (pos : Nat) (best : Option Nat),
      lmRec .never cs pos best = best := by
  intro cs
  induction cs with
  | nil => intro pos best; simp [lmRec, nullable]
  | cons c rest ih =>
      intro pos best
      simp only [lmRec, nullable, Bool.false_eq_true, ite_false, deriv]
      exact ih (pos+1) best

/-- The early stop is harmless: `longestMatch.go = lmRec`. -/
theorem longestMatch_go_eq_lmRec (r : Regex) (cs : List Char) (pos : Nat) (best : Option Nat) :
    longestMatch.go r cs pos best = lmRec r cs pos best := by
  induction cs generalizing r pos best with
  | nil =>
      by_cases h : isNever r
      · have hr : r = .never := by cases r <;> simp_all [isNever]
        subst hr
        simp [longestMatch.go, lmRec, nullable, isNever]
      · have hgo : longestMatch.go r [] pos best = (if r.nullable then some pos else best) := by
          simp [longestMatch.go, h]
        have hlm : lmRec r [] pos best = (if r.nullable then some pos else best) := by
          simp [lmRec]
        exact hgo.trans hlm.symm
  | cons c rest ih =>
      by_cases h : isNever r
      · have hr : r = .never := by cases r <;> simp_all [isNever]
        subst hr
        simp only [longestMatch.go, lmRec, nullable, Bool.false_eq_true, ite_false, isNever,
          ite_true, deriv]
        rw [lmRec_dead_frozen]
      · simp only [longestMatch.go, lmRec, h, Bool.false_eq_true, ite_false]
        exact ih _ _ _

/-- `lmRec` as a fold recording the last nullable position. -/
theorem lmRec_eq_foldl (r : Regex) (cs : List Char) (pos : Nat) (best : Option Nat) :
    lmRec r cs pos best =
      (List.range (cs.length + 1)).foldl
        (fun acc l => if nullable (derivs (cs.take l) r) then some (pos + l) else acc)
        best := by
  induction cs generalizing r pos best with
  | nil =>
      simp only [lmRec, List.length_nil, Nat.zero_add, List.range_one, List.foldl_cons,
        List.foldl_nil, List.take_zero, derivs_nil, Nat.add_zero]
      rfl
  | cons c rest ih =>
      have hrange : List.range (rest.length + 1 + 1)
          = 0 :: (List.range (rest.length + 1)).map (· + 1) := by
        rw [List.range_succ_eq_map]
      simp only [List.length_cons]
      rw [hrange, List.foldl_cons, List.foldl_map]
      simp only [lmRec, List.take_zero, derivs_nil, Nat.add_zero]
      rw [ih (deriv c r) (pos + 1)]
      congr 1
      funext acc l
      have hpos : pos + 1 + l = pos + (l + 1) := by omega
      rw [List.take_succ_cons, derivs_cons, hpos]

/-- Generic boolean "record last hit" fold over `List.range n`, seeded `none`:
    result is `none` iff `p` is false everywhere `< n`. -/
theorem lmFold_none (p : Nat → Bool) :
    ∀ (n : Nat),
      (List.range n).foldl (fun acc l => if p l then some l else acc) (none : Option Nat) = none
      ↔ ∀ l, l < n → p l = false := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      constructor
      · intro h
        have hpm : p m = false := by
          rcases hpm : p m with _ | _
          · rfl
          · rw [hpm] at h; simp at h
        rw [hpm] at h; simp only [Bool.false_eq_true, ite_false] at h
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact (ih.mp h) l hlt
        · subst heq; exact hpm
      · intro h
        have hpm : p m = false := h m (Nat.lt_succ_self m)
        rw [hpm]; simp only [Bool.false_eq_true, ite_false]
        exact ih.mpr (fun l hl => h l (Nat.lt_succ_of_lt hl))

/-- Same fold, `some m` result: `m < n`, `p m`, and `p` false strictly between `m`
    and `n`. -/
theorem lmFold_some (p : Nat → Bool) :
    ∀ (n m : Nat),
      (List.range n).foldl (fun acc l => if p l then some l else acc) (none : Option Nat) = some m
      → m < n ∧ p m = true ∧ ∀ l, m < l → l < n → p l = false := by
  intro n
  induction n with
  | zero => intro m h; simp at h
  | succ k ih =>
      intro m h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      rcases hpk : p k with _ | _
      · rw [hpk] at h; simp only [Bool.false_eq_true, ite_false] at h
        obtain ⟨hm, hpm, hbetween⟩ := ih m h
        refine ⟨Nat.lt_succ_of_lt hm, hpm, ?_⟩
        intro l hml hlk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlk with hlt | heq
        · exact hbetween l hml hlt
        · subst heq; exact hpk
      · rw [hpk] at h; simp only [ite_true, Option.some.injEq] at h
        subst h
        refine ⟨Nat.lt_succ_self k, hpk, ?_⟩
        intro l hml hlm; omega

/-- Completeness of the boolean last-hit fold: if `p m` holds, `m < n`, and `p` is
    false above `m` (up to `n`), the fold returns `some m`. -/
theorem lmFold_some_of (p : Nat → Bool) :
    ∀ (n m : Nat), m < n → p m = true → (∀ l, m < l → l < n → p l = false) →
      (List.range n).foldl (fun acc l => if p l then some l else acc) (none : Option Nat) = some m := by
  intro n
  induction n with
  | zero => intro m hlt _ _; omega
  | succ k ih =>
      intro m hlt hpm habove
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hmk | hmk
      · -- m < k: last index k has p false, recurse on prefix
        have hpk : p k = false := habove k hmk (Nat.lt_succ_self k)
        rw [hpk]; simp only [Bool.false_eq_true, ite_false]
        exact ih m hmk hpm (fun l hml hlk => habove l hml (Nat.lt_succ_of_lt hlk))
      · -- m = k: last index hits
        subst hmk
        rw [hpm]; simp

/-- **`longestMatch` result is a matching prefix, maximal among matching prefixes.**
    `longestMatch r cs = some m` iff `r` matches the length-`m` prefix and every
    matching prefix is no longer than `m`. -/
theorem longestMatch_some_iff {r : Regex} {cs : List Char} {m : Nat} :
    longestMatch r cs = some m ↔
      (matchesFull r (cs.take m) = true ∧ m ≤ cs.length ∧
        ∀ l, l ≤ cs.length → matchesFull r (cs.take l) = true → l ≤ m) := by
  rw [longestMatch, longestMatch_go_eq_lmRec, lmRec_eq_foldl]
  simp only [Nat.zero_add]
  constructor
  · intro h
    -- read the last-hit fold
    have := lmFold_some (fun l => nullable (derivs (cs.take l) r)) (cs.length + 1) m h
    obtain ⟨hlt, hnull, hbetween⟩ := this
    refine ⟨?_, by omega, ?_⟩
    · rw [matchesFull_eq_nullable_derivs]; exact hnull
    · intro l hl hml
      rcases Nat.lt_or_ge m l with hlt' | hge
      · exfalso
        have hlrange : l < cs.length + 1 := by omega
        have := hbetween l hlt' hlrange
        rw [matchesFull_eq_nullable_derivs] at hml
        rw [this] at hml; exact absurd hml (by simp)
      · omega
  · rintro ⟨hmatch, hmle, hmax⟩
    apply lmFold_some_of (fun l => nullable (derivs (cs.take l) r)) (cs.length + 1) m
    · omega
    · rw [← matchesFull_eq_nullable_derivs]; exact hmatch
    · intro l hml hln
      -- goal: nullable (derivs (cs.take l) r) = false, with m < l ≤ cs.length
      have hlle : l ≤ cs.length := by omega
      rw [← matchesFull_eq_nullable_derivs]
      cases hmc : matchesFull r (cs.take l) with
      | false => rfl
      | true =>
          have := hmax l hlle hmc
          omega

/-- `longestMatch r cs = none` iff no prefix of `cs` matches `r`. -/
theorem longestMatch_none_iff {r : Regex} {cs : List Char} :
    longestMatch r cs = none ↔ ∀ l, l ≤ cs.length → matchesFull r (cs.take l) = false := by
  rw [longestMatch, longestMatch_go_eq_lmRec, lmRec_eq_foldl]
  simp only [Nat.zero_add]
  rw [lmFold_none (fun l => nullable (derivs (cs.take l) r)) (cs.length + 1)]
  constructor
  · intro h l hl
    have := h l (by omega)
    rw [matchesFull_eq_nullable_derivs]; simpa using this
  · intro h l hl
    have := h l (by omega)
    rw [matchesFull_eq_nullable_derivs] at this; simpa using this

end Regex

end Lexer
