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
The flat `state×class` scanner agrees with `DFA.scan`.

`Lexer/DFA.lean` defines `DFA.scan` over a `List Char` (the specification all
soundness proofs are stated against) and, alongside it, the fast `FlatDFA` runtime:
a global alphabet partition plus flat `state × class` transition/accept arrays,
scanned over an `Array Char` by `DFA.flatScanArr`. Profiling (`LEXOPT_NOTES.md`)
shows this is ~2.2x faster on the scan than the derivative-vector `DFA.scan` on
Cedar, because each step is two array reads instead of `findSome?` over the
state's edge list with a `CharClass.mem` range scan.

This file proves the flat scanner agrees with `DFA.scan`, *given* that the flat
tables step and accept identically to the `DFA` (`StepAgree`/`AcceptAgree`). Those
two hypotheses are what a Boolean validator (`Lexer/Validator.lean`) discharges
per lexer with `native_decide`, a-posteriori, exactly like the parser's tables — so
the untrusted `DFA.flatOfDFA` constructor need not be proved correct.

The generic agreement is `flatScanArrGo_eq_scanGo`: with the two agreements, the
flat walk over an `Array Char` at index `i` returns the same `(rule, len)` as
`DFA.scan.go` over the suffix `cs.toList.drop i`, up to the `len` being an absolute
end index vs a relative length. From it, `flatScan_eq_scan` relates the whole-input
entry points.
-/
public import LeanParserGenerator.Lexer.DFA


@[expose] public section

namespace Lexer

open DFA
open FlatDFA

/-- The flat tables step identically to the `DFA` at every reachable state and every
    character: `step f sid c = dfa.states[sid].stepChar c`. A Boolean validator over
    representatives establishes this (docs/DESIGN.md §9.7 step 1). -/
def StepAgree (f : FlatDFA) (dfa : DFA) : Prop :=
  ∀ (sid : Nat), sid < dfa.states.size →
    ∀ (c : Char), step f sid c = (dfa.states[sid]!).stepChar c

/-- The flat tables accept identically to the `DFA` at every state:
    `acceptOf f sid = dfa.states[sid].accept`. -/
def AcceptAgree (f : FlatDFA) (dfa : DFA) : Prop :=
  ∀ (sid : Nat), sid < dfa.states.size →
    acceptOf f sid = (dfa.states[sid]!).accept

/-- The reachable-state closure the walk stays inside: every state the flat step
    can reach from a valid state is valid. Discharged from the validator (which
    checks targets are in range). -/
def StatesInRange (f : FlatDFA) (dfa : DFA) : Prop :=
  ∀ (sid : Nat), sid < dfa.states.size →
    ∀ (c : Char) (next : Nat), step f sid c = some next → next < dfa.states.size

/-- Relating `Array.toList.drop`: the head of the dropped list is the element at
    the index, and the tail is the drop of the next index. -/
theorem toList_drop_cons (cs : Array Char) (i : Nat) (h : i < cs.size) :
    cs.toList.drop i = cs[i] :: cs.toList.drop (i + 1) := by
  have hlt : i < cs.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons hlt]
  simp [Array.getElem_toList]

/-- `stepChar` inspects the character only through `e.cls.mem c` for each edge `e`.
    So two characters that agree on membership in every edge class of the state give
    the same step. This is what makes "check one representative per flat class" sound
    in the validator: within a flat class every edge membership is constant. -/
theorem stepChar_congr (st : DState) (c₁ c₂ : Char)
    (h : ∀ e ∈ st.trans, e.cls.mem c₁ = e.cls.mem c₂) :
    st.stepChar c₁ = st.stepChar c₂ := by
  unfold DState.stepChar
  -- prove by induction on the transition list that findSome? agrees
  have key : ∀ (l : List DTrans), (∀ e ∈ l, e.cls.mem c₁ = e.cls.mem c₂) →
      l.findSome? (fun e => if e.cls.mem c₁ then some e.target else none)
        = l.findSome? (fun e => if e.cls.mem c₂ then some e.target else none) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons e rest ih =>
      intro hmem
      have he : e.cls.mem c₁ = e.cls.mem c₂ := hmem e (by simp)
      have hrest : ∀ e' ∈ rest, e'.cls.mem c₁ = e'.cls.mem c₂ :=
        fun e' he' => hmem e' (by simp [he'])
      simp only [List.findSome?_cons, he]
      cases e.cls.mem c₂ with
      | true => rfl
      | false => simp only [ih hrest]
  have hmemlist : ∀ e ∈ st.trans.toList, e.cls.mem c₁ = e.cls.mem c₂ := by
    intro e he
    exact h e (by simpa using he)
  simpa [← Array.findSome?_toList] using key st.trans.toList hmemlist

/-- Core agreement: with step and accept agreement and states staying in range, the
    flat walk over `cs` at index `i` equals `scan.go` over the suffix `drop i`, when
    the index equals the spec position and there is enough fuel. -/
theorem flatScanArrGo_eq_scanGo (f : FlatDFA) (dfa : DFA)
    (hstep : StepAgree f dfa) (hacc : AcceptAgree f dfa) (hrange : StatesInRange f dfa)
    (cs : Array Char) :
    ∀ (fuel sid i : Nat) (best : Option (Nat × Nat)),
      sid < dfa.states.size → i ≤ cs.size → cs.size - i < fuel →
      DFA.flatScanArrGo f cs fuel sid i best
        = DFA.scan.go dfa sid (cs.toList.drop i) i best := by
  intro fuel
  induction fuel with
  | zero => intro sid i best _ _ hf; omega
  | succ fuel ih =>
    intro sid i best hsid hi hf
    rw [DFA.flatScanArrGo, DFA.scan.go.eq_def]
    -- rewrite the flat accept match into the DFA accept match
    rw [show acceptOf f sid = (dfa.states[sid]!).accept from hacc sid hsid]
    by_cases hlt : i < cs.size
    · -- there is a character at i
      rw [toList_drop_cons cs i hlt]
      simp only [hlt, dite_eq_left]
      have hstepc : step f sid cs[i] = (dfa.states[sid]!).stepChar cs[i] :=
        hstep sid hsid cs[i]
      rw [hstepc]
      cases hstepeq : (dfa.states[sid]!).stepChar cs[i] with
      | none => rfl
      | some next =>
        have hnext : next < dfa.states.size := by
          apply hrange sid hsid cs[i] next
          rw [hstepc]; exact hstepeq
        have hi' : i + 1 ≤ cs.size := hlt
        have hf' : cs.size - (i + 1) < fuel := by omega
        exact ih next (i + 1)
          (match (dfa.states[sid]!).accept with | some rule => some (rule, i) | none => best)
          hnext hi' hf'
    · -- i = cs.size, no character
      have hie : i = cs.size := by omega
      subst hie
      simp only [Nat.lt_irrefl, dite_eq_right, not_false_eq_true]
      rw [List.drop_eq_nil_of_le (by simp)]

/-- Whole-input agreement: the flat scanner over `cs` from `0` equals `DFA.scan` over
    the character list. -/
theorem flatScanArr_eq_scan (f : FlatDFA) (dfa : DFA)
    (hstep : StepAgree f dfa) (hacc : AcceptAgree f dfa) (hrange : StatesInRange f dfa)
    (cs : Array Char) (hstart : 0 < dfa.states.size) :
    DFA.flatScanArr f cs 0 = DFA.scan dfa cs.toList := by
  unfold DFA.flatScanArr DFA.scan
  have := flatScanArrGo_eq_scanGo f dfa hstep hacc hrange cs (cs.size + 1 - 0) 0 0 none
    hstart (by omega) (by omega)
  simpa using this

/-- `scan.go`'s recorded position is relative to its starting `pos`: shifting the
    start position by `k` shifts every recorded position by `k`. Stated as: running
    from `pos + k` with a `k`-shifted `best` equals running from `pos` and shifting
    the result's position by `k`. -/
theorem scanGo_pos_offset (dfa : DFA) :
    ∀ (sid : Nat) (cs : List Char) (pos k : Nat) (best : Option (Nat × Nat)),
      DFA.scan.go dfa sid cs (pos + k) (best.map (fun p => (p.1, p.2 + k)))
        = (DFA.scan.go dfa sid cs pos best).map (fun p => (p.1, p.2 + k)) := by
  intro sid cs
  induction cs generalizing sid with
  | nil =>
    intro pos k best
    rw [DFA.scan.go.eq_def, DFA.scan.go.eq_def]
    cases h : (dfa.states[sid]!).accept with
    | none => simp [h]
    | some rule => simp [h]
  | cons c rest ih =>
    intro pos k best
    rw [DFA.scan.go.eq_def, DFA.scan.go.eq_def]
    cases hacc : (dfa.states[sid]!).accept with
    | none =>
      simp only [hacc]
      cases hst : (dfa.states[sid]!).stepChar c with
      | none => simp
      | some next =>
        simp only []
        have := ih next (pos + 1) k best
        simpa [Nat.add_right_comm] using this
    | some rule =>
      simp only [hacc]
      cases hst : (dfa.states[sid]!).stepChar c with
      | none => simp
      | some next =>
        simp only []
        have := ih next (pos + 1) k (some (rule, pos))
        simpa [Nat.add_right_comm] using this

/-- `scan.go`'s recorded position is bounded by `pos + cs.length`, provided the
    incoming `best` position is `≤ pos`. -/
theorem scanGo_pos_le (dfa : DFA) :
    ∀ (sid : Nat) (cs : List Char) (pos : Nat) (best : Option (Nat × Nat)),
      (∀ r p, best = some (r, p) → p ≤ pos) →
      ∀ r p, DFA.scan.go dfa sid cs pos best = some (r, p) → p ≤ pos + cs.length := by
  intro sid cs
  induction cs generalizing sid with
  | nil =>
    intro pos best hbest r p h
    rw [DFA.scan.go.eq_def] at h
    simp only [List.length_nil, Nat.add_zero]
    cases hacc : (dfa.states[sid]!).accept with
    | none => simp only [hacc] at h; exact hbest r p h
    | some rule => simp only [hacc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  | cons c rest ih =>
    intro pos best hbest r p h
    rw [DFA.scan.go.eq_def] at h
    have hbest' : ∀ r' p', (match (dfa.states[sid]!).accept with
        | some rule => some (rule, pos) | none => best) = some (r', p') → p' ≤ pos := by
      intro r' p' hb
      cases hacc : (dfa.states[sid]!).accept with
      | none => rw [hacc] at hb; exact hbest r' p' hb
      | some rule => rw [hacc] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb; omega
    cases hst : (dfa.states[sid]!).stepChar c with
    | none =>
      simp only [hst] at h
      have := hbest' r p h
      simp only [List.length_cons]; omega
    | some next =>
      simp only [hst] at h
      have := ih next (pos + 1) _ (by
        intro r' p' hb; exact Nat.le_trans (hbest' r' p' hb) (by omega)) r p h
      simp only [List.length_cons]; omega

/-- If `DFA.scan` matches, the length does not exceed the input. -/
theorem scan_len_le (dfa : DFA) (cs : List Char) (rule len : Nat)
    (h : DFA.scan dfa cs = some (rule, len)) : len ≤ cs.length := by
  have := scanGo_pos_le dfa 0 cs 0 none (by intro r p hb; simp at hb) rule len h
  simpa using this

/-! ### The `String.Pos` flat scanner agrees with `scanStr` -/

/-- The flat `String.Pos` walk equals the derivative-vector `scanStr` walk, given the
    step/accept/range agreements. By induction on fuel; each step uses the pointwise
    agreements (`StepAgree`/`AcceptAgree`) and `StatesInRange` keeps the state valid. -/
theorem flatScanStrGo_eq_scanStrGo {s : String} (f : FlatDFA) (dfa : DFA)
    (hstep : StepAgree f dfa) (hacc : AcceptAgree f dfa) (hrange : StatesInRange f dfa) :
    ∀ (fuel sid : Nat) (p : s.Pos) (cs : Nat) (best : Option (Nat × Nat × s.Pos)),
      sid < dfa.states.size →
      DFA.flatScanStrGo f fuel sid p cs best = DFA.scanStrGo dfa fuel sid p cs best := by
  intro fuel
  induction fuel with
  | zero => intro sid p cs best _; rfl
  | succ fuel ih =>
    intro sid p cs best hsid
    rw [DFA.flatScanStrGo, DFA.scanStrGo]
    rw [show acceptOf f sid = (dfa.states[sid]!).accept from hacc sid hsid]
    by_cases h : p = s.endPos
    · simp only [h, dite_eq_left]
    · simp only [h, dite_eq_right, not_false_eq_true]
      rw [show step f sid (p.get h) = (dfa.states[sid]!).stepChar (p.get h) from hstep sid hsid _]
      cases hst : (dfa.states[sid]!).stepChar (p.get h) with
      | none => rfl
      | some next =>
        have hnext : next < dfa.states.size := by
          apply hrange sid hsid (p.get h) next
          rw [hstep sid hsid _]; exact hst
        exact ih next (p.next h) (cs + 1) _ hnext

/-- The `String.Pos` flat scanner equals `scanStr`, given the agreements. -/
theorem flatScanStr_eq_scanStr {s : String} (f : FlatDFA) (dfa : DFA)
    (hstep : StepAgree f dfa) (hacc : AcceptAgree f dfa) (hrange : StatesInRange f dfa)
    (hstart : 0 < dfa.states.size) (start : s.Pos) :
    DFA.flatScanStr f start = DFA.scanStr dfa start := by
  unfold DFA.flatScanStr DFA.scanStr
  exact flatScanStrGo_eq_scanStrGo f dfa hstep hacc hrange _ 0 start 0 none hstart

end Lexer
