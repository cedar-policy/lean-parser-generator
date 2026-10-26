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
The position-index runtime scanner equals the derivative-level `List Char`
scanner.

`Lexer/DFA.lean` defines two scanners: `DFA.scan` over a `List Char` (the
specification all soundness proofs are stated against) and `DFA.scanStr`, which
walks a `String` by its `String.Pos` cursor (the runtime, allocation-free,
docs/DESIGN.md §9.7 step 1). `Lexer/Engine.lean` likewise has `tokenizeAuxDFA`
(spec, `List Char`) and `tokenizeStr` (runtime, `String.Pos`).

This file proves `tokenizeStr c input = tokenize c input`, so the runtime path
inherits `tokenize_sound` (`Lexer/Tokenize.lean`) unchanged.

The bridge avoids UTF-8 byte arithmetic by relating a `String.Pos` `p` to the
remaining character list `charsFrom p = (s.sliceFrom p).copy.toList`, driven by:
  * `charsFrom_endPos`  : `charsFrom endPos = []`;
  * `charsFrom_next`    : `charsFrom p = p.get h :: charsFrom (p.next h)`.
-/
public import LeanParserGenerator.Lexer.Engine


@[expose] public section

set_option maxHeartbeats 1000000

namespace Lexer

open String

/-- The remaining characters of `s` from position `p` onward — the ghost
    `List Char` the position cursor tracks. -/
def charsFrom {s : String} (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

/-- At the end position, no characters remain. -/
theorem charsFrom_endPos (s : String) : charsFrom s.endPos = [] := by
  rw [charsFrom, String.toList_eq_nil_iff, ← String.utf8ByteSize_eq_zero_iff,
    Slice.utf8ByteSize_copy, utf8ByteSize_sliceFrom]
  simp

/-- `(s.sliceFrom p).copy` splits as the character at `p` followed by the copy from
    `p.next`. -/
theorem sliceFrom_copy_eq (s : String) (p : s.Pos) (h : p ≠ s.endPos) :
    (s.sliceFrom p).copy = String.singleton (p.get h) ++ (s.sliceFrom (p.next h)).copy := by
  have h1 := String.Pos.eq_copy_sliceTo_append_get (pos := p) h
  have h2 : s = (s.sliceTo p).copy ++ (s.sliceFrom p).copy := by simp
  have h3 : (s.sliceTo p).copy ++ (s.sliceFrom p).copy
      = (s.sliceTo p).copy ++ (String.singleton (p.get h) ++ (s.sliceFrom (p.next h)).copy) := by
    rw [← String.append_assoc]; exact h2.symm.trans h1
  exact (String.append_right_inj _).1 h3

/-- The remaining characters at `p` are `p.get h` then the remaining at `p.next h`. -/
theorem charsFrom_next {s : String} (p : s.Pos) (h : p ≠ s.endPos) :
    charsFrom p = p.get h :: charsFrom (p.next h) := by
  rw [charsFrom, charsFrom, sliceFrom_copy_eq s p h]
  simp [String.toList_append]

/-- `charsFrom` at the start position is the whole character list. -/
theorem charsFrom_startPos (s : String) : charsFrom s.startPos = s.toList := by
  rw [charsFrom]
  have : (s.sliceFrom s.startPos).copy = s := by
    apply String.toByteArray_inj.1
    simp
  rw [this]

/-- A string's character count is at most its UTF-8 byte size (each character is
    at least one byte). Lets the runtime use the O(1) `utf8ByteSize` as the scan
    fuel instead of the O(n) `toList.length`. -/
theorem toList_length_le_utf8ByteSize (s : String) :
    s.toList.length ≤ s.utf8ByteSize := by
  induction s using String.push_induction with
  | empty => simp
  | push b c ih =>
      rw [String.toList_push, List.length_append, String.utf8ByteSize_push]
      have := c.utf8Size_pos
      simp only [List.length_cons, List.length_nil]
      omega

/-- Project a `scanStr`-style accumulator `(rule, len, pos)` to the `scan`-style
    `(rule, len)`. -/
@[inline] def projRL {s : String} (o : Option (Nat × Nat × s.Pos)) : Option (Nat × Nat) :=
  o.map (fun t => (t.1, t.2.1))

/-- **Scanner agreement (walk).** With enough fuel, the position-cursor walk
    `scanStrGo`, projected to `(rule, len)`, equals the `List Char` walk
    `DFA.scan.go` on the remaining characters `charsFrom p`, at the same character
    counter and starting accumulator. Proof by induction on `fuel`, casing on
    whether `p` is the end position; `charsFrom_next`/`charsFrom_endPos` align the
    two recursions step for step. -/
theorem scanStrGo_eq_scanGo {s : String} (dfa : DFA) :
    ∀ (fuel sid : Nat) (p : s.Pos) (n : Nat) (best : Option (Nat × Nat × s.Pos)),
      (charsFrom p).length < fuel →
      projRL (DFA.scanStrGo dfa fuel sid p n best)
        = DFA.scan.go dfa sid (charsFrom p) n (projRL best)
  | 0, _, p, _, _, hlen => by exact absurd hlen (Nat.not_lt_zero _)
  | fuel + 1, sid, p, n, best, hlen => by
      by_cases hend : p = s.endPos
      · -- at end: scanStrGo does the accept-update then returns; charsFrom p = []
        have hnil : charsFrom p = [] := by rw [hend]; exact charsFrom_endPos s
        rw [hnil, DFA.scan.go]
        rw [DFA.scanStrGo]
        simp only [hend, dite_eq_left]
        cases (dfa.states[sid]!).accept <;> simp [projRL]
      · -- not end: peel one char
        have hcf : charsFrom p = p.get hend :: charsFrom (p.next hend) := charsFrom_next p hend
        have hlen' : (charsFrom (p.next hend)).length < fuel := by
          rw [hcf] at hlen; simpa using hlen
        rw [hcf, DFA.scan.go]
        rw [DFA.scanStrGo]
        simp only [hend, dite_eq_right, not_false_iff]
        cases hstep : (dfa.states[sid]!).stepChar (p.get hend) with
        | none =>
            simp only []
            cases (dfa.states[sid]!).accept <;> simp [projRL]
        | some next =>
            simp only [scanStrGo_eq_scanGo dfa fuel next (p.next hend) (n+1) _ hlen']
            cases (dfa.states[sid]!).accept <;> simp [projRL]

/-- **Scanner agreement (entry).** `scanStr` projected to `(rule, len)` equals
    `scan` on the whole input. -/
theorem scanStr_eq_scan {s : String} (dfa : DFA) :
    projRL (DFA.scanStr dfa s.startPos) = DFA.scan dfa s.toList := by
  rw [DFA.scanStr, DFA.scan]
  have hlen : (charsFrom s.startPos).length < s.utf8ByteSize + 1 := by
    rw [charsFrom_startPos]; have := toList_length_le_utf8ByteSize s; omega
  have := scanStrGo_eq_scanGo dfa (s.utf8ByteSize + 1) 0 s.startPos 0 none hlen
  rw [charsFrom_startPos] at this
  simpa [projRL] using this

/-- **Position drop.** If a `scanStrGo` walk (relative to a fixed remaining suffix
    `cs0` reached at char counter `n`, with the accumulator consistent) returns
    `(rule, len, p')`, then the remaining characters at `p'` are `cs0` dropped by
    `len`. This is what lets the tokenizer recurse at the returned position: it has
    consumed exactly `len` characters. -/
theorem scanStrGo_pos {s : String} (dfa : DFA) (cs0 : List Char) :
    ∀ (fuel sid : Nat) (p : s.Pos) (n : Nat) (best : Option (Nat × Nat × s.Pos)),
      (charsFrom p).length < fuel →
      charsFrom p = cs0.drop n →
      (∀ rb lb pb, best = some (rb, lb, pb) → charsFrom pb = cs0.drop lb) →
      ∀ rule len p', DFA.scanStrGo dfa fuel sid p n best = some (rule, len, p') →
        charsFrom p' = cs0.drop len := by
  intro fuel
  induction fuel with
  | zero => intro sid p n best hlen _ _ rule len p' _; exact absurd hlen (Nat.not_lt_zero _)
  | succ fuel ih =>
      intro sid p n best hlen hp hbest rule len p' heq
      rw [DFA.scanStrGo] at heq
      by_cases hend : p = s.endPos
      · rw [dite_eq_left hend] at heq
        cases hacc : (dfa.states[sid]!).accept with
        | none => rw [hacc] at heq; exact hbest rule len p' heq
        | some rule2 =>
            rw [hacc] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨_hr, hl, hp'⟩ := heq
            rw [← hp', ← hl]; exact hp
      · simp only [hend, dite_eq_right, not_false_iff] at heq
        have hcf : charsFrom p = p.get hend :: charsFrom (p.next hend) := charsFrom_next p hend
        have hlen' : (charsFrom (p.next hend)).length < fuel := by rw [hcf] at hlen; simpa using hlen
        have hb2inv : ∀ rb lb pb,
            (match (dfa.states[sid]!).accept with | some rule => some (rule, n, p) | none => best) = some (rb, lb, pb) →
            charsFrom pb = cs0.drop lb := by
          intro rb lb pb hbeq
          cases hacc : (dfa.states[sid]!).accept with
          | none => rw [hacc] at hbeq; exact hbest rb lb pb hbeq
          | some r2 =>
              rw [hacc] at hbeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbeq
              obtain ⟨_, hl, hpb⟩ := hbeq; rw [← hpb, ← hl]; exact hp
        have hpnext : charsFrom (p.next hend) = cs0.drop (n+1) := by
          have h1 : cs0.drop n = p.get hend :: charsFrom (p.next hend) := by rw [← hp, hcf]
          rw [List.drop_add_one_eq_tail_drop, h1]; simp
        cases hstep : (dfa.states[sid]!).stepChar (p.get hend) with
        | none => rw [hstep] at heq; exact hb2inv rule len p' heq
        | some next =>
            rw [hstep] at heq
            exact ih next (p.next hend) (n+1) _ hlen' hpnext hb2inv rule len p' heq

/-- `(s.sliceFrom p).copy` splits at `q ≥ p` as the extract `[p, q)` followed by the
    copy from `q`. The extract-side companion of `sliceFrom_copy_eq`. -/
theorem sliceFrom_copy_split (s : String) (p q : s.Pos) (h : p ≤ q) :
    (s.sliceFrom p).copy = (s.extract p q) ++ (s.sliceFrom q).copy := by
  apply String.toByteArray_inj.1
  rw [String.toByteArray_append, Slice.toByteArray_copy, String.toByteArray_extract,
      Slice.toByteArray_copy]
  simp only [String.startInclusive_sliceFrom, String.endExclusive_sliceFrom,
    String.offset_endPos, String.str_sliceFrom]
  have hq : q.offset.byteIdx ≤ s.rawEndPos.byteIdx := by
    have := q.isValid.le_rawEndPos; simp
  have hpq : p.offset.byteIdx ≤ q.offset.byteIdx := by simpa [Pos.le_iff, Pos.Raw.le_iff] using h
  rw [ByteArray.extract_eq_extract_append_extract q.offset.byteIdx hpq hq]

/-- **Lexeme agreement.** When `q ≥ p` and the characters remaining at `q` are the
    ones at `p` dropped by `len`, the extract `[p, q)` is exactly the length-`len`
    prefix of the characters at `p`, as a `String`. This is the lexeme the runtime
    tokenizer produces, equal to `String.ofList ((charsFrom p).take len)` — what
    `tokenizeAuxDFA` builds via `cs.take len`. -/
theorem extract_toList_eq {s : String} (p q : s.Pos) (len : Nat) (h : p ≤ q)
    (hq : charsFrom q = (charsFrom p).drop len) :
    (s.extract p q).toList = (charsFrom p).take len := by
  have hsplit : charsFrom p = (s.extract p q).toList ++ charsFrom q := by
    rw [charsFrom, sliceFrom_copy_split s p q h, String.toList_append]; rfl
  rw [hq] at hsplit
  have htd : (charsFrom p).take len ++ (charsFrom p).drop len = charsFrom p :=
    List.take_append_drop len _
  -- (s.extract p q).toList ++ drop len = take len ++ drop len
  have : (s.extract p q).toList ++ (charsFrom p).drop len
      = (charsFrom p).take len ++ (charsFrom p).drop len := by rw [← hsplit, htd]
  exact (List.append_cancel_right this)

/-- **Position monotonicity.** With a fixed lower bound `p0 ≤ p` that also bounds
    every accumulator position, the position `scanStrGo` returns is `≥ p0`. The
    walk only advances (`p ≤ p.next`), so `p0` stays a lower bound throughout. -/
theorem scanStrGo_pos_le {s : String} (dfa : DFA) (p0 : s.Pos) :
    ∀ (fuel sid : Nat) (p : s.Pos) (n : Nat) (best : Option (Nat × Nat × s.Pos)),
      p0 ≤ p →
      (∀ rb lb pb, best = some (rb, lb, pb) → p0 ≤ pb) →
      ∀ rule len p', DFA.scanStrGo dfa fuel sid p n best = some (rule, len, p') → p0 ≤ p' := by
  intro fuel
  induction fuel with
  | zero => intro sid p n best _ hbest rule len p' heq; rw [DFA.scanStrGo] at heq; exact hbest rule len p' heq
  | succ fuel ih =>
      intro sid p n best hp0 hbest rule len p' heq
      rw [DFA.scanStrGo] at heq
      by_cases hend : p = s.endPos
      · rw [dite_eq_left hend] at heq
        cases hacc : (dfa.states[sid]!).accept with
        | none => rw [hacc] at heq; exact hbest rule len p' heq
        | some r2 =>
            rw [hacc] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨_, _, hp'⟩ := heq; rw [← hp']; exact hp0
      · simp only [hend, dite_eq_right, not_false_iff] at heq
        have hb2 : ∀ rb lb pb,
            (match (dfa.states[sid]!).accept with | some rule => some (rule, n, p) | none => best) = some (rb, lb, pb) →
            p0 ≤ pb := by
          intro rb lb pb hbeq
          cases hacc : (dfa.states[sid]!).accept with
          | none => rw [hacc] at hbeq; exact hbest rb lb pb hbeq
          | some r2 =>
              rw [hacc] at hbeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbeq
              obtain ⟨_, _, hpb⟩ := hbeq; rw [← hpb]; exact hp0
        have hp0next : p0 ≤ p.next hend :=
          String.Pos.le_trans hp0 (String.Pos.le_of_lt String.Pos.lt_next)
        cases hstep : (dfa.states[sid]!).stepChar (p.get hend) with
        | none => rw [hstep] at heq; exact hb2 rule len p' heq
        | some next =>
            rw [hstep] at heq
            exact ih next (p.next hend) (n+1) _ hp0next hb2 rule len p' heq

/-- The remaining-character count at any position is at most the whole length. -/
theorem charsFrom_length_le {s : String} (p : s.Pos) :
    (charsFrom p).length ≤ s.toList.length := by
  have hsplit := sliceFrom_copy_split s s.startPos p (by simp [String.Pos.le_iff, Pos.Raw.le_iff])
  have : charsFrom s.startPos = (s.extract s.startPos p).toList ++ charsFrom p := by
    rw [charsFrom, hsplit, String.toList_append]; rfl
  rw [charsFrom_startPos] at this
  rw [this, List.length_append]
  omega

/-- The remaining-character count at any position is at most the whole byte size. -/
theorem charsFrom_length_le_byteSize {s : String} (p : s.Pos) :
    (charsFrom p).length ≤ s.utf8ByteSize :=
  Nat.le_trans (charsFrom_length_le p) (toList_length_le_utf8ByteSize s)

/-- **Per-position scan agreement.** `scanStr` at any position `p`, projected to
    `(rule, len)`, equals `scan` on the characters remaining at `p`. Same as
    `scanStr_eq_scan` but at an arbitrary position (used inside the tokenizer
    induction). -/
theorem scanStr_eq_scan_at {s : String} (dfa : DFA) (p : s.Pos) :
    projRL (DFA.scanStr dfa p) = DFA.scan dfa (charsFrom p) := by
  rw [DFA.scanStr, DFA.scan]
  have hlen : (charsFrom p).length < s.utf8ByteSize + 1 := by
    have := charsFrom_length_le_byteSize p; omega
  have := scanStrGo_eq_scanGo dfa (s.utf8ByteSize + 1) 0 p 0 none hlen
  simpa [projRL] using this

/-- Definitional unfolding of `tokenizeAuxDFA` on a non-empty input (the cons
    equation), stated by `rfl` to avoid the equation compiler's overlapping-pattern
    side goals when rewriting. -/
theorem tokenizeAuxDFA_cons {Tok : Type} (c : Compiled Tok) (fuel cpos : Nat)
    (ch : Char) (cs : List Char) (stack : List Nat) (acc : List Tok) :
    tokenizeAuxDFA c (fuel+1) (ch :: cs) cpos stack acc =
      (let mode := stack.headD c.start
       let dfa := c.dfas.getD mode default
       match DFA.scan dfa (ch :: cs) with
        | some (rule, len) =>
            if len = 0 then .error { pos := cpos, char := (ch::cs).head? }
            else
              let matched := String.ofList ((ch::cs).take len)
              let rest := (ch::cs).drop len
              let act := (c.acts.getD mode #[]).getD rule (fun _ => {})
              let a := act matched
              let acc := match a.emit with | some tok => tok :: acc | none => acc
              let stack := match a.trans with | .stay => stack | .push m => m :: stack | .pop => stack.tail
              tokenizeAuxDFA c fuel rest (cpos + len) stack acc
        | none => .error { pos := cpos, char := (ch::cs).head? }) := rfl

/-- **Tokenizer loop agreement.** The position-cursor loop `tokenizeStrAux` at
    position `p` (with char counter `cpos`) equals the `List Char` loop
    `tokenizeAuxDFA` on the characters remaining at `p`. By induction on `fuel`,
    aligning the scan (`scanStr_eq_scan_at`), the lexeme
    (`extract_toList_eq` + `scanStrGo_pos`), and the position advance
    (`scanStrGo_pos`) at each step. -/
theorem tokenizeStrAux_eq {Tok : Type} (c : Compiled Tok) (s : String)
    (fuel : Nat) (p : s.Pos) (cpos : Nat) (stack : List Nat) (acc : List Tok) :
    (charsFrom p).length < fuel →
    tokenizeStrAux c s fuel p cpos stack acc
      = tokenizeAuxDFA c fuel (charsFrom p) cpos stack acc := by
  fun_induction tokenizeStrAux c s fuel p cpos stack acc with
  | case1 p cpos stack acc => intro hlen; exact absurd hlen (Nat.not_lt_zero _)
  | case2 fuel cpos acc head tok heof => intro _; rw [charsFrom_endPos]; simp [tokenizeAuxDFA, heof]
  | case3 fuel cpos acc head heof => intro _; rw [charsFrom_endPos]; simp [tokenizeAuxDFA, heof]
  | case4 fuel cpos stack acc hne =>
      intro _
      rw [charsFrom_endPos]
      rcases stack with _ | ⟨a, _ | ⟨b, t⟩⟩
      · rfl
      · exact (hne a rfl).elim
      · rfl
  | case5 fuel p cpos stack acc hend _mode _dfa rule endPos hstr =>
      intro _
      have hcf : charsFrom p = p.get hend :: charsFrom (p.next hend) := charsFrom_next p hend
      have hscan := scanStr_eq_scan_at (c.dfas.getD (stack.headD c.start) default) p
      have hscaneq : DFA.scan (c.dfas.getD (stack.headD c.start) default)
          (p.get hend :: charsFrom (p.next hend)) = some (rule, 0) := by
        rw [← hcf, ← hscan, hstr]; rfl
      rw [hcf, tokenizeAuxDFA_cons]
      simp only [hscaneq, List.head?, ite_true]
  | case6 fuel p cpos stack acc hend _mode _dfa rule len endPos hstr hlen0
          _matched _act _a _acc2 _stack2 ih =>
      intro hlenf
      have hcf : charsFrom p = p.get hend :: charsFrom (p.next hend) := charsFrom_next p hend
      have hscan := scanStr_eq_scan_at (c.dfas.getD (stack.headD c.start) default) p
      have hscaneq : DFA.scan (c.dfas.getD (stack.headD c.start) default)
          (p.get hend :: charsFrom (p.next hend)) = some (rule, len) := by
        rw [← hcf, ← hscan, hstr]; rfl
      have hposdrop : charsFrom endPos = (charsFrom p).drop len := by
        apply scanStrGo_pos (c.dfas.getD (stack.headD c.start) default) (charsFrom p)
          (s.utf8ByteSize + 1) 0 p 0 none (by have := charsFrom_length_le_byteSize p; omega) rfl
          (by intro rb lb pb hb; simp at hb) rule len endPos
        rw [DFA.scanStr] at hstr; exact hstr
      have hple : p ≤ endPos := by
        apply scanStrGo_pos_le (c.dfas.getD (stack.headD c.start) default) p
          (s.utf8ByteSize + 1) 0 p 0 none (String.Pos.le_refl _) (by intro rb lb pb hb; simp at hb)
          rule len endPos
        rw [DFA.scanStr] at hstr; exact hstr
      have hlex : s.extract p endPos = String.ofList ((charsFrom p).take len) := by
        have := extract_toList_eq p endPos len hple hposdrop
        rw [← this, String.ofList_toList]
      have hfuel' : (charsFrom endPos).length < fuel := by
        have hpl : (charsFrom p).length = (charsFrom (p.next hend)).length + 1 := by rw [hcf]; simp
        have hlp : 0 < len := Nat.pos_of_ne_zero hlen0
        rw [hposdrop, List.length_drop]
        have hcflen : (charsFrom p).length < fuel + 1 := hlenf
        omega
      rw [hcf, tokenizeAuxDFA_cons]
      simp only [hscaneq, hlen0, ite_false]
      rw [ih hfuel']
      simp only [hposdrop, ← hcf, ← hlex]
      rfl
  | case7 fuel p cpos stack acc hend _mode _dfa hstr =>
      intro _
      have hcf : charsFrom p = p.get hend :: charsFrom (p.next hend) := charsFrom_next p hend
      have hscan := scanStr_eq_scan_at (c.dfas.getD (stack.headD c.start) default) p
      have hsc : DFA.scan (c.dfas.getD (stack.headD c.start) default)
          (p.get hend :: charsFrom (p.next hend)) = none := by
        rw [← hcf, ← hscan, hstr]; rfl
      rw [hcf, tokenizeAuxDFA_cons]
      simp only [hsc, List.head?]

/-- **`tokenizeAuxDFA` is fuel-insensitive above the input length.** Any two fuel
    budgets that both exceed the remaining character count give the same result:
    the loop consumes ≥1 character per step and stops at `[]`, so surplus fuel is
    never used. This lets the runtime pick the O(1) `utf8ByteSize` fuel while the
    spec keeps `toList.length`. -/
theorem tokenizeAuxDFA_fuel_irrel {Tok : Type} (c : Compiled Tok) :
    ∀ (f1 f2 : Nat) (cs : List Char) (cpos : Nat) (stack : List Nat) (acc : List Tok),
      cs.length < f1 → cs.length < f2 →
      tokenizeAuxDFA c f1 cs cpos stack acc = tokenizeAuxDFA c f2 cs cpos stack acc := by
  intro f1
  induction f1 with
  | zero => intro f2 cs cpos stack acc h1 _; exact absurd h1 (Nat.not_lt_zero _)
  | succ f1 ih =>
      intro f2 cs cpos stack acc h1 h2
      match f2, cs with
      | 0, _ => exact absurd h2 (Nat.not_lt_zero _)
      | f2+1, [] => rfl
      | f2+1, ch :: rest =>
          rw [tokenizeAuxDFA_cons, tokenizeAuxDFA_cons]
          cases hsc : DFA.scan (c.dfas.getD (stack.headD c.start) default) (ch :: rest) with
          | none => simp only [hsc]
          | some tup =>
              obtain ⟨rule, len⟩ := tup
              by_cases hlen0 : len = 0
              · subst hlen0; simp only [hsc, ite_true]
              · simp only [hsc, hlen0, ite_false]
                have hr1 : rest.length < f1 := by simpa [List.length_cons] using h1
                have hr2 : rest.length < f2 := by simpa [List.length_cons] using h2
                have hlp : 0 < len := Nat.pos_of_ne_zero hlen0
                have hlen' : ((ch :: rest).drop len).length < f1 := by
                  simp only [List.length_drop, List.length_cons]; omega
                have hlen'2 : ((ch :: rest).drop len).length < f2 := by
                  simp only [List.length_drop, List.length_cons]; omega
                exact ih f2 _ _ _ _ hlen' hlen'2

/-- **Tokenizer entry-point agreement.** The byte-index runtime tokenizer
    `tokenizeStr` returns exactly what the specification `tokenize` returns. The
    runtime is a verified-equal implementation of the proven `List Char` loop, so
    `Lexer.tokenize_sound` (`Lexer/Tokenize.lean`) transfers to it unchanged. -/
theorem tokenizeStr_eq_tokenize {Tok : Type} (c : Compiled Tok) (input : String) :
    tokenizeStr c input = tokenize c input := by
  rw [tokenizeStr, tokenize]
  have hbyte : (charsFrom input.startPos).length < input.utf8ByteSize + 1 := by
    have := charsFrom_length_le_byteSize input.startPos; omega
  have heq := tokenizeStrAux_eq c input (input.utf8ByteSize + 1) input.startPos 0 [c.start] [] hbyte
  rw [charsFrom_startPos] at heq
  rw [heq]
  -- align the two fuels (both exceed input.toList.length)
  apply tokenizeAuxDFA_fuel_irrel
  · have := toList_length_le_utf8ByteSize input; omega
  · omega

end Lexer
