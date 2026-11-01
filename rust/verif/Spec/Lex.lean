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

/-!
The lexer kernel (`lpg_kernel::lex`) as a Lean function over numbers.

`LexTables` is the DFA as the kernel reads it: the byte classes, the transitions of each
state by class (state 0 is dead), the rule plus one of each accepting state (the states from
`acceptFrom` on), the start state, the terminal of each rule, and the end-of-input terminal.

`lscan` is the longest-match scan from a position, one byte per step, in the shape of
`DFA.byteScanGo`: it records the last accepting state's rule and position. The kernel's
`scan` also skips runs of bytes that leave the state unchanged in an inner loop; the proof
about the Aeneas translation shows that this computes `lscan`. `llex` is the loop of `lex`:
scan, fail on no match or an empty match, push the token unless the rule's terminal is
`TERM_SKIP`, and end with the end-of-input token.
-/

namespace Spec

/-- `TERM_SKIP` and `RULE_EOF` of the kernel. -/
def termSkip : Nat := 65535
def ruleEof : Nat := 65535

/-- The lexer DFA as numbers. -/
structure LexDFA where
  /-- `class[b]`. -/
  cls : Nat → Nat
  /-- `trans[s][c]`. -/
  trans : Nat → Nat → Nat
  /-- `accept[s]`: the rule of an accepting state plus one. -/
  accept : Nat → Nat
  start : Nat
  acceptFrom : Nat

/-- The lexer tables as numbers: the DFA, the terminal of each rule, the end-of-input
    terminal. -/
structure LexTables where
  dfa : LexDFA
  /-- `rule_term[r]`. -/
  ruleTerm : Nat → Nat
  eof : Nat

/-- A token of the kernel: rule, terminal, start, end. -/
structure LTok where
  rule : Nat
  term : Nat
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- How `lex` ends. -/
inductive LStop where
  | ok
  | noMatch (pos : Nat)
  | tooLong
  deriving DecidableEq, Repr

/-- The match so far after visiting `row` at `i`. -/
def lrecord (t : LexDFA) (row i best e : Nat) : Nat × Nat :=
  if row ≥ t.acceptFrom then (t.accept row, i) else (best, e)

/-- The longest match: walk the DFA from `row` at `i`, one byte per step, and return the rule
    plus one of the last accepting state visited (or `best`) and where it was. -/
def lscan (t : LexDFA) (src : List Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, best, e => (best, e)
  | f + 1, row, i, best, e =>
    let r := lrecord t row i best e
    if h : i < src.length then
      let next := t.trans row (t.cls src[i])
      if next = 0 then r else lscan t src f next (i + 1) r.1 r.2
    else r

/-- The scan from `pos`, with enough steps. -/
def lscanFrom (t : LexDFA) (src : List Nat) (pos : Nat) : Nat × Nat :=
  lscan t src (src.length + 1 - pos) t.start pos 0 pos

/-- The loop of `lex` from `pos`, with `f` steps, after the tokens `acc`. -/
def llexGo (t : LexTables) (src : List Nat) : Nat → Nat → List LTok → LStop × List LTok
  | 0, pos, acc => (.noMatch pos, acc)
  | f + 1, pos, acc =>
    if pos ≥ src.length then
      (.ok, acc ++ [⟨ruleEof, t.eof, src.length, src.length⟩])
    else
      let (rule, e) := lscanFrom t.dfa src pos
      if rule = 0 ∨ e ≤ pos then (.noMatch pos, acc)
      else
        let term := t.ruleTerm (rule - 1)
        let acc := if term ≠ termSkip then acc ++ [⟨rule - 1, term, pos, e⟩] else acc
        llexGo t src f e acc

/-- `lex` on `src` after the tokens `acc`: too long, or the loop with one step per byte. -/
def llex (t : LexTables) (src : List Nat) (acc : List LTok) : LStop × List LTok :=
  if src.length > 2 ^ 32 - 1 then (.tooLong, acc)
  else llexGo t src (src.length + 1) 0 acc

/-! ### Facts about the scan -/

section
variable (t : LexDFA) (src : List Nat)

/-- A step of the scan reads the match so far only through `lrecord`. -/
theorem lscan_succ_congr (f row i b e b' e' : Nat)
    (h : lrecord t row i b e = lrecord t row i b' e') :
    lscan t src (f + 1) row i b e = lscan t src (f + 1) row i b' e' := by
  simp only [lscan, h]

theorem lrecord_lrecord (row i j b e : Nat) :
    lrecord t row j (lrecord t row i b e).1 (lrecord t row i b e).2 = lrecord t row j b e := by
  unfold lrecord
  by_cases h : row ≥ t.acceptFrom <;> simp [h]

/-- The end of the match is at most the length of the source. -/
theorem lscan_le (f row i b e : Nat) (hi : i ≤ src.length) (he : e ≤ src.length) :
    (lscan t src f row i b e).2 ≤ src.length := by
  induction f generalizing row i b e with
  | zero => simpa [lscan] using he
  | succ f ih =>
    have hr : (lrecord t row i b e).2 ≤ src.length := by
      unfold lrecord; split <;> simp [hi, he]
    simp only [lscan]
    split
    · rename_i hlt
      split
      · exact hr
      · exact ih _ _ _ _ (by omega) hr
    · exact hr

/-- Enough steps: more do not change the scan. -/
theorem lscan_fuel (f row i b e : Nat) (hi : i ≤ src.length) (hf : src.length + 1 - i ≤ f) :
    lscan t src f row i b e = lscan t src (src.length + 1 - i) row i b e := by
  induction f generalizing row i b e with
  | zero => omega
  | succ f ih =>
    have hpos : src.length + 1 - i = (src.length - i) + 1 := by omega
    rw [hpos]
    simp only [lscan]
    split
    · rename_i hlt
      split
      · rfl
      · rw [ih _ _ _ _ (by omega) (by omega)]
        have : src.length + 1 - (i + 1) = src.length - i := by omega
        rw [this]
    · rfl

/-- A run of bytes on which the state does not change can be skipped. -/
theorem lscan_run (row k j b e : Nat) (hkj : k ≤ j) (hj : j ≤ src.length)
    (hrun : ∀ m (h : m < src.length), k ≤ m → m < j → t.trans row (t.cls src[m]) = row)
    (hrow : row ≠ 0) :
    lscan t src (src.length + 1 - k) row k b e = lscan t src (src.length + 1 - j) row j b e := by
  induction h : j - k generalizing k b e with
  | zero =>
    have : k = j := by omega
    subst this; rfl
  | succ d ih =>
    have hk : k < src.length := by omega
    have hpos : src.length + 1 - k = (src.length - k) + 1 := by omega
    rw [hpos]
    simp only [lscan, hk, dite_true, hrun k hk (Nat.le_refl _) (by omega), hrow, ite_false]
    have : src.length - k = src.length + 1 - (k + 1) := by omega
    rw [this, ih (k + 1) _ _ (by omega) (fun m hm h1 h2 => hrun m hm (by omega) h2) (by omega)]
    have hj1 : src.length + 1 - j = (src.length - j) + 1 := by omega
    rw [hj1]
    apply lscan_succ_congr
    exact lrecord_lrecord t row k j b e

end

/-- One step of the scan with the canonical number of steps, before the end. -/
theorem lscan_step (t : LexDFA) (src : List Nat) (row i b e : Nat) (hi : i < src.length) :
    lscan t src (src.length + 1 - i) row i b e =
      if t.trans row (t.cls src[i]) = 0 then lrecord t row i b e
      else lscan t src (src.length + 1 - (i + 1)) (t.trans row (t.cls src[i])) (i + 1)
        (lrecord t row i b e).1 (lrecord t row i b e).2 := by
  have : src.length + 1 - i = (src.length + 1 - (i + 1)) + 1 := by omega
  rw [this]
  simp [lscan, hi]

/-- The scan at the end of the source. -/
theorem lscan_end (t : LexDFA) (src : List Nat) (row i b e : Nat) (hi : src.length ≤ i)
    (hi' : i ≤ src.length) :
    lscan t src (src.length + 1 - i) row i b e = lrecord t row i b e := by
  have : src.length + 1 - i = 0 + 1 := by omega
  rw [this]
  simp [lscan, show ¬ i < src.length by omega]

/-- The rule of a scan is the one it started with or an accepting state's. -/
theorem lscan_rule_le (t : LexDFA) (src : List Nat) (K : Nat) (hK : ∀ s, t.accept s ≤ K)
    (f row i b e : Nat) (hb : b ≤ K) : (lscan t src f row i b e).1 ≤ K := by
  induction f generalizing row i b e with
  | zero => simpa [lscan] using hb
  | succ f ih =>
    have hr : (lrecord t row i b e).1 ≤ K := by
      unfold lrecord; split
      · exact hK row
      · exact hb
    simp only [lscan]
    split
    · split
      · exact hr
      · exact ih _ _ _ _ hr
    · exact hr

/-! ### Facts about the loop -/

/-- The end of a scan from `pos` is at most the length. -/
theorem lscanFrom_le (t : LexDFA) (src : List Nat) (pos : Nat) (hpos : pos ≤ src.length) :
    (lscanFrom t src pos).2 ≤ src.length :=
  lscan_le t src _ _ _ _ _ hpos hpos

/-- Enough steps: more do not change the loop. -/
theorem llexGo_mono (t : LexTables) (src : List Nat) (f : Nat) :
    ∀ (g pos : Nat) (acc : List LTok), pos ≤ src.length → src.length + 1 - pos ≤ f → f ≤ g →
      llexGo t src f pos acc = llexGo t src g pos acc := by
  induction f with
  | zero => intro g pos acc _ hf _; omega
  | succ f ih =>
    intro g pos acc hpos hf hfg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    simp only [llexGo]
    split
    · rfl
    · split
      · rfl
      · rename_i hge hne
        have hle := lscanFrom_le t.dfa src pos hpos
        exact ih _ _ _ hle (by omega) (by omega)

theorem llexGo_fuel (t : LexTables) (src : List Nat) (f pos : Nat) (acc : List LTok)
    (hpos : pos ≤ src.length) (hf : src.length + 1 - pos ≤ f) :
    llexGo t src f pos acc = llexGo t src (src.length + 1 - pos) pos acc :=
  (llexGo_mono t src _ _ pos acc hpos (Nat.le_refl _) hf).symm

/-- One step of the loop with the canonical number of steps, before the end. -/
theorem llexGo_step (t : LexTables) (src : List Nat) (pos : Nat) (acc : List LTok)
    (hpos : pos < src.length) :
    llexGo t src (src.length + 1 - pos) pos acc =
      if (lscanFrom t.dfa src pos).1 = 0 ∨ (lscanFrom t.dfa src pos).2 ≤ pos then
        (.noMatch pos, acc)
      else
        llexGo t src (src.length + 1 - (lscanFrom t.dfa src pos).2) (lscanFrom t.dfa src pos).2
          (if t.ruleTerm ((lscanFrom t.dfa src pos).1 - 1) ≠ termSkip then
            acc ++ [⟨(lscanFrom t.dfa src pos).1 - 1, t.ruleTerm ((lscanFrom t.dfa src pos).1 - 1),
              pos, (lscanFrom t.dfa src pos).2⟩]
          else acc) := by
  have hf : src.length + 1 - pos = (src.length - pos) + 1 := by omega
  rw [hf]
  simp only [llexGo, show ¬ pos ≥ src.length by omega, ↓reduceIte]
  split
  · rfl
  · rename_i hne
    have hle := lscanFrom_le t.dfa src pos (by omega)
    exact llexGo_fuel t src _ _ _ hle (by omega)

/-- The loop at the end of the source. -/
theorem llexGo_end (t : LexTables) (src : List Nat) (pos : Nat) (acc : List LTok)
    (hpos : pos = src.length) :
    llexGo t src (src.length + 1 - pos) pos acc =
      (.ok, acc ++ [⟨ruleEof, t.eof, src.length, src.length⟩]) := by
  subst hpos
  simp [llexGo]

end Spec
