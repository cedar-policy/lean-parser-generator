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

import Spec.Lex
import LeanParserGenerator.Lexer.DFA
import LeanParserGenerator.Lexer.FlatScan
import LeanParserGenerator.Lexer.Engine

/-!
The scan of the Rust lexer DFA is the scan of the Lean lexer DFA.

The Rust DFA reads bytes; the Lean `DFA` of a lexer mode (`Lexer.DFA`, the one `DFA.scan` and
`Lexer.tokenize` use) reads characters. `LexSim d dfa φ` says that the Rust DFA `d` simulates
`dfa` on UTF-8: `φ` maps each Lean state to a Rust state that accepts the same rule, and
reading the bytes of a character from `φ s` reaches `φ t` where `dfa` steps from `s` to `t`,
or the dead state 0 where `dfa` has no step, without an accepting state in the middle of the
character. `lscanFrom_sim` then says that the Rust scan from a byte position is `DFA.scan` on
the characters from there: the same rule, and the end at the byte length of the matched
characters.

`LexSim` quantifies over all characters; `Spec/LexCheck.lean` decides it.
-/

namespace Spec

open Lexer

/-- The UTF-8 bytes of a character, as numbers. -/
def enc (c : Char) : List Nat := (String.utf8EncodeChar c).map (·.toNat)

/-- The UTF-8 bytes of characters. -/
def encChars (cs : List Char) : List Nat := cs.flatMap enc

@[simp] theorem encChars_nil : encChars [] = [] := rfl
@[simp] theorem encChars_cons (c : Char) (cs : List Char) :
    encChars (c :: cs) = enc c ++ encChars cs := rfl
theorem encChars_append (a b : List Char) : encChars (a ++ b) = encChars a ++ encChars b := by
  simp [encChars]

theorem enc_ne_nil (c : Char) : enc c ≠ [] := by
  have : (String.utf8EncodeChar c).length = c.utf8Size := String.length_utf8EncodeChar c
  have h := Char.utf8Size_pos c
  intro he
  have : (enc c).length = 0 := by rw [he]; rfl
  simp [enc] at this; omega

/-- The state after reading `bs` from `q`. -/
def run (d : LexDFA) : Nat → List Nat → Nat
  | q, [] => q
  | q, b :: bs => run d (d.trans q (d.cls b)) bs

/-- The states after each proper nonempty prefix of `bs` do not accept. -/
def Mids (d : LexDFA) (q : Nat) (bs : List Nat) : Prop :=
  ∀ k, 0 < k → k < bs.length → run d q (bs.take k) < d.acceptFrom

/-- The Rust DFA `d` simulates the Lean DFA `dfa` on UTF-8, with the states of `dfa` mapped
    by `φ`. -/
structure LexSim (d : LexDFA) (dfa : DFA) (φ : Nat → Nat) : Prop where
  start : φ 0 = d.start
  size : 0 < dfa.states.size
  /-- A state accepts the rule its Lean state accepts. -/
  accept : ∀ s, s < dfa.states.size → ∀ i b e,
    lrecord d (φ s) i b e =
      match (dfa.states[s]!).accept with
      | some r => (r + 1, i)
      | none => (b, e)
  /-- The bytes of a character go where the Lean step goes, through non-accepting states. -/
  step : ∀ s, s < dfa.states.size → ∀ c : Char,
    Mids d (φ s) (enc c) ∧
      run d (φ s) (enc c) = (match (dfa.states[s]!).stepChar c with
        | some t => φ t
        | none => 0)
  target : ∀ s, s < dfa.states.size → ∀ (c : Char) t,
    (dfa.states[s]!).stepChar c = some t → t < dfa.states.size
  ne0 : ∀ s, s < dfa.states.size → φ s ≠ 0
  /-- State 0 is dead: it does not accept and stays. -/
  dead : ∀ c, d.trans 0 c = 0
  deadNA : 0 < d.acceptFrom

theorem run_dead (d : LexDFA) (h : ∀ c, d.trans 0 c = 0) : ∀ bs, run d 0 bs = 0 := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [run, h, ih]

/-- Reading a character's bytes: the scan records at the first state, goes through the
    non-accepting states of the middle of the character, and either dies or continues from
    the state at the end of it. -/
theorem lscan_block (d : LexDFA) (src : List Nat) (hdead : ∀ c, d.trans 0 c = 0) :
    ∀ (bs : List Nat) (q i b e : Nat), bs ≠ [] → q ≠ 0 → Mids d q bs →
      i + bs.length ≤ src.length → (∀ k (h : k < bs.length), src[i + k]? = some bs[k]) →
      lscan d src (src.length + 1 - i) q i b e =
        if run d q bs = 0 then lrecord d q i b e
        else lscan d src (src.length + 1 - (i + bs.length)) (run d q bs) (i + bs.length)
          (lrecord d q i b e).1 (lrecord d q i b e).2 := by
  intro bs
  induction bs with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons x rest ih =>
    intro q i b e _ hq hmid hlen hsrc
    have hi : i < src.length := by simp at hlen; omega
    have hx : src[i] = x := by
      have := hsrc 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      rw [List.getElem?_eq_getElem hi] at this
      exact Option.some.inj this
    rw [lscan_step d src q i b e hi, hx]
    by_cases hn : d.trans q (d.cls x) = 0
    · simp only [hn, ↓reduceIte, run, run_dead d hdead]
    · cases rest with
      | nil => simp [run, hn]
      | cons y rest' =>
        simp only [hn, ↓reduceIte, run]
        have hnA : d.trans q (d.cls x) < d.acceptFrom := by
          have := hmid 1 (by omega) (by simp)
          simpa [run] using this
        have hmid' : Mids d (d.trans q (d.cls x)) (y :: rest') := by
          intro k hk hk'
          have := hmid (k + 1) (by omega) (by simp at hk' ⊢; omega)
          simpa [run] using this
        have h := ih (d.trans q (d.cls x)) (i + 1) (lrecord d q i b e).1 (lrecord d q i b e).2
          (by simp) hn hmid' (by simp at hlen ⊢; omega)
          (fun k hk => by
            have := hsrc (k + 1) (by simp at hk ⊢; omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
        rw [h]
        have hrec : lrecord d (d.trans q (d.cls x)) (i + 1) (lrecord d q i b e).1
            (lrecord d q i b e).2 = lrecord d q i b e := by
          unfold lrecord; simp [show ¬ d.trans q (d.cls x) ≥ d.acceptFrom by omega]
        have e1 : i + 1 + (y :: rest').length = i + (x :: y :: rest').length := by
          simp; omega
        simp only [hrec, e1, run]
        rfl

/-- The byte length of characters. -/
def ulen (cs : List Char) : Nat := (encChars cs).length

/-- A Lean scan result as the Rust scan reports it: the rule plus one and the byte end, or
    `init` for no match. -/
def toR (i0 : Nat) (cs0 : List Char) (init : Nat × Nat) : Option (Nat × Nat) → Nat × Nat
  | none => init
  | some (r, n) => (r + 1, i0 + ulen (cs0.take n))

theorem src_at (src : List Nat) (i : Nat) (cs : List Char) (hi : i ≤ src.length)
    (h : src.drop i = encChars cs) :
    i + (encChars cs).length = src.length ∧
      ∀ k (hk : k < (encChars cs).length), src[i + k]? = some (encChars cs)[k] := by
  constructor
  · have := congrArg List.length h
    simp at this
    omega
  · intro k hk
    have : (src.drop i)[k]? = (encChars cs)[k]? := by rw [h]
    rw [List.getElem?_drop, List.getElem?_eq_getElem hk] at this
    exact this

/-- **The Rust scan walks the Lean DFA.** From a byte position `i` where the rest of the source
    is the bytes of `cs`, in the state of the Lean state `sid`, with the match so far `best`
    (counted in characters from `cs0`, of which `cs` is the rest after `k`), the Rust scan
    reports what `DFA.scan.go` reports. -/
theorem lscan_sim (d : LexDFA) (dfa : DFA) (φ : Nat → Nat) (h : LexSim d dfa φ)
    (src : List Nat) (i0 : Nat) (cs0 : List Char) (init : Nat × Nat) :
    ∀ (cs : List Char) (sid k i : Nat) (best : Option (Nat × Nat)),
      sid < dfa.states.size → cs0.drop k = cs → k ≤ cs0.length → i = i0 + ulen (cs0.take k) →
      i ≤ src.length → src.drop i = encChars cs →
      lscan d src (src.length + 1 - i) (φ sid) i (toR i0 cs0 init best).1
          (toR i0 cs0 init best).2 =
        toR i0 cs0 init (DFA.scan.go dfa sid cs k best) := by
  intro cs
  induction cs with
  | nil =>
    intro sid k i best hsid hcs hk hi hile hsrc
    obtain ⟨hlen, _⟩ := src_at src i [] hile hsrc
    simp at hlen
    rw [lscan_end d src _ i _ _ (by omega) (by omega), h.accept sid hsid]
    cases ha : (dfa.states[sid]!).accept <;> simp [DFA.scan.go, ha, toR, hi]
  | cons c rest ih =>
    intro sid k i best hsid hcs hk hi hile hsrc
    obtain ⟨hlen, hat⟩ := src_at src i (c :: rest) hile hsrc
    obtain ⟨hmid, hrun⟩ := h.step sid hsid c
    have hk' : k < cs0.length := by
      rcases Nat.lt_or_ge k cs0.length with h' | h'
      · exact h'
      · have : cs0.drop k = [] := List.drop_eq_nil_of_le h'
        rw [this] at hcs; cases hcs
    have hblock := lscan_block d src h.dead (enc c) (φ sid) i (toR i0 cs0 init best).1
      (toR i0 cs0 init best).2 (enc_ne_nil c) (h.ne0 sid hsid) hmid
      (by simp at hlen; omega)
      (fun j hj => by
        have := hat j (by simp; omega)
        simpa [List.getElem_append_left hj] using this)
    rw [hblock, hrun]
    -- the match after recording the state `sid`
    have hrec : lrecord d (φ sid) i (toR i0 cs0 init best).1 (toR i0 cs0 init best).2 =
        toR i0 cs0 init (match (dfa.states[sid]!).accept with
          | some rule => some (rule, k)
          | none => best) := by
      rw [h.accept sid hsid]
      cases (dfa.states[sid]!).accept with
      | none => rfl
      | some r => simp [toR, hi]
    have hgo : DFA.scan.go dfa sid (c :: rest) k best =
        match (dfa.states[sid]!).stepChar c with
        | some next => DFA.scan.go dfa next rest (k + 1)
            (match (dfa.states[sid]!).accept with
              | some rule => some (rule, k)
              | none => best)
        | none => (match (dfa.states[sid]!).accept with
              | some rule => some (rule, k)
              | none => best) := by
      simp only [DFA.scan.go]; rfl
    rw [hgo]
    cases hst : (dfa.states[sid]!).stepChar c with
    | none =>
      simp only [↓reduceIte]
      exact hrec
    | some t =>
      have ht := h.target sid hsid c t hst
      simp only [h.ne0 t ht, ↓reduceIte]
      rw [hrec]
      have htake : cs0.take (k + 1) = cs0.take k ++ [c] := by
        rw [List.take_add_one, ← List.head?_drop, hcs]; rfl
      apply ih t (k + 1) (i + (enc c).length) _ ht
      · rw [← List.drop_drop, hcs]; rfl
      · omega
      · rw [htake, hi]; simp [ulen, encChars_append]; omega
      · simp at hlen; omega
      · rw [← List.drop_drop, hsrc]; simp

/-- **The Rust scan is `DFA.scan`.** From byte `i0`, where the rest of the source is the bytes
    of `cs0`: no match is `(0, i0)`, and a match of rule `r` over `n` characters is
    `(r + 1, i0 + ulen (cs0.take n))`. -/
theorem lscanFrom_sim (d : LexDFA) (dfa : DFA) (φ : Nat → Nat) (h : LexSim d dfa φ)
    (src : List Nat) (i0 : Nat) (cs0 : List Char) (hi0 : i0 ≤ src.length)
    (hsrc : src.drop i0 = encChars cs0) :
    lscanFrom d src i0 = toR i0 cs0 (0, i0) (DFA.scan dfa cs0) := by
  have := lscan_sim d dfa φ h src i0 cs0 (0, i0) cs0 0 0 i0 none h.size (by simp) (by simp)
    (by simp [ulen]) hi0 hsrc
  unfold lscanFrom DFA.scan
  rw [← h.start]
  exact this

/-! ### The tokenizers -/

/-- A match of the rule-level run: the rule, the byte span, the matched characters. -/
structure RTok where
  rule : Nat
  start : Nat
  stop : Nat
  text : List Char

/-- The longest-match run of `dfa` over `cs` from byte `i`, with every match (skipped or
    not): how it ends (`none`, or the byte position of the error) and the matches. This is
    the loop that both lexers run; `llex_rules` and `tokenize_rules` say how each one reports
    it. -/
def ruleRun (dfa : DFA) : Nat → List Char → Nat → Option Nat × List RTok
  | 0, _, i => (some i, [])
  | _ + 1, [], _ => (none, [])
  | f + 1, c :: cs, i =>
    match DFA.scan dfa (c :: cs) with
    | some (r, n) =>
      if n = 0 then (some i, [])
      else
        let e := i + ulen ((c :: cs).take n)
        let rest := ruleRun dfa f ((c :: cs).drop n) e
        (rest.1, ⟨r, i, e, (c :: cs).take n⟩ :: rest.2)
    | none => (some i, [])

/-- The token of the Rust lexer for a match, unless its rule is skipped. -/
def toLTok (t : LexTables) (m : RTok) : Option LTok :=
  if t.ruleTerm m.rule ≠ termSkip then some ⟨m.rule, t.ruleTerm m.rule, m.start, m.stop⟩
  else none

/-- How the Rust lexer reports a run that ends with `stop` after the matches `rs`. -/
def rustOut (t : LexTables) (len : Nat) (acc : List LTok) :
    Option Nat × List RTok → LStop × List LTok
  | (none, rs) => (.ok, acc ++ rs.filterMap (toLTok t) ++ [⟨ruleEof, t.eof, len, len⟩])
  | (some p, rs) => (.noMatch p, acc ++ rs.filterMap (toLTok t))

theorem ulen_take_pos (c : Char) (cs : List Char) (n : Nat) (hn : n ≠ 0) :
    0 < ulen ((c :: cs).take n) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [List.take_succ_cons, ulen, encChars_cons, List.length_append]
  have : (enc c).length ≠ 0 := by
    intro h; exact enc_ne_nil c (List.eq_nil_of_length_eq_zero h)
  omega

/-- **The Rust lexer loop is the rule-level run.** -/
theorem llex_rules (t : LexTables) (dfa : DFA) (φ : Nat → Nat) (h : LexSim t.dfa dfa φ)
    (src : List Nat) :
    ∀ (f : Nat) (cs : List Char) (i : Nat) (acc : List LTok), cs.length + 1 ≤ f →
      i ≤ src.length → src.drop i = encChars cs →
      llexGo t src (src.length + 1 - i) i acc = rustOut t src.length acc (ruleRun dfa f cs i) := by
  intro f
  induction f with
  | zero => intro cs i acc hf; omega
  | succ f ih =>
    intro cs i acc hf hi hsrc
    cases cs with
    | nil =>
      have : i = src.length := by
        have := congrArg List.length hsrc; simp at this; omega
      rw [llexGo_end t src i acc this]
      simp [ruleRun, rustOut]
    | cons c cs' =>
      have hlt : i < src.length := by
        have := congrArg List.length hsrc
        simp at this
        have := enc_ne_nil c
        have : (enc c).length ≠ 0 := fun h' => this (List.eq_nil_of_length_eq_zero h')
        omega
      rw [llexGo_step t src i acc hlt, lscanFrom_sim t.dfa dfa φ h src i (c :: cs') hi hsrc]
      simp only [ruleRun]
      cases hsc : DFA.scan dfa (c :: cs') with
      | none => simp [toR, rustOut]
      | some p =>
        obtain ⟨r, n⟩ := p
        by_cases hn : n = 0
        · subst hn; simp [toR, rustOut, ulen]
        · have hpos := ulen_take_pos c cs' n hn
          have hnle := Lexer.scan_len_le dfa (c :: cs') r n hsc
          simp only [toR, hn, ↓reduceIte, Nat.add_sub_cancel]
          simp only [show ¬ (r + 1 = 0 ∨ i + ulen (List.take n (c :: cs')) ≤ i) by omega,
            ↓reduceIte]
          have hsplit : encChars (c :: cs') =
              encChars ((c :: cs').take n) ++ encChars ((c :: cs').drop n) := by
            rw [← encChars_append, List.take_append_drop]
          have hsrc' : src.drop (i + ulen ((c :: cs').take n)) = encChars ((c :: cs').drop n) := by
            rw [← List.drop_drop, hsrc, hsplit, ulen, List.drop_left]
          have hle : i + ulen ((c :: cs').take n) ≤ src.length := by
            have := congrArg List.length hsrc
            rw [hsplit] at this
            simp [ulen] at this ⊢; omega
          have hlen' : ((c :: cs').drop n).length + 1 ≤ f := by
            simp at hf ⊢; omega
          rw [ih _ _ _ hlen' hle hsrc']
          cases hr : ruleRun dfa f ((c :: cs').drop n) (i + ulen ((c :: cs').take n)) with
          | mk st rs =>
            cases st <;> by_cases ht : t.ruleTerm r = termSkip <;>
              simp [rustOut, toLTok, ht, List.filterMap_cons]

variable {Tok : Type}

/-- The token of the Lean lexer for a match: what the rule's action emits on its text. -/
def emitOf (c : Compiled Tok) (m : Nat) (r : RTok) : Option Tok :=
  (((c.acts.getD m #[]).getD r.rule (fun _ => {})) (String.ofList r.text)).emit

/-- How `tokenizeAuxDFA` reports a run. -/
def LeanOut (c : Compiled Tok) (m : Nat) (acc : List Tok) :
    Option Nat × List RTok → Except LexError (List Tok) → Prop
  | (none, rs), res => res = .ok (acc.reverse ++ rs.filterMap (emitOf c m) ++ c.eofToken.toList)
  | (some _, _), res => ∃ e, res = .error e

/-- **The Lean lexer loop is the rule-level run**, in one mode whose actions stay in it. -/
theorem tokenize_rules (c : Compiled Tok) (m : Nat)
    (hstay : ∀ (s : String) (rule : Nat),
      (((c.acts.getD m #[]).getD rule (fun _ => {})) s).trans = Trans.stay) :
    ∀ (f : Nat) (cs : List Char) (pos i : Nat) (acc : List Tok),
      LeanOut c m acc (ruleRun (c.dfas.getD m default) f cs i)
        (tokenizeAuxDFA c f cs pos [m] acc) := by
  intro f
  induction f with
  | zero => intro cs pos i acc; exact ⟨_, rfl⟩
  | succ f ih =>
    intro cs pos i acc
    cases cs with
    | nil =>
      simp only [ruleRun, LeanOut, tokenizeAuxDFA]
      cases c.eofToken <;> simp
    | cons ch cs' =>
      simp only [ruleRun, tokenizeAuxDFA, List.headD_cons]
      cases hsc : DFA.scan (c.dfas.getD m default) (ch :: cs') with
      | none => exact ⟨_, rfl⟩
      | some p =>
        obtain ⟨r, n⟩ := p
        by_cases hn : n = 0
        · simp only [hn, ↓reduceIte]; exact ⟨_, rfl⟩
        · simp only [hn, ↓reduceIte, hstay]
          have := ih ((ch :: cs').drop n) (pos + n)
            (i + ulen ((ch :: cs').take n))
            (match (((c.acts.getD m #[]).getD r (fun _ => {}))
                (String.ofList ((ch :: cs').take n))).emit with
              | some tok => tok :: acc | none => acc)
          cases hr : ruleRun (c.dfas.getD m default) f ((ch :: cs').drop n)
              (i + ulen ((ch :: cs').take n)) with
          | mk st rs =>
            rw [hr] at this
            cases st with
            | some e => exact this
            | none =>
              simp only [LeanOut] at this ⊢
              refine this.trans ?_
              cases he : (((c.acts.getD m #[]).getD r (fun _ => {}))
                  (String.ofList ((ch :: cs').take n))).emit with
              | none =>
                have he' : emitOf c m ⟨r, i, i + ulen ((ch :: cs').take n), (ch :: cs').take n⟩ =
                    none := he
                simp [List.filterMap_cons, he']
              | some tok =>
                have he' : emitOf c m ⟨r, i, i + ulen ((ch :: cs').take n), (ch :: cs').take n⟩ =
                    some tok := he
                simp [List.filterMap_cons, he']

/-! ### The two reports of a run, token by token -/

theorem scan_go_rule (dfa : DFA) :
    ∀ (cs : List Char) (sid k : Nat) (best : Option (Nat × Nat)) (r n : Nat),
      (∀ r' n', best = some (r', n') → ∃ s : Nat, (dfa.states[s]!).accept = some r') →
      DFA.scan.go dfa sid cs k best = some (r, n) → ∃ s : Nat, (dfa.states[s]!).accept = some r := by
  intro cs
  induction cs with
  | nil =>
    intro sid k best r n hb h
    simp only [DFA.scan.go] at h
    cases ha : (dfa.states[sid]!).accept with
    | none => rw [ha] at h; exact hb r n h
    | some r' => rw [ha] at h; simp at h; exact ⟨sid, by rw [ha, h.1]⟩
  | cons c cs ih =>
    intro sid k best r n hb h
    have hb' : ∀ r' n', (match (dfa.states[sid]!).accept with
        | some rule => some (rule, k)
        | none => best) = some (r', n') → ∃ s : Nat, (dfa.states[s]!).accept = some r' := by
      intro r' n' h'
      cases ha : (dfa.states[sid]!).accept with
      | none => rw [ha] at h'; exact hb r' n' h'
      | some x => rw [ha] at h'; simp at h'; exact ⟨sid, by rw [ha, h'.1]⟩
    simp only [DFA.scan.go] at h
    split at h
    · exact ih _ _ _ r n hb' h
    · exact hb' r n h

/-- A rule that `DFA.scan` reports is the rule of an accepting state. -/
theorem scan_rule (dfa : DFA) (cs : List Char) (r n : Nat) (h : DFA.scan dfa cs = some (r, n)) :
    ∃ s : Nat, (dfa.states[s]!).accept = some r :=
  scan_go_rule dfa cs 0 0 none r n (by intro r' n' h; cases h) h

/-- Every match of the run is of the rule of an accepting state. -/
theorem ruleRun_rule (dfa : DFA) :
    ∀ (f : Nat) (cs : List Char) (i : Nat) (m : RTok), m ∈ (ruleRun dfa f cs i).2 →
      ∃ s : Nat, (dfa.states[s]!).accept = some m.rule := by
  intro f
  induction f with
  | zero => intro cs i m h; simp [ruleRun] at h
  | succ f ih =>
    intro cs i m h
    cases cs with
    | nil => simp [ruleRun] at h
    | cons c cs =>
      simp only [ruleRun] at h
      split at h
      · rename_i r n hsc
        split at h
        · simp at h
        · rcases List.mem_cons.mp h with rfl | h
          · exact scan_rule dfa _ _ _ hsc
          · exact ih _ _ m h
      · simp at h

/-- Two lists whose elements are related one by one. -/
inductive Rel2 {β γ : Type} (P : β → γ → Prop) : List β → List γ → Prop where
  | nil : Rel2 P [] []
  | cons {b c bs cs} : P b c → Rel2 P bs cs → Rel2 P (b :: bs) (c :: cs)

theorem filterMap_rel2 {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (P : β → γ → Prop) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).isSome = (g x).isSome ∧
        ∀ b c, f x = some b → g x = some c → P b c) →
      Rel2 P (xs.filterMap f) (xs.filterMap g) := by
  intro xs
  induction xs with
  | nil => intro _; exact Rel2.nil
  | cons x xs ih =>
    intro h
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filterMap_cons]
    cases hf : f x with
    | none =>
      cases hg : g x with
      | none => exact ht
      | some c => rw [hf, hg] at hx; simp at hx
    | some b =>
      cases hg : g x with
      | none => rw [hf, hg] at hx; simp at hx
      | some c => exact Rel2.cons (hx.2 b c hf hg) ht

end Spec
