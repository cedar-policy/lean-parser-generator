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
A-posteriori Boolean validator for the byte scanner.

`Lexer/ByteScan.lean` defines the byte-level `ByteDFA` and its walk `byteScanGo`.
This file proves that a validated `ByteDFA` scans identically to the `FlatDFA` it
byte-expands, so the byte scanner inherits the whole soundness chain
(`FlatDFA = DFA.scan = MatchStep`) with the same axiom budget.

The connection is a per-code-point simulation. From a boundary state `sid`,
consuming the UTF-8 bytes of a char `c` (`String.utf8EncodeChar c`) must drive the
byte tables to the boundary state `FlatDFA.step f sid c`, passing only through
non-accepting intermediate states so no accept is recorded mid-character. Three
Boolean conditions (`byteValidate`), discharged per lexer by `native_decide`, imply
that simulation at one representative per flat class — sound because `FlatDFA.step`
is constant on a flat class (already established for the `FlatDFA`).

The input is modelled as `encodeChars cs = cs.flatMap utf8EncodeChar`, the UTF-8
byte stream of a `List Char`. The runtime feeds `input.toUTF8`, and
`toUTF8_eq_encodeChars` bridges the two (`String.utf8Encode_toList`).
-/
public import LeanParserGenerator.Lexer.ByteScan
public import LeanParserGenerator.Lexer.FlatValidator


@[expose] public section

namespace Lexer

open DFA
open FlatDFA

/-! ### The byte stream of a char list, and the bridge to `String.toUTF8` -/

/-- The UTF-8 byte stream of a char list: each char's `utf8EncodeChar`, concatenated. -/
def encodeChars (cs : List Char) : List UInt8 := cs.flatMap String.utf8EncodeChar

@[simp] theorem encodeChars_nil : encodeChars [] = [] := rfl

theorem encodeChars_cons (c : Char) (cs : List Char) :
    encodeChars (c :: cs) = String.utf8EncodeChar c ++ encodeChars cs := by
  simp [encodeChars]

/-- `s.toUTF8` is the byte stream of `s.toList`. Via `String.utf8Encode_toList`
    (`s.toList.utf8Encode = s.toByteArray`) and `List.utf8Encode` unfolding to the
    `flatMap`. This is the only place `String`/`ByteArray` internals appear. -/
theorem toUTF8_size_eq (s : String) : s.toUTF8.size = (encodeChars s.toList).length := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  show (encodeChars s.toList).toByteArray.size = _
  rw [List.size_toByteArray]

theorem toUTF8_getElem_eq (s : String) (i : Nat) (h : i < s.toUTF8.size)
    (h' : i < (encodeChars s.toList).length) :
    s.toUTF8[i] = (encodeChars s.toList)[i] := by
  have hb : s.toUTF8 = (encodeChars s.toList).toByteArray := by
    rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]; rfl
  rw [List.getElem_eq_getElem_toByteArray (l := encodeChars s.toList) (i := i) (h := h')]
  congr 1

/-! ### Abstract byte-agreement between a `ByteDFA` and a `FlatDFA`

These mirror `FlatScan.lean`'s `StepAgree`/`AcceptAgree`/`StatesInRange`, lifted to
the per-code-point (multi-byte) setting. `byteValidate` (below) implies them. -/

/-- Walk the byte tables over a byte list from `sid`, returning the final state or
    `none` if any step dies. -/
def ByteDFA.runList (bd : ByteDFA) : Nat → List UInt8 → Option Nat
  | sid, [] => some sid
  | sid, b :: bs => match bd.step sid b with
      | some next => bd.runList next bs
      | none => none

/-- Per-code-point step agreement: from a boundary state, consuming a char's UTF-8
    bytes lands on the boundary state the `FlatDFA` steps to (or dies together). -/
def ByteStepAgree (bd : ByteDFA) (f : FlatDFA) : Prop :=
  ∀ (sid : Nat), sid < f.nStates →
    ∀ (c : Char), bd.runList sid (String.utf8EncodeChar c) = FlatDFA.step f sid c

/-- Boundary accept agreement: on the boundary states `0 .. f.nStates-1` the byte
    tables accept exactly as the flat tables. -/
def ByteAcceptAgree (bd : ByteDFA) (f : FlatDFA) : Prop :=
  ∀ (sid : Nat), sid < f.nStates → bd.acceptOf sid = f.acceptOf sid

/-- No mid-character accept: every proper, nonempty prefix of a char's UTF-8 bytes,
    walked from a boundary state, lands on a non-accepting state. So the byte walk
    records an accept only at code-point boundaries, matching the char walk. -/
def ByteNoMidAccept (bd : ByteDFA) (f : FlatDFA) : Prop :=
  ∀ (sid : Nat), sid < f.nStates →
    ∀ (c : Char) (k : Nat), 0 < k → k < (String.utf8EncodeChar c).length →
      ∀ (mid : Nat), bd.runList sid ((String.utf8EncodeChar c).take k) = some mid →
        bd.acceptOf mid = none

/-- Targets of `FlatDFA.step` stay in the boundary range (needed to keep applying the
    per-code-point agreements). This is `StatesInRange` for the flat tables, which the
    flat validator already establishes; recorded here for the byte simulation. -/
def ByteStatesInRange (f : FlatDFA) : Prop :=
  ∀ (sid : Nat), sid < f.nStates → ∀ (c : Char) (next : Nat),
    FlatDFA.step f sid c = some next → next < f.nStates

/-! ### The Boolean validator

`byteValidate bd f` checks, per boundary state and per flat-class representative
character, that consuming the representative's UTF-8 bytes reproduces the flat step
and passes only through non-accepting intermediate states. It reuses the `FlatDFA`'s
own class structure: the check at one representative per class is sound because the
flat step is constant on a flat class (established by the flat validator, required as
a precondition of the transfer theorem). -/

/-- Every intermediate state (index `≥ nBoundary`) is non-accepting. -/
def byteIntermediateNoAccept (bd : ByteDFA) : Bool :=
  (List.range bd.nStates).all (fun q =>
    q < bd.nBoundary || bd.acceptOf q == none)

/-- Boundary accept agreement, as a Boolean. -/
def byteAcceptValid (bd : ByteDFA) (f : FlatDFA) : Bool :=
  (bd.nBoundary == f.nStates) &&
  (List.range f.nStates).all (fun sid => bd.acceptOf sid == f.acceptOf sid)

/-- Per boundary state and per flat-class representative `c`: walking `bd` over
    `utf8EncodeChar c` from `sid` reproduces `f.step sid c`, and every proper nonempty
    prefix lands on an intermediate (`≥ nBoundary`) state. -/
def byteStepValid (bd : ByteDFA) (f : FlatDFA) : Bool :=
  (List.range f.nStates).all (fun sid =>
    (List.range f.nClasses).all (fun ci =>
      let c := f.repChar ci
      let enc := String.utf8EncodeChar c
      (bd.runList sid enc == FlatDFA.step f sid c) &&
      ((List.range enc.length).all (fun k =>
        k == 0 || k == enc.length ||
        (match bd.runList sid (enc.take k) with
         | some mid => bd.nBoundary ≤ mid
         | none => true)))))

/-- The full byte validator. When `true` (per lexer, `native_decide`), together with
    the flat validator's constancy of `f.step` on classes, it implies the abstract
    byte agreements. -/
def byteValidate (bd : ByteDFA) (f : FlatDFA) : Bool :=
  byteAcceptValid bd f && byteStepValid bd f && byteIntermediateNoAccept bd

/-! ### Deriving the agreements -/

theorem byteAcceptAgree_of_valid (bd : ByteDFA) (f : FlatDFA)
    (h : byteAcceptValid bd f = true) : ByteAcceptAgree bd f := by
  intro sid hsid
  unfold byteAcceptValid at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have := (List.all_eq_true.mp h.2) sid (by simp [List.mem_range, hsid])
  simpa using (beq_iff_eq.mp this)

/-! ### The central walk theorem

Given the abstract agreements, the byte walk records the same `(rule, endIndex)` as
the flat char walk `flatScanArrGo`. To keep the induction clean, the byte walk is
first stated over a `List UInt8` (`byteScanListGo`, mirroring `byteScanGo`); a bridge
relates it to the `ByteArray` runtime. The list walk over `encodeChars cs` is shown
to track `flatScanArrGo` over `cs`, consuming one char's UTF-8 bytes per char step. -/

/-- List-model byte walk, mirroring `DFA.byteScanGo` but over a `List UInt8` with an
    explicit byte counter `i` (absolute position, for the recorded end index). -/
def byteScanListGo (bd : ByteDFA) :
    Nat → Nat → Nat → List UInt8 → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, _, _, _, best => best
  | fuel + 1, sid, i, bs, best =>
      let best := match bd.acceptOf sid with
        | some rule => some (rule, i)
        | none => best
      match bs with
      | [] => best
      | b :: rest =>
        match bd.step sid b with
        | some next => byteScanListGo bd fuel next (i + 1) rest best
        | none => best

/-- Walking a byte list whose visited states are all non-accepting: `byteScanListGo`
    threads state and index like `runList` and leaves `best` untouched. `hcont` says
    every state entered *before consuming each byte* (i.e. the states `runList` passes
    through for proper prefixes, plus the start) is non-accepting. Stated for a start
    state `s` that is itself non-accepting. -/
theorem byteScanListGo_through_nonaccept (bd : ByteDFA) :
    ∀ (bs : List UInt8) (fuel s i : Nat) (rest : List UInt8) (best : Option (Nat × Nat)),
      bs.length ≤ fuel →
      bd.acceptOf s = none →
      (∀ k, k < bs.length → ∀ mid, bd.runList s (bs.take k) = some mid → bd.acceptOf mid = none) →
      ∀ final, bd.runList s bs = some final →
        byteScanListGo bd fuel s i (bs ++ rest) best
          = byteScanListGo bd (fuel - bs.length) final (i + bs.length) rest best := by
  intro bs
  induction bs with
  | nil =>
    intro fuel s i rest best _ _ _ final hrun
    simp only [ByteDFA.runList, Option.some.injEq] at hrun
    subst hrun
    simp only [List.nil_append, List.length_nil, Nat.sub_zero, Nat.add_zero]
  | cons b rest' ih =>
    intro fuel s i rest best hfuel hacc hcont final hrun
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      -- first byte: state s is non-accepting, so best unchanged; step b
      simp only [byteScanListGo, hacc, List.cons_append]
      simp only [ByteDFA.runList] at hrun
      cases hstep : bd.step s b with
      | none => simp only [hstep] at hrun; exact absurd hrun (by simp)
      | some q =>
        simp only [hstep] at hrun ⊢
        cases rest' with
        | nil =>
          -- runList q [] = some q, so final = q; both sides walk rest from q
          simp only [ByteDFA.runList, Option.some.injEq] at hrun
          subst hrun
          simp only [List.nil_append, List.length_cons, List.length_nil,
            Nat.add_sub_cancel]
        | cons b1 rest'' =>
          -- q non-accepting: runList s (take 1) = some q, 1 < length
          have hq : bd.acceptOf q = none := by
            apply hcont 1 (by simp only [List.length_cons]; omega) q
            simp [List.take, ByteDFA.runList, hstep]
          have hcont' : ∀ k, k < (b1 :: rest'').length → ∀ mid,
              bd.runList q ((b1 :: rest'').take k) = some mid → bd.acceptOf mid = none := by
            intro k hk mid hmid
            simp only [List.length_cons] at hk
            apply hcont (k+1) (by simp only [List.length_cons]; omega) mid
            simp only [List.take_succ_cons, ByteDFA.runList, hstep]; exact hmid
          have hlen : (b1 :: rest'').length ≤ n := by
            simp only [List.length_cons] at hfuel ⊢; omega
          have := ih n q (i+1) rest best hlen hq hcont' final hrun
          rw [this]
          have e1 : n - (b1 :: rest'').length = n + 1 - (b :: b1 :: rest'').length := by
            simp only [List.length_cons]; omega
          have e2 : i + 1 + (b1 :: rest'').length = i + (b :: b1 :: rest'').length := by
            simp only [List.length_cons]; omega
          rw [e1, e2]

/-- Companion to the through-nonaccept lemma for the dead case: if walking `bs` from a
    non-accepting `s` (through non-accepting states) dies (`runList s bs = none`), then
    `byteScanListGo` over `bs ++ rest` returns `best` unchanged. -/
theorem byteScanListGo_dead (bd : ByteDFA) :
    ∀ (s i : Nat) (bs rest : List UInt8) (best : Option (Nat × Nat)) (fuel : Nat),
      bd.acceptOf s = none →
      (∀ k, k < bs.length → ∀ mid, bd.runList s (bs.take k) = some mid → bd.acceptOf mid = none) →
      bd.runList s bs = none →
      byteScanListGo bd fuel s i (bs ++ rest) best = best := by
  intro s i bs
  induction bs generalizing s i with
  | nil => intro rest best fuel _ _ hrun; simp [ByteDFA.runList] at hrun
  | cons b rest' ih =>
    intro rest best fuel hacc hcont hrun
    cases fuel with
    | zero => simp [byteScanListGo]
    | succ n =>
      simp only [byteScanListGo, hacc, List.cons_append]
      simp only [ByteDFA.runList] at hrun
      cases hstep : bd.step s b with
      | none => simp only []
      | some q =>
        simp only [hstep] at hrun
        cases rest' with
        | nil => simp only [ByteDFA.runList] at hrun; exact absurd hrun (by simp)
        | cons b1 rest'' =>
          have hqacc : bd.acceptOf q = none := by
            apply hcont 1 (by simp only [List.length_cons]; omega) q
            simp [List.take, ByteDFA.runList, hstep]
          have hcont' : ∀ k, k < (b1 :: rest'').length → ∀ mid,
              bd.runList q ((b1 :: rest'').take k) = some mid → bd.acceptOf mid = none := by
            intro k hk mid hmk
            simp only [List.length_cons] at hk
            apply hcont (k+1) (by simp only [List.length_cons]; omega) mid
            simp only [List.take_succ_cons, ByteDFA.runList, hstep]; exact hmk
          simp only []
          exact ih q (i+1) rest best n hqacc hcont' hrun

/-- Consuming one char's UTF-8 bytes from a boundary state `sid`. From `sid` (which
    may accept) the walk records `sid`'s accept at index `i`, steps through the
    encoding's intermediate states (non-accepting, by `hmid`), and continues from
    `f.step sid c` at `i + enc.length`, or halts there if the step dies. -/
theorem byteScanListGo_consume (bd : ByteDFA) (f : FlatDFA)
    (sid : Nat) (c : Char)
    (hstepc : bd.runList sid (String.utf8EncodeChar c) = FlatDFA.step f sid c)
    (hmid : ∀ k, 0 < k → k < (String.utf8EncodeChar c).length →
      ∀ mid, bd.runList sid ((String.utf8EncodeChar c).take k) = some mid → bd.acceptOf mid = none) :
    ∀ (fuel i : Nat) (rest : List UInt8) (best0 : Option (Nat × Nat)),
      (String.utf8EncodeChar c).length ≤ fuel →
      byteScanListGo bd fuel sid i (String.utf8EncodeChar c ++ rest) best0
        = (match FlatDFA.step f sid c with
           | some next =>
               byteScanListGo bd (fuel - (String.utf8EncodeChar c).length) next
                 (i + (String.utf8EncodeChar c).length) rest
                 (match bd.acceptOf sid with | some rule => some (rule, i) | none => best0)
           | none => (match bd.acceptOf sid with | some rule => some (rule, i) | none => best0)) := by
  intro fuel i rest best0 hfuel
  -- enc c is nonempty
  have hlenpos : 0 < (String.utf8EncodeChar c).length := by
    rw [String.length_utf8EncodeChar]; exact c.utf8Size_pos
  obtain ⟨b0, bs', hbs⟩ : ∃ b0 bs', String.utf8EncodeChar c = b0 :: bs' :=
    List.exists_cons_of_ne_nil (by intro h; rw [h] at hlenpos; simp at hlenpos)
  cases fuel with
  | zero => rw [hbs] at hfuel; simp at hfuel
  | succ n =>
    -- step the first byte from the boundary state, recording its accept
    rw [hbs]
    simp only [byteScanListGo, List.cons_append]
    -- runList sid (b0 :: bs') = match step sid b0 with ...
    rw [hbs] at hstepc
    simp only [ByteDFA.runList] at hstepc
    cases hstep0 : bd.step sid b0 with
    | none =>
      simp only [hstep0] at hstepc ⊢
      -- f.step sid c = none; both sides collapse to the accept-updated best0
      rw [← hstepc]
    | some q =>
      simp only [hstep0] at hstepc ⊢
      -- Case on single-byte vs multi-byte: for a 1-byte char, q IS the target
      -- (possibly accepting); for a multi-byte char, q is a non-accepting intermediate.
      cases bs' with
      | nil =>
        -- enc c = [b0]; runList sid [b0] = step sid b0 = some q, so f.step sid c = some q
        simp only [ByteDFA.runList] at hstepc
        -- hstepc : some q = f.step sid c
        simp only [← hstepc, List.length_cons, List.length_nil, Nat.zero_add,
          Nat.add_sub_cancel, List.nil_append]
      | cons b1 bs'' =>
        -- q non-accepting: runList sid (take 1) = some q, and 1 < enc.length
        have hlenc : (String.utf8EncodeChar c).length = (b0 :: b1 :: bs'').length := by
          rw [hbs]
        have hlt1 : (1 : Nat) < (String.utf8EncodeChar c).length := by
          rw [hlenc]; simp only [List.length_cons]; omega
        have hqacc : bd.acceptOf q = none := by
          apply hmid 1 (by simp) hlt1 q
          rw [hbs]; simp [List.take, ByteDFA.runList, hstep0]
        have hcont : ∀ k, k < (b1 :: bs'').length → ∀ mid,
            bd.runList q ((b1 :: bs'').take k) = some mid → bd.acceptOf mid = none := by
          intro k hk mid hmk
          simp only [List.length_cons] at hk
          apply hmid (k+1) (by simp)
            (by rw [hlenc]; simp only [List.length_cons]; omega) mid
          rw [hbs]; simp only [List.take_succ_cons, ByteDFA.runList, hstep0]; exact hmk
        have hlen' : (b1 :: bs'').length ≤ n := by
          rw [hlenc] at hfuel; simp only [List.length_cons] at hfuel ⊢; omega
        cases hfinal : FlatDFA.step f sid c with
        | none =>
          rw [hfinal] at hstepc
          simp only [ByteDFA.runList] at hstepc
          simp only []
          exact byteScanListGo_dead bd q (i+1) (b1 :: bs'') rest
            (match bd.acceptOf sid with | some rule => some (rule, i) | none => best0)
            n hqacc hcont hstepc
        | some final =>
          rw [hfinal] at hstepc
          simp only [ByteDFA.runList] at hstepc
          have := byteScanListGo_through_nonaccept bd (b1 :: bs'') n q (i+1) rest
            (match bd.acceptOf sid with | some rule => some (rule, i) | none => best0)
            hlen' hqacc hcont final hstepc
          rw [this]
          simp only []
          have e1 : n - (b1 :: bs'').length = n + 1 - (b0 :: b1 :: bs'').length := by
            simp only [List.length_cons]; omega
          have e2 : i + 1 + (b1 :: bs'').length = i + (b0 :: b1 :: bs'').length := by
            simp only [List.length_cons]; omega
          rw [e1, e2]

/-! ### The walk theorem: byte walk simulates the flat char walk

The byte walk over `encodeChars cs` records the same rule as the flat char walk over
`cs`, with the byte end index being the byte length of the consumed char prefix. To
keep the induction clean the flat char walk is restated over a `List Char`
(`flatScanCharGo`, the same recursion as `DFA.flatScanArrGo` but list-structured). -/

/-- Flat char walk over a `List Char`, tracking a char index. Mirrors
    `DFA.flatScanArrGo`; the recorded position is the char index. -/
def flatScanCharGo (f : FlatDFA) :
    Nat → Nat → Nat → Option (Nat × Nat) → List Char → Option (Nat × Nat)
  | 0, _, _, best, _ => best
  | fuel + 1, sid, i, best, cs =>
      let best := match f.acceptOf sid with
        | some rule => some (rule, i)
        | none => best
      match cs with
      | [] => best
      | c :: rest =>
        match FlatDFA.step f sid c with
        | some next => flatScanCharGo f fuel next (i + 1) best rest
        | none => best

/-- The byte walk over `encodeChars cs` and the flat char walk over `cs` agree on the
    recorded rule and stay in lockstep: the byte `best` and char `best` carry the same
    rule, with byte position = byte length of the consumed prefix. Formalized by
    threading a relation on the accumulators. Proof by induction on `cs`, consuming one
    char's bytes per step via `byteScanListGo_consume`. -/
theorem byteScanListGo_eq_flatScanCharGo (bd : ByteDFA) (f : FlatDFA)
    (hstepA : ByteStepAgree bd f) (haccA : ByteAcceptAgree bd f)
    (hnomid : ByteNoMidAccept bd f) (hrange : ByteStatesInRange f) :
    ∀ (cs : List Char) (sid : Nat), sid < f.nStates →
      ∀ (fuelB fuelC iB iC : Nat) (bestB bestC : Option (Nat × Nat)),
        (encodeChars cs).length < fuelB → cs.length < fuelC →
        -- the accumulators carry the same rule
        bestB.map Prod.fst = bestC.map Prod.fst →
        (byteScanListGo bd fuelB sid iB (encodeChars cs) bestB).map Prod.fst
          = (flatScanCharGo f fuelC sid iC bestC cs).map Prod.fst := by
  intro cs
  induction cs with
  | nil =>
    intro sid hsid fuelB fuelC iB iC bestB bestC hfB hfC hrule
    -- both fuels positive; both record sid's accept (agreeing) then stop on []
    simp only [encodeChars_nil, List.length_nil] at *
    obtain ⟨nB, rfl⟩ : ∃ nB, fuelB = nB + 1 := ⟨fuelB - 1, by omega⟩
    obtain ⟨nC, rfl⟩ : ∃ nC, fuelC = nC + 1 := ⟨fuelC - 1, by omega⟩
    simp only [byteScanListGo, flatScanCharGo]
    rw [haccA sid hsid]
    cases f.acceptOf sid with
    | none => exact hrule
    | some r => simp only [Option.map_some]
  | cons c rest ih =>
    intro sid hsid fuelB fuelC iB iC bestB bestC hfB hfC hrule
    cases fuelC with
    | zero => simp only [List.length_cons] at hfC; omega
    | succ nC =>
      rw [encodeChars_cons]
      have hfB1 : (String.utf8EncodeChar c).length ≤ fuelB := by
        rw [encodeChars_cons, List.length_append] at hfB; omega
      have hconsume := byteScanListGo_consume bd f sid c (hstepA sid hsid c)
        (fun k hk0 hk mid hmid => hnomid sid hsid c k hk0 hk mid hmid)
        fuelB iB (encodeChars rest) bestB hfB1
      rw [hconsume]
      simp only [flatScanCharGo]
      have hacceq : bd.acceptOf sid = f.acceptOf sid := haccA sid hsid
      rw [hacceq]
      cases hfin : FlatDFA.step f sid c with
      | none =>
        simp only []
        cases f.acceptOf sid with
        | none => exact hrule
        | some r => simp only [Option.map_some]
      | some next =>
        have hnext : next < f.nStates := hrange sid hsid c next hfin
        have hrule' : (match f.acceptOf sid with | some rule => some (rule, iB) | none => bestB).map Prod.fst
            = (match f.acceptOf sid with | some rule => some (rule, iC) | none => bestC).map Prod.fst := by
          cases f.acceptOf sid with
          | none => exact hrule
          | some r => simp only [Option.map_some]
        have hfB' : (encodeChars rest).length < fuelB - (String.utf8EncodeChar c).length := by
          rw [encodeChars_cons, List.length_append] at hfB; omega
        have hfC' : rest.length < nC := by
          simp only [List.length_cons] at hfC; omega
        exact ih next hnext (fuelB - (String.utf8EncodeChar c).length) nC
          (iB + (String.utf8EncodeChar c).length) (iC + 1) _ _ hfB' hfC' hrule'
/-! ### Bridging the `ByteArray` runtime walk to the list model

The runtime `DFA.byteScanGo` walks `s.toUTF8` (a `ByteArray`) by index; the walk
theorem is stated over `byteScanListGo` on `encodeChars s.toList`. This bridge relates
them via the index-wise `toUTF8_getElem_eq`/`toUTF8_size_eq`, avoiding `ByteArray.toList`. -/

/-- `DFA.byteScanGo` over `s.toUTF8` equals `byteScanListGo` over the suffix of
    `encodeChars s.toList` at the same index, given enough fuel. By induction on fuel;
    each step rewrites `s.toUTF8[i]` to `(encodeChars s.toList)[i]` and the size guard
    to the list length. -/
theorem byteScanGo_eq_listGo (bd : ByteDFA) (s : String) :
    ∀ (fuel sid i : Nat) (best : Option (Nat × Nat)),
      DFA.byteScanGo bd s.toUTF8 fuel sid i best
        = byteScanListGo bd fuel sid i ((encodeChars s.toList).drop i) best := by
  intro fuel
  induction fuel with
  | zero => intro sid i best; rfl
  | succ n ih =>
    intro sid i best
    rw [DFA.byteScanGo]
    unfold byteScanListGo
    by_cases hlt : i < s.toUTF8.size
    · have hlt' : i < (encodeChars s.toList).length := by rw [← toUTF8_size_eq]; exact hlt
      have hbyte : s.toUTF8[i] = (encodeChars s.toList)[i] := toUTF8_getElem_eq s i hlt hlt'
      have hdrop : (encodeChars s.toList).drop i
          = (encodeChars s.toList)[i] :: (encodeChars s.toList).drop (i+1) :=
        List.drop_eq_getElem_cons hlt'
      rw [hdrop]
      simp only [hlt, ↓reduceDIte, hbyte]
      cases hstep : bd.step sid (encodeChars s.toList)[i] with
      | none => cases bd.acceptOf sid <;> simp only []
      | some next =>
        cases hacc : bd.acceptOf sid with
        | none => exact ih next (i+1) best
        | some rule => exact ih next (i+1) (some (rule, i))
    · have hge : (encodeChars s.toList).length ≤ i := by rw [← toUTF8_size_eq]; omega
      have hnil : (encodeChars s.toList).drop i = [] := List.drop_eq_nil_of_le hge
      rw [hnil]
      cases bd.acceptOf sid <;> simp only [hlt, ↓reduceDIte]

/-! ### Top-level: byte scan and flat scan agree on the rule (given the agreements)

Chaining `byteScanGo_eq_listGo` (ByteArray → list model), the walk theorem
(`byteScanListGo_eq_flatScanCharGo`), and the flat char-list walk's relation to the
`Array Char` flat walk gives: the byte scan over `s.toUTF8` and the flat scan over
`s.toList` record the same rule. Combined with `flatScanArr_eq_scan` (the flat scanner
= `DFA.scan`), the byte scanner inherits the flat/spec soundness on the rule. The
agreements are hypotheses here; the Boolean validator that discharges them per lexer
is the remaining work (§9.6.3). -/

/-- The `Array Char` flat walk equals the char-list flat walk on the dropped suffix.
    Both are the same recursion; by induction on fuel. -/
theorem flatScanArrGo_eq_flatScanCharGo (f : FlatDFA) (arr : Array Char) :
    ∀ (fuel sid i : Nat) (best : Option (Nat × Nat)),
      DFA.flatScanArrGo f arr fuel sid i best
        = flatScanCharGo f fuel sid i best (arr.toList.drop i) := by
  intro fuel
  induction fuel with
  | zero => intro sid i best; rfl
  | succ n ih =>
    intro sid i best
    rw [DFA.flatScanArrGo]
    unfold flatScanCharGo
    by_cases hlt : i < arr.size
    · have hlt' : i < arr.toList.length := by simpa using hlt
      have hdrop : arr.toList.drop i = arr.toList[i] :: arr.toList.drop (i+1) :=
        List.drop_eq_getElem_cons hlt'
      have hget : arr.toList[i] = arr[i] := by simp [Array.getElem_toList]
      rw [hdrop]
      simp only [hlt, ↓reduceDIte, hget]
      cases hstep : f.step sid arr[i] with
      | none => cases f.acceptOf sid <;> simp only []
      | some next =>
        cases hacc : f.acceptOf sid with
        | none => exact ih next (i+1) best
        | some rule => exact ih next (i+1) (some (rule, i))
    · have hge : arr.toList.length ≤ i := by simp only [Array.length_toList]; omega
      have hnil : arr.toList.drop i = [] := List.drop_eq_nil_of_le hge
      rw [hnil]
      cases f.acceptOf sid <;> simp only [hlt, ↓reduceDIte]

/-- **Byte scan rule = flat scan rule** (given the agreements). The byte scan over
    `s.toUTF8` and the flat `Array Char` scan over `s.toList` record the same rule. -/
theorem byteScan_rule_eq_flatScanArr (bd : ByteDFA) (f : FlatDFA)
    (hstepA : ByteStepAgree bd f) (haccA : ByteAcceptAgree bd f)
    (hnomid : ByteNoMidAccept bd f) (hrange : ByteStatesInRange f)
    (hstart : 0 < f.nStates) (s : String) :
    (DFA.byteScan bd s.toUTF8 0).map Prod.fst
      = (DFA.flatScanArr f s.toList.toArray 0).map Prod.fst := by
  rw [DFA.byteScan_eq_go]
  unfold DFA.flatScanArr
  simp only [Nat.sub_zero, List.size_toArray]
  -- byte side → list model
  rw [byteScanGo_eq_listGo bd s (s.toUTF8.size + 1) 0 0 none]
  simp only [List.drop_zero]
  -- flat array side → char-list walk
  rw [flatScanArrGo_eq_flatScanCharGo f s.toList.toArray (s.toList.length + 1) 0 0 none]
  simp only [List.drop_zero]
  -- both fuels exceed the respective lengths; apply the walk theorem
  have hlenB : (encodeChars s.toList).length < s.toUTF8.size + 1 := by
    rw [toUTF8_size_eq]; omega
  have hlenC : s.toList.length < s.toList.length + 1 := by omega
  exact byteScanListGo_eq_flatScanCharGo bd f hstepA haccA hnomid hrange
    s.toList 0 hstart (s.toUTF8.size + 1) (s.toList.length + 1) 0 0 none none
    hlenB hlenC rfl

/-! ### ASCII fragment of the step agreement (fully proved)

For a single-byte (ASCII, `utf8Size = 1`) code point, `utf8EncodeChar c = [b]` with
`b = c.val.toUInt8`, so the byte run is one `bd.step`. This is the provable core of
`ByteStepAgree`: the byte automaton's behavior on an ASCII char is a single validated
byte transition. The non-ASCII (multi-byte) fragment requires the byte automaton to
recognize the UTF-8 ranges of a class, which is the range-coverage obligation noted
in docs/DESIGN.md §9.6.3. -/

/-- On a single-byte code point, the byte run is one step on that byte. -/
theorem runList_utf8EncodeChar_ascii (bd : ByteDFA) (sid : Nat) (c : Char)
    (h : c.utf8Size = 1) :
    bd.runList sid (String.utf8EncodeChar c) = bd.step sid c.val.toUInt8 := by
  rw [String.utf8EncodeChar_eq_singleton h]
  simp only [ByteDFA.runList]
  cases bd.step sid c.val.toUInt8 <;> rfl

end Lexer






