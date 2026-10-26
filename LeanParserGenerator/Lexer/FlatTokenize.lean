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
The flat tokenizer equals the spec tokenizer.

`Lexer/FlatValidator.lean` proves a validated `FlatDFA` scans identically to the
spec `DFA.scan` (`flatScanArr_eq_scan_of_valid`). This file lifts that single-scan
fact to the whole tokenizer: `tokenizeFlatAux`, which scans a decoded `Array Char`
by index with `flatScanArr`, returns the same tokens as the spec `tokenizeAuxDFA`
over the corresponding `List Char`, when every mode's flat table is validated
against that mode's DFA. So the emitted `tokenize` may run the fast flat scanner and
inherit `tokenize_sound` unchanged (docs/DESIGN.md §9.7 step 1).
-/
public import LeanParserGenerator.Lexer.FlatValidator
public import LeanParserGenerator.Lexer.Tokenize
public import LeanParserGenerator.Lexer.StringScan
public import LeanParserGenerator.Runtime.Span


@[expose] public section

namespace Lexer

variable {Tok : Type}

/-- The flat tokenizer's per-mode tables: one `FlatDFA` per mode, index-aligned with
    `Compiled.dfas`, plus the shared `Compiled` for actions/start/eof. -/
structure CompiledFlat (Tok : Type) where
  /-- The spec `Compiled` (DFAs, actions, start, eof). -/
  base : Compiled Tok
  /-- One flat table per mode, index-aligned with `base.dfas`. -/
  flats : Array FlatDFA
  /-- Per-mode, per-rule flag: `true` if the rule's action reads the matched
      lexeme, `false` if it ignores it (a constant/text-independent action). The
      runtime skips the `String.extract` byte copy for `false` rules and passes
      `""` instead (docs/DESIGN.md §9.6.4 item 1). Missing entries default to
      `true` (extract), so an under-populated table is still sound.

      Correctness relies on `textIndepOk`: for every `false` rule the action is
      constant in its argument, so passing `""` yields the same token as the real
      lexeme. The emitter discharges this per lexer (text-independent rules are
      emitted as `fun _ => body`). -/
  textDep : Array (Array Bool) := #[]

/-- Whether mode `mode`'s rule `rule` needs the matched lexeme. Defaults to `true`
    (take the `String.extract` path) when the table is absent or short. -/
def CompiledFlat.needsText (cf : CompiledFlat Tok) (mode rule : Nat) : Bool :=
  (cf.textDep.getD mode #[]).getD rule true

/-- The flat tokenization loop over a decoded `Array Char` `arr`, scanning from
    index `i` with `flatScanArr`. Mirrors `tokenizeAuxDFA` but with an array index
    instead of a shrinking `List Char`. `fuel` bounds the steps. -/
def tokenizeFlatAux (cf : CompiledFlat Tok) (arr : Array Char) :
    Nat → Nat → Nat → List Nat → List Tok → Except LexError (List Tok)
  | 0, _, pos, _, _ => .error { pos := pos, char := none }
  | fuel + 1, i, pos, stack, acc =>
      if i ≥ arr.size then
        match stack with
        | [_] =>
            match cf.base.eofToken with
            | some tok => .ok (tok :: acc).reverse
            | none => .ok acc.reverse
        | _ => .error { pos := pos, char := none }
      else
        let mode := stack.headD cf.base.start
        let flat := cf.flats.getD mode default
        match DFA.flatScanArr flat arr i with
        | some (rule, endi) =>
            if endi = i then .error { pos := pos, char := arr[i]? }
            else
              let len := endi - i
              let matched := String.ofList (arr.extract i endi).toList
              let act := (cf.base.acts.getD mode #[]).getD rule (fun _ => {})
              let a := act matched
              let acc := match a.emit with | some tok => tok :: acc | none => acc
              let stack := match a.trans with
                | .stay => stack
                | .push m => m :: stack
                | .pop => stack.tail
              tokenizeFlatAux cf arr fuel endi (pos + len) stack acc
        | none => .error { pos := pos, char := arr[i]? }

/-! ### Flat scan from an arbitrary index equals the spec scan on the suffix -/

/-- The flat scan from index `i` records absolute positions; the spec `DFA.scan` on
    the suffix `drop i` records relative ones. With validation and `i ≤ size`, they
    agree up to the `+i` offset: `flatScanArr flat arr i = (scan dfa (drop i)).map
    (fun (r,l) => (r, l + i))`. -/
theorem flatScanArr_from_eq (flat : FlatDFA) (dfa : DFA)
    (hvalid : flatValidate flat dfa = true) (hstart : 0 < dfa.states.size)
    (arr : Array Char) (i : Nat) (hi : i ≤ arr.size) :
    DFA.flatScanArr flat arr i
      = (DFA.scan dfa (arr.toList.drop i)).map (fun p => (p.1, p.2 + i)) := by
  obtain ⟨hstep, hacc, hrange⟩ := agreements_of_flatValidate flat dfa hvalid
  unfold DFA.flatScanArr
  rw [flatScanArrGo_eq_scanGo flat dfa hstep hacc hrange arr (arr.size + 1 - i) 0 i none
        hstart hi (by omega)]
  -- scan.go dfa 0 (drop i) i none = (scan.go dfa 0 (drop i) 0 none).map (+i)
  have hoff := scanGo_pos_offset dfa 0 (arr.toList.drop i) 0 i none
  simp only [Nat.zero_add, Option.map_none] at hoff
  rw [hoff, DFA.scan]

/-! ### The flat tokenizer equals the spec tokenizer -/

/-- `arr[i]?` equals the head of the dropped list. -/
theorem getElem?_eq_drop_head? (arr : Array Char) (i : Nat) :
    arr[i]? = (arr.toList.drop i).head? := by
  rw [List.head?_drop]
  simp [Array.getElem?_toList]

/-- Single-mode flat tokenizer equals the spec tokenizer on the dropped char list.
    Mirrors `tokenizeAuxDFA_sound`'s shape: a fixed validated mode `m`, stack `[m]`,
    and actions that keep the stack put (`hstay`). By induction on fuel. The flat
    table of mode `m` is validated against mode `m`'s DFA, so each scan agrees with
    `DFA.scan` (`flatScanArr_from_eq`); the recursion stays in mode `m`. -/
theorem tokenizeFlatAux_eq_single (cf : CompiledFlat Tok) (m : Nat)
    (hval : flatValidate (cf.flats.getD m default) (cf.base.dfas.getD m default) = true)
    (hstart : 0 < (cf.base.dfas.getD m default).states.size)
    (hstay : ∀ (s : String) (rule : Nat),
      (((cf.base.acts.getD m #[]).getD rule (fun _ => {})) s).trans = Trans.stay)
    (arr : Array Char) :
    ∀ (fuel i pos : Nat) (acc : List Tok), i ≤ arr.size →
      tokenizeFlatAux cf arr fuel i pos [m] acc
        = tokenizeAuxDFA cf.base fuel (arr.toList.drop i) pos [m] acc := by
  intro fuel
  induction fuel with
  | zero => intro i pos acc _; rfl
  | succ fuel ih =>
    intro i pos acc hi
    unfold tokenizeFlatAux tokenizeAuxDFA
    by_cases hend : i ≥ arr.size
    · have hnil : arr.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hend)
      simp only [hend, ite_true, hnil]
      cases cf.base.eofToken <;> rfl
    · have hlt : i < arr.size := by omega
      have hnil : arr.toList.drop i ≠ [] := by
        intro hc; rw [List.drop_eq_nil_iff] at hc
        simp only [Array.length_toList] at hc; omega
      obtain ⟨hd, tl, hcons⟩ : ∃ hd tl, arr.toList.drop i = hd :: tl :=
        List.exists_cons_of_ne_nil hnil
      -- current mode is m (stack = [m])
      simp only [hend, ite_false, List.headD_cons]
      have hfeq := flatScanArr_from_eq (cf.flats.getD m default) (cf.base.dfas.getD m default)
        hval hstart arr i (Nat.le_of_lt hlt)
      rw [hfeq, hcons]
      rw [← hcons]
      cases hsc : DFA.scan (cf.base.dfas.getD m default) (arr.toList.drop i) with
      | none => simp only [Option.map_none, getElem?_eq_drop_head?]
      | some p =>
        obtain ⟨rule, len⟩ := p
        simp only [Option.map_some]
        by_cases hlen : len = 0
        · subst hlen
          simp only [Nat.zero_add, getElem?_eq_drop_head?, ite_true]
        · have hendi_ne : len + i ≠ i := by omega
          have hsub : len + i - i = len := by omega
          simp only [hendi_ne, ite_eq_right, not_false_eq_true, hsub]
          -- the Array.extract lexeme equals the spec (drop i).take len lexeme
          have hlex : (arr.extract i (len + i)).toList = (arr.toList.drop i).take len := by
            rw [Array.toList_extract, List.extract_eq_take_drop]
            congr 1
          rw [hlex]
          have hstaytr := hstay (String.ofList ((arr.toList.drop i).take len)) rule
          simp only [hstaytr]
          have hdrop : arr.toList.drop (len + i) = (arr.toList.drop i).drop len := by
            rw [List.drop_drop]; rw [Nat.add_comm]
          have hile : len + i ≤ arr.size := by
            have hll := scan_len_le (cf.base.dfas.getD m default) (arr.toList.drop i) rule len hsc
            rw [List.length_drop, Array.length_toList] at hll
            omega
          have hrec := ih (len + i) (pos + len)
            (match (((cf.base.acts.getD m #[]).getD rule (fun _ => {}))
                (String.ofList ((arr.toList.drop i).take len))).emit with
              | some tok => tok :: acc | none => acc) hile
          rw [ite_eq_right hlen]
          rw [hdrop] at hrec
          exact hrec

/-- The flat tokenizer entry point: decode `input` to an `Array Char` once, then
    scan by index with the flat tables. Fuel is the char count. -/
def tokenizeFlat (cf : CompiledFlat Tok) (input : String) : Except LexError (List Tok) :=
  let arr := input.toList.toArray
  tokenizeFlatAux cf arr (arr.size + 1) 0 0 [cf.base.start] []

/-- **The flat tokenizer equals the spec `tokenize`** for a single validated start
    mode whose actions keep the mode stack put. So the emitted `tokenize` may run the
    fast flat scanner and inherit `tokenize_sound` (`Lexer/Tokenize.lean`) unchanged. -/
theorem tokenizeFlat_eq_tokenize (cf : CompiledFlat Tok)
    (hval : flatValidate (cf.flats.getD cf.base.start default)
      (cf.base.dfas.getD cf.base.start default) = true)
    (hstart : 0 < (cf.base.dfas.getD cf.base.start default).states.size)
    (hstay : ∀ (s : String) (rule : Nat),
      (((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) s).trans = Trans.stay)
    (input : String) :
    tokenizeFlat cf input = tokenize cf.base input := by
  unfold tokenizeFlat tokenize
  have harr : (input.toList.toArray).toList = input.toList := by simp
  have hsize : (input.toList.toArray).size = input.toList.length := by simp
  have := tokenizeFlatAux_eq_single cf cf.base.start hval hstart hstay
    (input.toList.toArray) ((input.toList.toArray).size + 1) 0 0 [] (by omega)
  rw [this]
  simp only [List.drop_zero, hsize]

/-! ### String.Pos flat tokenizer (the fast runtime: no `toList`, `String.extract` lexeme)

`tokenizeFlat` above decodes `input.toList.toArray` and slices lexemes from the array.
`tokenizeFlatStr` scans the `String` directly by `String.Pos` with the flat tables
(`flatScanStr`) and slices lexemes with `String.extract` (a byte copy) — the same shape
as `tokenizeStr` but with the fast flat scanner. It is proved equal to `tokenizeStr`
(hence to `tokenize`) by the pointwise scan agreement `flatScanStr_eq_scanStr`. -/

/-- Byte-index flat tokenization loop, mirroring `tokenizeStrAux` but scanning with
    `flatScanStr` (the flat tables) instead of `DFA.scanStr`. -/
def tokenizeFlatStrAux (cf : CompiledFlat Tok) (input : String) :
    Nat → input.Pos → Nat → List Nat → List Tok → Except LexError (List Tok)
  | 0, _, cpos, _, _ => .error { pos := cpos, char := none }
  | fuel + 1, p, cpos, stack, acc =>
      if hend : p = input.endPos then
        match stack with
        | [_] =>
            match cf.base.eofToken with
            | some tok => .ok (tok :: acc).reverse
            | none => .ok acc.reverse
        | _ => .error { pos := cpos, char := none }
      else
        let mode := stack.headD cf.base.start
        let flat := cf.flats.getD mode default
        match DFA.flatScanStr flat p with
        | some (rule, len, endPos) =>
            if len = 0 then .error { pos := cpos, char := some (p.get hend) }
            else
              -- Skip the `String.extract` byte copy when the rule's action
              -- ignores the lexeme (docs/DESIGN.md §9.6.4 item 1). `needsText`
              -- defaults to `true`, so an absent `textDep` table is still sound.
              -- `bif` (Bool `cond`) avoids a `Decidable` wrapper, keeping the
              -- equivalence proof's rewrites clean.
              let matched := bif cf.needsText mode rule then input.extract p endPos else ""
              let act := (cf.base.acts.getD mode #[]).getD rule (fun _ => {})
              let a := act matched
              let acc := match a.emit with | some tok => tok :: acc | none => acc
              let stack := match a.trans with
                | .stay => stack
                | .push m => m :: stack
                | .pop => stack.tail
              tokenizeFlatStrAux cf input fuel endPos (cpos + len) stack acc
        | none => .error { pos := cpos, char := some (p.get hend) }

/-- The fast flat tokenizer entry point over `String.Pos`. -/
def tokenizeFlatStr (cf : CompiledFlat Tok) (input : String) : Except LexError (List Tok) :=
  tokenizeFlatStrAux cf input (input.utf8ByteSize + 1) input.startPos 0 [cf.base.start] []

/-- Single-mode flat `String.Pos` tokenizer loop equals `tokenizeStrAux` on stack `[m]`,
    when mode `m` is validated and actions keep the stack put. The scanners agree
    pointwise (`flatScanStr_eq_scanStr`); the recursion stays in mode `m`. -/
theorem tokenizeFlatStrAux_eq_single (cf : CompiledFlat Tok) (m : Nat)
    (hval : flatValidate (cf.flats.getD m default) (cf.base.dfas.getD m default) = true)
    (hstartm : 0 < (cf.base.dfas.getD m default).states.size)
    (hstay : ∀ (s : String) (rule : Nat),
      (((cf.base.acts.getD m #[]).getD rule (fun _ => {})) s).trans = Trans.stay)
    (htext : ∀ (rule : Nat), cf.needsText m rule = false →
      ∀ (s : String), ((cf.base.acts.getD m #[]).getD rule (fun _ => {})) s
        = ((cf.base.acts.getD m #[]).getD rule (fun _ => {})) "")
    (input : String) :
    ∀ (fuel : Nat) (p : input.Pos) (cpos : Nat) (acc : List Tok),
      tokenizeFlatStrAux cf input fuel p cpos [m] acc
        = tokenizeStrAux cf.base input fuel p cpos [m] acc := by
  obtain ⟨hstep, hacc, hrange⟩ := agreements_of_flatValidate _ _ hval
  intro fuel
  induction fuel with
  | zero => intro p cpos acc; rfl
  | succ fuel ih =>
    intro p cpos acc
    unfold tokenizeFlatStrAux tokenizeStrAux
    by_cases hend : p = input.endPos
    · simp only [hend, dite_eq_left]
      cases cf.base.eofToken <;> rfl
    · simp only [hend, dite_eq_right, not_false_eq_true, List.headD_cons]
      rw [flatScanStr_eq_scanStr (cf.flats.getD m default) (cf.base.dfas.getD m default)
        hstep hacc hrange hstartm p]
      cases hsc : DFA.scanStr (cf.base.dfas.getD m default) p with
      | none => rfl
      | some res =>
        obtain ⟨rule, len, endPos⟩ := res
        by_cases hlen : len = 0
        · simp only [hlen, ite_eq_left]
        · simp only [hlen, ite_eq_right, not_false_eq_true]
          -- The runtime's lexeme, applied to the action, equals the spec's
          -- `input.extract`: for text-dependent rules literally; for
          -- text-independent rules the action is constant (`htext`).
          have hmatched :
              ((cf.base.acts.getD m #[]).getD rule (fun _ => {}))
                (bif cf.needsText m rule then input.extract p endPos else "")
              = ((cf.base.acts.getD m #[]).getD rule (fun _ => {})) (input.extract p endPos) := by
            cases hn : cf.needsText m rule with
            | true => rfl
            | false =>
                simp only [Bool.cond_false]
                exact (htext rule hn (input.extract p endPos)).symm
          rw [hmatched]
          have hstaytr := hstay (input.extract p endPos) rule
          simp only [hstaytr]
          exact ih endPos (cpos + len) _

/-- **The fast flat `String.Pos` tokenizer equals the spec `tokenize`** for a single
    validated start mode with stack-preserving actions. So the emitted `tokenize` may
    run it and inherit `tokenize_sound`, with no `toList` and byte-copy lexemes. -/
theorem tokenizeFlatStr_eq_tokenize (cf : CompiledFlat Tok)
    (hval : flatValidate (cf.flats.getD cf.base.start default)
      (cf.base.dfas.getD cf.base.start default) = true)
    (hstartm : 0 < (cf.base.dfas.getD cf.base.start default).states.size)
    (hstay : ∀ (s : String) (rule : Nat),
      (((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) s).trans = Trans.stay)
    (htext : ∀ (rule : Nat), cf.needsText cf.base.start rule = false →
      ∀ (s : String), ((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) s
        = ((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) "")
    (input : String) :
    tokenizeFlatStr cf input = tokenize cf.base input := by
  rw [← Lexer.tokenizeStr_eq_tokenize cf.base input]
  unfold tokenizeFlatStr tokenizeStr
  exact tokenizeFlatStrAux_eq_single cf cf.base.start hval hstartm hstay htext input _ _ _ _

/-! ### Positioned flat tokenizer (spans on tokens)

`tokenizeFlatStrPosAux` is `tokenizeFlatStrAux` with the accumulator carrying
`Runtime.Positioned Tok` (each emitted token wrapped with its byte `Span`
`⟨p.offset, endPos.offset⟩`) instead of a bare `Tok`. The EOF token gets a
zero-width span at `input.endPos` (Menhir's end position). Everything else — the
scan, the fuel, the mode stack, the lexeme handling — is identical, so erasing the
spans (`·.map (·.val)`) recovers `tokenizeFlatStrAux` exactly. This is what lets the
generated `tokenize` return positioned tokens while inheriting `tokenize_sound`
through the bare path unchanged. -/

/-- Byte-index flat tokenization loop that records a `Span` per emitted token.
    Mirrors `tokenizeFlatStrAux` step for step; the accumulator holds
    `Runtime.Positioned Tok`. -/
def tokenizeFlatStrPosAux (cf : CompiledFlat Tok) (input : String) :
    Nat → input.Pos → Nat → List Nat → List (Runtime.Positioned Tok) →
      Except LexError (List (Runtime.Positioned Tok))
  | 0, _, cpos, _, _ => .error { pos := cpos, char := none }
  | fuel + 1, p, cpos, stack, acc =>
      if hend : p = input.endPos then
        match stack with
        | [_] =>
            match cf.base.eofToken with
            | some tok =>
                .ok ({ val := tok, span := Runtime.Span.point input.endPos.offset } :: acc).reverse
            | none => .ok acc.reverse
        | _ => .error { pos := cpos, char := none }
      else
        let mode := stack.headD cf.base.start
        let flat := cf.flats.getD mode default
        match DFA.flatScanStr flat p with
        | some (rule, len, endPos) =>
            if len = 0 then .error { pos := cpos, char := some (p.get hend) }
            else
              let matched := bif cf.needsText mode rule then input.extract p endPos else ""
              let act := (cf.base.acts.getD mode #[]).getD rule (fun _ => {})
              let a := act matched
              let acc := match a.emit with
                | some tok => { val := tok, span := ⟨p.offset, endPos.offset⟩ } :: acc
                | none => acc
              let stack := match a.trans with
                | .stay => stack
                | .push m => m :: stack
                | .pop => stack.tail
              tokenizeFlatStrPosAux cf input fuel endPos (cpos + len) stack acc
        | none => .error { pos := cpos, char := some (p.get hend) }

/-- The positioned flat tokenizer entry point. Same scan as `tokenizeFlatStr`, but
    each token carries its source `Span`. -/
def tokenizeFlatStrPos (cf : CompiledFlat Tok) (input : String) :
    Except LexError (List (Runtime.Positioned Tok)) :=
  tokenizeFlatStrPosAux cf input (input.utf8ByteSize + 1) input.startPos 0 [cf.base.start] []

/-- **Span erasure (loop).** Mapping `·.val` over the positioned loop's accumulator
    and result recovers the bare `tokenizeFlatStrAux`. By induction on fuel: the two
    loops take identical branches (same scan, same lexeme, same stack moves); only
    the accumulator differs, by a `Positioned.mk _ span` wrapper whose `.val` is the
    bare token, and `List.map` commutes with the `::`/`reverse`/EOF-prepend. -/
theorem tokenizeFlatStrPosAux_val (cf : CompiledFlat Tok) (input : String) :
    ∀ (fuel : Nat) (p : input.Pos) (cpos : Nat) (stack : List Nat)
      (acc : List (Runtime.Positioned Tok)),
      (tokenizeFlatStrPosAux cf input fuel p cpos stack acc).map (fun toks => toks.map (·.val))
        = tokenizeFlatStrAux cf input fuel p cpos stack (acc.map (·.val)) := by
  intro fuel
  induction fuel with
  | zero => intro p cpos stack acc; rfl
  | succ fuel ih =>
    intro p cpos stack acc
    unfold tokenizeFlatStrPosAux tokenizeFlatStrAux
    by_cases hend : p = input.endPos
    · simp only [hend, dite_true]
      rcases stack with _ | ⟨a, _ | ⟨b, t⟩⟩
      · rfl
      · cases cf.base.eofToken with
        | none => simp [Except.map, List.map_reverse]
        | some tok => simp [Except.map, List.map_reverse]
      · rfl
    · simp only [hend, dite_false]
      cases hsc : DFA.flatScanStr (cf.flats.getD (stack.headD cf.base.start) default) p with
      | none => rfl
      | some res =>
        obtain ⟨rule, len, endPos⟩ := res
        by_cases hlen : len = 0
        · simp only [hlen, ite_true]; rfl
        · simp only [hlen, ite_false]
          -- the emit branch: the positioned acc's `.val`-map equals the bare acc
          cases hemit : (((cf.base.acts.getD (stack.headD cf.base.start) #[]).getD rule
              (fun _ => {})) (bif cf.needsText (stack.headD cf.base.start) rule then
                input.extract p endPos else "")).emit with
          | none =>
              exact ih endPos (cpos + len) _ acc
          | some tok =>
              have := ih endPos (cpos + len)
                (match (((cf.base.acts.getD (stack.headD cf.base.start) #[]).getD rule
                    (fun _ => {})) (bif cf.needsText (stack.headD cf.base.start) rule then
                      input.extract p endPos else "")).trans with
                  | .stay => stack | .push m => m :: stack | .pop => stack.tail)
                ({ val := tok, span := ⟨p.offset, endPos.offset⟩ } :: acc)
              simpa [List.map_cons] using this

/-- **Span erasure (entry).** The positioned tokenizer's token values are exactly the
    bare `tokenizeFlatStr` output, so `tokenize_sound` transfers to it through
    `tokenizeFlatStr_eq_tokenize` with no re-proof. -/
theorem tokenizeFlatStrPos_val (cf : CompiledFlat Tok) (input : String) :
    (tokenizeFlatStrPos cf input).map (fun toks => toks.map (·.val))
      = tokenizeFlatStr cf input := by
  rw [tokenizeFlatStrPos, tokenizeFlatStr]
  have := tokenizeFlatStrPosAux_val cf input (input.utf8ByteSize + 1) input.startPos 0
    [cf.base.start] []
  simpa using this

end Lexer
