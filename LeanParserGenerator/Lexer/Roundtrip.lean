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
public import LeanParserGenerator.Lexer.Engine
public import LeanParserGenerator.Lexer.StringScan
public import LeanParserGenerator.Lexer.DFA
public import LeanParserGenerator.Lexer.FlatTokenize


@[expose] public section

namespace Lexer
open DFA
variable {Tok : Type}

/-! ### Scan suffix stability

The single-scan walk `DFA.scan.go` stops at the first character with no matching
edge (a dead transition). So once the walk over a prefix `xs` dies, whatever
follows is irrelevant. This is the general fact behind the per-token peel: the
separator breaks maximal munch regardless of the rest of the input. -/

/-- The walk from `sid` over `xs` "dies within `xs` w.r.t. `ys`": either a step in
    `xs` finds no edge (the walk stops before reaching `ys`), or `xs` is exhausted
    at a state with no edge on `ys`'s first char. Either way, appending `ys`
    cannot extend the match. -/
def DiesOn (dfa : DFA) : Nat → List Char → List Char → Prop
  | sid, [], ys =>
      match ys with
      | [] => True
      | c :: _ => (dfa.states[sid]!).stepChar c = none
  | sid, c :: rest, ys =>
      match (dfa.states[sid]!).stepChar c with
      | none => True
      | some next => DiesOn dfa next rest ys

/-- `DiesOn` is decidable: it recurses on `xs`, and each leaf is either `True` or a
    `stepChar c = none` equality (decidable). This is what lets the per-token peel
    check `DiesOn dfa sid (renderTok t).toList (sep ++ …)` by `decide`/`native_decide`
    even with a variable tail, because the only character it inspects from the
    suffix is the (concrete) separator head. -/
instance decidableDiesOn (dfa : DFA) : ∀ (sid : Nat) (xs ys : List Char), Decidable (DiesOn dfa sid xs ys)
  | sid, [], ys =>
      match ys with
      | [] => isTrue trivial
      | _ :: _ => by unfold DiesOn; simp only; exact inferInstance
  | sid, c :: rest, ys => by
      unfold DiesOn
      cases (dfa.states[sid]!).stepChar c with
      | none => exact isTrue trivial
      | some next => simp only; exact decidableDiesOn dfa next rest ys

/-- `DiesOn` inspects the suffix `ys` only through its first character: the walk
    over `xs` either finds no edge inside `xs` (independent of `ys`), or reaches the
    end of `xs` and tests `ys`'s head. So the tail of `ys` is irrelevant, and a
    variable tail can be replaced by `[]`/anything with the same head. This is what
    makes the per-token peel's side condition `decide`-able with a variable rest:
    only the (concrete) separator head matters. -/
theorem diesOn_head (dfa : DFA) :
    ∀ (sid : Nat) (xs : List Char) (c : Char) (rest rest' : List Char),
      DiesOn dfa sid xs (c :: rest) → DiesOn dfa sid xs (c :: rest') := by
  intro sid xs
  induction xs generalizing sid with
  | nil => intro c rest rest' h; unfold DiesOn at h ⊢; simpa using h
  | cons a as ih =>
      intro c rest rest' h
      unfold DiesOn at h ⊢
      cases hstep : (dfa.states[sid]!).stepChar a with
      | none => exact trivial
      | some next => simp only [hstep] at h ⊢; exact ih next c rest rest' h

/-- Suffix stability: if the walk over `xs` dies within `xs` w.r.t. `ys`, scanning
    `xs ++ ys` gives the same result as scanning `xs`. Proved by induction on `xs`
    following the `DFA.scan.go` recursion. -/
theorem scan_go_append (dfa : DFA) :
    ∀ (xs : List Char) (sid pos : Nat) (best : Option (Nat × Nat)) (ys : List Char),
      DiesOn dfa sid xs ys →
      DFA.scan.go dfa sid (xs ++ ys) pos best = DFA.scan.go dfa sid xs pos best := by
  intro xs
  induction xs with
  | nil =>
      intro sid pos best ys hdies
      cases ys with
      | nil => rfl
      | cons c cs =>
          unfold DiesOn at hdies
          simp only at hdies
          rw [List.nil_append, DFA.scan.go, DFA.scan.go]
          simp only [hdies]
  | cons c rest ih =>
      intro sid pos best ys hdies
      rw [List.cons_append, DFA.scan.go, DFA.scan.go]
      unfold DiesOn at hdies
      cases hstep : (dfa.states[sid]!).stepChar c with
      | none => rfl
      | some next =>
          simp only [hstep] at hdies ⊢
          exact ih next (pos+1) _ ys hdies

/-- **Scan suffix-independence at a separator (the general per-token peel core).**
    If the walk over the token's lexeme `lit` dies as soon as it meets the
    separator character `sepCh` (checked by `DiesOn dfa 0 lit [sepCh]`, decidable
    and typically discharged by `native_decide`), then scanning
    `lit ++ (sepCh :: rest)` gives the same `(rule, len)` as scanning `lit` alone —
    *for every* `rest`. This is what makes the first token of a rendered list peel
    off independently of everything after its separator: the
    only suffix character that could have mattered is the separator head, and the
    token's lexeme already dies on it. `diesOn_head` drops the variable tail so the
    side condition is a finite `native_decide` check on `[sepCh]`. -/
theorem scan_lit_sep_indep (dfa : DFA) (lit : List Char) (sepCh : Char) (rest : List Char)
    (hdies : DiesOn dfa 0 lit [sepCh]) :
    DFA.scan dfa (lit ++ sepCh :: rest) = DFA.scan dfa lit := by
  unfold DFA.scan
  exact scan_go_append dfa lit 0 0 none (sepCh :: rest)
    (diesOn_head dfa 0 lit sepCh [] rest hdies)

/-- `tokenizeAuxDFA` on empty input does not depend on the (positive) fuel. -/
theorem tokenizeAuxDFA_nil_eq (c : Compiled Tok) (f g pos : Nat) (stack : List Nat)
    (acc : List Tok) :
    tokenizeAuxDFA c (f+1) [] pos stack acc = tokenizeAuxDFA c (g+1) [] pos stack acc := by
  cases stack with
  | nil => rfl
  | cons a t => cases t <;> rfl

/-- Fuel monotonicity: if a run succeeds with `fuel`, it gives the same result
    with any `fuel' ≥ fuel`. The loop only recurses after consuming `len ≥ 1`
    characters, so `input.length` steps always suffice and extra fuel is inert. -/
theorem tokenizeAuxDFA_fuel_mono (c : Compiled Tok) :
    ∀ (fuel : Nat) (cs : List Char) (pos : Nat) (stack : List Nat) (acc : List Tok)
      (toks : List Tok) (fuel' : Nat),
      fuel ≤ fuel' →
      tokenizeAuxDFA c fuel cs pos stack acc = .ok toks →
      tokenizeAuxDFA c fuel' cs pos stack acc = .ok toks
  | 0, _, _, _, _, _, _, _, h => by simp [tokenizeAuxDFA] at h
  | fuel + 1, cs, pos, stack, acc, toks, fuel', hle, h => by
      cases fuel' with
      | zero => omega
      | succ k =>
      have hle' : fuel ≤ k := by omega
      cases cs with
      | nil => rw [tokenizeAuxDFA_nil_eq c k fuel]; exact h
      | cons ch cs =>
          rw [tokenizeAuxDFA_cons] at h ⊢
          cases hscan : DFA.scan (c.dfas.getD (stack.headD c.start) default) (ch :: cs) with
          | none => simp only [hscan] at h ⊢; exact h
          | some p =>
              obtain ⟨rule, len⟩ := p
              by_cases hlen : len = 0
              · simp only [hscan, hlen, ite_true] at h ⊢; exact h
              · simp only [hscan, hlen, ite_false] at h ⊢
                exact tokenizeAuxDFA_fuel_mono c fuel _ _ _ _ toks k hle' h

/-- One emitting step of the single-mode loop: if the scanner picks `(rule, len)`
    on `cs` with `len ≥ 1`, the rule's action emits `tok` and keeps the mode
    stack put (`stay`), then the loop prepends `tok` to the accumulator and
    recurses on the remaining input. A clean reusable form of `tokenizeAuxDFA_cons`. -/
theorem tokenizeAuxDFA_step_emit (c : Compiled Tok) (fuel : Nat) (ch : Char)
    (cs : List Char) (pos : Nat) (m : Nat) (acc : List Tok) (rule len : Nat) (tok : Tok)
    (hscan : DFA.scan (c.dfas.getD m default) (ch :: cs) = some (rule, len))
    (hlen : len ≠ 0)
    (hemit : (((c.acts.getD m #[]).getD rule (fun _ => {}))
        (String.ofList ((ch :: cs).take len))).emit = some tok)
    (hstay : (((c.acts.getD m #[]).getD rule (fun _ => {}))
        (String.ofList ((ch :: cs).take len))).trans = Trans.stay) :
    tokenizeAuxDFA c (fuel+1) (ch :: cs) pos [m] acc
      = tokenizeAuxDFA c fuel ((ch :: cs).drop len) (pos + len) [m] (tok :: acc) := by
  rw [tokenizeAuxDFA_cons]
  simp only [List.headD_cons, hscan, hlen, ite_false, hemit, hstay]

/-- One skipping step (e.g. whitespace): the scanner picks a rule that emits
    nothing and stays; the loop drops the consumed prefix and continues with the
    accumulator unchanged. -/
theorem tokenizeAuxDFA_step_skip (c : Compiled Tok) (fuel : Nat) (ch : Char)
    (cs : List Char) (pos : Nat) (m : Nat) (acc : List Tok) (rule len : Nat)
    (hscan : DFA.scan (c.dfas.getD m default) (ch :: cs) = some (rule, len))
    (hlen : len ≠ 0)
    (hemit : (((c.acts.getD m #[]).getD rule (fun _ => {}))
        (String.ofList ((ch :: cs).take len))).emit = none)
    (hstay : (((c.acts.getD m #[]).getD rule (fun _ => {}))
        (String.ofList ((ch :: cs).take len))).trans = Trans.stay) :
    tokenizeAuxDFA c (fuel+1) (ch :: cs) pos [m] acc
      = tokenizeAuxDFA c fuel ((ch :: cs).drop len) (pos + len) [m] acc := by
  rw [tokenizeAuxDFA_cons]
  simp only [List.headD_cons, hscan, hlen, ite_false, hemit, hstay]

/-- **Emit-peel for a fixed lexeme (the reusable per-constant-token step).** Given a
    token whose lexeme is the non-empty `ch :: lit`, whose winning scan over that
    lexeme alone is `(rule, len)` with `len = (ch::lit).length`, whose action emits
    `tok` and stays, and whose lexeme *dies* on the separator character `sepCh`
    (`DiesOn`, decidable), the loop on `(ch :: lit) ++ sepCh :: rest` peels exactly
    `tok` and continues on `sepCh :: rest` — **for every `rest`**. This composes
    `scan_lit_sep_indep` (suffix independence of the token scan) with
    `tokenizeAuxDFA_step_emit`. All the per-token facts are `native_decide`-checkable
    on the fixed lexeme; only `rest` is universally quantified. -/
theorem peel_emit (c : Compiled Tok) (fuel : Nat) (ch : Char) (lit : List Char)
    (sepCh : Char) (rest : List Char) (pos : Nat) (rule len : Nat) (tok : Tok)
    (hdies : DiesOn (c.dfas.getD c.start default) 0 (ch :: lit) [sepCh])
    (hscanlit : DFA.scan (c.dfas.getD c.start default) (ch :: lit) = some (rule, len))
    (hlen : len = (ch :: lit).length)
    (hemit : (((c.acts.getD c.start #[]).getD rule (fun _ => {})) (String.ofList (ch :: lit))).emit
        = some tok)
    (hstay : (((c.acts.getD c.start #[]).getD rule (fun _ => {})) (String.ofList (ch :: lit))).trans
        = Trans.stay)
    (acc : List Tok) :
    tokenizeAuxDFA c (fuel+1) ((ch :: lit) ++ sepCh :: rest) pos [c.start] acc
      = tokenizeAuxDFA c fuel (sepCh :: rest) (pos + len) [c.start] (tok :: acc) := by
  -- The whole-input scan equals the lexeme-alone scan (suffix independence).
  have hscan : DFA.scan (c.dfas.getD c.start default) ((ch :: lit) ++ sepCh :: rest)
      = some (rule, len) := (scan_lit_sep_indep _ (ch :: lit) sepCh rest hdies).trans hscanlit
  -- Rewrite the input as a cons so the step lemma applies.
  rw [List.cons_append]
  -- The consumed lexeme is `(ch :: (lit ++ sepCh :: rest)).take len = ch :: lit`.
  have htake : (ch :: (lit ++ sepCh :: rest)).take len = ch :: lit := by
    rw [hlen]; simp
  have hdrop : (ch :: (lit ++ sepCh :: rest)).drop len = sepCh :: rest := by
    rw [hlen]; simp
  have hemit' : (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
      (String.ofList ((ch :: (lit ++ sepCh :: rest)).take len))).emit = some tok := by
    rw [htake]; exact hemit
  have hstay' : (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
      (String.ofList ((ch :: (lit ++ sepCh :: rest)).take len))).trans = Trans.stay := by
    rw [htake]; exact hstay
  have hscan' : DFA.scan (c.dfas.getD c.start default) (ch :: (lit ++ sepCh :: rest))
      = some (rule, len) := by rw [← List.cons_append]; exact hscan
  have hlen0 : len ≠ 0 := by rw [hlen]; simp
  have := tokenizeAuxDFA_step_emit c fuel ch (lit ++ sepCh :: rest) pos c.start acc rule len tok
    hscan' hlen0 hemit' hstay'
  rw [this, hdrop]

/-- **Skip-peel for a fixed separator (the reusable separator step).** Symmetric to
    `peel_emit` for a rule that emits nothing (`emit = none`) and stays — the
    separator's `skip` rule. Given the separator lexeme `sepCh :: slit` whose scan is
    `(rule, len)` with `len` its length, whose action emits nothing and stays, and
    which dies on the first character `nextCh` of what follows, the loop on
    `(sepCh :: slit) ++ nextCh :: rest` drops the separator and continues on
    `nextCh :: rest` with the accumulator unchanged — for every `rest`. For a
    single-space separator `slit = []`, `nextCh` is the head of the next rendered
    token, which is not whitespace, so the space dies on it. -/
theorem peel_skip (c : Compiled Tok) (fuel : Nat) (sepCh : Char) (slit : List Char)
    (nextCh : Char) (rest : List Char) (pos : Nat) (rule len : Nat)
    (hdies : DiesOn (c.dfas.getD c.start default) 0 (sepCh :: slit) [nextCh])
    (hscanlit : DFA.scan (c.dfas.getD c.start default) (sepCh :: slit) = some (rule, len))
    (hlen : len = (sepCh :: slit).length)
    (hemit : (((c.acts.getD c.start #[]).getD rule (fun _ => {})) (String.ofList (sepCh :: slit))).emit
        = none)
    (hstay : (((c.acts.getD c.start #[]).getD rule (fun _ => {})) (String.ofList (sepCh :: slit))).trans
        = Trans.stay)
    (acc : List Tok) :
    tokenizeAuxDFA c (fuel+1) ((sepCh :: slit) ++ nextCh :: rest) pos [c.start] acc
      = tokenizeAuxDFA c fuel (nextCh :: rest) (pos + len) [c.start] acc := by
  have hscan : DFA.scan (c.dfas.getD c.start default) ((sepCh :: slit) ++ nextCh :: rest)
      = some (rule, len) := (scan_lit_sep_indep _ (sepCh :: slit) nextCh rest hdies).trans hscanlit
  rw [List.cons_append]
  have htake : (sepCh :: (slit ++ nextCh :: rest)).take len = sepCh :: slit := by
    rw [hlen]; simp
  have hdrop : (sepCh :: (slit ++ nextCh :: rest)).drop len = nextCh :: rest := by
    rw [hlen]; simp
  have hemit' : (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
      (String.ofList ((sepCh :: (slit ++ nextCh :: rest)).take len))).emit = none := by
    rw [htake]; exact hemit
  have hstay' : (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
      (String.ofList ((sepCh :: (slit ++ nextCh :: rest)).take len))).trans = Trans.stay := by
    rw [htake]; exact hstay
  have hscan' : DFA.scan (c.dfas.getD c.start default) (sepCh :: (slit ++ nextCh :: rest))
      = some (rule, len) := by rw [← List.cons_append]; exact hscan
  have hlen0 : len ≠ 0 := by rw [hlen]; simp
  have := tokenizeAuxDFA_step_skip c fuel sepCh (slit ++ nextCh :: rest) pos c.start acc rule len
    hscan' hlen0 hemit' hstay'
  rw [this, hdrop]

/-! ### Universal printer/lexer roundtrip

A token is roundtrippable when its rendered spelling is a nonempty complete lexer
match, the action emits that same token and stays in the start mode, and the fixed
one-character separator stops both scans at the token boundary. These are the
structural facts needed by `peel_emit` and `peel_skip`. The public theorem is
universal over every list whose elements satisfy this predicate; it does not use a
finite corpus or a generated list of examples. -/

/-- `getD` returns the indexed element when the index is in bounds. -/
theorem getD_eq_getElem {α : Type} (a : Array α) (i : Nat) (d : α)
    (h : i < a.size) : a.getD i d = a[i] :=
  (Array.getElem_eq_getD d).symm

/-- If every action in an array stays in the current mode, so does `getD`; its
    out-of-bounds default action also stays. -/
theorem getD_act_trans_stay (arr : Array (String → Act Tok))
    (hall : ∀ x ∈ arr, ∀ s, (x s).trans = Trans.stay) (rule : Nat) (s : String) :
    ((arr.getD rule (fun _ => {})) s).trans = Trans.stay := by
  rw [Array.getD]
  split
  · next h => exact hall _ (Array.getElem_mem h) s
  · rfl

def RoundtrippableTok (c : Compiled Tok) (renderTok : Tok → String) (sepCh : Char)
    (t : Tok) : Prop :=
  match (renderTok t).toList with
  | [] => False
  | ch :: lit =>
      DiesOn (c.dfas.getD c.start default) 0 (ch :: lit) [sepCh] ∧
      DiesOn (c.dfas.getD c.start default) 0 [sepCh] [ch] ∧
      match DFA.scan (c.dfas.getD c.start default) (ch :: lit) with
      | none => False
      | some (rule, len) =>
          len = (ch :: lit).length ∧
          (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
              (String.ofList (ch :: lit))).emit = some t ∧
          (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
              (String.ofList (ch :: lit))).trans = Trans.stay

instance [DecidableEq Tok] (c : Compiled Tok) (renderTok : Tok → String) (sepCh : Char)
    (t : Tok) :
    Decidable (RoundtrippableTok c renderTok sepCh t) := by
  unfold RoundtrippableTok
  split
  · exact inferInstance
  · split <;> exact inferInstance

def SeparatorOk (c : Compiled Tok) (sepCh : Char) : Prop :=
  match DFA.scan (c.dfas.getD c.start default) [sepCh] with
  | none => False
  | some (rule, len) =>
      len = 1 ∧
      (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
          (String.singleton sepCh)).emit = none ∧
      (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
          (String.singleton sepCh)).trans = Trans.stay

instance (c : Compiled Tok) (sepCh : Char) : Decidable (SeparatorOk c sepCh) := by
  unfold SeparatorOk
  split <;> exact inferInstance

theorem peel_skip_eof (c : Compiled Tok) (fuel pos rule len : Nat) (sepCh : Char)
    (hscan : DFA.scan (c.dfas.getD c.start default) [sepCh] = some (rule, len))
    (hlen : len = 1)
    (hemit : (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
      (String.singleton sepCh)).emit = none)
    (hstay : (((c.acts.getD c.start #[]).getD rule (fun _ => {}))
      (String.singleton sepCh)).trans = Trans.stay)
    (acc : List Tok) :
    tokenizeAuxDFA c (fuel + 1) [sepCh] pos [c.start] acc =
      tokenizeAuxDFA c fuel [] (pos + 1) [c.start] acc := by
  have h := tokenizeAuxDFA_step_skip c fuel sepCh [] pos c.start acc rule len hscan
    (by omega)
    (by simpa [hlen] using hemit)
    (by simpa [hlen] using hstay)
  simpa [hlen] using h

/-- Render each token and append the separator after it. -/
def render (renderTok : Tok → String) (sep : String) (ts : List Tok) : String :=
  ts.foldr (fun t acc => renderTok t ++ sep ++ acc) ""

@[simp] theorem render_nil (renderTok : Tok → String) (sep : String) :
    render renderTok sep [] = "" := rfl

@[simp] theorem render_cons (renderTok : Tok → String) (sep : String) (t : Tok)
    (ts : List Tok) :
    render renderTok sep (t :: ts) = renderTok t ++ sep ++ render renderTok sep ts := rfl

/-- Every element of a token list satisfies `P`. -/
inductive Forall (P : Tok → Prop) : List Tok → Prop where
  | nil : Forall P []
  | cons {t : Tok} {ts : List Tok} : P t → Forall P ts → Forall P (t :: ts)


@[simp] theorem Forall.append {P : Tok → Prop} {xs ys : List Tok}
    (hxs : Forall P xs) (hys : Forall P ys) : Forall P (xs ++ ys) := by
  induction hxs with
  | nil => exact hys
  | cons head tail ih => exact .cons head ih
theorem hpeel_of_roundtrippable (c : Compiled Tok) (renderTok : Tok → String) (sepCh : Char)
    (hsep : SeparatorOk c sepCh) :
    ∀ (t : Tok) (ts : List Tok) (acc : List Tok) (f pos : Nat),
      RoundtrippableTok c renderTok sepCh t →
      Forall (RoundtrippableTok c renderTok sepCh) ts →
      (render renderTok (String.singleton sepCh) (t :: ts)).length < f →
      tokenizeAuxDFA c f
          (render renderTok (String.singleton sepCh) (t :: ts)).toList
          pos [c.start] acc =
        tokenizeAuxDFA c f
          (render renderTok (String.singleton sepCh) ts).toList
          (pos + (renderTok t ++ String.singleton sepCh).length) [c.start] (t :: acc) := by
  intro t ts acc f pos ht hts hf
  unfold RoundtrippableTok at ht
  cases hr : (renderTok t).toList with
  | nil => simp only [hr] at ht
  | cons ch lit =>
      simp only [hr] at ht
      rcases ht with ⟨htdies, hsepdies, ht⟩
      cases hs : DFA.scan (c.dfas.getD c.start default) (ch :: lit) with
      | none => simp only [hs] at ht
      | some out =>
          obtain ⟨rule, len⟩ := out
          simp only [hs] at ht
          rcases ht with ⟨hlen, hemit, hstay⟩
          unfold SeparatorOk at hsep
          cases hsscan : DFA.scan (c.dfas.getD c.start default) [sepCh] with
          | none => simp only [hsscan] at hsep
          | some sout =>
              obtain ⟨sepRule, sepLen⟩ := sout
              simp only [hsscan] at hsep
              rcases hsep with ⟨hsepLen, hsepEmit, hsepStay⟩
              have hrender : renderTok t = String.ofList (ch :: lit) := by
                apply String.toList_inj.mp
                simp only [hr, String.toList_ofList]
              have hprefixLen : (renderTok t ++ String.singleton sepCh).length = len + 1 := by
                rw [String.length_append, String.length_singleton, hlen,
                  ← String.length_toList, hr]
              have hlenPos : 0 < len := by rw [hlen]; simp
              have hwholeLen :
                  (render renderTok (String.singleton sepCh) (t :: ts)).length =
                    (renderTok t ++ String.singleton sepCh).length +
                      (render renderTok (String.singleton sepCh) ts).length := by
                simp [render, String.length_append, Nat.add_assoc]
              rw [hwholeLen] at hf
              have hf2 : ∃ k, f = k + 2 := by
                have hpref : 2 ≤ (renderTok t ++ String.singleton sepCh).length := by
                  rw [hprefixLen]
                  omega
                exact ⟨f - 2, by omega⟩
              obtain ⟨k, rfl⟩ := hf2
              have hemitStep := peel_emit c (k + 1) ch lit sepCh
                (render renderTok (String.singleton sepCh) ts).toList pos rule len t
                htdies hs hlen hemit hstay acc
              have hemitStep' :
                  tokenizeAuxDFA c (k + 2)
                      (render renderTok (String.singleton sepCh) (t :: ts)).toList
                      pos [c.start] acc =
                    tokenizeAuxDFA c (k + 1)
                      (sepCh :: (render renderTok (String.singleton sepCh) ts).toList)
                      (pos + len) [c.start] (t :: acc) := by
                rw [render_cons, hrender]
                simpa only [String.toList_append, String.toList_ofList,
                  String.toList_singleton, List.append_assoc, List.singleton_append,
                  Nat.add_assoc] using hemitStep
              rw [hemitStep']
              cases ts with
              | nil =>
                  simp only [render_nil, String.toList_empty]
                  have hskip := peel_skip_eof c k (pos + len) sepRule sepLen sepCh hsscan
                    hsepLen hsepEmit hsepStay (t :: acc)
                  rw [hskip]
                  rw [hprefixLen]
                  apply tokenizeAuxDFA_fuel_irrel c
                  · have : 0 < k := by
                      simp only [render_nil, String.length_empty, Nat.add_zero] at hf
                      rw [hprefixLen] at hf
                      omega
                    exact this
                  · simp
              | cons u us =>
                  cases hts with
                  | cons hu hus =>
                      unfold RoundtrippableTok at hu
                      cases huRender : (renderTok u).toList with
                      | nil => simp only [huRender] at hu
                      | cons uch ulit =>
                          simp only [huRender] at hu
                          have hsdies : DiesOn (c.dfas.getD c.start default) 0 [sepCh] [uch] := hu.2.1
                          have hskip := peel_skip c k sepCh [] uch
                            (ulit ++ sepCh :: (render renderTok (String.singleton sepCh) us).toList)
                            (pos + len) sepRule sepLen hsdies hsscan hsepLen
                            (by simpa using hsepEmit) (by simpa using hsepStay) (t :: acc)
                          have hskip' :
                              tokenizeAuxDFA c (k + 1)
                                  (sepCh :: (render renderTok (String.singleton sepCh) (u :: us)).toList)
                                  (pos + len) [c.start] (t :: acc) =
                                tokenizeAuxDFA c k
                                  (render renderTok (String.singleton sepCh) (u :: us)).toList
                                  (pos + len + 1) [c.start] (t :: acc) := by
                            rw [render_cons]
                            simpa only [String.toList_append, String.toList_singleton, huRender,
                              List.append_assoc, List.singleton_append, List.cons_append,
                              List.nil_append, hsepLen] using hskip
                          rw [hskip']
                          rw [hprefixLen]
                          have hsuf :
                              (render renderTok (String.singleton sepCh) (u :: us)).length < k := by
                            rw [hprefixLen] at hf
                            omega
                          have hsufk :
                              (render renderTok (String.singleton sepCh) (u :: us)).toList.length < k := by
                            simpa only [String.length_toList] using hsuf
                          apply tokenizeAuxDFA_fuel_irrel c
                          · exact hsufk
                          · omega


variable (renderTok : Tok → String) (sep : String)

theorem tokenize_render_fold_pred (c : Compiled Tok) (f : Nat) (P : Tok → Prop)
    (hpeel : ∀ (t : Tok) (ts : List Tok) (acc : List Tok) (pos : Nat),
      P t → Forall P ts →
      (render renderTok sep (t :: ts)).length < f →
      tokenizeAuxDFA c f (render renderTok sep (t :: ts)).toList pos [c.start] acc =
        tokenizeAuxDFA c f (render renderTok sep ts).toList
          (pos + (renderTok t ++ sep).length) [c.start] (t :: acc)) :
    ∀ (ts : List Tok) (acc : List Tok) (pos : Nat),
      Forall P ts →
      (render renderTok sep ts).length < f →
      tokenizeAuxDFA c f (render renderTok sep ts).toList pos [c.start] acc =
        tokenizeAuxDFA c f [] (pos + (render renderTok sep ts).length)
          [c.start] (ts.reverse ++ acc)
  | [], acc, pos, _, _ => by simp [render]
  | t :: ts, acc, pos, hall, hlt => by
      cases hall with
      | cons ht hts =>
          have hsuf : (render renderTok sep ts).length < f := by
            have h := hlt
            simp only [render_cons, String.length_append] at h
            omega
          rw [hpeel t ts acc pos ht hts hlt]
          rw [tokenize_render_fold_pred c f P hpeel ts (t :: acc)
            (pos + (renderTok t ++ sep).length) hts hsuf]
          cases f with
          | zero => omega
          | succ f => simp [tokenizeAuxDFA]

theorem tokenize_render_pred (c : Compiled Tok) (eof : Tok) (P : Tok → Prop)
    (heof : c.eofToken = some eof)
    (hpeel : ∀ (t : Tok) (ts : List Tok) (acc : List Tok) (f pos : Nat),
      P t → Forall P ts →
      (render renderTok sep (t :: ts)).length < f →
      tokenizeAuxDFA c f (render renderTok sep (t :: ts)).toList pos [c.start] acc =
        tokenizeAuxDFA c f (render renderTok sep ts).toList
          (pos + (renderTok t ++ sep).length) [c.start] (t :: acc)) :
    ∀ (ts : List Tok), Forall P ts →
      Lexer.tokenize c (render renderTok sep ts) = .ok (ts ++ [eof]) := by
  intro ts hall
  unfold Lexer.tokenize
  simp only []
  rw [tokenize_render_fold_pred renderTok sep c ((render renderTok sep ts).toList.length + 1)
    P (fun t ts' acc pos hp hs hlen => hpeel t ts' acc _ pos hp hs hlen)
    ts [] 0 hall (by rw [String.length_toList]; omega)]
  rw [tokenizeAuxDFA]
  · rw [heof]; simp
  · omega


/-- Universal roundtrip for the validated flat string tokenizer used by generated
    `tokenizeBare` definitions. The generated module supplies the finite table
    premises and the separator check; `RoundtrippableTok` carries the per-token
    renderer/action facts. -/
theorem tokenizeFlatStr_render (cf : CompiledFlat Tok) (eof : Tok)
    (renderTok : Tok → String) (sepCh : Char)
    (hval : flatValidate (cf.flats.getD cf.base.start default)
      (cf.base.dfas.getD cf.base.start default) = true)
    (hstartm : 0 < (cf.base.dfas.getD cf.base.start default).states.size)
    (hstay : ∀ (s : String) (rule : Nat),
      (((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) s).trans = Trans.stay)
    (htext : ∀ (rule : Nat), cf.needsText cf.base.start rule = false →
      ∀ (s : String), ((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) s
        = ((cf.base.acts.getD cf.base.start #[]).getD rule (fun _ => {})) "")
    (heof : cf.base.eofToken = some eof)
    (hsep : SeparatorOk cf.base sepCh) :
    ∀ (ts : List Tok), Forall (RoundtrippableTok cf.base renderTok sepCh) ts →
      tokenizeFlatStr cf (render renderTok (String.singleton sepCh) ts) =
        .ok (ts ++ [eof]) := by
  intro ts hall
  rw [tokenizeFlatStr_eq_tokenize cf hval hstartm hstay htext]
  apply tokenize_render_pred renderTok (String.singleton sepCh) cf.base eof
    (RoundtrippableTok cf.base renderTok sepCh) heof
  · intro t rest acc f pos ht hrest hfuel
    exact hpeel_of_roundtrippable cf.base renderTok sepCh hsep t rest acc f pos
      ht hrest hfuel
  · exact hall

end Lexer
