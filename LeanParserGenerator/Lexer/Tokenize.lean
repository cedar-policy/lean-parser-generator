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
Tokenizer-level consequences of DFA validation (docs/DESIGN.md §9.7 step 4).

`Lexer/Validator.lean` proves that a validated DFA's `scan` computes exactly the
derivative-defined maximal munch (`scan_sound`), so two validated DFAs for the same
rules scan identically (`scan_deterministic`). The tokenizer loop `tokenizeAuxDFA`
uses the DFAs only through `DFA.scan`, so those facts lift to the whole tokenizer:
its token output is a function of the rule regexes, not of the untrusted table
shape. That is the tokenizer-level unambiguity/soundness the design asks for, one
level above the single-scan theorem.
-/
public import LeanParserGenerator.Lexer.Engine
public import LeanParserGenerator.Lexer.Validator


@[expose] public section

namespace Lexer

variable {Tok : Type}

/-- If two compiled lexers scan every mode/input identically and agree on actions,
    start mode, and EOF token, then `tokenizeAuxDFA` returns the same result on
    every state. The DFAs enter only through `DFA.scan`. -/
theorem tokenizeAuxDFA_congr {c₁ c₂ : Compiled Tok}
    (hscan : ∀ (m : Nat) (cs : List Char),
      DFA.scan (c₁.dfas.getD m default) cs = DFA.scan (c₂.dfas.getD m default) cs)
    (hacts : c₁.acts = c₂.acts) (hstart : c₁.start = c₂.start)
    (heof : c₁.eofToken = c₂.eofToken) :
    ∀ (fuel : Nat) (cs : List Char) (pos : Nat) (stack : List Nat) (acc : List Tok),
      tokenizeAuxDFA c₁ fuel cs pos stack acc = tokenizeAuxDFA c₂ fuel cs pos stack acc
  | 0, _, _, _, _ => by simp [tokenizeAuxDFA]
  | _+1, [], pos, stack, acc => by
      simp only [tokenizeAuxDFA, heof]
  | fuel+1, c :: cs, pos, stack, acc => by
      unfold tokenizeAuxDFA
      simp only [hstart, hscan (stack.headD c₂.start) (c :: cs)]
      -- After aligning the scan result, the recursion and action lookup agree.
      cases DFA.scan (c₂.dfas.getD (stack.headD c₂.start) default) (c :: cs) with
      | none => rfl
      | some p =>
          obtain ⟨rule, len⟩ := p
          by_cases hlen : len = 0
          · simp [hlen]
          · simp only [hlen, ite_false, hacts]
            exact tokenizeAuxDFA_congr hscan hacts hstart heof fuel _ _ _ _

/-- **Tokenizer unambiguity.** Two compiled lexers that agree on actions, start
    mode, and EOF token, and whose per-mode DFAs scan identically, tokenize every
    input identically. Instantiated with `scan_deterministic`, this says a
    validated lexer's tokens depend only on its rules, not on the untrusted DFA
    construction. -/
theorem tokenize_congr {c₁ c₂ : Compiled Tok}
    (hscan : ∀ (m : Nat) (cs : List Char),
      DFA.scan (c₁.dfas.getD m default) cs = DFA.scan (c₂.dfas.getD m default) cs)
    (hacts : c₁.acts = c₂.acts) (hstart : c₁.start = c₂.start)
    (heof : c₁.eofToken = c₂.eofToken) (input : String) :
    tokenize c₁ input = tokenize c₂ input := by
  simp only [tokenize, hstart]
  exact tokenizeAuxDFA_congr hscan hacts hstart heof _ _ _ _ _

/-! ### Tokenization soundness (single mode)

`Lexer/Spec.lean`'s `Tokenization` witnesses that a whole input decomposes into a
sequence of maximal-munch tokens (each a `MatchStep`). The single-scan soundness
`scan_matchStep` (`Lexer/Validator.lean`) says one `DFA.scan` step is a `MatchStep`;
this section lifts that to the whole `tokenizeAuxDFA` loop for a single mode, which
is the base the design establishes first (docs/DESIGN.md §9.4, §9.7 step 2).

"Single mode" means the mode stack stays a singleton throughout the run. The stack
only moves when a matched rule's action `trans` is a `push`/`pop`; the hypothesis
`hstay` says the mode's actions all `stay`, so the recursion keeps the stack at
`[m]` and the relevant DFA is always the validated one for `rules`. `Tokenization`
records only the maximal-munch lengths, not the emitted tokens or the mode, so this
is exactly the object a single-mode run produces. -/

/-- **Single-mode tokenization soundness.** If a single-mode run of `tokenizeAuxDFA`
    (mode `m`, whose DFA is validated for `rules` and whose actions all keep the
    mode stack put) succeeds on input `cs`, then `cs` has a maximal-munch
    `Tokenization` derivation for `rules`. Each accepted step is a `MatchStep`
    (`scan_matchStep`), and the loop peels them off left to right. -/
theorem tokenizeAuxDFA_sound {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : Lexer.validate rules dfa cert = true) (c : Compiled Tok) (m : Nat)
    (hdfa : c.dfas.getD m default = dfa)
    (hstay : ∀ (s : String) (rule : Nat),
      (((c.acts.getD m #[]).getD rule (fun _ => {})) s).trans = Trans.stay) :
    ∀ (fuel : Nat) (cs : List Char) (pos : Nat) (acc : List Tok) (toks : List Tok),
      tokenizeAuxDFA c fuel cs pos [m] acc = .ok toks →
      Lexer.Tokenization rules cs
  | 0, _, _, _, _, h => by simp [tokenizeAuxDFA] at h
  | _ + 1, [], _, _, _, _ => Lexer.Tokenization.nil
  | fuel + 1, c' :: cs, pos, acc, toks, h => by
      -- unfold one step; the current mode is m so the DFA is `dfa`
      simp only [tokenizeAuxDFA, List.headD_cons, hdfa] at h
      -- case on the scan result
      cases hscan : DFA.scan dfa (c' :: cs) with
      | none => rw [hscan] at h; simp at h
      | some p =>
          obtain ⟨rule, len⟩ := p
          rw [hscan] at h
          by_cases hlen : len = 0
          · simp [hlen] at h
          · have hlenpos : 0 < len := Nat.pos_of_ne_zero hlen
            -- this step is a MatchStep
            have hms : Lexer.MatchStep rules (c' :: cs) rule len :=
              scan_matchStep hval hscan hlenpos
            -- the stack stays [m] because the action is `.stay`
            have hstep : tokenizeAuxDFA c fuel ((c' :: cs).drop len) (pos + len) [m]
                (match (((c.acts.getD m #[]).getD rule (fun _ => {}))
                    (String.ofList ((c' :: cs).take len))).emit with
                  | some tok => tok :: acc | none => acc) = .ok toks := by
              have htr := hstay (String.ofList ((c' :: cs).take len)) rule
              simp only [hlen, ite_false] at h
              -- rewrite the stack-update to [m] using htr
              simp only [htr] at h
              exact h
            -- recurse to get the tail Tokenization
            have htail := tokenizeAuxDFA_sound hval c m hdfa hstay fuel
              ((c' :: cs).drop len) (pos + len) _ toks hstep
            exact Lexer.Tokenization.cons hms htail

/-- **`tokenize` is sound for a single-mode lexer.** If the compiled lexer's start
    mode is validated for `rules` and all its actions keep the mode stack put, then
    a successful `tokenize` implies the input has a maximal-munch `Tokenization`
    derivation. This is the entry-point form of `tokenizeAuxDFA_sound`. -/
theorem tokenize_sound {rules : Array Regex} {dfa : DFA} {cert : LexCert}
    (hval : Lexer.validate rules dfa cert = true) (c : Compiled Tok)
    (hdfa : c.dfas.getD c.start default = dfa)
    (hstay : ∀ (s : String) (rule : Nat),
      (((c.acts.getD c.start #[]).getD rule (fun _ => {})) s).trans = Trans.stay)
    {input : String} {toks : List Tok}
    (h : tokenize c input = .ok toks) :
    Lexer.Tokenization rules input.toList := by
  simp only [tokenize] at h
  exact tokenizeAuxDFA_sound hval c c.start hdfa hstay _ _ _ _ _ h

end Lexer
