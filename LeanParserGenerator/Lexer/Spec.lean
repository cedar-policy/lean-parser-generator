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
The specification objects the lexer tables are validated against
(docs/DESIGN.md §9.7 step 2).

The lexer has no analogue of the parser's `ParseTree`; because tokenization is a
linear scan, the derivation is a *sequence*, not a tree. This file defines:

  * `bestMatch` — the spec-only maximal-munch winner for a mode's ordered rule
    list, defined directly by `Regex.longestMatch` (it was removed from the
    executable `Engine.lean`; here it returns as a specification, not an execution
    path). It returns the winning rule index and consumed length, ties broken by
    rule order.
  * `MatchStep` — the proposition that `(rule, len)` is the maximal-munch winner
    at a position: the rule matches the consumed prefix, no rule matches longer,
    and no earlier rule matches the same length.
  * `Tokenization` — a witness that a run of `bestMatch` steps consumes the whole
    input. Its "size" is the input length, so unlike the parser's `ptSize` it
    needs no fuel bound.

`bestMatch` and `MatchStep` are the statement of what `DFA.scan` computes; the
generic theorem in `Lexer/Validator.lean` proves `DFA.scan = bestMatch` for
validated tables.
-/
public import LeanParserGenerator.Lexer.Regex


@[expose] public section

namespace Lexer

open Regex

/-! ### Spec-only maximal munch over a rule list -/

/-- The maximal-munch winner for a mode's ordered rule regexes on input `cs`:
    scan every rule's `longestMatch`, keep the longest, break ties by earliest
    rule index. Returns `(ruleIdx, length)` or `none` if no rule matches a
    non-empty prefix. This is the specification `DFA.scan` is proved to compute
    (docs/DESIGN.md §9.7 step 2). -/
def bestMatch (rules : Array Regex) (cs : List Char) : Option (Nat × Nat) := Id.run do
  let mut best : Option (Nat × Nat) := none
  for h : i in [0:rules.size] do
    match Regex.longestMatch rules[i] cs with
    | some len =>
        if len > 0 then
          match best with
          | none => best := some (i, len)
          | some (_, blen) => if len > blen then best := some (i, len)
    | none => pure ()
  return best

/-- `(rule, len)` is the maximal-munch winner among `rules` on `cs`:

    * `rule` is a valid index and its regex matches the length-`len` prefix;
    * `len ≥ 1` (zero-length matches are not tokens);
    * no rule matches a strictly longer prefix;
    * no *earlier* rule matches the same length (tie-break by rule order).

    This is the relational form of `bestMatch`; the generic theorem shows
    `bestMatch rules cs = some (rule, len) ↔ MatchStep rules cs rule len`. -/
structure MatchStep (rules : Array Regex) (cs : List Char) (rule len : Nat) : Prop where
  /-- The winning rule index is in range. -/
  ruleLt : rule < rules.size
  /-- The winning rule matches the consumed prefix exactly. -/
  matchesPrefix : Regex.matchesFull rules[rule]! (cs.take len) = true
  /-- Tokens are non-empty. -/
  lenPos : 0 < len
  /-- No rule matches a strictly longer prefix. -/
  maximal : ∀ (j : Nat), j < rules.size →
    ∀ (l : Nat), l ≤ cs.length → Regex.matchesFull rules[j]! (cs.take l) = true → l ≤ len
  /-- No earlier rule matches the same length. -/
  earliest : ∀ (j : Nat), j < rule →
    Regex.matchesFull rules[j]! (cs.take len) = true → False

/-! ### The tokenization derivation

For a single-mode lexer, a `Tokenization` witnesses that repeatedly taking the
maximal-munch winner consumes the whole input. Each step records the winning rule
and the consumed length; the step is required to be a `MatchStep`, and the
remaining input is what is left after dropping the consumed prefix. This is the
lexer's analogue of the parser's `ParseTree`, but a sequence rather than a tree
(docs/DESIGN.md §9.7 step 2). Its size is the input length, so it needs no fuel
bound: `Cons` strictly shortens the input, so the relation is well-founded.

Multi-mode lexers additionally thread a mode stack; the single-mode case is the
base the generic theorem establishes first. -/

/-- A maximal-munch tokenization of `cs` by a single mode's `rules`. `Nil` closes
    at end of input; `Cons` peels off one maximal-munch token. -/
inductive Tokenization (rules : Array Regex) : List Char → Prop where
  /-- The input is fully consumed. -/
  | nil : Tokenization rules []
  /-- Peel off one maximal-munch token of length `len` (rule `rule`) and continue
      on the remaining input. -/
  | cons {cs : List Char} {rule len : Nat} :
      MatchStep rules cs rule len →
      Tokenization rules (cs.drop len) →
      Tokenization rules cs

end Lexer
