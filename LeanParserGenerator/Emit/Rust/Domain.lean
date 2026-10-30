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
Domain checks for partial known functions (docs/RUST_PARSER.md, decision D10).

`String.toNat!` panics unless its argument is all digits. In a lexer action the
argument is the lexeme, so the language of the rule's regex must be inside the
function's domain. `lang` abstracts a string expression to a regex for its set of
possible values, and `subset` decides inclusion with the lexer's derivative
construction. Only the lexeme and `String.replace` of a single character by the empty
string are understood; any other expression gives `none` (not checked).
-/
public import LeanParserGenerator.Emit.Rust.Classify
public import LeanParserGenerator.Lexer.DFA


@[expose] public section

namespace Emit.Rust

open Lexer

/-- Remove one code point from a class. -/
def _root_.Lexer.CharClass.erase (k : CharClass) (ch : Nat) : CharClass :=
  if k.neg then { k with rs := (ch, ch) :: k.rs }
  else
    { k with rs := k.rs.flatMap fun (lo, hi) =>
        if ch < lo || hi < ch then [(lo, hi)]
        else (if lo < ch then [(lo, ch - 1)] else []) ++ (if ch < hi then [(ch + 1, hi)] else []) }

/-- The language of `r` with every occurrence of `ch` deleted (a homomorphism). -/
def _root_.Lexer.Regex.erase (ch : Char) : Regex → Regex
  | .never => .never
  | .epsilon => .epsilon
  | .cls k =>
    if k.mem ch then .alt (.cls (k.erase ch.toNat)) .epsilon else .cls k
  | .cat a b => .cat (erase ch a) (erase ch b)
  | .alt a b => .alt (erase ch a) (erase ch b)
  | .star a => .star (erase ch a)

/-- The set of values of a string expression, given the lexeme's language. -/
def lang (lexeme : Regex) : AExpr → Option Regex
  | .var _ => some lexeme
  | .app (.field x "replace") #[.str from_, .str ""] =>
    match from_.toList with
    | [c] => (lang lexeme x).map (Lexer.Regex.erase c)
    | _ => none
  | _ => none

/-- `L(r) ⊆ L(d)`, by exploring the derivatives of both regexes together. `none` if the
    construction runs out of fuel. -/
def subset (r d : Regex) : Option Bool :=
  (DFA.build?WithVecs #[r, d]).map fun (_, vecs) =>
    vecs.all fun v => !(v[0]!).nullable || (v[1]!).nullable

/-- The verdict for one call of a partial known function in a lexer action. -/
inductive Verdict where
  | proved
  | violated
  | notChecked (why : String)

def Verdict.describe : Verdict → String
  | .proved => "proved: the rule's language is inside the domain"
  | .violated => "NOT SATISFIED: the rule's language is not inside the domain"
  | .notChecked w => s!"not checked ({w})"

/-- Check a call `fn recv` in the action of a lexer rule whose lexeme language is
    `rule`. -/
def checkCall (rule : Regex) (fn : String) (recv : AExpr) : Verdict :=
  match (knownFn? fn).bind (·.domain) with
  | none => .notChecked "total"
  | some d =>
    match lang rule recv with
    | none => .notChecked "the argument is not the lexeme or a replace of it"
    | some l =>
      match subset l d with
      | some true => .proved
      | some false => .violated
      | none => .notChecked "regex exploration ran out of fuel"

end Emit.Rust
