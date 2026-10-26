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
The input token stream, abstracted behind a type class so the interpreter
observes the input only through sequential `head`/`tail` (see docs/DESIGN.md
§5.4). This is the `buffer` of §2.4 in Validating LR(1) Parsers, generalized
from a concrete coinductive stream to any instance of the class.

  * The interpreter and all correctness theorems are stated over an arbitrary
    `[TokenStream S Token]`; soundness/safety therefore hold for *any* instance,
    including a lazy runtime stream produced by the (untrusted) lexer.
  * `natStream` is the total, transparent witness instance (`Nat → Token`) used
    for reasoning. The efficient memoized lazy instance lives on the lexer side.
  * `appList` prepends a finite list of tokens to a stream; it lets us state
    completeness over `word ++ rest`.
-/


@[expose] public section

namespace Runtime

/-- Sequential access to an infinite stream of tokens. The only interface the
    trusted core uses to read input. -/
class TokenStream (S : Type) (Token : outParam Type) where
  /-- The token at the front of the stream. -/
  head : S → Token
  /-- The stream with its front token removed. -/
  tail : S → S

/-- A token stream that additionally supports prepending a finite word in front,
    with the expected `head`/`tail` computation laws. Correctness proofs (which
    reconstruct the original input as `appList word rest`) are stated over an
    `[AppStream]`; the runtime lazy stream need not be one, since the proofs are
    erased. The witness `NatStream` is the canonical instance. -/
class AppStream (S : Type) (Token : outParam Type) extends TokenStream S Token where
  /-- Prepend a finite word in front of a stream. -/
  appList : List Token → S → S
  /-- Prepending the empty word is the identity. -/
  appList_nil : ∀ s, appList [] s = s
  /-- `head` of a nonempty prepend is the first prepended token. -/
  head_appList_cons : ∀ t ts s, head (appList (t :: ts) s) = t
  /-- `tail` of a nonempty prepend drops the first prepended token. -/
  tail_appList_cons : ∀ t ts s, tail (appList (t :: ts) s) = appList ts s
  /-- A stream equals its head prepended to its tail. This stream "eta" law lets
      a `shift` re-associate the consumed word. -/
  stream_eta : ∀ s, s = appList [head s] (tail s)

namespace AppStream

variable {S Token : Type} [inst : AppStream S Token]

open TokenStream (head tail)

/-- Prepending `w₁ ++ w₂` is prepending `w₂` then `w₁`. -/
theorem appList_append (w₁ w₂ : List Token) (s : S) :
    appList (w₁ ++ w₂) s = appList w₁ (appList w₂ s) := by
  induction w₁ with
  | nil => simp [appList_nil]
  | cons t ts ih =>
    have hh : head (appList ((t :: ts) ++ w₂) s) = head (appList (t :: ts) (appList w₂ s)) := by
      simp [head_appList_cons]
    have ht : tail (appList ((t :: ts) ++ w₂) s) = tail (appList (t :: ts) (appList w₂ s)) := by
      simp only [List.cons_append, tail_appList_cons, ih]
    rw [stream_eta (appList ((t :: ts) ++ w₂) s), stream_eta (appList (t :: ts) (appList w₂ s)),
        hh, ht]

/-- Consuming the head of `s` re-associates: `appList word s` with one more token
    peeled equals `appList (word ++ [head s]) (tail s)`. -/
theorem appList_shift (word : List Token) (s : S) :
    appList word s = appList (word ++ [head s]) (tail s) := by
  rw [appList_append]
  rw [show appList [head s] (tail s) = s from (stream_eta s).symm]

end AppStream

namespace TokenStream

variable {S Token : Type} [TokenStream S Token]

/-- Observe the first `n` tokens of a stream (as a list), advancing by `tail`.
    A read-only helper; construction (e.g. prepending a word) is only available on
    concrete streams that expose a "cons", such as `NatStream` below. -/
def take (n : Nat) (s : S) : List Token :=
  match n with
  | 0 => []
  | n + 1 => head s :: take n (tail s)

end TokenStream

/-- The total, transparent witness stream: a function from position to token.
    Equivalent to Mathlib's `Stream'`, but defined locally to keep the trusted
    core Mathlib-free. Used only for reasoning; the runtime uses a lazy instance. -/
def NatStream (Token : Type) : Type := Nat → Token

namespace NatStream

variable {Token : Type}

instance : TokenStream (NatStream Token) Token where
  head s := s 0
  tail s := fun n => s (n + 1)

/-- Prepend a finite list of tokens in front of a `NatStream`. This is the
    concrete `app_buf` for the witness instance. -/
def appList : List Token → NatStream Token → NatStream Token
  | [], s => s
  | t :: ts, s =>
      fun n => match n with
        | 0 => t
        | n + 1 => appList ts s n

instance : AppStream (NatStream Token) Token where
  appList := appList
  appList_nil _ := rfl
  head_appList_cons _ _ _ := rfl
  tail_appList_cons _ _ _ := rfl
  stream_eta s := by
    funext n
    cases n with
    | zero => rfl
    | succ m => rfl

end NatStream

end Runtime
