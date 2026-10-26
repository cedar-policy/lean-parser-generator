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
A byte-level (`UInt8`/`ByteArray`) flat scanner.

`Lexer/FlatScan.lean` walks a `String` by `String.Pos`, i.e. over already-decoded
`Char`s: each step calls `String.Pos.get`/`next`, which decode a UTF-8 code point.
This file walks the raw UTF-8 `ByteArray` one byte at a time with a `ByteDFA` whose
alphabet is `UInt8` (a 256-entry direct class table, no `String.Pos` decode and no
`bsearch`), folding the UTF-8 decode into the scan (docs/DESIGN.md §9.6.3).

The `ByteDFA` is a byte-expansion of a `FlatDFA`: its states are the char-DFA states
(the *boundary* states, where a code point has just been fully consumed) plus
intermediate states threading the 2–4 continuation bytes of a multi-byte code point.
Only boundary states accept. Over the UTF-8 bytes of one code point `c`, the byte
tables drive a boundary state `sid` to the boundary state `FlatDFA.step f sid c`, so
the byte walk and the char walk record the same `(rule, endPosition)`.

The construction (`byteOfFlat`) is untrusted; `Lexer/ByteValidator.lean` checks
a-posteriori that the byte tables agree with the `FlatDFA` at every state and code
point, the same route the `FlatDFA` itself takes against the `DFA`.
-/
public import LeanParserGenerator.Lexer.FlatScan
public import Std.Data.HashMap


@[expose] public section

namespace Lexer

open DFA
open FlatDFA

/-- A byte-level flat DFA. States are indexed `0 .. nStates-1`; the first
    `nBoundary` states are the code-point-boundary states, index-aligned with the
    source `FlatDFA`'s states. `trans[s*256 + b]` is `target+1` (0 = dead). Only
    boundary states carry an accept (`accept[s]`, `-1` if none); intermediate
    (mid-code-point) states never accept. -/
structure ByteDFA where
  /-- Number of byte-states (boundary + intermediate). -/
  nStates : Nat
  /-- Number of boundary states (= the source `FlatDFA`'s `nStates`). Boundary
      states are `0 .. nBoundary-1`. -/
  nBoundary : Nat
  /-- Flat transition table: `trans[s*256 + b]` = target+1 (0 = dead). -/
  trans : Array Nat
  /-- Per-state accept rule index, or `-1`. Nonnegative only on boundary states. -/
  accept : Array Int
  deriving Inhabited

namespace ByteDFA

/-- The byte step: target state for byte `b` from state `sid`, or `none` (dead). One
    array read into the flat 256-wide table. -/
@[inline] def step (bd : ByteDFA) (sid : Nat) (b : UInt8) : Option Nat :=
  let t := bd.trans.getD (sid * 256 + b.toNat) 0
  if t == 0 then none else some (t - 1)

/-- The accept rule of a state as an `Option`, from the `-1`-sentinel array. -/
@[inline] def acceptOf (bd : ByteDFA) (sid : Nat) : Option Nat :=
  let a := bd.accept.getD sid (-1)
  if a < 0 then none else some a.toNat

end ByteDFA

namespace DFA

/-! ### Byte scanning over a `ByteArray`

The scanner walks `bytes` by byte index. `best` records the last accept as
`(rule, byteEndIndex)`; because only boundary states accept, every recorded
`byteEndIndex` lands on a code-point boundary. This mirrors `flatScanArrGo`'s shape
so the agreement proof (`Lexer/ByteValidator.lean`) can relate the two walks. -/

/-- One byte-DFA walk over `bytes` from byte index `i`, recording the last accept as
    `(rule, byteEnd)`. `fuel` bounds the walk. -/
def byteScanGo (bd : ByteDFA) (bytes : ByteArray) :
    Nat → Nat → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, _, _, best => best
  | fuel + 1, sid, i, best =>
      let best := match bd.acceptOf sid with
        | some rule => some (rule, i)
        | none => best
      if h : i < bytes.size then
        match bd.step sid bytes[i] with
        | some next => byteScanGo bd bytes fuel next (i + 1) best
        | none => best
      else best

/-- Longest accepting prefix of `bytes` from byte index `start`, using the byte
    tables. Returns `(rule, byteEndIndex)`; the end index is a code-point boundary. -/
def byteScan (bd : ByteDFA) (bytes : ByteArray) (start : Nat) : Option (Nat × Nat) :=
  byteScanGo bd bytes (bytes.size + 1 - start) 0 start none

end DFA

/-! ### Untrusted construction: byte-expand a `FlatDFA`

The construction must not enumerate code points: a single char class (e.g. the
Unicode catch-all `[126, 0x10FFFF]`) spans over a million of them. Instead a class's
code-point interval is compiled to a bounded set of **UTF-8 byte-range sequences**
(the standard Daciuk/`utf8-ranges` construction): each sequence is a list of
`(lo, hi)` byte ranges, one per byte position, such that a byte string matches the
sequence iff it is the UTF-8 encoding of a code point in the interval. The number of
sequences is bounded (≤ a few dozen for any interval), independent of the interval
width. -/

namespace Utf8Ranges

/-- Encode a code point to its UTF-8 bytes (as a plain `Array UInt8`). -/
def enc (n : Nat) : Array UInt8 := (String.utf8EncodeChar (DFA.repOf n)).toArray

/-- The maximum code point representable with `k` UTF-8 bytes. -/
def maxForLen : Nat → Nat
  | 1 => 0x7F
  | 2 => 0x7FF
  | 3 => 0xFFFF
  | _ => 0x10FFFF

/-- The minimum code point requiring `k` UTF-8 bytes. -/
def minForLen : Nat → Nat
  | 1 => 0
  | 2 => 0x80
  | 3 => 0x800
  | _ => 0x10000

/-- One byte-range sequence: per byte position, an inclusive `(lo, hi)` range. A byte
    string matches iff position-wise each byte is in range. -/
abbrev Seq := Array (UInt8 × UInt8)

/-- Split `[lo, hi]` (guaranteed same UTF-8 byte-length `k`, no surrogates) into
    byte-range sequences. The standard recursion on byte positions: with prefix bytes
    fixed and a current position `i` where `el[i] ≤ eh[i]`, if `el`'s tail is all-min
    (`0x80…`) and `eh`'s tail is all-max (`0xBF…`) the whole `[i..]` is one sequence
    with byte `i` ranging `el[i]..eh[i]` and later bytes full continuation range.
    Otherwise peel: the low leading value `el[i]` with its tail `[el tail, max]`, the
    high leading value `eh[i]` with tail `[min, eh tail]`, and the interior leading
    values with full tails. Each peeled tail recurses one position deeper. -/
partial def splitSameLen (lo hi : Nat) : Array Seq :=
  let el := enc lo
  let eh := enc hi
  let k := el.size
  go el eh k 0 #[]
where
  /-- `pfx` holds the already-fixed `(b,b)` prefix ranges for positions `< i`. -/
  go (el eh : Array UInt8) (k i : Nat) (pfx : Seq) : Array Seq :=
    if i ≥ k then #[pfx]
    else
      let contLo : UInt8 := 0x80
      let contHi : UInt8 := 0xBF
      let bLo := el.getD i 0
      let bHi := eh.getD i 0
      if bLo == bHi then
        -- leading byte fixed; recurse deeper
        go el eh k (i+1) (pfx.push (bLo, bLo))
      else
        let nTail := k - i - 1
        let loTailAllMin := (List.range nTail).all (fun t => el.getD (i+1+t) 0 == contLo)
        let hiTailAllMax := (List.range nTail).all (fun t => eh.getD (i+1+t) 0 == contHi)
        if loTailAllMin && hiTailAllMax then
          Id.run do
            let mut seq := pfx.push (bLo, bHi)
            for _ in [0:nTail] do seq := seq.push (contLo, contHi)
            pure #[seq]
        else
          Id.run do
            let mut out : Array Seq := #[]
            -- low boundary: leading byte bLo, tail [el tail, max]
            out := out ++ go2 el (mkAllMax el i k) k (i+1) (pfx.push (bLo, bLo))
            -- interior leading values (bLo+1 .. bHi-1): full continuation tails
            if bLo.toNat + 1 ≤ bHi.toNat then
              -- only when there is a gap
              if bLo.toNat + 1 < bHi.toNat then
                let mut seq := pfx.push (UInt8.ofNat (bLo.toNat+1), UInt8.ofNat (bHi.toNat-1))
                for _ in [0:nTail] do seq := seq.push (contLo, contHi)
                out := out.push seq
              -- high boundary: leading byte bHi, tail [min, eh tail]
              out := out ++ go2 (mkAllMin eh i k) eh k (i+1) (pfx.push (bHi, bHi))
            pure out
  /-- Same as `go` but for a boundary tail: `el`/`eh` already clamped so the tail is a
      contiguous block; recurse position-wise. -/
  go2 (el eh : Array UInt8) (k i : Nat) (pfx : Seq) : Array Seq :=
    go el eh k i pfx
  /-- `el` with positions `> i` set to max continuation `0xBF`. -/
  mkAllMax (el : Array UInt8) (i k : Nat) : Array UInt8 := Id.run do
    let mut e := el
    for t in [0:k-i-1] do e := e.set! (i+1+t) 0xBF
    pure e
  /-- `eh` with positions `> i` set to min continuation `0x80`. -/
  mkAllMin (eh : Array UInt8) (i k : Nat) : Array UInt8 := Id.run do
    let mut e := eh
    for t in [0:k-i-1] do e := e.set! (i+1+t) 0x80
    pure e

/-- Compile a code-point interval `[lo, hi]` (may cross byte-length boundaries and the
    surrogate gap) into UTF-8 byte-range sequences. Splits at length boundaries and
    around the surrogate range `[0xD800, 0xDFFF]`, then same-length splits each piece. -/
def compile (lo hi : Nat) : Array Seq := Id.run do
  if hi < lo then return #[]
  let mut out : Array Seq := #[]
  -- split at UTF-8 length boundaries
  let lenBounds : List (Nat × Nat) :=
    [(minForLen 1, maxForLen 1), (minForLen 2, maxForLen 2),
     (minForLen 3, maxForLen 3), (minForLen 4, maxForLen 4)]
  for (blo, bhi) in lenBounds do
    let plo := Nat.max lo blo
    let phi := Nat.min hi bhi
    if plo ≤ phi then
      -- exclude the surrogate gap [0xD800, 0xDFFF] (invalid code points)
      let segs : List (Nat × Nat) :=
        if phi < 0xD800 || plo > 0xDFFF then [(plo, phi)]
        else
          (if plo < 0xD800 then [(plo, 0xD7FF)] else []) ++
          (if phi > 0xDFFF then [(0xE000, phi)] else [])
      for (slo, shi) in segs do
        out := out ++ splitSameLen slo shi
  return out

end Utf8Ranges

namespace ByteDFA

/-- Build a `ByteDFA` from a `FlatDFA` (untrusted; validated a-posteriori by
    `Lexer/ByteValidator.lean`).

    Boundary states `0 .. f.nStates-1` are the char-DFA states. For each boundary
    state `sid` and each flat class `ci` with a char-DFA edge to `tgt`, the class's
    code-point interval is compiled to UTF-8 byte-range sequences
    (`Utf8Ranges.compile`) and each sequence is installed as a byte-range chain
    `sid --seq[0]--> q₁ --seq[1]--> … --> tgt`. The `qⱼ` are fresh intermediate
    states, interned by their byte-range prefix so sequences sharing a prefix share
    states. Accepts are copied from the source on boundary states only. -/
def byteOfFlat (f : FlatDFA) : ByteDFA := Id.run do
  let nBoundary := f.nStates
  let mut nStates := nBoundary
  -- intermediate states interned by (sid, byte-range prefix of the sequence)
  let mut interned : Std.HashMap (Nat × Array (UInt8 × UInt8)) Nat := {}
  let mut edges : Array (Nat × UInt8 × Nat) := #[]  -- (from, byte, to)
  let mut accepts : Array (Nat × Int) := #[]
  for sid in [0:nBoundary] do
    let a := f.accept.getD sid (-1)
    if a ≥ 0 then accepts := accepts.push (sid, a)
  -- Intermediate states are interned by the future they encode: the remaining
  -- byte-range suffix of the sequence and the eventual target. Two chains with the
  -- same suffix+target are the same state, so continuation tails are shared across
  -- all source states and classes — without this the Unicode catch-all class blows
  -- the state count up per source state.
  for sid in [0:nBoundary] do
    for ci in [0:f.nClasses] do
      let lo := f.bounds.getD ci 0
      let hi := f.bounds.getD (ci + 1) 0 - 1
      -- the class's target under the char DFA (constant on the class)
      let rep := DFA.repOf lo
      if let some tgt := FlatDFA.step f sid rep then
        for seq in Utf8Ranges.compile lo hi do
          -- install the byte-range chain sid --seq[0]--> q1 --seq[1]--> … --> tgt
          let m := seq.size
          let mut cur := sid
          for j in [0:m] do
            let (blo, bhi) := seq.getD j (0, 0)
            let isLast := j + 1 == m
            let nextState ←
              if isLast then pure tgt
              else
                let key := (tgt, seq.extract (j+1) m)
                match interned.get? key with
                | some q => pure q
                | none =>
                    let q := nStates
                    nStates := nStates + 1
                    interned := interned.insert key q
                    pure q
            -- add one edge per byte value in [blo, bhi]
            let mut bv := blo.toNat
            while bv ≤ bhi.toNat do
              edges := edges.push (cur, UInt8.ofNat bv, nextState)
              bv := bv + 1
            cur := nextState
  let mut trans : Array Nat := Array.replicate (nStates * 256) 0
  for (fromS, b, toS) in edges do
    trans := trans.set! (fromS * 256 + b.toNat) (toS + 1)
  let mut accept : Array Int := Array.replicate nStates (-1)
  for (sid, a) in accepts do
    accept := accept.set! sid a
  return { nStates := nStates, nBoundary := nBoundary, trans := trans, accept := accept }

end ByteDFA

end Lexer
