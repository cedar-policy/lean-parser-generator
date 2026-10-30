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
An untrusted DFA compiler and scanner for the lexer.

This is the lexer's scanning path (docs/DESIGN.md §9.2). Construction is untrusted:
we build one DFA per lexer mode from that mode's ordered rule list, then scan input
by array-indexed state transitions with maximal munch. What the tables are supposed
to compute is stated by `Regex.matchesFull` and `Regex.longestMatch`; proving that
they do is later work (§9.4), so this file is not on the verified path.

Construction (Owens–Reppy–Turon, "Regular-expression derivatives reexamined"):

  * A DFA *state* is the vector of per-rule regex derivatives (`Array Regex`),
    one component per rule in the mode. This makes the combined automaton do
    maximal munch across all rules in a single input walk.
  * A state's *accept* is the least rule index whose component is `nullable`, so
    ties between rules matching the same length go to the earlier rule.
  * Outgoing transitions are grouped into *character classes*: sets of characters
    on which every component derives identically. We compute a representative
    character per class and take one derivative vector per class.
  * States are deduplicated by `BEq Regex` (which compares `CharClass`es by key),
    keeping the state set finite.

The alphabet is not enumerated. Each transition is `(CharClass, targetState)`;
scanning tests a character against each class in order. `CharClass.all` is the
catch-all for "any other character".
-/
public import LeanParserGenerator.Lexer.Regex


@[expose] public section

namespace Lexer

open Regex

/-- A compiled transition: characters in `cls` go to state `target`. -/
structure DTrans where
  /-- The character class guarding this edge. -/
  cls : CharClass
  /-- The target state index. -/
  target : Nat
  deriving Inhabited

/-- A DFA state: its outgoing transitions and, if accepting, the least accepting
    rule index (into the mode's rule list). `accept = none` is non-accepting. -/
structure DState where
  /-- Outgoing edges, tested in order; the last is typically `CharClass.all`. -/
  trans : Array DTrans := #[]
  /-- The winning rule index if this state accepts, else `none`. -/
  accept : Option Nat := none
  deriving Inhabited

/-- A compiled DFA for one lexer mode: an array of states (state 0 is the start)
    and the number of rules the accept indices refer to. -/
structure DFA where
  /-- States, indexed by id; state 0 is the start state. -/
  states : Array DState
  deriving Inhabited

/-- The transition target for `c` from a state: the first edge whose class matches.
    `none` if no edge matches (dead — no rule can continue). Defined with
    `Array.findSome?` so the verification can reason about it structurally
    (docs/DESIGN.md §9.7 step 4). -/
def DState.stepChar (s : DState) (c : Char) : Option Nat :=
  s.trans.findSome? (fun e => if e.cls.mem c then some e.target else none)

namespace DFA

/-! ### Character-class partitioning -/

/-- Collect every `CharClass` mentioned in a regex. -/
def classesOf : Regex → List CharClass
  | .never | .epsilon => []
  | .cls k => [k]
  | .cat a b | .alt a b => classesOf a ++ classesOf b
  | .star a => classesOf a

/-- The largest code point we distinguish, `0x10FFFF`. The alphabet is
    `[0, maxCodePoint]`. -/
def maxCodePoint : Nat := 0x10FFFF

/-- A safe representative code point for the interval starting at `lo`: `lo`
    itself, unless it lands in the UTF-16 surrogate gap `[0xD800, 0xDFFF]` (which
    `Char.ofNat` would replace with U+FFFD), in which case use the first code
    point past the gap. Only meaningful when the interval actually contains a
    valid scalar value; the verification (docs/DESIGN.md §9.7 step 0) quantifies
    over valid scalar values, so the surrogate gap is never a match position. -/
def repOf (lo : Nat) : Char :=
  if 0xD800 ≤ lo && lo ≤ 0xDFFF then Char.ofNat 0xE000 else Char.ofNat lo

/-- Normalize a `CharClass` to a sorted list of disjoint inclusive intervals over
    `[0, maxCodePoint]`. Ranges are merged and, if negated, complemented. Since
    `CharClass` is now ranges-only (docs/DESIGN.md §9.7 step 0: no opaque
    predicates), this is exact everywhere and has no bounded-window
    approximation. -/
def classIntervals (k : CharClass) : List (Nat × Nat) :=
  let neg := k.neg
  let rs := k.rs
  -- sort by lo, merge overlaps/adjacencies
  let sorted := (rs.filter (fun r => r.1 ≤ r.2)).toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let merged := sorted.foldl (fun (acc : List (Nat × Nat)) r =>
    match acc with
    | [] => [r]
    | (lo, hi) :: rest =>
        if r.1 ≤ hi + 1 then (lo, max hi r.2) :: rest
        else r :: acc) []
    |>.reverse
  if !neg then merged
  else
    -- complement within [0, maxCodePoint]
    let rec complement (next : Nat) (rs : List (Nat × Nat)) : List (Nat × Nat) :=
      match rs with
      | [] => if next ≤ maxCodePoint then [(next, maxCodePoint)] else []
      | (lo, hi) :: rest =>
          let pre := if next < lo then [(next, lo - 1)] else []
          pre ++ complement (hi + 1) rest
    complement 0 merged

/-- All boundary points (interval starts, and one past each interval end) across
    every class in the state, giving the cut points that define atoms. Always
    includes `0` and `maxCodePoint + 1`. -/
def boundaries (st : Array Regex) : Array Nat := Id.run do
  let mut pts : Array Nat := #[0, maxCodePoint + 1]
  for r in st do
    for k in classesOf r do
      for (lo, hi) in classIntervals k do
        pts := pts.push lo
        pts := pts.push (hi + 1)
  -- dedup + sort
  let sorted := pts.qsort (· < ·)
  let mut out : Array Nat := #[]
  for p in sorted do
    if p ≤ maxCodePoint + 1 && (out.isEmpty || out.back! != p) then
      out := out.push p
  return out

/-- Derive every component of a state by a character, giving the successor state
    vector. -/
def stepState (st : Array Regex) (c : Char) : Array Regex :=
  st.map (deriv c)

/-- Is a state dead (all components the empty language)? Such states are never
    accepting and have no useful transitions. -/
def stateDead (st : Array Regex) : Bool :=
  st.all isNever

/-- The accept index of a state: the least rule index whose component is nullable. -/
def stateAccept (st : Array Regex) : Option Nat :=
  st.findIdx? nullable

/-! ### Construction -/

/-- Find the index of a state vector already in `states`, by componentwise `BEq`. -/
def findState (states : Array (Array Regex)) (st : Array Regex) : Option Nat :=
  states.findIdx? (fun s => s.size == st.size && (s.zip st).all (fun p => p.1 == p.2))

/-- Vector equality by componentwise `BEq`. -/
def vecEq (a b : Array Regex) : Bool :=
  a.size == b.size && (a.zip b).all (fun p => p.1 == p.2)

/-- Partition the alphabet into atoms (maximal intervals on which every component
    derives identically), group atoms by successor vector, and emit one transition
    per group whose `CharClass` is the exact union of that group's intervals.

    Atoms partition `[0, maxCodePoint]` exactly, so each group's intervals describe
    precisely the characters reaching its successor: the edges are disjoint, their
    order does not matter, and no catch-all `CharClass.all` edge is emitted (one
    would overlap the others and, with first-match scanning, shadow them).
    Classification is exact: `CharClass` is ranges-only (§9.7 step 0), so every
    class has an exact interval decomposition and there is no bounded-window
    approximation. -/
def transitionsOf (st : Array Regex) : Array (CharClass × Array Regex) := Id.run do
  let bs := boundaries st
  -- groups: successor vector ↦ accumulated intervals
  let mut groups : Array (Array Regex × List (Nat × Nat)) := #[]
  let mut i := 0
  while i + 1 < bs.size do
    let lo := bs[i]!
    let hiExcl := bs[i+1]!   -- exclusive
    let hi := hiExcl - 1
    i := i + 1
    if lo > maxCodePoint then
      continue
    let succ := stepState st (repOf lo)
    if stateDead succ then
      continue
    match groups.findIdx? (fun g => vecEq g.1 succ) with
    | some j =>
        let g := groups[j]!
        groups := groups.set! j (g.1, (lo, hi) :: g.2)
    | none =>
        groups := groups.push (succ, [(lo, hi)])
  -- Atoms partition [0, maxCodePoint] exactly, so each group's own intervals
  -- describe precisely the characters that reach its successor. Edges are
  -- therefore disjoint and their order does not matter; no catch-all `all` class
  -- is needed (using one would overlap the other edges and, with first-match
  -- scanning, shadow them — the bug this construction had before).
  let mut result : Array (CharClass × Array Regex) := #[]
  for g in groups do
    let (succ, intervals) := g
    result := result.push (.ranges false intervals.reverse, succ)
  return result

/-- Build the DFA for a mode from its rule regexes (in rule order). Untrusted: the
    resulting DFA is not proved to match the rules' regexes; see docs/DESIGN.md
    §9.4. `fuel` bounds the number of states.

    Returns `none` on fuel exhaustion, i.e. when the worklist was not emptied
    (docs/DESIGN.md §9.7 step 0b): leaving unprocessed states as the `default`
    placeholder would make the scanner silently reject valid input, so a partial
    build is a failure, not a table. Derivative automata are finite, so a generous
    bound like the default `4096` suffices for lexer-sized rule sets. -/
def build? (ruleRegexes : Array Regex) (fuel : Nat := 4096) : Option DFA := Id.run do
  let start : Array Regex := ruleRegexes
  let mut vectors : Array (Array Regex) := #[start]
  let mut states : Array DState := #[default]
  let mut worklist : List Nat := [0]
  let mut steps := fuel
  while !worklist.isEmpty && steps > 0 do
    steps := steps - 1
    match worklist with
    | [] => pure ()
    | sid :: rest =>
        worklist := rest
        let st := vectors[sid]!
        let edges := transitionsOf st
        let mut dtrans : Array DTrans := #[]
        for edge in edges do
          let succ := edge.2
          let tid ←
            match findState vectors succ with
            | some i => pure i
            | none =>
                let i := vectors.size
                vectors := vectors.push succ
                states := states.push default
                worklist := worklist ++ [i]
                pure i
          dtrans := dtrans.push { cls := edge.1, target := tid }
        states := states.set! sid { trans := dtrans, accept := stateAccept st }
  -- The worklist must have emptied; otherwise fuel ran out mid-construction and
  -- some states are still the `default` placeholder.
  if worklist.isEmpty then
    return some { states := states }
  else
    return none

/-- Like `build?`, but also returns the per-state derivative vectors — the
    validator certificate (`Lexer.LexCert.vecs`, docs/DESIGN.md §9.7 step 3). The
    construction already computes these vectors, so returning them is free. The
    vectors are index-aligned with `DFA.states`. -/
def build?WithVecs (ruleRegexes : Array Regex) (fuel : Nat := 4096) :
    Option (DFA × Array (Array Regex)) := Id.run do
  let start : Array Regex := ruleRegexes
  let mut vectors : Array (Array Regex) := #[start]
  let mut states : Array DState := #[default]
  let mut worklist : List Nat := [0]
  let mut steps := fuel
  while !worklist.isEmpty && steps > 0 do
    steps := steps - 1
    match worklist with
    | [] => pure ()
    | sid :: rest =>
        worklist := rest
        let st := vectors[sid]!
        let edges := transitionsOf st
        let mut dtrans : Array DTrans := #[]
        for edge in edges do
          let succ := edge.2
          let tid ←
            match findState vectors succ with
            | some i => pure i
            | none =>
                let i := vectors.size
                vectors := vectors.push succ
                states := states.push default
                worklist := worklist ++ [i]
                pure i
          dtrans := dtrans.push { cls := edge.1, target := tid }
        states := states.set! sid { trans := dtrans, accept := stateAccept st }
  if worklist.isEmpty then
    return some ({ states := states }, vectors)
  else
    return none

/-- Panicking wrapper around `build?` for the untrusted elaboration-time emitter,
    where a `none` is a construction bug rather than a recoverable outcome. -/
def build! (ruleRegexes : Array Regex) (fuel : Nat := 4096) : DFA :=
  match build? ruleRegexes fuel with
  | some d => d
  | none => panic! "Lexer.DFA.build!: fuel exhausted before the worklist emptied"

/-! ### Scanning -/

/-- Longest accepting prefix of `cs` from the start state. Returns the winning
    rule index and match length, or `none` if no non-empty prefix matches.

    Walks the input once, following transitions and recording the most recent
    accepting state (maximal munch). This is the DFA analog of
    `Regex.longestMatch` fused across all rules. -/
def scan (dfa : DFA) (cs : List Char) : Option (Nat × Nat) :=
  let rec go (sid : Nat) (cs : List Char) (pos : Nat)
      (best : Option (Nat × Nat)) : Option (Nat × Nat) :=
    let st := dfa.states[sid]!
    let best := match st.accept with
      | some rule => some (rule, pos)
      | none => best
    match cs with
    | [] => best
    | c :: rest =>
        match st.stepChar c with
        | some next => go next rest (pos + 1) best
        | none => best
  go 0 cs 0 none

/-! ### String position scanning (the runtime scanner)

`scan` above walks a `List Char`, which chases a linked list and (in the tokenizer)
forces per-token `take`/`drop`/`String.ofList`. `scanStr` does the same walk over a
`String` directly, reading characters by the dependent `String.Pos` cursor
(`get`/`next`/`endPos`, whose `@[extern]` runtime implementations are O(1) and
allocate nothing). It carries both the character count `len` and the end
`String.Pos`, so the tokenizer can slice the lexeme with `String.extract` in
O(match length) without rebuilding a list.

`scanStr` is proved to agree with `scan` on the corresponding character list
(`Lexer.scanStr_go_eq_scan_go`, `Lexer/StringScan.lean`), so the derivative-level
`DFA.scan` remains the specification and all soundness proofs transfer to the
running object. This is docs/DESIGN.md §9.7 step 1, now the running scanner. The
dependent `String.Pos` API (rather than the flat `String.Pos.Raw`) is used because
its list-decomposition lemmas (`Pos.eq_copy_sliceTo_append_get`, `sliceFrom`) make
the agreement provable without UTF-8 byte arithmetic. -/

/-- One walk of the DFA over `s` starting at position `p`, following transitions
    and recording the last accepting state. `charsSoFar` counts the characters
    consumed from the scan start (so the recorded length matches `scan`'s character
    count); `best` holds the last accept as `(rule, charLen, pos)`. `fuel` bounds
    the walk (each step advances `p` past one character), so this is structurally
    terminating without `partial`. -/
def scanStrGo {s : String} (dfa : DFA) :
    Nat → Nat → s.Pos → Nat → Option (Nat × Nat × s.Pos) → Option (Nat × Nat × s.Pos)
  | 0, _, _, _, best => best
  | fuel + 1, sid, p, charsSoFar, best =>
      let st := dfa.states[sid]!
      let best := match st.accept with
        | some rule => some (rule, charsSoFar, p)
        | none => best
      if h : p = s.endPos then best
      else
        let c := p.get h
        match st.stepChar c with
        | some next => scanStrGo dfa fuel next (p.next h) (charsSoFar + 1) best
        | none => best

/-- Longest accepting prefix of `s` starting at position `start`, over a `String`
    read by the dependent `String.Pos` cursor. Returns `(rule, charLen, endPos)`:
    the winning rule, the number of characters it consumed, and the position just
    past the match. `none` if no non-empty prefix matches. The runtime analog of
    `scan`; see `Lexer/StringScan.lean` for agreement with `scan`.

    `fuel` is `s.utf8ByteSize + 1`; each UTF-8 character is at least one byte, so
    the byte size bounds the remaining character count, and computing it is O(1)
    (unlike `s.toList.length`, which would make each call — hence the tokenizer —
    quadratic). -/
def scanStr {s : String} (dfa : DFA) (start : s.Pos) :
    Option (Nat × Nat × s.Pos) :=
  scanStrGo dfa (s.utf8ByteSize + 1) 0 start 0 none

end DFA

/-! ### Flat state×class table scanner (the fast runtime object, docs/DESIGN.md §9.7 step 1)

Profiling (`LEXOPT_NOTES.md`) shows the scan is ~87% of lex-only time and the
per-character cost is `DState.stepChar`: `Array.findSome?` over the state's edges,
each doing `CharClass.mem` (a `List` range scan). Replacing that per-character work
with two array reads — one `classOf : Char → classId`, one flat
`state × classId → target` lookup — is ~2.2x faster on the scan on Cedar
(measured, with the emitted `(rule,len)` sequence identical to `DFA.scan`).

`FlatDFA` is built from a `DFA` by an *untrusted* constructor (`DFA.flatOfDFA`). Its
agreement with `DFA.scan` (the specification) is established a-posteriori by a
Boolean validator (`Lexer/Validator.lean`) discharged per lexer with `native_decide`,
exactly like the parser's tables — so this representation is not on the trusted path
and its constructor need not be proved correct. -/

/-- A flattened DFA: a global alphabet partition into `nClasses` half-open intervals
    (`bounds[i]..bounds[i+1]`), an ASCII fast-path class table, and flat
    `state × class` transition and per-state accept arrays.

    * `bounds` is sorted, starts at `0`, ends at `maxCodePoint + 1`, size `nClasses+1`.
    * `ascii[b]` (for `b < 128`) is the class of code point `b`.
    * `trans[s * nClasses + ci]` is `target + 1`, or `0` for a dead (no) edge.
    * `accept[s]` is the winning rule index, or `-1` if non-accepting. -/
structure FlatDFA where
  /-- Sorted class boundaries, size `nClasses + 1`. -/
  bounds : Array Nat
  /-- Number of alphabet classes. -/
  nClasses : Nat
  /-- Number of states (state 0 is the start). -/
  nStates : Nat
  /-- ASCII fast-path: `ascii[b]` = class of code point `b`, for `b < 128`. -/
  ascii : Array Nat
  /-- Flat transition table: `trans[s*nClasses+ci]` = target+1 (0 = dead). -/
  trans : Array Nat
  /-- Per-state accept rule index, or `-1`. -/
  accept : Array Int
  deriving Inhabited

namespace FlatDFA

/-- Binary search step: the largest index `i ∈ [lo, hi]` with `bounds[i] ≤ n`,
    assuming `bounds[lo] ≤ n` and the search window `[lo, hi]`. Explicit
    well-founded recursion on `hi - lo` (provable, unlike an `Id.run` while-loop). -/
def bsearch (bounds : Array Nat) (n lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if bounds.getD mid 0 ≤ n then bsearch bounds n mid hi
    else bsearch bounds n lo mid
  else lo
termination_by hi - lo
decreasing_by
  · -- mid < hi and mid > lo when lo+1<hi, so hi-mid < hi-lo
    simp_wf; omega
  · simp_wf; omega

/-- The class of a code point by binary search over `bounds`: the largest `i` with
    `bounds[i] ≤ n`. -/
def classOfNat (f : FlatDFA) (n : Nat) : Nat :=
  bsearch f.bounds n 0 (f.bounds.size - 1)

/-- The class of a character: an O(1) ASCII table lookup for `< 128`, else the
    binary search. -/
@[inline] def classOf (f : FlatDFA) (c : Char) : Nat :=
  let n := c.toNat
  if n < 128 then f.ascii.getD n 0 else f.classOfNat n

/-- The flat step: the target state for character `c` from state `sid`, or `none`
    (dead). Mirrors `DState.stepChar` but by two array reads. -/
@[inline] def step (f : FlatDFA) (sid : Nat) (c : Char) : Option Nat :=
  let ci := f.classOf c
  let t := f.trans.getD (sid * f.nClasses + ci) 0
  if t == 0 then none else some (t - 1)

/-- The accept rule of a state as an `Option`, from the `-1`-sentinel array. -/
@[inline] def acceptOf (f : FlatDFA) (sid : Nat) : Option Nat :=
  let a := f.accept.getD sid (-1)
  if a < 0 then none else some a.toNat

end FlatDFA

namespace DFA

/-- Untrusted: build a `FlatDFA` from a `DFA`. Boundaries are the sorted distinct
    endpoints of every edge class of every state (a global refinement of all edge
    classes), so `stepChar` is constant on each resulting class. Each `(state,
    class)` cell records the DFA's transition target; the ASCII table caches the
    class of every code point `< 128`. -/
def flatOfDFA (dfa : DFA) : FlatDFA := Id.run do
  -- Collect boundaries. Use the RAW range endpoints of each edge class (`lo`, `hi+1`)
  -- — the same cut points the validator's `intervalConst` checks (`CharClass.mem`
  -- changes value only at a raw endpoint, whether or not the class is negated) — plus
  -- `0` and `maxCodePoint+1`. This makes every flat class endpoint-free for every edge
  -- class, so `stepChar` is constant on it.
  let mut bs : Array Nat := #[0, maxCodePoint + 1]
  for st in dfa.states do
    for e in st.trans do
      for (lo, hi) in e.cls.rs do
        bs := bs.push lo
        bs := bs.push (hi + 1)
  let sorted := bs.qsort (· < ·)
  let mut bounds : Array Nat := #[]
  for p in sorted do
    if p ≤ maxCodePoint + 1 && (bounds.isEmpty || bounds.back! != p) then
      bounds := bounds.push p
  let nClasses := bounds.size - 1
  let nStates := dfa.states.size
  -- classOf by binary search over the frozen bounds
  let classOfN := fun (n : Nat) => Id.run do
    let mut lo := 0
    let mut hi := bounds.size - 1
    while lo + 1 < hi do
      let mid := (lo + hi) / 2
      if bounds[mid]! ≤ n then lo := mid else hi := mid
    pure lo
  -- flat transition + accept tables
  let mut trans : Array Nat := Array.replicate (nStates * nClasses) 0
  let mut accept : Array Int := Array.replicate nStates (-1)
  for sid in [0:nStates] do
    let st := dfa.states[sid]!
    match st.accept with
    | some r => accept := accept.set! sid (Int.ofNat r)
    | none => pure ()
    for e in st.trans do
      for (lo, hi) in classIntervals e.cls do
        let mut ci := classOfN lo
        while ci < nClasses && bounds[ci]! ≤ hi do
          if bounds[ci+1]! - 1 ≤ hi then
            trans := trans.set! (sid * nClasses + ci) (e.target + 1)
          ci := ci + 1
  let ascii : Array Nat := (Array.range 128).map classOfN
  return { bounds := bounds, nClasses := nClasses, nStates := nStates,
           ascii := ascii, trans := trans, accept := accept }

/-! ### Flat scanning over an `Array Char`

The input is decoded to an `Array Char` once (`String.toList.toArray`), then scanned
by index. This mirrors `DFA.scan`'s `go` recursion so the agreement proof
(`Lexer/Validator.lean`) relates `flatScanArrGo` to `scan` on the character list.
`scan` (the `List Char` spec) is unchanged. -/

/-- One flat DFA walk over `cs` from index `i`, recording the last accept. Mirrors
    `scan.go` with `FlatDFA.step`/`acceptOf` in place of `DState.stepChar`/`accept`.
    `fuel` bounds the walk (structurally terminating). -/
def flatScanArrGo (f : FlatDFA) (cs : Array Char) :
    Nat → Nat → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, _, _, best => best
  | fuel + 1, sid, i, best =>
      let best := match f.acceptOf sid with
        | some rule => some (rule, i)
        | none => best
      if h : i < cs.size then
        match f.step sid cs[i] with
        | some next => flatScanArrGo f cs fuel next (i + 1) best
        | none => best
      else best

/-- Longest accepting prefix of `cs` from index `start`, using the flat table.
    `fuel = cs.size + 1 - start`. Returns `(rule, endIndex)`. -/
def flatScanArr (f : FlatDFA) (cs : Array Char) (start : Nat) : Option (Nat × Nat) :=
  flatScanArrGo f cs (cs.size + 1 - start) 0 start none

/-! ### Flat scanning over a `String` by `String.Pos` (the fast runtime scanner)

`flatScanArr` above walks an `Array Char` (so the tokenizer must decode `input.toList`
first). `flatScanStr` does the same flat-table walk over a `String` directly by its
`String.Pos` cursor, exactly like `scanStr` but with `FlatDFA.step`/`acceptOf` in place
of `DState.stepChar`/`accept`. This avoids the `toList` decode and lets the tokenizer
slice the lexeme with `String.extract` (a byte copy). It agrees with `scanStr`
(`Lexer/FlatScan.lean`, `flatScanStr_eq_scanStr`), which already agrees with `scan`. -/

/-- One flat DFA walk over `s` from position `p`, recording the last accept. Mirrors
    `scanStrGo` with `FlatDFA.step`/`acceptOf`. -/
def flatScanStrGo {s : String} (f : FlatDFA) :
    Nat → Nat → s.Pos → Nat → Option (Nat × Nat × s.Pos) → Option (Nat × Nat × s.Pos)
  | 0, _, _, _, best => best
  | fuel + 1, sid, p, charsSoFar, best =>
      let best := match FlatDFA.acceptOf f sid with
        | some rule => some (rule, charsSoFar, p)
        | none => best
      if h : p = s.endPos then best
      else
        let c := p.get h
        match FlatDFA.step f sid c with
        | some next => flatScanStrGo f fuel next (p.next h) (charsSoFar + 1) best
        | none => best

/-- The result of a scan: no accepting prefix, or the rule, the number of characters,
    and the end position of the longest one. One constructor with three fields,
    instead of `Option (Nat × Nat × s.Pos)`, which allocates a `some` and two pairs. -/
inductive ScanRes (s : String) where
  | miss : ScanRes s
  | hit (rule len : Nat) (endPos : s.Pos) : ScanRes s

namespace ScanRes

/-- The `Option` form the specification (`scanStr`) uses. -/
def toOption {s : String} : ScanRes s → Option (Nat × Nat × s.Pos)
  | .miss => none
  | .hit r l e => some (r, l, e)

/-- Eliminator used by the tokenizers, so that proofs can rewrite it to a `match` on
    the `Option` form. -/
@[inline] def elim {s : String} {α : Sort _} (r : ScanRes s)
    (hit : Nat → Nat → s.Pos → α) (miss : α) : α :=
  match r with
  | .miss => miss
  | .hit a b c => hit a b c

theorem elim_eq {s : String} {α : Sort _} (r : ScanRes s) (hit : Nat → Nat → s.Pos → α)
    (miss : α) :
    r.elim hit miss = match r.toOption with
      | some (a, b, c) => hit a b c
      | none => miss := by
  cases r <;> rfl

end ScanRes

/-- The best accepting prefix, from its unpacked fields: rule `r` (negative for none),
    `c` characters, ending at `q`. -/
@[inline] def packBest {s : String} (r : Int) (c : Nat) (q : s.Pos) : ScanRes s :=
  if r < 0 then .miss else .hit r.toNat c q

/-- `flatScanStrGo` with the best match carried as three loose arguments instead of an
    `Option (Nat × Nat × s.Pos)`. The packed form allocates a `some` and two tuples at
    every accepting state, which is every character of an identifier or number; this
    form allocates nothing in the loop. `flatScanStrGoU_eq` proves it equal. -/
def flatScanStrGoU {s : String} (f : FlatDFA) :
    Nat → Nat → s.Pos → Nat → Int → Nat → s.Pos → ScanRes s
  | 0, _, _, _, r, c, q => packBest r c q
  | fuel + 1, sid, p, chars, r, c, q =>
      let a := f.accept.getD sid (-1)
      let r' := if a < 0 then r else a
      let c' := if a < 0 then c else chars
      let q' := if a < 0 then q else p
      if h : p = s.endPos then packBest r' c' q'
      else
        let ch := p.get h
        match FlatDFA.step f sid ch with
        | some next => flatScanStrGoU f fuel next (p.next h) (chars + 1) r' c' q'
        | none => packBest r' c' q'

theorem flatScanStrGoU_eq {s : String} (f : FlatDFA) :
    ∀ (fuel sid : Nat) (p : s.Pos) (chars : Nat) (r : Int) (c : Nat) (q : s.Pos)
      (best : Option (Nat × Nat × s.Pos)), best = (packBest r c q).toOption →
      (flatScanStrGoU f fuel sid p chars r c q).toOption
        = flatScanStrGo f fuel sid p chars best := by
  intro fuel
  induction fuel with
  | zero => intro sid p chars r c q best h; rw [h]; rfl
  | succ fuel ih =>
    intro sid p chars r c q best h
    rw [flatScanStrGoU, flatScanStrGo]
    have hb : (match FlatDFA.acceptOf f sid with
        | some rule => some (rule, chars, p)
        | none => best) =
        (packBest (if f.accept.getD sid (-1) < 0 then r else f.accept.getD sid (-1))
          (if f.accept.getD sid (-1) < 0 then c else chars)
          (if f.accept.getD sid (-1) < 0 then q else p)).toOption := by
      unfold FlatDFA.acceptOf
      by_cases ha : f.accept.getD sid (-1) < 0
      · simp only [ha, ite_true]; exact h
      · simp only [ha, ite_false]
        unfold packBest
        have ha' : ¬ (f.accept.getD sid (-1) < 0) := ha
        simp only [ha', ite_false]
        rfl
    simp only [hb]
    by_cases hend : p = s.endPos
    · simp only [hend, dite_true]
    · simp only [hend, dite_false]
      cases FlatDFA.step f sid (p.get hend) with
      | none => rfl
      | some next => exact ih next (p.next hend) (chars + 1) _ _ _ _ rfl

/-- Longest accepting prefix of `s` from `start`, over a `String` by its `String.Pos`
    cursor, using the flat tables. The fast runtime analog of `scanStr`; the
    tokenizers call this and match on the result directly. -/
def flatScanStrR {s : String} (f : FlatDFA) (start : s.Pos) : ScanRes s :=
  flatScanStrGoU f (s.utf8ByteSize + 1) 0 start 0 (-1) 0 start

/-- The `Option` form of `flatScanStrR`, which the proofs use. -/
def flatScanStr {s : String} (f : FlatDFA) (start : s.Pos) :
    Option (Nat × Nat × s.Pos) :=
  (flatScanStrR f start).toOption

/-- The runtime scanner is the specification walk `flatScanStrGo` from the empty best. -/
theorem flatScanStr_eq_go {s : String} (f : FlatDFA) (start : s.Pos) :
    flatScanStr f start = flatScanStrGo f (s.utf8ByteSize + 1) 0 start 0 none :=
  flatScanStrGoU_eq f _ _ _ _ _ _ _ _ rfl

end DFA

end Lexer
