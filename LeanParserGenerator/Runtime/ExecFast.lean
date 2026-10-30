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
public import LeanParserGenerator.Runtime.Exec
public import LeanParserGenerator.Runtime.Span

/-!
The allocation-lean LR engine that generated parsers run.

`Exec.run` (over `ExecTable`) stays the specification. The engine here computes the
same result with fewer allocations per step (docs/DESIGN.md §13):

* The stack is a generated type `S`, a cons list with one cell constructor per
  semantic type. A cell holds the state, the two span offsets, and the unwrapped
  semantic value as fields. The specification stack is `List (Nat × (Span × V))`,
  which costs a cons, two pairs, a `Span` and a `V` box per cell. `StackOps.toList`
  maps a stack to the specification stack it represents.
* Tokens are read lazily from the `List (Positioned T)` the lexer produced: `term`
  gives the terminal index, and `StackOps.pushTok` pushes a token's cell. The
  specification runs on `input.map decode`, a second list as long as the input.
* The loop is one tail-recursive function on a `Nat` fuel. The specification
  iterates a `Result ⊕ (Stack × List)`-valued step with logarithmic fuel, so every
  step allocates a `Sum` and a `Prod`.
* A reduce is one call to the generated `fuse : Nat → S → S`, which matches the top
  cells, builds the semantic value, looks up the goto state, and returns the new
  stack. It returns the empty stack when it cannot (the shape does not match, or
  there is no goto, as on the augmented production). The engine then takes the
  slow path through `reduceInline`. A successful `fuse` result is never empty,
  because it pushes a cell.

The generator proves `StackOps.Lawful` and `FuseOK` for each grammar. Given them,
`runFast_eq_run` equals the specification, so every refinement theorem about
`Exec.run` transfers.
-/

@[expose] public section

namespace Runtime.Exec

variable {W T S : Type}

/-- The operations the engine needs on a generated stack type `S`, whose cells
carry semantic values of type `W` (the spec stack holds `Span × W`), for tokens of
type `T`. A class, so that the engine's `[StackOps W T S]` argument is specialized
away at the generated call site, instead of called through closures. -/
class StackOps (W T S : Type) where
  /-- The empty stack. -/
  nil : S
  /-- The decline marker: `fail stk` is returned by a fused reduce that cannot
      reduce `stk`. It carries `stk` so the engine can take the slow path without
      the caller keeping a second reference to the stack, which would prevent the
      fused reduce from reusing the cells it matches. -/
  fail : S → S
  /-- Whether the value is a decline marker. -/
  isFail : S → Bool
  /-- The stack inside a decline marker. -/
  unfail : S → S
  /-- The state on top, or the given start state when the stack is empty. -/
  top : Nat → S → Nat
  /-- Push a cell for a shifted token, in the given state. -/
  pushTok : Nat → Positioned T → S → S
  /-- Push a cell for the end-of-input value, in the given state. -/
  pushEof : Nat → S → S
  /-- The value on top, for `accept`. -/
  accept : S → Result (Span × W)
  /-- The specification stack this stack represents. -/
  toList : S → Stack (Span × W)
  /-- The inverse of `toList`, used by the slow reduce path. -/
  ofList : Stack (Span × W) → S

/-- The laws relating `StackOps` to the specification stack. `val` gives a token's
semantic value and `eofv` the end-of-input cell. -/
structure StackOps.Lawful (ops : StackOps W T S) (val : T → W) (eofv : Span × W) : Prop where
  toList_nil : ops.toList ops.nil = []
  isFail_fail : ∀ s, ops.isFail (ops.fail s) = true
  unfail_fail : ∀ s, ops.unfail (ops.fail s) = s
  top_eq : ∀ start s, ops.top start s =
    match ops.toList s with
    | [] => start
    | (st, _) :: _ => st
  pushTok_eq : ∀ st tok s,
    ops.toList (ops.pushTok st tok s) = (st, (tok.span, val tok.val)) :: ops.toList s
  pushEof_eq : ∀ st s, ops.toList (ops.pushEof st s) = (st, eofv) :: ops.toList s
  accept_eq : ∀ s, ops.accept s =
    match ops.toList s with
    | (_, v) :: _ => .ok v
    | [] => .err "accept on empty stack"
  toList_ofList : ∀ l, ops.toList (ops.ofList l) = l

theorem StackOps.Lawful.top_eq_flat {ops : StackOps W T S} {val : T → W} {eofv : Span × W}
    (hl : ops.Lawful val eofv) (f : FlatTable (Span × W)) (s : S) :
    ops.top f.startState s = f.topState (ops.toList s) := by
  rw [hl.top_eq]
  cases ops.toList s <;> rfl

/-- Push the goto cell `mk s'` for nonterminal `lhs` over `tl`, or return `fail` (the
decline marker, built by the caller around the original stack, and only on that path)
when the goto entry is missing. The generated `fuse<p>` calls this with the raw table
arrays, literal widths, and a constructor application for `mk`; it is inlined, so
`mk` is not allocated as a closure. -/
@[inline] def pushGotoWith (gotoData : Array (Option Nat)) (gotoWidth lhs top : Nat)
    (mk : Nat → S) (fail : Unit → S) : S :=
  match gotoData.getD (top * gotoWidth + lhs) none with
  | some s' => mk s'
  | none => fail ()

/-- `g` is a correct fused reduce for production `p`: it either declines, returning
a marker around its argument, or returns the stack `reduceInline` returns. -/
def FuseOKAt (ops : StackOps W T S) (f : FlatTable (Span × W)) (p : Nat) (g : S → S) : Prop :=
  ∀ stk : S,
    (ops.isFail (g stk) = true → ops.unfail (g stk) = stk) ∧
    (ops.isFail (g stk) = false →
      reduceInline f p (ops.toList stk) = .inr (ops.toList (g stk)))

/-- The obligation the engine needs: `fuse p` is correct for every `p`. -/
def FuseOK (ops : StackOps W T S) (f : FlatTable (Span × W)) (fuse : Nat → S → S) : Prop :=
  ∀ p, FuseOKAt ops f p (fuse p)

/-- The fused reduce that always declines. -/
@[inline] def fuseNone (ops : StackOps W T S) : S → S := fun stk => ops.fail stk

theorem fuseOKAt_none {ops : StackOps W T S} {val : T → W} {eofv : Span × W}
    (hl : ops.Lawful val eofv) (f : FlatTable (Span × W)) (p : Nat) :
    FuseOKAt ops f p (fuseNone ops) := by
  intro stk
  refine ⟨fun _ => hl.unfail_fail stk, fun h => ?_⟩
  have h' : ops.isFail (ops.fail stk) = false := h
  rw [hl.isFail_fail] at h'
  cases h'

/-- Dispatch on the production index: `fuseIf k a b p` is `a p` below `k` and `b p`
from `k` on. The generated `fuse` nests these into a balanced tree, so a reduce
reaches its `fuse<p>` after about `log₂ n` comparisons, with a direct call. (A `match`
on `Nat` literals compiles to a chain of up to `n` comparisons, and an array of
closures costs an indirect call.) -/
@[inline] def fuseIf (k : Nat) (a b : Nat → S → S) : Nat → S → S :=
  fun p => if p < k then a p else b p

/-- The leaf of the dispatch tree: `g` for production `q`, and no fused reduce for any
other index (the engine then takes the slow path). -/
@[inline] def fuseLeaf (ops : StackOps W T S) (q : Nat) (g : S → S) : Nat → S → S :=
  fun p => if p = q then g else fuseNone ops

theorem fuseOK_if {ops : StackOps W T S} {f : FlatTable (Span × W)} {k : Nat}
    {a b : Nat → S → S} (ha : FuseOK ops f a) (hb : FuseOK ops f b) :
    FuseOK ops f (fuseIf k a b) := by
  intro p
  unfold fuseIf
  by_cases h : p < k
  · simp only [h, ite_true]; exact ha p
  · simp only [h, ite_false]; exact hb p

theorem fuseOK_leaf {ops : StackOps W T S} {val : T → W} {eofv : Span × W}
    (hl : ops.Lawful val eofv) {f : FlatTable (Span × W)} {q : Nat} {g : S → S}
    (hg : FuseOKAt ops f q g) : FuseOK ops f (fuseLeaf ops q g) := by
  intro p
  unfold fuseLeaf
  by_cases h : p = q
  · subst h; simp only [ite_true]; exact hg
  · simp only [h, ite_false]; exact fuseOKAt_none hl f p

/-- The shared shape of the per-production proofs. If `popN`+`sem` on `stk` give the
cell `(⟨b, e⟩, v)` over `rest`, and `mk s'` is that cell in state `s'` over `rest`
(never a decline marker), then the fused reduce
`pushGotoWith … (top rest) mk (fail stk)` is correct for `stk`. -/
theorem fuseOKAt_of_pop {ops : StackOps W T S} {val : T → W} {eofv : Span × W}
    (hl : ops.Lawful val eofv) (f : FlatTable (Span × W)) (p : Nat) (stk rest : S)
    (b e : String.Pos.Raw) (v : W) (mk : Nat → S)
    (hred : popNsem f p (ops.toList stk) = some ((⟨b, e⟩, v), ops.toList rest))
    (hmk : ∀ s', ops.toList (mk s') = (s', (⟨b, e⟩, v)) :: ops.toList rest)
    (hmkf : ∀ s', ops.isFail (mk s') = false) :
    (ops.isFail (pushGotoWith f.gotoData f.gotoWidth (f.lhsData.getD p 0)
        (ops.top f.startState rest) mk (fun _ => ops.fail stk)) = true →
      ops.unfail (pushGotoWith f.gotoData f.gotoWidth (f.lhsData.getD p 0)
        (ops.top f.startState rest) mk (fun _ => ops.fail stk)) = stk) ∧
    (ops.isFail (pushGotoWith f.gotoData f.gotoWidth (f.lhsData.getD p 0)
        (ops.top f.startState rest) mk (fun _ => ops.fail stk)) = false →
      reduceInline f p (ops.toList stk) =
        .inr (ops.toList (pushGotoWith f.gotoData f.gotoWidth (f.lhsData.getD p 0)
          (ops.top f.startState rest) mk (fun _ => ops.fail stk)))) := by
  unfold pushGotoWith
  generalize hg : f.gotoData.getD (ops.top f.startState rest * f.gotoWidth +
    f.lhsData.getD p 0) none = g
  cases g with
  | none =>
    refine ⟨fun _ => hl.unfail_fail stk, fun h => ?_⟩
    rw [hl.isFail_fail] at h
    cases h
  | some s' =>
    refine ⟨fun h => ?_, fun _ => ?_⟩
    · rw [hmkf] at h; cases h
    unfold reduceInline
    unfold popNsem at hred
    cases hp : popN (f.lenData.getD p 0) (ops.toList stk) with
    | none => rw [hp] at hred; cases hred
    | some r =>
      obtain ⟨args, stk'⟩ := r
      rw [hp] at hred
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hred
      obtain ⟨hsem, hrest⟩ := hred
      simp only [hsem, hrest, ← hl.top_eq_flat, hg]
      rw [hmk]

/-- Reduce by `p`: try the generated `fuse`, and fall back to `reduceInline` on the
original stack when it declines, passing the new stack to `k`. -/
@[inline] def reduceFast [ops : StackOps W T S] (f : FlatTable (Span × W))
    (fuse : Nat → S → S) (p : Nat) (stk : S) (k : S → Result (Span × W)) :
    Result (Span × W) :=
  let r := fuse p stk
  if ops.isFail r then
    match reduceInline f p (ops.toList (ops.unfail r)) with
    | .inl x => x
    | .inr l => k (ops.ofList l)
  else k r

/-- The engine loop. `fuel` counts parser steps; running out gives `.timeout`. -/
@[specialize] def goFast [ops : StackOps W T S] (f : FlatTable (Span × W))
    (fuse : Nat → S → S) (term : T → Nat) :
    Nat → S → List (Positioned T) → Result (Span × W)
  | 0, _, _ => .timeout
  | fuel + 1, stk, input =>
    let s := ops.top f.startState stk
    match f.defRedData.getD s none with
    | some p =>
      reduceFast (ops := ops) f fuse p stk (fun stk' => goFast f fuse term fuel stk' input)
    | none =>
      let t := match input with
        | [] => f.eof.1
        | tok :: _ => term tok.val
      match f.actionData.getD (s * f.actWidth + t) .error with
      | .shift s' =>
        match input with
        | [] => goFast f fuse term fuel (ops.pushEof s' stk) []
        | tok :: rest => goFast f fuse term fuel (ops.pushTok s' tok stk) rest
      | .reduce p =>
        reduceFast (ops := ops) f fuse p stk (fun stk' => goFast f fuse term fuel stk' input)
      | .accept => ops.accept stk
      | .error => .reject s t

/-- Run the engine; at most `2^logNSteps` steps, as `Exec.run`. -/
@[inline] def runFast [ops : StackOps W T S] (f : FlatTable (Span × W))
    (fuse : Nat → S → S) (term : T → Nat) (input : List (Positioned T))
    (logNSteps : Nat := 20) : Result (Span × W) :=
  goFast f fuse term (2 ^ logNSteps) ops.nil input

/-! ### Correctness -/

/-- The token the specification sees: `decode` of a positioned token. -/
def decodeWith (term : T → Nat) (val : T → W) (pt : Positioned T) : Nat × (Span × W) :=
  (term pt.val, (pt.span, val pt.val))

/-- `k` steps of `stepInline`, stopping early on a result. -/
def iterInline (f : FlatTable V) : Nat → Stack V → List (Nat × V) →
    Result V ⊕ (Stack V × List (Nat × V))
  | 0, stk, input => .inr (stk, input)
  | k + 1, stk, input =>
    match stepInline f stk input with
    | .inl r => .inl r
    | .inr (stk', input') => iterInline f k stk' input'

theorem iterInline_add (f : FlatTable V) (a b : Nat) (stk : Stack V) (input : List (Nat × V)) :
    iterInline f (a + b) stk input =
      match iterInline f a stk input with
      | .inl r => .inl r
      | .inr (stk', input') => iterInline f b stk' input' := by
  induction a generalizing stk input with
  | zero => simp [iterInline]
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [iterInline]
    cases stepInline f stk input with
    | inl r => rfl
    | inr r => obtain ⟨stk', input'⟩ := r; exact ih stk' input'

theorem parseFixInline_eq_iter (f : FlatTable V) (logN : Nat) (stk : Stack V)
    (input : List (Nat × V)) :
    parseFixInline f stk input logN = iterInline f (2 ^ logN) stk input := by
  induction logN generalizing stk input with
  | zero =>
    simp only [parseFixInline, Nat.pow_zero, iterInline]
    cases stepInline f stk input with
    | inl r => rfl
    | inr r => obtain ⟨stk', input'⟩ := r; rfl
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [Nat.pow_succ]; omega, iterInline_add]
    simp only [parseFixInline, ih]
    cases iterInline f (2 ^ n) stk input with
    | inl r => rfl
    | inr r => obtain ⟨stk', input'⟩ := r; rfl

section Proofs
variable (ops : StackOps W T S) (f : FlatTable (Span × W)) (fuse : Nat → S → S)
  (term : T → Nat) (val : T → W)
  (hl : ops.Lawful val f.eof.2) (hfuse : FuseOK ops f fuse)
include hl hfuse

theorem reduceFast_eq (p : Nat) (stk : S) (k : S → Result (Span × W))
    (k' : Stack (Span × W) → Result (Span × W)) (hk : ∀ s, k s = k' (ops.toList s)) :
    reduceFast (ops := ops) f fuse p stk k =
      match reduceInline f p (ops.toList stk) with
      | .inl r => r
      | .inr l => k' l := by
  unfold reduceFast
  dsimp only
  obtain ⟨h1, h2⟩ := hfuse p stk
  cases hn : ops.isFail (fuse p stk) with
  | true =>
    simp only [ite_true]
    rw [h1 hn]
    cases reduceInline f p (ops.toList stk) with
    | inl r => rfl
    | inr l => show k (ops.ofList l) = k' l; rw [hk, hl.toList_ofList]
  | false =>
    rw [h2 hn]
    simp only [Bool.false_eq_true, ite_false]
    exact hk _

theorem goFast_eq (fuel : Nat) (stk : S) (input : List (Positioned T)) :
    goFast (ops := ops) f fuse term fuel stk input =
      match iterInline f fuel (ops.toList stk) (input.map (decodeWith term val)) with
      | .inl r => r
      | .inr _ => .timeout := by
  induction fuel generalizing stk input with
  | zero => simp [goFast, iterInline]
  | succ n ih =>
    unfold goFast
    simp only [iterInline, stepInline, hl.top_eq_flat]
    cases hd : f.defRedData.getD (f.topState (ops.toList stk)) none with
    | some p =>
      dsimp only
      rw [reduceFast_eq ops f fuse val hl hfuse p stk _
        (fun l => match iterInline f n l (input.map (decodeWith term val)) with
          | .inl r => r | .inr _ => .timeout) (fun s => ih s input)]
      cases reduceInline f p (ops.toList stk) <;> rfl
    | none =>
      dsimp only
      cases input with
      | nil =>
        simp only [List.map_nil, List.getD_nil, List.drop_nil]
        cases ha : f.actionData.getD (f.topState (ops.toList stk) * f.actWidth + f.eof.fst)
            .error with
        | shift s' => simp only [ih, hl.pushEof_eq, List.map_nil]
        | reduce p =>
          show reduceFast (ops := ops) f fuse p stk _ = _
          rw [reduceFast_eq ops f fuse val hl hfuse p stk _
            (fun l => match iterInline f n l (List.map (decodeWith term val) []) with
              | .inl r => r | .inr _ => .timeout) (fun s => ih s [])]
          dsimp only
          cases reduceInline f p (ops.toList stk) <;> rfl
        | accept => rw [hl.accept_eq]; cases ops.toList stk <;> rfl
        | error => rfl
      | cons tok rest =>
        simp only [List.map_cons, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero,
          decodeWith]
        cases ha : f.actionData.getD (f.topState (ops.toList stk) * f.actWidth + term tok.val)
            .error with
        | shift s' => simp only [ih, hl.pushTok_eq, List.map_cons, decodeWith]
        | reduce p =>
          show reduceFast (ops := ops) f fuse p stk _ = _
          rw [reduceFast_eq ops f fuse val hl hfuse p stk _
            (fun l => match iterInline f n l (List.map (decodeWith term val) (tok :: rest)) with
              | .inl r => r | .inr _ => .timeout) (fun s => ih s (tok :: rest))]
          dsimp only
          cases reduceInline f p (ops.toList stk) <;> rfl
        | accept => rw [hl.accept_eq]; cases ops.toList stk <;> rfl
        | error => rfl

/-- **The fast engine equals the specification.** With `decodeWith term val` as the
token decoder, `runFast` returns exactly `Exec.run` of the closure table. -/
theorem runFast_eq_run (input : List (Positioned T)) (logNSteps : Nat) :
    runFast (ops := ops) f fuse term input logNSteps =
      run f.toExecTable (input.map (decodeWith term val)) logNSteps := by
  rw [← runInline_eq_run]
  unfold runFast runInline
  rw [goFast_eq ops f fuse term val hl hfuse, parseFixInline_eq_iter, hl.toList_nil]
  cases iterInline f (2 ^ logNSteps) [] (input.map (decodeWith term val)) <;> rfl

end Proofs

end Runtime.Exec
