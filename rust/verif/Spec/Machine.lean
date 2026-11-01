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

import Spec.Tables
import Spec.Fuel

/-!
The loop of `lpg_kernel::parse`, as a Lean function on lists and numbers.

`mstep` is one iteration of the Rust loop, written the same way (same tests, same order,
same values), with the tables read through `RustTables`. `Spec/MachineSim.lean` proves that it
refines `Exec.step`; `Kernel/ParseBody.lean` proves that the extracted Rust loop body is
`mstep`. Splitting the proof there keeps the semantic argument (lists, no panics, no
overflows) apart from the argument about the Aeneas translation (vectors, casts, bounds).

Numbers are `Nat`s: the proof about the Rust shows that none of them overflows.
-/

namespace Spec

open Runtime.Exec

/-- A cell of the parse stack. -/
structure MEntry where
  state : Nat
  start : Nat
  deriving DecidableEq, Repr

/-- A node of the trace. -/
structure MNode where
  kind : Nat
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- A token, as the kernel reads it. -/
structure MTok where
  term : Nat
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- The variables of the Rust loop. `stack` and `nodes` are in the order of the vectors
    (bottom, and first, first). -/
structure MState where
  stack : List MEntry
  nodes : List MNode
  ti : Nat
  prevEnd : Nat
  state : Nat

/-- How a run ends. -/
inductive MStop where
  | ok
  | err (token state term : Nat)
  deriving DecidableEq, Repr

/-- `TERM_INCONSISTENT` and `TERM_OUT_OF_FUEL` of the kernel. -/
def termInconsistent : Nat := 65535
def termOutOfFuel : Nat := 65534

/-- What the kernel is called with: the tables, the number of terminals and the tokens. -/
structure MConf where
  tables : RustTables
  nt : Nat
  toks : List MTok

/-- The initial variables: the stack holds the entry of state 0. -/
def MState.init : MState :=
  { stack := [⟨0, 0⟩], nodes := [], ti := 0, prevEnd := 0, state := 0 }

/-- The outcome of an iteration: the next variables, or the end of the run with the final
    stack and nodes. -/
abbrev MRes := MState ⊕ (MStop × List MEntry × List MNode)

/-- The lookahead: the token at `ti`, or the end-of-input terminal at the previous end. -/
def MConf.look (c : MConf) (m : MState) : MTok :=
  (c.toks[m.ti]?).getD ⟨c.tables.eof, m.prevEnd, m.prevEnd⟩

/-- The part of an iteration that reduces by `prod`. -/
def mreduce (c : MConf) (m : MState) (prod : Nat) : MRes :=
  let n := c.tables.rhsLen prod
  if n ≥ m.stack.length then
    .inr (.err m.ti m.state termInconsistent, m.stack, m.nodes)
  else
    let base := m.stack.length - n
    let start := if n > 0 then (m.stack.getD base ⟨0, 0⟩).start else m.prevEnd
    let stack1 := m.stack.take base
    let top := (stack1.getD (base - 1) ⟨0, 0⟩).state
    let g := c.tables.goto top (c.tables.lhs prod)
    let nodes1 := m.nodes ++ [⟨prodFlag + prod, start, m.prevEnd⟩]
    if g = noneCell then
      .inr (.ok, stack1, nodes1)
    else
      .inl { m with stack := stack1 ++ [⟨g, start⟩], nodes := nodes1, state := g }

/-- One iteration of the loop of `lpg_kernel::parse` (without the fuel). -/
def mstep (c : MConf) (m : MState) : MRes :=
  let dr := c.tables.defaultReduce m.state
  if dr ≠ noneCell then
    mreduce c m dr
  else
    let la := c.look m
    if la.term ≥ c.nt then
      .inr (.err m.ti m.state la.term, m.stack, m.nodes)
    else
      let a := c.tables.action m.state la.term
      if a = 0 then
        .inr (.err m.ti m.state la.term, m.stack, m.nodes)
      else if a % 2 = 1 then
        .inl { stack := m.stack ++ [⟨a / 2, la.start⟩]
               nodes := m.nodes ++ [⟨la.term, la.start, la.stop⟩]
               ti := m.ti + 1
               prevEnd := la.stop
               state := a / 2 }
      else
        mreduce c m (a / 2 - 1)

/-- The loop with `n` units of fuel. -/
def mrunN (c : MConf) : Nat → MState → MStop × List MEntry × List MNode
  | 0, m => (.err m.ti m.state termOutOfFuel, m.stack, m.nodes)
  | n + 1, m =>
    match mstep c m with
    | .inl m' => mrunN c n m'
    | .inr out => out

/-- One iteration of the loop with its fuel check: out of fuel, or the next variables and the
    remaining fuel, or the end of the run. This is the body of the Rust loop. -/
def mbody (c : MConf) (f : Nat) (m : MState) : (MState × Nat) ⊕ (MStop × List MEntry × List MNode) :=
  if f = 0 then
    .inr (.err m.ti m.state termOutOfFuel, m.stack, m.nodes)
  else
    match mstep c m with
    | .inl m' => .inl (m', f - 1)
    | .inr out => .inr out

theorem mrunN_eq (c : MConf) (f : Nat) (m : MState) :
    mrunN c f m =
      match mbody c f m with
      | .inl (m', f') => mrunN c f' m'
      | .inr out => out := by
  cases f with
  | zero => simp [mrunN, mbody]
  | succ n =>
    simp only [mrunN, mbody]
    cases mstep c m <;> simp

/-! ### `mbody` and `mstep` by cases -/

section
variable {c : MConf} {m : MState}

theorem mbody_zero (f : Nat) (h : f = 0) :
    mbody c f m = .inr (.err m.ti m.state termOutOfFuel, m.stack, m.nodes) := by
  simp [mbody, h]

theorem mbody_pos (f : Nat) (h : f ≠ 0) :
    mbody c f m =
      match mstep c m with
      | .inl m' => .inl (m', f - 1)
      | .inr out => .inr out := by
  simp [mbody, h]

theorem mstep_default (h : c.tables.defaultReduce m.state ≠ noneCell) :
    mstep c m = mreduce c m (c.tables.defaultReduce m.state) := by
  simp [mstep, h]

theorem mstep_term (h : c.tables.defaultReduce m.state = noneCell)
    (ht : (c.look m).term ≥ c.nt) :
    mstep c m = .inr (.err m.ti m.state (c.look m).term, m.stack, m.nodes) := by
  simp [mstep, h, ht]

theorem mstep_error (h : c.tables.defaultReduce m.state = noneCell)
    (ht : ¬ (c.look m).term ≥ c.nt) (ha : c.tables.action m.state (c.look m).term = 0) :
    mstep c m = .inr (.err m.ti m.state (c.look m).term, m.stack, m.nodes) := by
  simp [mstep, h, ht, ha]

theorem mstep_shift (h : c.tables.defaultReduce m.state = noneCell)
    (ht : ¬ (c.look m).term ≥ c.nt) (ha : c.tables.action m.state (c.look m).term ≠ 0)
    (hodd : c.tables.action m.state (c.look m).term % 2 = 1) :
    mstep c m = .inl { stack := m.stack ++ [⟨c.tables.action m.state (c.look m).term / 2,
                                              (c.look m).start⟩]
                       nodes := m.nodes ++ [⟨(c.look m).term, (c.look m).start, (c.look m).stop⟩]
                       ti := m.ti + 1
                       prevEnd := (c.look m).stop
                       state := c.tables.action m.state (c.look m).term / 2 } := by
  simp [mstep, h, ht, ha, hodd]

theorem mstep_reduce (h : c.tables.defaultReduce m.state = noneCell)
    (ht : ¬ (c.look m).term ≥ c.nt) (ha : c.tables.action m.state (c.look m).term ≠ 0)
    (heven : ¬ c.tables.action m.state (c.look m).term % 2 = 1) :
    mstep c m = mreduce c m (c.tables.action m.state (c.look m).term / 2 - 1) := by
  simp [mstep, h, ht, ha, heven]

end

end Spec
