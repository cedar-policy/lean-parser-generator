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

import Spec.Trace

/-!
What the Rust parser tables mean.

The Rust kernel (`rust/lpg-kernel`) reads its tables as numbers: an action cell is 0 for an
error, `(target << 1) | 1` for a shift and `(production + 1) << 1` for a reduce; a goto or
default-reduce cell is `NONE = 65535` when absent. `RustTables` is those numbers as functions
(a proof instantiates it with the extracted arrays), and `RustTables.exec` is the
`Runtime.Exec.ExecTable` they denote.

The Lean tables that the generator writes use only `Act.shift`, `Act.reduce` and `Act.error`
(`Emit/Codegen.lean`), so the encoding loses nothing. A missing goto is an accept, in
`Exec.reduce` and in the kernel.

`Event.code` is the number the kernel stores in a trace node: the terminal for a shifted
token, and `PROD_FLAG | production` for a reduction.
-/

namespace Spec

open Runtime.Exec

/-- The cell value for "no entry" in the goto and default-reduce tables. -/
def noneCell : Nat := 65535

/-- The flag bit of a production in a trace node. -/
def prodFlag : Nat := 0x8000

/-- Decode an action cell. -/
def decodeAct (cell : Nat) : Act :=
  if cell = 0 then .error
  else if cell % 2 = 1 then .shift (cell / 2)
  else .reduce (cell / 2 - 1)

/-- Decode a goto or default-reduce cell. -/
def decodeOpt (cell : Nat) : Option Nat :=
  if cell = noneCell then none else some cell

/-- The number a trace node stores for an event. For a production below `prodFlag`, setting
    the flag bit (the kernel's `PROD_FLAG | p`) is adding it. -/
def Event.code : Event → Nat
  | .tok t => t
  | .red p => prodFlag + p

theorem Event.code_injective {a b : Event}
    (ha : match a with | .tok t => t < prodFlag | .red p => p < prodFlag)
    (hb : match b with | .tok t => t < prodFlag | .red p => p < prodFlag)
    (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp [Event.code, prodFlag] at * <;> omega

/-- The parser tables as numbers, as the kernel reads them. -/
structure RustTables where
  numStates : Nat
  /-- The terminal the parser reads when the tokens run out. -/
  eof : Nat
  /-- `ACTION[state][terminal]` -/
  action : Nat → Nat → Nat
  /-- `GOTO[state][nonterminal]` -/
  goto : Nat → Nat → Nat
  /-- `DEFAULT_REDUCE[state]` -/
  defaultReduce : Nat → Nat
  /-- `LHS[production]` -/
  lhs : Nat → Nat
  /-- `RHS_LEN[production]` -/
  rhsLen : Nat → Nat

variable {V : Type}

/-- The `ExecTable` that `r` denotes, with semantic actions `sem` and end-of-input value
    `eofv`. The start state is 0, as in the kernel. -/
def RustTables.exec (r : RustTables) (eofv : V) (sem : Nat → List V → V) : ExecTable V where
  numStates := r.numStates
  startState := 0
  eof := (r.eof, eofv)
  action := fun s t => decodeAct (r.action s t)
  goto := fun s n => decodeOpt (r.goto s n)
  defaultReduce := fun s => decodeOpt (r.defaultReduce s)
  prodLhs := r.lhs
  prodRhsLen := r.rhsLen
  sem := sem

/-- The decoded tables never contain an accept action. -/
theorem decodeAct_ne_accept (cell : Nat) : decodeAct cell ≠ .accept := by
  unfold decodeAct
  split
  · intro h; cases h
  · split <;> intro h <;> cases h

end Spec
