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

import Lake
open Lake DSL

/-- Proofs that the Rust backend agrees with the Lean specification.

This is a separate package from the generator because it needs Aeneas, and through it
Mathlib, which the generator does not. Nothing in the generator's own build depends on it.

The Rust kernel (`../lpg-kernel`) is translated to Lean by Charon and Aeneas
(`leanparsergenerator --rust-extract-kernel ../lpg-kernel Kernel`); the translation is
checked in, so building this package needs neither tool. It is proved against the Lean runtime
(`LeanParserGenerator.Runtime`, `LeanParserGenerator.Lexer`) once. A grammar's proof package,
which `%option gen_rust_verif` writes, requires this one and translates the grammar's crate
with the kernel as an external dependency (docs/RUST_VERIFICATION.md). -/
package «LeanParserGeneratorVerif» where
  leanOptions := #[
    ⟨`weak.linter.unusedVariables, false⟩,
    ⟨`weak.linter.dupNamespace, false⟩
  ]

require LeanParserGenerator from "../.."

-- The revision matches the Charon that `--rust-extract-kernel` and `gen_rust_verif` run.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @
  "74aabd52f77001cf9eaad51b4f4b867a7dc6b111" / "backends" / "lean"

/-- The specifications the Rust is proved against, and the facts about them that do not
    mention Rust. Needs only the generator's runtime. -/
@[default_target]
lean_lib «Spec» where
  roots := #[`Spec]

/-- The translation of the Rust kernels and the proofs about it. -/
@[default_target]
lean_lib «Kernel» where
  roots := #[`Kernel]

/-- The proofs about the translation of the kernel. -/
@[default_target]
lean_lib «KernelProofs» where
  roots := #[`Kernel.ParseBody, `Kernel.Tables, `Kernel.LexBody, `Kernel.LexTables]
