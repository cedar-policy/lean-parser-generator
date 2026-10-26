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
public import cedar.CedarLexer
public import cedar.CedarParser
public import LeanParserGenerator.Lexer.ByteTokenize


public section

open Lexer Cedar

/-- The byte-expanded compilation of Cedar's flat lexer (built once), for the
    `[byte lex]` comparison (docs/DESIGN.md §9.6.3). -/
def cedarByte : Lexer.CompiledByte Tok := Lexer.CompiledByte.ofFlat CedarLexer.cflat

/-- Byte lex-only token count (0 on error). -/
def cedarBenchByteLex (src : String) : Nat :=
  match Lexer.tokenizeByte cedarByte src with | .ok t => t.length | .error _ => 0

/-- End-to-end lex+parse of one policy, returning a small checksum derived from
    the AST (0 on failure). This is the unit the benchmark times. -/
def cedarBenchLexParse (src : String) (fuel : Nat) : Nat :=
  match CedarLexer.tokenize src with
  | .ok toks =>
    match CedarParser.parse toks fuel with
    | some p => p.policies.length + 1
    | none   => 0
  | .error _ => 0

/-- Lex only: returns the token count (0 on error). -/
def cedarBenchLex (src : String) : Nat :=
  match CedarLexer.tokenize src with
  | .ok toks => toks.length
  | .error _ => 0

/-- Parse only, from a pre-tokenized list. -/
def cedarBenchParse (toks : List (Runtime.Positioned Tok)) (fuel : Nat) : Nat :=
  match CedarParser.parse toks fuel with
  | some p => p.policies.length + 1
  | none   => 0

/-- Throughput benchmark over a Cedar policy corpus given as file-path arguments:
    end-to-end `[lex+parse]`, `[lex only]`, `[parse only]`, and `[byte lex]` (the
    byte scanner vs the flat scanner, with a token-identical check, §9.6.3).
    Native-compiled via `lake build`; run with `lake exe cedar-bench <files...>`. -/
def main (args : List String) : IO Unit := do
  let mut sources : Array String := #[]
  for p in args do
    sources := sources.push (← IO.FS.readFile p)
  let totalBytes := sources.foldl (fun a s => a + s.utf8ByteSize) 0
  IO.println s!"corpus: {sources.size} policies, {totalBytes} bytes"

  let fuel := 20
  let mut ok := 0
  for s in sources do
    if cedarBenchLexParse s fuel > 0 then ok := ok + 1
  IO.println s!"parsed OK: {ok}/{sources.size}"

  -- warm up
  for s in sources do
    let _ := cedarBenchLexParse s fuel

  let iters := (← IO.getEnv "BENCH_ITERS").bind (·.toNat?) |>.getD 2000
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for _ in [0:iters] do
    for s in sources do
      acc := acc + cedarBenchLexParse s fuel
  let ns := ((← IO.monoNanosNow) - t0).toFloat
  let total := (iters * sources.size).toFloat
  IO.println s!"iters={iters}, checksum acc={acc}"
  IO.println s!"[lex+parse] total: {ns / 1.0e6} ms, per policy: {(ns / 1000.0) / total} us, {total / (ns / 1.0e9)} policies/s"

  -- lex-only timing
  let t1 ← IO.monoNanosNow
  let mut accL : Nat := 0
  for _ in [0:iters] do
    for s in sources do
      accL := accL + cedarBenchLex s
  let nsL := ((← IO.monoNanosNow) - t1).toFloat
  IO.println s!"[lex only]  per policy: {(nsL / 1000.0) / total} us (acc={accL})"

  -- parse-only timing (pre-tokenize once)
  let toksArr := sources.map (fun s => (CedarLexer.tokenize s).toOption.getD [])
  let t2 ← IO.monoNanosNow
  let mut accP : Nat := 0
  for _ in [0:iters] do
    for toks in toksArr do
      accP := accP + cedarBenchParse toks fuel
  let nsP := ((← IO.monoNanosNow) - t2).toFloat
  IO.println s!"[parse only] per policy: {(nsP / 1000.0) / total} us (acc={accP})"

  -- byte lex-only timing + token-identical check vs the flat scanner (§9.6.3).
  let mut mism := 0
  for s in sources do
    if reprStr (CedarLexer.tokenize s) != reprStr (Lexer.tokenizeByte cedarByte s) then
      mism := mism + 1
  IO.println s!"[byte lex] token-identical: {sources.size - mism}/{sources.size}"
  for s in sources do let _ := cedarBenchByteLex s
  let t4 ← IO.monoNanosNow
  let mut accB : Nat := 0
  for _ in [0:iters] do
    for s in sources do
      accB := accB + cedarBenchByteLex s
  let nsB := ((← IO.monoNanosNow) - t4).toFloat
  IO.println s!"[byte lex] per policy: {(nsB / 1000.0) / total} us (acc={accB}), speedup vs flat lex: {nsL / nsB}x"

  -- Cross-check: building the tables at run time with `Compiled.ofTokenizer`
  -- reproduces the emitted DFA state count. The emitted tables are generated
  -- offline (docs/DESIGN.md §9); this is a behavioral sanity check.
  let t3 ← IO.monoNanosNow
  let built := Lexer.Compiled.ofTokenizer CedarLexer.tokenizer
  let builtStates := built.dfas.foldl (fun a d => a + d.states.size) 0
  let nsB := ((← IO.monoNanosNow) - t3).toFloat
  let emittedStates := CedarLexer.lexer.dfas.foldl (fun a d => a + d.states.size) 0
  IO.println s!"[dfa build] run-time construction: {nsB / 1.0e6} ms ({builtStates} states)"
  IO.println s!"[dfa build] emitted tables: {emittedStates} states, 0 ms (generated offline)"
