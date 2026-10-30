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
Small text helpers shared by the Rust emitters.
-/


@[expose] public section

namespace Emit.Rust

/-- A Rust array literal body, with elements packed greedily into lines of at most
    `width` columns. -/
def packLines (elems : Array String) (indent : String := "    ") (width : Nat := 100) : String :=
  Id.run do
    let mut lines : Array String := #[]
    let mut cur := indent
    let mut first := true
    for e in elems do
      let piece := e ++ ","
      if first then
        cur := cur ++ piece
        first := false
      else if cur.length + 1 + piece.length ≤ width then
        cur := cur ++ " " ++ piece
      else
        lines := lines.push cur
        cur := indent ++ piece
    if !first then lines := lines.push cur
    return "\n".intercalate lines.toList

/-- `pub static NAME: [ty; n] = [ … ];` -/
def staticArr (name ty : String) (elems : Array String) : String :=
  s!"#[rustfmt::skip]\nstatic {name}: [{ty}; {elems.size}] = [\n{packLines elems}\n];"

/-- The narrowest unsigned Rust type holding values up to `maxVal`. -/
def uintTy (maxVal : Nat) : String :=
  if maxVal < 256 then "u8" else if maxVal < 65536 then "u16" else "u32"

end Emit.Rust
