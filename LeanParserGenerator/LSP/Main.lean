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

/-
Executable root for the `.lig` language server.

The `main` entry lives here, in a module that is only ever compiled as the root
of the `LigLsp` `lean_exe`. It is deliberately kept out of `LSP/Server.lean` so
that no library folded into the FFI-linked `Cedar` archive can contribute a
program `main` — otherwise the FFI-linked fuzz/test binaries would launch this
stdio server and block reading stdin instead of running.
-/

import LeanParserGenerator.LSP.Server

def main (args : List String) : IO UInt32 :=
  LeanParserGenerator.LSP.main args
