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
Hand-written result type for the calculator `.lig` example. The token type is
generated into `CalcLexer` from the `%token` declarations (docs/DESIGN.md §9), so
it no longer lives here; the parser imports `CalcLexer` for it.
-/


@[expose] public section

namespace Calc

end Calc
