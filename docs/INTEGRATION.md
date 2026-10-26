# Integrating LeanParserGenerator into an existing repository

This guide assumes an existing Lake package named `MyProject`. The generated
**parser** is the module application code calls; the paired **dependent
specification module** contains validation, refinement, and parser-facing proof
corollaries.

## 1. Add the dependency

For local development:

```lean
-- lakefile.lean
import Lake
open Lake DSL

package MyProject where

require LeanParserGenerator from "../LeanParserGenerator"
```

For a Git dependency, pin an immutable revision rather than relying on a moving
branch:

```lean
require LeanParserGenerator from git "ssh://git.amazon.com/pkg/LeanParserGenerator" @ "<commit-hash>"
```

Use the same Lean toolchain as LeanParserGenerator, then run `lake update`.

## 2. Define the AST and token type

The AST and token constructors are ordinary handwritten Lean definitions. For
example, `MyProject/ExprAst.lean`:

```lean
namespace MyProject

inductive Expr where
  | number : Nat → Expr
  | add : Expr → Expr → Expr
  deriving Repr, BEq

inductive Tok where
  | NUM : Nat → Tok
  | PLUS
  | EOF
  deriving Repr, BEq, Inhabited

end MyProject
```

Token constructor names and payload types must agree with the `.lig` `%token`
declarations. The EOF constructor must agree with `%eof`.

## 3. Choose a lexer regime

There are two regimes, and no third.

**Generated (recommended).** Put a `%lexer { … }` block in the `.lig` (§4). The
generator emits the token type and the tokenizer into `ExprLexer.lean`, and the
parser modules import it. You write no token type and no lexer by hand.

**Hand-written.** Omit the `%lexer` block. Then you hand-write the token type
(`MyProject/ExprAst.lean`) and a lexer — any ordinary Lean function producing the
token list the parser consumes — and `%header` imports them. Use this when the
token stream comes from an existing lexer or a non-regular tokenizer.

The examples below use the generated regime.

## 4. Define the `.lig` grammar

Create `grammar/Expr.lig`:

```text
%header {
import MyProject.ExprAst
open MyProject
}
%tokentype Tok
%token <Nat> NUM
%token PLUS
%token EOF
%eof EOF
%lexer {
  let digit = ['0'-'9']
  | digit+ as s          => { Tok.NUM s.toNat! }
  | "+"                  => { Tok.PLUS }
  | (' ' | '\t' | '\n')+ => skip
  eof => { Tok.EOF }
}
%start expr
%%
expr :: Expr
  | lhs=expr PLUS rhs=atom { Expr.add lhs rhs }
  | value=atom             { value }
atom :: Expr
  | value=NUM              { Expr.number value }
```

`%header` is copied into every generated module (parser backends and the lexer). It
must import every type and declaration used by token payloads, nonterminal types,
and semantic actions. `%lexerheader { … }` (optional) is copied only into the lexer
module — put lexer-only helpers (keyword folding, string stripping) there. The
`%token` declarations are the single source of truth for the token type: the
generated `ExprLexer` module defines `inductive Tok` from them. Bindings such as
`lhs=expr` become Lean variables in the action.

## 5. Generate and import the modules

Generate the lexer and both parser backends together so they share one prepared
grammar and table set. With just the `.lig` as argument, the CLI infers every
output from its stem and writes the modules next to it. Put the `.lig` where you want
the generated modules and set `%option module_prefix` to their dotted prefix:

```text
%option module_prefix MyProject.Generated
%option roundtrip_lexer
```

with `grammar/Expr.lig` moved to `MyProject/Generated/Expr.lig`, then:

```sh
lake exe leanparsergenerator MyProject/Generated/Expr.lig
```

This writes `MyProject/Generated/ExprVerified.lean`, `ExprParser.lean`,
`ExprLexer.lean` (the `%lexer` block owns the token type; the parser modules import
it as `MyProject.Generated.ExprLexer`), and `ExprLexerRoundtrip.lean`. The base
name is the `.lig` stem, so name the file in the CamelCase you want for the modules.

Alternatively, when the generated files must live apart from the `.lig`, the
command line can spell out every output path, module name, and the parser's import
path:

```sh
lake exe leanparsergenerator \
  grammar/Expr.lig \
  MyProject/Generated/ExprVerified.lean \
  MyProject/Generated/ExprParser.lean \
  MyProject.Generated.ExprVerified \
  MyProject.Generated.ExprParser \
  MyProject.Generated.ExprParser \
  MyProject/Generated/ExprLexer.lean \
  ExprLexer \
  MyProject.Generated.ExprLexer
```

The last three arguments are the lexer output path, its module name (used as the
def prefix), and its dotted import path (which the parser modules import for the
token type). Omit them for a hand-written-lexer grammar. Generated files should not
be edited manually.

Application code normally imports the lexer and parser only:

```lean
import MyProject.ExprLexer
import MyProject.Generated.ExprParser

namespace MyProject

open Lexer

def parseExpr (source : String) : Except Lexer.LexError (Option Expr) := do
  let tokens ← Lexer.tokenize exprLexer source
  pure (Generated.ExprParser.parse tokens)

end MyProject
```

Use `Generated.ExprParser.run` instead of `parse` when rejection, timeout, and
internal-error outcomes must remain distinct.

## 6. Use the generated guarantees

Import the paired specification module in proof-oriented code:

```lean
import MyProject.Generated.ExprVerified
```

It exports corollaries stated directly about `ExprParser`:

- `parser_sound`: a successful `ExprParser.parse` result has an input-linked
  `ParserStartTree` with the returned semantics;
- `parser_err_free`: `ExprParser.run` satisfies `Runtime.Exec.ResultErrFree`;
- `parser_ne_err`: `ExprParser.run` cannot equal `.err message`;
- `parser_complete`: a supplied `ParserStartTree` is accepted whenever
  `Grammar.ptSize tree ≤ 2 ^ logNSteps`;
- `parser_unambiguous`: two start parse trees for one token word have equal
  semantics;
- `parse_eq_dependent`: the parser equals the dependent specification parser at
  matching logarithmic fuel.

`ParserStartTree` is rooted at the augmented start symbol `S'`; its token word
therefore includes the grammar's EOF token. Most callers use `parser_sound` and
never construct this dependent tree explicitly.

## 7. Automate generation with Lake

The following target was validated against Lake 4.33. It rebuilds the generator,
checks source/output modification times, and regenerates both modules before the
library compilation jobs that depend on it:

```lean
import Lake
open Lake DSL

package MyProject where

require LeanParserGenerator from "../LeanParserGenerator"

target generatedExprParser (pkg : NPackage __name__) : Unit := do
  let some generator ← findLeanExe? `leanparsergenerator
    | error "LeanParserGenerator executable target not found"
  let exeJob ← generator.fetch
  exeJob.bindM fun exeFile => do
    Job.async do
      let ligPath := pkg.dir / "grammar/Expr.lig"
      let verifiedPath := pkg.dir / "MyProject/Generated/ExprVerified.lean"
      let parserPath := pkg.dir / "MyProject/Generated/ExprParser.lean"

      if let some outputDir := verifiedPath.parent then
        IO.FS.createDirAll outputDir

      let regenerate ← do
        if !(← System.FilePath.pathExists verifiedPath) ||
            !(← System.FilePath.pathExists parserPath) then
          pure true
        else
          let inputTime := (← ligPath.metadata).modified
          let generatorTime := (← exeFile.metadata).modified
          let verifiedTime := (← verifiedPath.metadata).modified
          let parserTime := (← parserPath.metadata).modified
          pure (verifiedTime < inputTime || verifiedTime < generatorTime ||
            parserTime < inputTime || parserTime < generatorTime)

      if regenerate then
        -- Explicit arguments: the outputs live in `MyProject/Generated/`, apart
        -- from the `.lig` in `grammar/`. If instead the `.lig` sits with its
        -- outputs and carries `%option module_prefix MyProject.Generated`, this is
        -- just `args := #[ligPath.toString]`.
        let output ← IO.Process.output {
          cmd := exeFile.toString
          args := #[ligPath.toString, verifiedPath.toString, parserPath.toString,
            "MyProject.Generated.ExprVerified",
            "MyProject.Generated.ExprParser",
            "MyProject.Generated.ExprParser"]
          cwd := pkg.dir }
        if output.exitCode != 0 then
          error s!"parser generation failed:\n{output.stderr}"
        IO.print output.stdout

@[default_target]
lean_lib MyProject where
  roots := #[`MyProject.ExprAst, `MyProject.ExprLexer,
    `MyProject.Generated.ExprParser,
    `MyProject.App]
  needs := #[generatedExprParser]

-- The dependent-specification module carries the expensive `native_decide`
-- certificates. Keep it OFF the default path in its own non-default library so a
-- plain `lake build` does not re-check the proofs, and so Lake caches each
-- certificate to `.olean` — an unchanged `lake build MyProjectVerified` is then a
-- trace no-op instead of a full re-check. For large grammars (Cedar/C99-scale)
-- the difference is minutes-to-seconds; this repository's `VerifiedMid`/`VerifiedHeavy`
-- targets are the same pattern (DESIGN §10, §14).
lean_lib MyProjectVerified where
  roots := #[`MyProject.ExprAst, `MyProject.ExprLexer,
    `MyProject.Generated.ExprParser,
    `MyProject.Generated.ExprVerified]
  needs := #[generatedExprParser]
```

Build the executable parser with `lake build` (fast, on the default path) and
re-check the proofs on demand with `lake build MyProjectVerified` (cached).

### First build and CI

Lake discovers Lean modules before ordinary library jobs run. If generated files
are committed—which is recommended for inspection and review—plain `lake build`
is sufficient and the target refreshes stale outputs automatically.

If generated files are not committed, bootstrap them before the first module
discovery:

```sh
lake build generatedExprParser
lake build
```

Use the same two commands in a clean CI checkout. Subsequent `lake build` calls
regenerate automatically whenever the `.lig` file or generator executable is
newer. Exit code `2` means Pager reported LR(1) conflicts after writing the
outputs; this production-oriented example intentionally treats it as a build
failure rather than compiling a conflict-resolved parser. Frontend errors and
other nonzero statuses likewise fail before stale parser code is compiled.

For several grammars, put their paths/module names in an array and run the same
mtime-and-process block for each entry, as demonstrated by this repository's
`parsers` target.
