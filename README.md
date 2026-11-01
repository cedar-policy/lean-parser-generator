# LeanParserGenerator: A Generator of Validated Parsers in Lean

`lean-parser-generator` turns an LR(1) grammar, written in a `.lig` file, into a Lean parser. The grammar carries ordinary Lean semantic actions, so parsing can produce whatever value is useful to the application: an abstract syntax tree, a policy, a command, or simply a number.

The generated parser is meant to be used as ordinary compiled Lean code. Alongside it, `lean-parser-generator` emits a dependent specification of the same grammar and a collection of certificates. Lean checks these certificates and proves that the parser agrees with the dependent specification. The LR(1) construction and the code generator are not trusted: if either produces a wrong table, Lean rejects the certificates.

This follows the a-posteriori validation architecture described in [Validating LR(1) Parsers](https://xavierleroy.org/publi/validated-parser.pdf), which Menhir's verified back end also uses. The implementation here uses Pager's LR(1) construction and a small Lean runtime. [`docs/GUARANTEES.md`](docs/GUARANTEES.md) lists what Lean proves about a generated parser and what the proofs assume.


## Requirements

Lean 4.36.0 and Lake 5.0.0, as pinned in `lean-toolchain`. Install them with [elan](https://github.com/leanprover/elan); a checkout picks the right toolchain automatically. Generated modules use Lean's module system, so a project that imports them must build with the same Lean version. The default `lake build` takes about 30 seconds from a clean checkout on a 32-core machine and has no dependencies besides Lean.

## A first parser

We show how to use `lean-parser-generator` with a small example. Suppose that we want to parse sums of natural numbers. We begin by writing an ordinary Lean module that defines what the parser should produce (an abstract syntax tree `Ast`), in `MyProject/ExprAst.lean`:

```lean
module

@[expose] public section

namespace Expr

inductive Ast where
  | number : Nat → Ast
  | add : Ast → Ast → Ast
  deriving Repr, BEq

end Expr
```
Generated files use Lean's module system, so every module they import must be a `module` too. That is why the file starts with `module` and `@[expose] public section`.
Then, we write the `.lig` file that defines our grammar, from which the parser is generated. The file starts with a `%header{...}` block that specifies Lean code that is printed as-is in the generated file. In our example, we import the previous module and open the `Expr` namespace. The `%option module_prefix` line gives the dotted prefix of the generated modules, so that they live under `MyProject`, next to the `.lig` file:
```text
%header {
import MyProject.ExprAst
open Expr
}
%option module_prefix MyProject
```

Next, there is a choice. Either the token type and the lexer are defined outside the `.lig` file, in which case the `%header` imports them, or they are defined in the `.lig` file together with the grammar, which is the usual case. `lean-parser-generator` looks for a `%lexer {...}` block in the `.lig` file to generate a lexer:
```text
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
```
One `%tokentype` declaration and a few `%token` declarations precede the `%lexer` block itself. The type of the tokens is generated from the `%tokentype` and `%token` declarations, and then the generated type can be used (as `<token type>.<token kind>`) inside the lexer definition. The token type is declared in the root namespace under the `%tokentype` name, so two grammars that are imported into one program need different `%tokentype` names.

The body of the `%lexer` block is a list of rules. A `let` line names a regular expression so that rules can reuse it (`digit` above). Each rule has the form `| regex => action`. A regex is built from quoted strings, character classes (`['0'-'9']`, or `[^ '\n']` for the complement), sequencing, alternation with `|`, grouping with parentheses, and the postfix operators `*` and `+`. Writing `as s` after a regex binds the matched text to `s`, a `String`. The action is either `skip`, which discards the match (whitespace and comments), or a Lean expression that builds a token. The lexer takes the longest match at each position, and a tie goes to the earlier rule. The `eof` rule gives the token that ends the stream. The full syntax, including lexer modes and the remaining regex operators, is in [DESIGN §8](docs/DESIGN.md) and [`docs/LEXER.md`](docs/LEXER.md).

Finally, the main part of the `.lig` file is the grammar definition itself. A grammar has a start symbol designated by `%start` and then grammar productions for each non-terminal symbol:
```text
%start expr
%%
expr :: Ast
  | lhs=expr PLUS rhs=atom { Ast.add lhs rhs }
  | value=atom             { value }
atom :: Ast
  | value=NUM              { Ast.number value }
```

Put together, `MyProject/Expr.lig` is:
```text
%header {
import MyProject.ExprAst
open Expr
}
%option module_prefix MyProject
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
expr :: Ast
  | lhs=expr PLUS rhs=atom { Ast.add lhs rhs }
  | value=atom             { value }
atom :: Ast
  | value=NUM              { Ast.number value }
```

The `%token` declarations are shared by lexer and parser generator as the source of truth for what tokens are. From them the generated lexer module defines `inductive Tok` (deriving `Repr`, `BEq`, `Inhabited`, and `DecidableEq`), builds the DFA tables offline, validates them, and exports `tokenize`. The lexer is generated together with the parser (see "Generating and calling the parser" below). Helpers that only the lexer needs, such as keyword folding or string unquoting, go in a `%lexerheader { … }` block, which is copied only into the lexer module.

## Generating and calling the parser

Build the generator and ask it for a parser and its dependent specification:

```sh
lake build leanparsergenerator

lake exe leanparsergenerator MyProject/Expr.lig
```

The generator infers the outputs from the input path and writes them next to the `.lig` file. For our example, it writes `MyProject/ExprVerified.lean`, `MyProject/ExprParser.lean`, and `MyProject/ExprLexer.lean` (the last one because the grammar has a `%lexer` block). The base name comes from the `.lig` stem (`Expr.lig` → `Expr`), so a grammar file named in the CamelCase you want for the modules produces those module names directly.

### `%option` reference

`%option` lines in the `.lig` file change which modules are written and how. They never change the grammar that the proofs are about. An unknown option, a missing value, or a value on a flag is a syntax error.

| Option | Value | Effect |
|---|---|---|
| `%option module_prefix <path>` | dotted module path | The prefix the generated modules live under inside a larger module tree. With `%option module_prefix myproject.expr` the parser imports its lexer as `myproject.expr.ExprLexer` and a caller imports `myproject.expr.ExprParser`. Without it the modules are top-level. `--module-prefix` overrides it. |
| `%option compress_tables` | none | Write the executable parser's tables in a compact form. The tables hold the same values at runtime and the proofs are unchanged, but the generated source is smaller and compiles faster. See [`docs/DESIGN.md`](docs/DESIGN.md) §10. |
| `%option gen_rust <path>` | file path, relative to the `.lig` file | Also write the Rust parser to `<path>`. Experimental. `--rust-out` overrides it. |
| `%option gen_rust_verif <dir>` | directory, relative to the `.lig` file | Also write the proof package of the Rust code to `<dir>`. Needs `%option gen_rust`, and the Aeneas tools. Experimental. `--skip-rust-verif` skips it. |
| `%option rust_verif_optional` | none | With `gen_rust_verif`: a warning, not an error, when the grammar has actions the proof package cannot cover. Experimental. |
| `%option rust_ctx <type>` | Rust type | The Rust parser passes a context `ctx: &'a <type>` to the `!!rust{…}` actions, for example an arena they allocate the AST from. Experimental, see [`docs/USING_RUST_GENERATOR.md`](docs/USING_RUST_GENERATOR.md). |
| `%option rust_list <path>` | Rust module path | The list type of the macro rules in the Rust parser is `<path>::List<'a, T>`. Needs `rust_ctx`. Experimental. |
| `%option roundtrip_lexer` | none | Also write `<Base>LexerRoundtrip.lean`. Experimental, see [`docs/ROUNDTRIP.md`](docs/ROUNDTRIP.md). |
| `%option roundtrip_parser <function>` | Lean function name | Also write `<Base>ParserRoundtrip.lean`. Experimental. |
| `%option roundtrip_format <function>` | Lean function name | Add `format`, `relex` and `fullRoundtrip` to the parser roundtrip module. Experimental. |

### Command line reference

```text
leanparsergenerator [options] <input.lig>
leanparsergenerator --print-grammar bnf|markdown <input.lig>
leanparsergenerator --rust-report [-v] <input.lig>
leanparsergenerator --help | --version
```

| Option | Effect |
|---|---|
| `--out-dir <dir>` | Write the Lean modules to `<dir>` instead of next to the `.lig` file. Use it when the generated files must live apart from the grammar. |
| `--module-prefix <path>` | Dotted module prefix of the generated modules. Overrides `%option module_prefix`. |
| `--rust-out <file>` | Also write the Rust parser to `<file>`. Overrides `%option gen_rust`. Experimental. |
| `--only <output>` | Write only this output: `verified`, `parser`, `lexer`, or `rust`. Repeat the flag to select several. Roundtrip modules are written only without `--only`. |
| `--print-grammar bnf\|markdown` | Print the grammar that the proofs are about. Writes no files. See [`docs/GUARANTEES.md`](docs/GUARANTEES.md). |
| `--rust-report [-v]` | Report which semantic actions the Rust backend can emit. Writes no files. Experimental. |
| `-h`, `--help`, `--version` | Show the usage text or the version. |

The base name of the generated modules is the `.lig` file name without the extension, with the first letter in upper case (`expr.lig` gives `ExprParser`). The generator rejects a file name that does not give valid Lean module names: the name must use only ASCII letters, digits and underscores and must not start with a digit. For example, `my-grammar.lig` and `calc.v2.lig` are rejected, and the error suggests a valid name. The same rule applies to each part of a module prefix. A rejected name or prefix is an error with exit code 1 and nothing is written.

The exit code is 0 on success. It is 1 on any error: bad arguments, an input file that cannot be read, a `.lig` syntax error, or a failure during generation. Syntax errors are reported as `file:line:col: parse error: …`. It is 2 when Pager reports LR(1) conflicts. In that case the conflicts are printed to standard error and the requested output is still written, so a build script that wants conflicts to fail the build must treat 2 as failure.

### What the generator checks

Before it writes anything, the generator runs the checks that the language server runs. An error stops the generation with exit code 1 and nothing is written. A warning is printed to standard error and the generation goes on. Every message has a position in the `.lig` file: `error: file:line:col: message` or `warning: file:line:col: message`. The generator reports all the errors it finds, not only the first.

Errors:
- a symbol in a production that is neither a declared token nor a nonterminal;
- a start symbol that is not a rule head;
- the `%eof` token used inside a production;
- a binder name used twice in one alternative;
- a lexer rule whose pattern matches no string, for example a class that excludes every character;
- in a `%lexer` block, a character range whose lower bound is greater than its upper bound (`['9'-'0']`), and a backslash escape that does not exist (`'\d'`). There are no shorthand classes, so write `['0'-'9']`. A backslash before punctuation stands for that character.

Warnings:
- a token declared twice, or a nonterminal given two result types;
- a lexer rule that matches the empty string, such as `['0'-'9']*`. The lexer never emits a token for an empty match, so only the non-empty strings the rule matches have an effect;
- a lexer rule that can never win, because every string it matches is also matched by an earlier rule of the same mode. The usual cause is a keyword rule placed after the identifier rule. Move it before.

A nonterminal that no production uses is reported only by the language server. LR(1) conflicts are reported separately, as described above.

[`docs/INTEGRATION.md`](docs/INTEGRATION.md) shows how to call the generator from a Lake target. The roundtrip options add experimental proof modules. They are not needed to get a working parser.

Application code imports the generated parser and lexer and calls `parse` on the tokens produced by the lexer:

```lean
import MyProject.ExprLexer
import MyProject.ExprParser

def parseExpr (source : String) : Except Lexer.LexError (Option Expr.Ast) := do
  let tokens ← ExprLexer.tokenize source
  pure (ExprParser.parse tokens)
```

`tokenize` returns `.error` when no lexer rule matches at some position. The `Lexer.LexError` carries the character offset (`pos`) of the failure and the offending character (`char`, or `none` at the end of input).

`ExprParser` already imports `ExprLexer` for the token type, so a caller that only needs `parse` can import `ExprParser` alone. When the lexer is hand-written, the caller should import the application's own token module and lexer instead.

`parse` returns `some value` when the input is accepted and `none` otherwise. It returns `none` in two different cases: the input is not in the language, or the parser ran out of fuel. The next section explains the fuel and how to tell the two cases apart.

### Fuel

The parser runs for at most `2 ^ logNSteps` steps, where `logNSteps` is an optional argument of `parse` with default `20`. The default is about one million steps. A step is a shift or a reduction, so the steps needed grow with the number of nodes in the parse tree. This is the quantity `ptSize` that `parser_complete` bounds (see [`docs/GUARANTEES.md`](docs/GUARANTEES.md)). I measured the largest input that fits in the default on two grammars:

| Grammar | Largest input | Tokens | Steps per token |
|---|---|---|---|
| The `expr` grammar above, on `1 + 1 + … + 1` | 262,143 numbers | 524,286 | 2 |
| The Cedar policy grammar, on `permit(principal, action, resource) when { principal.x == 1 };` repeated | 12,945 policies | 220,066 | about 5 |

So the default accepts somewhere between 200,000 and 500,000 tokens, depending on the grammar. A valid input larger than that makes `parse` return `none`, and nothing reports an error. If your inputs can be that large, pass a larger `logNSteps`. The steps per token depend on the grammar, so leave room. `Nat.log2 tokens.length + 4` gives at least 8 steps per token, which is more than either grammar needed:

```lean
ExprParser.parse tokens (Nat.log2 tokens.length + 4)
```

A larger value costs nothing on a small input, because the parser stops as soon as it has an answer (`1 + 2` with `logNSteps := 60` returns immediately).

To tell a rejected input from a timeout, call `diagnose`. `errorMessage` returns `none` for a timeout, so it does not tell them apart:

```lean
match ExprParser.diagnose tokens with
| .ok _ => -- accepted
| .error e => -- rejected, with the position and the expected tokens in `e`
| .timeout => -- out of fuel, retry with a larger logNSteps
| .internal msg => -- inconsistent tables, which `parser_err_free` rules out
```

The generated parser module also defines `run`, which `parse` is built on and which the theorems in the specification module are about (`parser_err_free`, `parser_ne_err`). It is not part of the stable API. Its result carries the parser's internal value type, a sum type with one constructor per semantic type, so reading the start value from it means matching on constructors that change when the grammar changes. Use `parse` for the value and `diagnose` for errors. [`docs/GUARANTEES.md`](docs/GUARANTEES.md) explains the guarantees.

The parser treats a finite list as an EOF-padded stream. Thus a lexer may append the declared EOF token—as the lexer above does—and exhausted input is also padded with that same token.

## Using a hand-written lexer

A `.lig` file does not need a `%lexer` block. Without one, the generator emits no lexer module, and the token type and the lexer are ordinary hand-written Lean that `%header` imports. The lexer is just a function that produces the token list the parser consumes. This is the right choice when the tokens come from an existing lexer, or when the token language is not regular (the `imp` and `c99` fixtures in `test/` do this). A hand-written lexer gets no maximal-munch guarantee from Lean. The parser theorems are not affected, since they start at tokens. Wrap each token with `Runtime.Positioned.dummy` if there are no real source positions (see the next section).

## Source positions

Every token carries a source span. The generated lexer's `tokenize` returns
`List (Runtime.Positioned Tok)`—each token paired with a `Runtime.Span`, a
half-open byte range into the input—and `parse` consumes that list, so the
`parseExpr` above already threads positions without any extra work. A hand-written
lexer builds the same list; when it has no real positions it wraps each token with
`Runtime.Positioned.dummy` (the zero-width `Span.dummy`).

An action can refer to the span of any bound symbol. For a binder `x=sym`, the
name `x_span : Runtime.Span` is in scope in the action body alongside `x`. So
`add := l=expr p=PLUS r=expr { … }` may use `p_span` for the operator's span or
`l_span`/`r_span` for the operands'. A production's own span is the merge of its
first and last symbols. An action that never mentions `_span` costs nothing—spans
ride in the parser value but the binder is only introduced where it is named, and
generated code does not warn about the ones you ignore.

`parse` returns the start value only and drops its span. Line and column are
not stored; they are computed from the source at render time. The generated
`errorMessage` does this for syntax errors:

```lean
ExprParser.errorMessage tokens source
-- some "43:30: unexpected PLUS; expected one of: NUM, LPAR (in parser state 12)"
```

Passing the `source` string renders `line:col`; without it the location is the
token index. `diagnose`/`diagnoseSpanned` return the structured error if you want
to build your own message. This diagnostic layer is unverified, but proved
consistent with the verified engine (`diagnose_run_agrees`); see
[`docs/ERROR_MESSAGES.md`](docs/ERROR_MESSAGES.md). The parser theorem itself is
unchanged: spans ride in the executable parser's value and are erased on the
dependent side, so the soundness, completeness, and error-freedom results in
[`docs/GUARANTEES.md`](docs/GUARANTEES.md) are exactly as before.

## Putting a generated parser in an existing project

In a real repository, the handwritten AST, token type, and lexer live beside the
rest of the application. The `.lig` header imports them. The generated parser
and specification modules can live under the application's normal module prefix
and can be imported like any other Lean source files.

A Lake target can run the generator executable from the dependency, compare the
modification times of the grammar, the generator and the generated files, and
regenerate the outputs before the library is compiled. Lake discovers modules
before it runs library jobs, so if the generated modules are not committed, a
clean checkout has to generate them once before the first library build. If they
are committed, plain `lake build` is enough and refreshes stale files.

Check the proofs separately from the general project build. The specification module (`ExprVerified`) carries the `native_decide` certificates. Checking it from scratch takes about 20 seconds for the Cedar grammar and about 30 seconds for the C99 grammar in this repository (32-core machine; CPU time is roughly 40 s and 55 s). `ExprParser` does not import it, so the application builds and runs without it. Put the generated `*Verified` modules in their own non-default `lean_lib`, so that `lake build` stays fast, and build that library in a separate CI job or when the grammar changes. Lake caches the result, and an unchanged rebuild takes about a second. The proofs give no guarantee unless this check runs.

[`docs/INTEGRATION.md`](docs/INTEGRATION.md) shows a full setup, built with Lean 4.36.0 and Lake 5.0.0. It covers local and pinned Git dependencies, the source layout, the generator command, the parser and proof imports, a Lake target that regenerates stale outputs, and the commands for a clean CI checkout.

## Why are there two generated modules?

`ExprParser` is the parser that programs call. It uses ordinary natural-number
states, flat action and goto tables, and a generated sum type for semantic
values. It uses no dependent types.

`ExprVerified` is the dependent specification module. It defines the exact
`Grammar`, LR automaton, dependent semantic-value types, and validation
certificates. Its interpreter has the rich types needed by the proofs and
currently runs by kernel reduction rather than as the application parser.

The specification module also contains a generated refinement witness. It
connects the numbered grammar and flat LR tables to their dependent counterparts,
checks token decoding, and shows production by production that both parsers
invoke the same semantic action. The generic simulation theorem then proves
that `ExprParser` and the dependent specification parser have the same result at
the same fuel.

Both modules are generated from one prepared grammar and one Pager construction.
They should be generated together, and generated source should not be edited by
hand.

## Status

This is an alpha release, version 0.1.0-alpha.1. Before 1.0, a minor version may change a stable interface, and [`CHANGELOG.md`](CHANGELOG.md) will say so. Experimental interfaces may change or disappear in any release.

| Interface | Status |
|---|---|
| Command line: `leanparsergenerator [options] <input.lig>`, its flags and exit codes | Stable |
| `.lig` directives, grammar rules, semantic actions, and the `%lexer` block | Stable |
| Generated API: `parse`, `tokenize`, `errorMessage`, `diagnose`, and the exported theorems (`parser_sound`, `parser_complete`, `parser_err_free`, `parser_ne_err`, `parser_unambiguous`, `parse_eq_dependent`) | Stable |
| `%option module_prefix` and `%option compress_tables`, see the [`%option` reference](#option-reference) | Stable |
| Roundtrip modules (`%option roundtrip_lexer`, `roundtrip_parser`, `roundtrip_format`), see [`docs/ROUNDTRIP.md`](docs/ROUNDTRIP.md) | Experimental |
| Rust backend (`%option gen_rust`, `--rust-out`, `--rust-report`), see [`docs/USING_RUST_GENERATOR.md`](docs/USING_RUST_GENERATOR.md). It has no proofs. | Experimental |
| Language server and VS Code extension, see [`docs/LANGUAGE_SERVER.md`](docs/LANGUAGE_SERVER.md) | Experimental |

## Further reading

[`docs/GUARANTEES.md`](docs/GUARANTEES.md) states what is proved, how to read the checked grammar, the trust boundary, and how the module system affects the generated API. [`docs/DESIGN.md`](docs/DESIGN.md) describes the architecture, runtime invariants, `.lig` syntax, validation algorithms, refinement proof, and inspectable grammar view in detail.

[`docs/INTEGRATION.md`](docs/INTEGRATION.md) explains how to add a parser to another Lake package and keep the generated modules up to date.

[`docs/USING_RUST_GENERATOR.md`](docs/USING_RUST_GENERATOR.md) explains the experimental Rust backend (`%option gen_rust`, `--rust-out`): what it generates, how to call it, and how it differs from the Lean lexer and parser. [`docs/RUST_PARSER.md`](docs/RUST_PARSER.md) has its design and the decisions behind it.

[`test/README.md`](test/README.md) lists the calculator, IMP, and Cedar fixtures, their generated modules, and the commands used to rebuild and test them.

To build this repository and its default regression suites:

```sh
lake build
```

## Contributing

Contribution guidelines, the code of conduct, the security policy, governance and the maintainer list are shared across the `cedar-policy` organization and live in the [`cedar-policy/.github`](https://github.com/cedar-policy/.github) repository: [CONTRIBUTING](https://github.com/cedar-policy/.github/blob/main/CONTRIBUTING.md), [CODE_OF_CONDUCT](https://github.com/cedar-policy/.github/blob/main/CODE_OF_CONDUCT.md), [SECURITY](https://github.com/cedar-policy/.github/blob/main/SECURITY.md). Do not report security issues in a public issue. Changes that users can see go in [`CHANGELOG.md`](CHANGELOG.md).

Source files carry the Cedar copyright notice, and a pre-commit hook checks for it. After cloning, install the hook once:

```sh
scripts/install-hooks.sh
```

Git does not version `.git/hooks`, which is why this step is needed. `scripts/check-copyright.sh --all` checks every file, and `scripts/check-copyright.sh --fix --all` adds the notice to files that lack it. Generated files (marked with a `-- Generated by` comment) are skipped. CI runs the same check.
