# LeanParserGenerator

LeanParserGenerator turns an LR(1) grammar, written in a `.lig` file, into a Lean
parser. The grammar carries ordinary Lean semantic actions, so parsing can
produce whatever value is useful to the application: an abstract syntax tree, a
policy, a command, or simply a number.

The generated parser is meant to be used as ordinary compiled Lean code. Alongside
it, LeanParserGenerator emits a dependent specification of the same grammar and
a collection of certificates. Lean checks these certificates and proves that the
parser agrees with the dependent specification. The construction of the LR(1)
automaton and the code generator themselves do not have to be trusted.

This follows the a-posteriori validation architecture described in
[Validating LR(1) Parsers](https://xavierleroy.org/publi/validated-parser.pdf),
which Menhir's verified back end also uses. The implementation here uses Pager's
LR(1) construction and a small Lean runtime.

## A first parser

It is easiest to see the pieces in a small example. Suppose that we want to parse
sums of natural numbers. We begin, in an ordinary Lean module, with the value
that parsing should produce:

```lean
namespace Expr

inductive Ast where
  | number : Nat → Ast
  | add : Ast → Ast → Ast
  deriving Repr, BEq

end Expr
```

The token type belongs to the application, not the generator by default — but a
grammar can also ask the generator to produce it. There are two regimes, and no
third:

**Generated lexer.** Add a `%lexer { … }` block to the `.lig`. The generator then
emits the token type *and* the tokenizer into a lexer module, and the parser
imports that module for the token type:

```text
%header {
import MyProject.ExprAst
open Expr
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
expr :: Ast
  | lhs=expr PLUS rhs=atom { Ast.add lhs rhs }
  | value=atom             { value }
atom :: Ast
  | value=NUM              { Ast.number value }
```

The `%token` declarations are the single source of truth for the token type: the
generated lexer module defines `inductive Tok` from them (deriving `Repr`, `BEq`,
`Inhabited`, `DecidableEq`), builds and validates the DFA tables offline, and
exports `tokenize`. The lexer is generated together with the parser (§Generating).
Lexer-only helpers (keyword folding, string stripping) go in a `%lexerheader { … }`
block, copied only into the lexer module.

**Hand-written lexer.** Omit the `%lexer` block. Then the token type and the lexer
are ordinary hand-written Lean that `%header` imports — a lexer is just a function
producing the token list the parser consumes. This is the right regime when the
token stream comes from an existing lexer or a non-regular tokenizer.

At present the lexer's emitted DFA tables are validated for maximal-munch soundness
by `native_decide`, discharged for all three generated lexers (calculator, Cedar,
CedarSchema). The validator conditions are interval arithmetic over
character classes, so there is no code-point budget gate — Unicode-wide classes are
handled by testing one representative per boundary cell, not per code point. The
emitted `tokenize` runs a fast flat `state × class` scanner over a `String.Pos`
cursor, proved equal to the derivative-level specification tokenizer, so it inherits
that soundness (see the design's lexer section). The remaining unverified boundary
is the bytes-to-characters layer that feeds the scanner.

Each lexer also emits a byte-level scanner (`tokenizeByte`, over `String.toUTF8` by
byte index) that folds the UTF-8 decode into the scan. It is ~1.15–1.18x faster on the
Cedar corpus (tokens byte-for-byte identical) and is validated per lexer by
`native_decide` (`byteValidated{m}`), with the byte-scan simulation of the flat scanner
proved up to that Boolean. The proved `tokenize` stays on the flat `String.Pos`
scanner; `tokenizeByte` is the validated fast path (see the design's lexer section).


The `%header` block is copied into the generated modules. It should therefore
import every type and definition used by token payloads, rule result types, or
semantic actions.

## Generating and calling the parser

Build the generator and ask it for a parser and its dependent specification:

```sh
lake build leanparsergenerator

lake exe leanparsergenerator grammar/Expr.lig
```

From the input path alone the generator infers its outputs, writing them next to
the `.lig`: `ExprVerified.lean`, `ExprParser.lean`, `ExprLexer.lean` (when the
grammar has a `%lexer` block), `ExprLexerRoundtrip.lean` (when the grammar also
sets `%option roundtrip_lexer`), and `ExprParserRoundtrip.lean` (when the grammar
sets `%option roundtrip_parser <printer>`). The base name comes from the `.lig`
stem (`Expr.lig` → `Expr`), so a grammar file named in the CamelCase you want for
the modules produces those module names directly.

Three `%option` directives shape this. `%option module_prefix <path>` is the dotted
prefix the modules live under inside a larger module tree — with
`%option module_prefix myproject.expr` the parser imports its lexer as
`myproject.expr.ExprLexer` and a caller imports `myproject.expr.ExprParser`;
without it the modules are top-level. `%option roundtrip_lexer` adds the lexer
roundtrip module (printer/lexer inverse on tokens). `%option roundtrip_parser
<unparse>` names a user token generator `StartTy → List Tok` and adds the parser
roundtrip module, which proves that generating an AST's tokens and parsing them
back returns that AST (DESIGN §16.5); the module is hole-free, proving the
roundtrip over a `corpus` of ASTs you list in your `<Base>Unparse` module and
printing what it proved with `#eval guarantees`. Adding `%option roundtrip_format
<renderTok>` (a complete token renderer) also proves a formatter-idempotence lemma
— formatting the token stream with whitespace re-lexes to the same tokens — and the
full AST↔source roundtrip, the composition of the two roundtrips, both hole-free
over the same corpus. The older explicit-argument forms (spelling out each output
path, module name, and the parser's import path) still work as overrides; the
complete form is shown in [`docs/INTEGRATION.md`](docs/INTEGRATION.md).

Application code imports the generated parser and lexer and calls `parse` on the
tokens the lexer produces:

```lean
import ExprLexer
import ExprParser

def parseExpr (source : String) : Except Lexer.LexError (Option Expr.Ast) := do
  let tokens ← ExprLexer.tokenize source
  pure (ExprParser.parse tokens)
```

`ExprParser` already imports `ExprLexer` for the token type, so a caller that only
needs `parse` can import `ExprParser` alone. In the hand-written regime the caller
imports the application's own token module and lexer instead.

`parse` returns `some value` when the input is accepted and `none` otherwise.
The optional logarithmic-fuel argument, whose default is `20`, controls the
maximum number of parser steps; a value `n` permits up to `2^n` steps.

Sometimes an application must distinguish a syntax error from fuel exhaustion,
or inspect an unexpected internal table error. In that case, use `run` instead:

```lean
ExprParser.run tokens
```

Its result distinguishes `.ok`, `.reject`, `.timeout`, and `.err`. For generated,
validated parsers, the `.err` case is proved unreachable.

The parser treats a finite list as an EOF-padded stream. Thus a lexer may append
the declared EOF token—as the lexer above does—and exhausted input is also padded
with that same token.

## Source positions

Every token carries a source span. The generated lexer's `tokenize` returns
`List (Runtime.Positioned Tok)`—each token paired with a `Runtime.Span`, a
half-open byte range into the input—and `parse`/`run` consume that list, so the
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

`parse` returns the start value only and drops the span. When the top-level span
is wanted, `run` returns it: its `.ok` case is `(span, value)`. Line and column are
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
dependent side, so the soundness, completeness, and error-freedom results below
are exactly as before.

## Why are there two generated modules?

`ExprParser` is the parser that programs call. It uses ordinary natural-number
states, flat action and goto tables, and a generated sum type for semantic
values. It is non-dependent and compiles normally.

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

## What does Lean prove?

The claims are about the exact `Grammar` found in the generated specification
module. For that grammar, Lean proves the following facts.

If `ExprParser.parse` returns a semantic value, `parser_sound` supplies a parse
tree, connected to the input stream, whose semantics is that value. The theorem
`parser_err_free`—or its equality-shaped companion `parser_ne_err`—states that
`ExprParser.run` cannot encounter an internal inconsistency in the generated
tables.

In the other direction, `parser_complete` says that a supplied start parse tree
is accepted whenever the logarithmic fuel bound covers the size of the tree.
The type `ParserStartTree` is rooted at the augmented start symbol `S'`, so its
word includes EOF. Finally, `parser_unambiguous` says that two start parse trees
for the same token word have equal semantics.

These corollaries are exported directly by every paired specification module:

```text
parser_sound
parser_err_free
parser_ne_err
parser_complete
parser_unambiguous
parse_eq_dependent
```

A caller does not have to assemble a validator proof or a refinement witness.
The lower-level declarations remain available for developments that need them.

There are two important boundaries to keep in mind. First, the `.lig` frontend
is unverified: the theorem concerns the emitted Lean grammar, not the author's
intention for the source file. Second, the parser theorem begins with tokens, not
characters: the lexer has its own separate maximal-munch soundness against its
emitted DFA tables (validated by `native_decide`, see the design's lexer section),
but that guarantee is not yet threaded into the parser theorem, and the
bytes-to-characters decoding layer and the `lexre` regex frontend remain
unverified.

## Looking at the grammar that was checked

Generated dependent definitions are precise, but a large match over `Fin`
indices is not pleasant to audit. Every specification module therefore exports
`verifiedGrammarView` together with `verifiedGrammarView_agrees`.

The view records terminals, nonterminals, semantic type names, `$`, `S'`, the
start and EOF mappings, and every production in source order. Semantic actions
are rendered in a compact form, while a comment points to the actual generated
Lean declaration used by the grammar:

```bnf
[0] expr ::= lhs:expr PLUS rhs:atom    { Ast.add lhs rhs }  -- semanticAction0
```

The view can be read in the generated source, or rendered as BNF or Markdown:

```sh
lake exe leanparsergenerator --print-grammar bnf grammar/Expr.lig
lake exe leanparsergenerator --print-grammar markdown grammar/Expr.lig
```

Rendering is opt-in; normal builds remain quiet. Names, source binders, type
strings, and action strings are presentation metadata. The structural agreement
theorem and the referenced Lean action declarations are authoritative.

## Putting a generated parser in an existing project

In a real repository, the handwritten AST, token type, and lexer live beside the
rest of the application. The `.lig` header imports them. The generated parser
and specification modules can live under the application's normal module prefix
and can be imported like any other Lean source files.

A Lake target can fetch the generator executable from the dependency, compare
the modification times of the grammar, generator, and generated files, and
regenerate both outputs before the library is compiled. There is one practical
bootstrap detail: Lake discovers modules before ordinary library jobs run. If
generated modules are not committed, a clean checkout must generate them once
before the first library build. If they are committed—as is often convenient for
review—plain `lake build` is enough and stale files are refreshed automatically.

[`docs/INTEGRATION.md`](docs/INTEGRATION.md) gives a complete, tested setup. It
includes local and pinned Git dependencies, source layout, the full generator
command, parser and proof imports, a Lake 4.33 target, multiple-output mtime
checks, and clean-checkout CI commands.

## The trust boundary

Pager construction and code emission are untrusted computations. Their output
must satisfy Boolean safety, completeness, grammar-view, and structural
refinement checks. If a table is corrupted, or if a generated semantic
dispatcher no longer agrees with the dependent action, Lean cannot construct the
refinement witness.

Large generated checks are discharged with `native_decide`; this is what makes
Cedar-sized tables practical to compile. Using `native_decide` trusts evaluation
by Lean's native compiler. Kernel-checked linking theorems turn the resulting
Boolean equalities into the parser guarantees described above.

The generic proofs contain no `sorry`, custom axioms, or `Classical.choice`.

## The module system

The library and every generated module use Lean's module system. Each file has a
`module` header and imports are `public import`. Generated code draws a deliberate
boundary between its public API and its internals:

- A generated parser exposes its value type, `run`, and `parse`. Its LR tables,
  `decode`, and `sem` are internal — a caller that `import`s the parser sees only
  the API. The paired specification module reaches those internals with `import
  all` (same package) for its refinement proofs.
- A generated lexer exposes the token type and `tokenize`/`tokenizeByte`; the DFA
  tables and validator certificates are internal.
- The specification module is exposed in full, because its grammar, automaton,
  dependent types, and the exported corollaries are the API that proofs use.

Because `native_decide` runs at the meta phase, a module reduced by a generated
`native_decide` certificate is also `meta import`ed. None of this changes the
trust boundary or the axiom budget; the certificates still depend only on
`propext`, `Classical.choice`, `Quot.sound`, and their own `native_decide` axioms.
[`docs/DESIGN.md` §16.2](docs/DESIGN.md) describes the design in full.

## Further reading

[`docs/DESIGN.md`](docs/DESIGN.md) describes the architecture, runtime
invariants, `.lig` syntax, validation algorithms, refinement proof, and
inspectable grammar view in detail.

[`docs/INTEGRATION.md`](docs/INTEGRATION.md) is the practical guide for adding a
parser to another Lake package and keeping generated modules up to date.

[`test/README.md`](test/README.md) lists the calculator, IMP, and Cedar
fixtures, their generated modules, and the commands used to rebuild and test
them.

To build this repository and its default regression suites:

```sh
lake build
```
