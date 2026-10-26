# LeanParserGenerator

`lean-parser-generator` turns an LR(1) grammar, written in a `.lig` file, into a Lean parser. The grammar carries ordinary Lean semantic actions, so parsing can produce whatever value is useful to the application: an abstract syntax tree, a policy, a command, or simply a number.

The generated parser is meant to be used as ordinary compiled Lean code. Alongside it, `lean-parser-generator` emits a dependent specification of the same grammar and a collection of certificates. Lean checks these certificates and proves that the parser agrees with the dependent specification. The construction of the LR(1) automaton and the code generator themselves do not have to be trusted.

This follows the a-posteriori validation architecture described in [Validating LR(1) Parsers](https://xavierleroy.org/publi/validated-parser.pdf), which Menhir's verified back end also uses. The implementation here uses Pager's LR(1) construction and a small Lean runtime.

## A first parser

We show how to use `lean-parser-generator` with a small example. Suppose that we want to parser sums of natural numbers. We begin by writing an ordinary Lean module that describes that the parser should produce (an abstract syntax tree `Ast`):

```lean
namespace Expr

inductive Ast where
  | number : Nat → Ast
  | add : Ast → Ast → Ast
  deriving Repr, BEq

end Expr
```
Then, we write the `.lig` file that defines our grammar, from which the parser is generated. The file starts with a `%header{...}` block that specifies Lean code that is printed as-is in the generated file. In our example, we import the previous module and open the `Expr` namespace:
```text
%header {
import MyProject.ExprAst
open Expr
}
```

Next, the user has a choice: they have either defined a token type and a lexer outside the `.lig` definition, and in that case, this should be handled through the imports in the `%header`. Usually, one also want to define tokens and lexing at the same time as defining the grammar. `lean-parser-generator` looks for a `%lexer {...}` block in the `.lig` file to generate a lexer:
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
One `%tokentype` declaration and a few `%token` definition precede the `%lexer` block itself. The type of the tokens is generated from the `%tokentype` and `%token` declarations, and then the generated type can be used (as `<token type>.<token kind>`) inside the lexer definition.

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

The `%token` declarations are the single source of truth for the token type. From them the generated lexer module defines `inductive Tok` (deriving `Repr`, `BEq`, `Inhabited`, and `DecidableEq`), builds the DFA tables offline, validates them, and exports `tokenize`. The lexer is generated together with the parser (see "Generating and calling the parser" below). Helpers that only the lexer needs, such as keyword folding or string unquoting, go in a `%lexerheader { … }` block, which is copied only into the lexer module.

## Generating and calling the parser

Build the generator and ask it for a parser and its dependent specification:

```sh
lake build leanparsergenerator

lake exe leanparsergenerator grammar/Expr.lig
```

The generator infers the outputs from the input path, writing next to the `.lig` file: for example, the outputs above are `ExprVerified.lean`, `ExprParser.lean`, `ExprLexer.lean` (when the grammar has a `%lexer` block). The base name comes from the `.lig` stem (`Expr.lig` → `Expr`), so a grammar file named in the CamelCase you want for the modules produces those module names directly.

The outputs can be controlled by different `%option` directives in the `.lig` file:
- `%option module_prefix <path>` is the dotted prefix the modules live under inside a larger module tree — with `%option module_prefix myproject.expr` the parser imports its lexer as `myproject.expr.ExprLexer` and a caller imports `myproject.expr.ExprParser`; without it the modules are top-level.

- `%option roundtrip_lexer`, `%option roundtrip_parser <unparse>`, and `%option roundtrip_format <renderTok>` generate extra proof modules. They are experimental. They are not needed to get a working parser, and they are described in "Roundtrip proofs (experimental)" below.

Alternatively, the command line can spell out each output path, module name, and import path. This is useful when the generated files must live apart from the `.lig` file. [`docs/INTEGRATION.md`](docs/INTEGRATION.md) shows the complete form.

Application code imports the generated parser and lexer and calls `parse` on the tokens produced by the lexer:

```lean
import ExprLexer
import ExprParser

def parseExpr (source : String) : Except Lexer.LexError (Option Expr.Ast) := do
  let tokens ← ExprLexer.tokenize source
  pure (ExprParser.parse tokens)
```

`ExprParser` already imports `ExprLexer` for the token type, so a caller that only needs `parse` can import `ExprParser` alone. In the hand-written regime the caller imports the application's own token module and lexer instead.

`parse` returns `some value` when the input is accepted and `none` otherwise. The optional logarithmic-fuel argument, whose default is `20`, controls the maximum number of parser steps; a value `n` permits up to `2^n` steps.

Sometimes an application must distinguish a syntax error from fuel exhaustion, or inspect an unexpected internal table error. In that case, use `run` instead:

```lean
ExprParser.run tokens
```

Its result distinguishes `.ok`, `.reject`, `.timeout`, and `.err`. For generated, validated parsers, the `.err` case is proved unreachable.

The parser treats a finite list as an EOF-padded stream. Thus a lexer may append the declared EOF token—as the lexer above does—and exhausted input is also padded with that same token.

## Using a hand-written lexer

A `.lig` file does not need a `%lexer` block. Without one, the generator emits no lexer module, and the token type and the lexer are ordinary hand-written Lean that `%header` imports. The lexer is just a function that produces the token list the parser consumes. This is the right choice when the tokens come from an existing lexer, or when the token language is not regular (the `imp` and `c99` fixtures in `test/` do this). A hand-written lexer gets no maximal-munch guarantee from Lean, and the parser theorem below is unaffected by that, since it starts at tokens. Wrap each token with `Runtime.Positioned.dummy` if there are no real source positions (see the next section).

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

## Roundtrip proofs (experimental)

These options generate additional modules, and they are experimental. They check that the lexer and the parser are inverses of a printer. This is a different property from the theorems in "What does Lean prove?". None of them is needed to use the parser.

- `%option roundtrip_lexer` adds `<Base>LexerRoundtrip.lean`. For every token constructor with a fixed spelling, it proves that lexing the spelling gives back the token. For a token that carries a value, it looks for a lexeme the whole lexer maps to that constructor. When it finds none, the module says so in a comment, and the token has no coverage theorem. The statement is about the tokens the lexer can produce, not about all values of the token type: `IDENTIFIER "if"` is a well-typed token that no input lexes to, if `"if"` is folded to a keyword. [`docs/LEXER.md`](docs/LEXER.md) has the details.
- `%option roundtrip_parser <unparse>` adds `<Base>ParserRoundtrip.lean`. You supply `<unparse> : StartTy → List Tok`. The module proves that `parse (unparse t) = some t`. The proof covers only the ASTs you list in a `corpus` in your `<Base>Unparse` module, not every AST. `#eval guarantees` prints what was proved for that corpus. See DESIGN §16.5.
- `%option roundtrip_format <renderTok>` takes a complete token renderer and adds two more theorems over the same corpus: formatting the token stream with whitespace and lexing it again gives the same tokens, and the composition of the two roundtrips (AST to source text and back to the AST).

These modules are generated next to the others, and `lake build` checks them like any other module.

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
