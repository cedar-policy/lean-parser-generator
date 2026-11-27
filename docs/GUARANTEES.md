# Guarantees and trust boundary

What Lean proves about a generated parser, how to read the grammar those proofs are about, and what the proofs assume. The README has the quickstart.

## Proven parser properties

The claims are about the exact `Grammar` found in the generated specification module. For that grammar, Lean proves the following facts.

If `ExprParser.parse` returns a semantic value, `parser_sound` supplies a parse tree, connected to the input stream, whose semantics is that value. The theorem `parser_err_free`—or its equality-shaped companion `parser_ne_err`—states that `ExprParser.run` cannot encounter an internal inconsistency in the generated tables.

In the other direction, `parser_complete` says that a supplied start parse tree is accepted whenever the logarithmic fuel bound covers the size of the tree. The type `ParserStartTree` is rooted at the augmented start symbol `S'`, so its word includes EOF. Finally, `parser_unambiguous` says that two start parse trees for the same token word have equal semantics.

These corollaries are exported directly by the specification module (e.g. `ExprVerified`):

```text
parser_sound
parser_err_free
parser_ne_err
parser_complete
parser_unambiguous
parse_eq_dependent
```

A caller does not have to assemble a validator proof or a refinement witness. The lower-level declarations remain available for developments that need them.

There are two important boundaries to keep in mind.
First, the `.lig` frontend is unverified: the theorems and proofs are for the emitted Lean grammar, not the author's intention for the source file. This mismatch is alleviated by the fact that `lean-parser-generator`'s parser is itself proven correct using itself.
Second, the parser theorem begins with tokens, not characters: the lexer has its own separate maximal-munch soundness against its emitted DFA tables (validated by `native_decide`, see the design's lexer section), but that guarantee is not yet threaded into the parser theorem, and the bytes-to-characters decoding layer and the `lexre` regex frontend remain unverified.

## Looking at the grammar that was checked

Generated dependent definitions are precise, but a large match over `Fin` indices is not pleasant to audit. Every specification module therefore exports `verifiedGrammarView` together with `verifiedGrammarView_agrees`.

The view records terminals, nonterminals, semantic type names, `$`, `S'`, the start and EOF mappings, and every production in source order. Semantic actions are rendered in a compact form, while a comment points to the actual generated Lean declaration used by the grammar:

```bnf
[0] expr ::= lhs:expr PLUS rhs:atom    { Ast.add lhs rhs }  -- semanticAction0
```

The view can be read in the generated source, or rendered as BNF or Markdown:

```sh
lake exe leanparsergenerator --print-grammar bnf MyProject/Expr.lig
lake exe leanparsergenerator --print-grammar markdown MyProject/Expr.lig
```

Names, binders, type strings, and action strings in the view are for reading only, and Lean does not check them. What Lean checks is the shape of the grammar: `verifiedGrammarView_agrees` proves that the view has the same terminals, nonterminals, start symbol, and productions as the grammar the theorems are about. For what an action does, read the `semanticActionN` declaration named in the comment.

## The trust boundary

We reiterate and emphasize what assumptions we make when we claim "generated parsers are proven valid".

Pager construction and code emission are untrusted computations. Their output must satisfy Boolean safety, completeness, grammar-view, and structural refinement checks. If a table is corrupted, or if a generated semantic dispatcher no longer agrees with the dependent action, Lean cannot construct the refinement witness.

Large generated checks are discharged with `native_decide`; this is what makes Cedar-sized tables practical to compile. Using `native_decide` trusts evaluation by Lean's native compiler. Kernel-checked linking theorems turn the resulting Boolean equalities into the parser guarantees described above.

The generic proofs contain no `sorry`, custom axioms, or `Classical.choice`.

## The module system

The library and every generated module use Lean's module system. Each file has a `module` header and imports are `public import`. Generated code draws a deliberate boundary between its public API and its internals:

- A generated parser exposes its value type, `run`, and `parse`. Its LR tables, `decode`, and `sem` are internal — a caller that `import`s the parser sees only the API. The paired specification module reaches those internals with `import all` (same package) for its refinement proofs.
- A generated lexer exposes the token type and `tokenize`/`tokenizeByte`; the DFA tables and validator certificates are internal.
- The specification module is exposed in full, because its grammar, automaton, dependent types, and the exported corollaries are the API that proofs use.

Because `native_decide` runs at the meta phase, a module reduced by a generated `native_decide` certificate is also `meta import`ed. None of this changes the trust boundary or the axiom budget; the certificates still depend only on `propext`, `Classical.choice`, `Quot.sound`, and their own `native_decide` axioms.
[`DESIGN.md` §16.2](DESIGN.md) describes the design in full.
