# Guarantees and trust boundary

This page states what Lean proves about a generated parser, how to read the grammar those proofs are about, and what the proofs assume. The README has the quickstart.

## Proven parser properties

The theorems are about the `Grammar` in the generated specification module (`ExprVerified` in the README example). They are exported from that module:

```text
parser_sound
parser_err_free
parser_ne_err
parser_complete
parser_unambiguous
parse_eq_dependent
```

If `ExprParser.parse` returns a value, `parser_sound` gives a parse tree for the input whose semantics is that value. `parser_err_free` and its equality form `parser_ne_err` state that `ExprParser.run`, the internal function that `parse` is built on, never returns `.err`, the result that would mean the generated tables are inconsistent.

In the other direction, `parser_complete` says that the parser accepts any input that has a start parse tree (`ParserStartTree`), as long as `2 ^ logNSteps` is at least the size of the tree. The README section "Fuel" shows what this means for the size of the input. The type `ParserStartTree` is rooted at the augmented start symbol `S'`, so its word includes EOF. `parser_unambiguous` says that two start parse trees for the same token word have equal semantics. `parse_eq_dependent` says that `ExprParser` and the dependent specification parser return the same result at the same fuel.

A caller does not have to assemble a validator proof or a refinement witness. The lower-level declarations are still available for proofs that need them.

### What the theorems do not cover

The `.lig` frontend is not verified. The theorems are about the grammar that the frontend emitted into the Lean file. If the frontend misreads the `.lig` file, the proofs hold for the grammar it misread. The generator parses `.lig` files with a hand-written parser. A second parser, generated from `lig.lig`, reads the structure of a `.lig` file (directives, rules, alternatives) and has the proofs that every generated parser has. The Lean code inside `%header`, `%lexer` and the action bodies is still read by a hand-written scanner, so the generated parser covers the structure only. `lig-bootstrap-test` checks that the two parsers give the same result on the `.lig` files in this repository. That is a test on those files, not a proof. To check what the generator read, use the grammar view in the next section. [`DESIGN.md`](DESIGN.md) §15 has the details.

The theorems start at tokens, not characters. The generated lexer has its own maximal-munch soundness theorem against its DFA tables, checked with `native_decide` (see [`LEXER.md`](LEXER.md)). That theorem is not connected to the parser theorems. The decoding of bytes into characters and the `lexre` regex frontend are not verified.

## Looking at the grammar that was checked

The generated dependent definitions are precise but hard to read: they are large matches over `Fin` indices. Every specification module therefore exports `verifiedGrammarView` and `verifiedGrammarView_agrees`.

The view records the terminals, nonterminals, semantic type names, `$`, `S'`, the start and EOF mappings, and every production in source order. Each semantic action is rendered in a short form, with a comment that names the generated Lean declaration the grammar uses:

```bnf
[0] expr ::= lhs:expr PLUS rhs:atom    { Ast.add lhs rhs }  -- semanticAction0
```

The view can be read in the generated source, or printed as BNF or Markdown:

```sh
lake exe leanparsergenerator --print-grammar bnf MyProject/Expr.lig
lake exe leanparsergenerator --print-grammar markdown MyProject/Expr.lig
```

Lean does not check the names, binders, type strings and action strings in the view. They are there for reading. Lean checks the shape of the grammar: `verifiedGrammarView_agrees` proves that the view has the same terminals, nonterminals, start symbol and productions as the grammar the theorems are about. To see what an action does, read the `semanticActionN` declaration named in the comment.

## The trust boundary

Pager construction and code emission are not trusted. Their output has to pass Boolean checks for safety, completeness, the grammar view, and structural refinement. If a table is corrupted, or a generated semantic dispatcher disagrees with the dependent action, Lean cannot construct the refinement witness.

The large checks are discharged with `native_decide`. This is what makes Cedar-sized tables practical to check, and it means that Lean's native compiler is trusted to evaluate those checks correctly. Theorems checked by the kernel turn the resulting Boolean equalities into the guarantees above.

The repository contains no `sorry`. I checked the axioms of the six exported theorems on the calc grammar with `#print axioms`:

- `parser_sound`, `parser_err_free`, `parser_ne_err`, `parser_unambiguous` and `parse_eq_dependent` depend on `propext`, `Quot.sound`, and the `native_decide` axioms of the generated safety and refinement checks.
- `parser_complete` additionally depends on `Classical.choice` and on the `native_decide` axiom of the generated completeness check.

## The module system

The library and every generated module use Lean's module system. Each file has a `module` header, and imports are `public import`. The generated code separates its public API from its internals:

- A generated parser exposes its value type, `parse`, `diagnose` and `errorMessage`. It also exposes `run`, because the theorems are stated about it, but `run` is not a stable interface. The LR tables, `decode` and `sem` are internal, so a caller that imports the parser sees only the API. The specification module reaches the internals with `import all`, which is allowed because both modules are in the same package, and uses them in its refinement proofs.
- A generated lexer exposes the token type, `tokenize` and `tokenizeByte`. The DFA tables and validator certificates are internal.
- The specification module is exposed in full, because its grammar, automaton, dependent types and exported theorems are what proofs use.

`native_decide` runs at the meta phase, so a module that a generated `native_decide` certificate reduces is also imported with `meta import`. This does not change the trust boundary or the axioms listed above. [`DESIGN.md`](DESIGN.md) §16.2 has the full design.
