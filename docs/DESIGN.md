# LeanParserGenerator — Design

LeanParserGenerator generates Pager LR(1) parsers from external `.lig` grammar
files. Its dependent specification backend follows Menhir's a-posteriori validation model: parser
construction is untrusted, generated certificates are checked in Lean, and a
small generic runtime carries the proofs.

The verified core proves soundness, validated Err-freedom, operational
completeness, and semantic unambiguity. Generated refinement witnesses now relate every paired
native executable engine to that dependent specification at matching logarithmic
fuel.

## 1. Architecture and guarantees

```text
.lig grammar
    │
    ▼
untrusted frontend → IR → Pager construction → code generation
                                             │
                    ┌────────────────────────┴───────────────────────┐
                    ▼                                                ▼
          dependent specification module                 parser module
          Grammar + Automaton                            generated value type V
          safety/completeness certificates              Runtime.Exec tables
                    │
                    ▼
          trusted validators + interpreter + theorems
```

The generic runtime proves:

| Guarantee | Assumption | Public theorem |
|---|---|---|
| Parsed results correspond to parse trees with the returned semantics | none | `Runtime.parseCorrect` |
| Internal `.Err` is unreachable on arbitrary inputs | `Safe` | `Runtime.parse_err_free`, `parse_ne_err` |
| A supplied parse tree is followed exactly; timeout obeys the tree-size fuel bound; `.Fail` and `.Err` are impossible on that trace | `Complete` | `Runtime.parseComplete` |
| Two parse trees for one word have equal semantics | `Complete` | `Runtime.unambiguity` |
| Parser execution simulates the dependent interpreter at matching fuel | generated `ExecRefinement`, `Safe` | `Runtime.Refinement.run_refines`, generated `parse_eq_dependent` |

`Safe` and `Complete` are derived from executable Boolean validators:

```lean
theorem safetyValidation :
    safeValidator (A := automatonInst) = true := by native_decide

theorem safety : Safe :=
  safe_of_safeValidator safetyValidation

theorem completenessValidation :
    completeValidator (A := automatonInst) = true := by native_decide

theorem completeness : Complete :=
  complete_of_completeValidator completenessValidation
```

`native_decide` discharges generated certificate and finite refinement-agreement
checks. It trusts compiled Boolean evaluation; the parametric runtime theorems
themselves use no `sorry`, custom axioms, or `Classical.choice`.

The validators establish that the emitted automaton satisfies the runtime
properties. They do not prove that the untrusted frontend preserved the author's
intended grammar; semantic correctness is relative to the emitted `Grammar`.

## 2. Trust boundary

**Trusted verified core** (`LeanParserGenerator/Runtime`, excluding `Exec.lean`):

- dependent grammar, parse-tree, automaton, and stream interfaces;
- interpreter;
- safety and completeness validators plus their linking theorems;
- soundness, operational safety, completeness, and unambiguity proofs.

**Untrusted implementation:**

- `.lig` frontend and normalized IR;
- nullable/FIRST analysis and Pager construction;
- certificate annotation and code emitters;
- lexer DFA construction and table emission (the emitted tables are validated by
  `native_decide` and the scanner is proved sound, §9.7–9.8 — parallel to the
  parser: construction is untrusted, the checked tables are not; the `lexre`
  frontend and the bytes-to-`Char` layer stay unverified);
- `Runtime/Exec.lean` and the executable backend.

A malformed automaton certificate or refinement witness fails generated
validation. `Runtime/Exec.lean` remains an implementation rather than part of the
specification; `Runtime.Refinement.run_refines` proves its generated instances
simulate the trusted dependent interpreter.

## 3. Repository layout

```text
LeanParserGenerator/
├─ Runtime/
│  ├─ Alphabet.lean
│  ├─ Grammar.lean
│  ├─ Automaton.lean
│  ├─ Buffer.lean
│  ├─ Interpreter.lean
│  ├─ Correct.lean
│  ├─ Safety.lean
│  ├─ Complete.lean
│  ├─ Validator/Safe.lean
│  ├─ Validator/Complete.lean
│  ├─ Exec.lean                 # native non-dependent engine
│  ├─ Span.lean                 # source spans on tokens/values, line:col rendering
│  ├─ Diagnostic.lean           # Menhir-style syntax-error diagnostics (unverified)
│  └─ Refinement.lean           # generic native/dependent simulation
├─ IR/Grammar.lean
├─ Construct/
│  ├─ Analysis.lean             # nullable and FIRST
│  ├─ LR0.lean                  # item cores and augmentation
│  ├─ LR1.lean                  # canonical LR(1) operations and Pager
│  ├─ Tables.lean               # Pager tables
│  └─ Annotate.lean             # validator certificate
├─ Frontend/File.lean           # .lig parser
├─ Emit/Codegen.lean            # parser backend
├─ Emit/CodegenVerified.lean    # dependent specification backend
├─ Emit/CodegenLexer.lean       # lexer backend
└─ Lexer/
   ├─ Regex.lean                # regex, CharClass, nullable/deriv, longestMatch
   ├─ Engine.lean               # Tokenizer, Compiled tables, tokenize, tokenizeStr
   ├─ DFA.lean                  # untrusted DFA construction, scan/scanStr, FlatDFA + flatScan
   ├─ Spec.lean                 # bestMatch, MatchStep, Tokenization spec objects
   ├─ Validator.lean            # LexCert certificate and Boolean validate
   ├─ Tokenize.lean             # tokenize_congr unambiguity + tokenize_sound
   ├─ StringScan.lean           # byte-index scanStr/tokenizeStr = List Char spec (bridge)
   ├─ FlatScan.lean             # flat state×class scan = DFA.scan given agreements
   ├─ FlatValidator.lean        # a-posteriori flatValidate → the three agreements
   └─ FlatTokenize.lean         # tokenizeFlatStr = tokenize (the emitted runtime)
```

The `%lexer { … }` surface syntax is parsed by `Frontend/File.lean` (the
`scanRegex*` functions), the same frontend that reads the rest of the `.lig`.

`Main.lean` is the `leanparsergenerator` CLI. `test/` contains grammars,
hand-written token/AST modules, committed generated modules, and regression tests.

## 4. Verified runtime

### 4.1 Grammar split

The computable grammar signature is separate from semantic types:

```lean
class GrammarSig where
  Terminal : Type
  NonTerminal : Type
  Production : Type
  prodLhs : Production → NonTerminal
  prodRhsRev : Production → List (Symbol Terminal NonTerminal)

class Grammar extends GrammarSig where
  semT : Symbol Terminal NonTerminal → Type
  prodAction : (p : Production) →
    arrowsRight (semT (.NT (prodLhs p))) ((prodRhsRev p).map semT)
  Token : Type
  tokenTerm : Token → Terminal
  tokenSem : (tok : Token) → semT (.T (tokenTerm tok))
```

Validators depend only on `GrammarSig`, so generated validation expressions are
native-computable. The interpreter and semantic theorems depend on `Grammar`.
Productions store the RHS in reverse stack-pop order.

### 4.2 Automaton certificate

`Automaton` supplies action/goto tables and the annotations checked by the two
validators:

- `lastSymb`;
- `pastSymb` and `pastStates` stack-shape summaries;
- LR(1) items and lookaheads;
- nullable and FIRST tables;
- initial-state start nonterminal.

Shift and goto values carry equalities tying target states to incoming symbols.
This makes malformed stack transitions explicit in the type of the table.

### 4.3 Interpreter and streams

The dependent stack is:

```lean
List (Σ state : NonInitState, semT (lastSymb state))
```

`TokenStream` abstracts sequential `head` and `tail`. Proofs use the transparent
`Nat → Token` instance; other stream implementations can use the same runtime.
`parseFix` uses logarithmic fuel: `logN` permits up to `2^logN` steps.

The dependent stack's element type depends on a runtime state through
`semT : Symbol → Type`. Lean therefore cannot compile the generic verified
interpreter after type erasure. Generated dependent specification parsers run by kernel
reduction (`decide`), while their Boolean certificates use `native_decide`.

## 5. Pager construction

`Construct/LR1.lean` implements Menhir's two-phase Pager design:

1. Build closed LR(1) candidates and transitions.
2. Group states by LR(0) core.
3. Drop candidates subsumed by an existing family member.
4. Repeatedly fuse states satisfying Pager's token-wise weak compatibility
   criterion.
5. Traverse again, redirect each transition candidate to a subsuming family
   member, and number only reachable states.

Compatibility is not transitive, so the growing fused candidate is checked again
against the remaining family. The grammar has no distinguished `error` token;
its generated `$` is an ordinary terminal, so Menhir's special error/stream-end
compatibility predicates are not needed.

Completed items reduce only on their LR(1) lookaheads. The exact final
`Collection.lr1Items` array is consumed both by table construction and certificate
annotation, preventing the executable tables and validator items from drifting.

`nullable` and `firstSets` are computed once in `pagerFrom` and passed into
`lr1Closure`/`lr1Goto`/`lr1Start`. LR(1) closure is called once per (state, symbol)
during both the discovery and numbering traversals — thousands of times on a
large grammar — so recomputing the two fixpoints inside `lr1Closure` (as an earlier
version did) made construction quadratic in the analysis cost. Threading the cached
tables through cut c99 construction from ~25 s to ~3 s with no change to the result.

`numberPager` keeps a `Std.HashMap (List AnnItem) Nat` from each discovered state to
its number, so the dedup lookup for a transition target is O(1). The previous
`states.findIdx? (· == target)` scanned every discovered state comparing full item
lists, which is O(states² × itemsize). The map mirrors `states` exactly — a state is
pushed and inserted together — so state numbering, and therefore the emitted
automaton, is unchanged.

Permanent tests cover:

- an LR(1)-not-LALR grammar requiring split same-core states;
- a genuinely ambiguous grammar that must still report a conflict;
- the no-incoming-edge invariant for state 0;
- generated safety/completeness validation and parser behavior.

## 6. Generated backends

One CLI invocation parses and constructs the grammar once, then renders both
modules from a shared `PreparedGrammar`:

```sh
leanparsergenerator Foo.lig FooVerified.lean FooParser.lean
```

Module names default to the two output stems. Explicit
`--backend verified|executable` remains available for a single output.

### 6.1 Dependent specification module

The dependent specification output contains:

- finite index types for terminals, nonterminals, productions, and states;
- a computable `GrammarSig` and `Automaton`;
- the dependent semantic `Grammar`;
- validator certificates and derived `Safe`/`Complete` properties;
- a kernel-reducible parser entry point.

### 6.2 Parser module

The executable output contains:

- a generated sum type `V` covering every semantic value type;
- `abbrev VP := Runtime.Span × V`, the engine value: each stack cell carries the
  semantic value together with its source span;
- token decoding `decode : Runtime.Positioned Tok → Nat × VP`, attaching each
  token's span;
- semantic actions over `List VP`: `sem`/`redv` bind, for a symbol `x`, both the
  value `x` and its span `x_span`, and fold the production's span as
  `Runtime.Span.merge (first symbol) (last symbol)` (Menhir's `$startpos`/
  `$endpos`; a single symbol folds to its own span, an empty RHS to the dummy
  span). An action that never mentions `x_span` pays nothing — generated `sem`/
  `redv` set `linter.unusedVariables false` so an ignored span binder is not a
  warning;
- flat Pager action/goto arrays;
- `run : List (Runtime.Positioned Tok) → Runtime.Exec.Result VP` and
  `parse : List (Runtime.Positioned Tok) → Option StartTy`, which drops the span;
- Menhir-style diagnostics wrappers `terminalName`/`diagnose`/`diagnoseSpanned`/
  `errorMessage` (§ error messages), where `diagnoseSpanned` recovers the
  offending token's span from `VP` for `line:col` rendering.

Both modules are generated from identical augmented grammar, state graph, and
parse tables. The paired specification module additionally emits a symbol-indexed
encoding into `VP` — `refinementEncodeValue` wraps each dependent value as
`(Runtime.Span.dummy, .ctor value)` — native-checked table/decoder obligations,
per-production semantic-action proofs, `parserRunRefines`, and
`parse_eq_dependent`. The dependent side has no spans: the refinement feeds
`Span.dummy`-tagged values, and because `Span.merge dummy dummy` reduces to
`dummy`, the per-production `refinementSemanticAgrees` still closes by `rfl`, so
the span machinery does not disturb the verified refinement.
The generic simulation in `Runtime/Refinement.lean` relates stacks, shifts,
reductions, finite EOF-padded inputs, matching logarithmic fuel, and final parser
results. The sum representation uses no `unsafeCast`.

## 7. Generator invariants

These constraints are not obvious from the emitted APIs and must be preserved:

1. **Augmentation is `S' → S $`.** Consuming `$` makes the accepted start
   language prefix-free and gives completeness the required start behavior. The
   augmented action ignores `$` and returns the `S` value.
2. **State 0 is only `Init`.** Pager state `k + 1` maps to `Ninit ⟨k⟩`; state 0
   has no incoming edge. The disjoint types are required by safety validation.
3. **Dependent tables use reducible `match`-on-`Fin`.** Shift/goto equalities
   close by `rfl` only when `lastSymb` reduces by iota; array lookup is too opaque.
4. **Production contents use one dependent match.** `prodContents` returns the
   `(lhs, rhsRev)` pair and action together through `box`. Separate large matches
   cause quadratic type reduction on Cedar-sized grammars.
5. **Large finite matches have a catch-all.** Lean does not always recognize
   consecutive `Fin` literal arms as exhaustive at large cardinalities.
6. **`grammarInst` extends the emitted `sigInst`.** Their signatures must be
   definitionally equal so validators and interpreter use the same automaton.
7. **Executable tables are flat arrays.** Thousands of generated match arms are
   expensive to elaborate; row-major arrays keep generated modules tractable.

## 8. `.lig` grammar syntax

A grammar is read at build time:

```text
%header {
import calc.CalcAst
open Calc
}
%tokentype Tok
%token PLUS TIMES LPAR RPAR
%token <Int> NUM
%token EOF
%eof EOF
%start expr
%%
expr :: Int
  | e=expr PLUS t=term    { e + t }
  | t=term                { t }
term :: Int
  | t=term TIMES f=factor { t * f }
  | f=factor              { f }
factor :: Int
  | LPAR e=expr RPAR      { e }
  | n=NUM                 { n }
```

- `%header` is copied verbatim into the generated module.
- `%tokentype` names the user's token inductive.
- `%token` declaration order fixes terminal indices; `%token <T>` carries a
  semantic value of type `T`.
- `%eof` names the token mapped to generated `$`.
- `%start` names the entry nonterminal.
- `%option <name>` sets a code-generation option (§below). The three accepted
  names are `compress_tables` (compact table literals, §10.`%option compress_tables`),
  `roundtrip_lexer` (also emit the lexer roundtrip module, §16.4), and the
  value-carrying `module_prefix <path>` (the dotted prefix the generated modules
  live under, e.g. `%option module_prefix calc` so the parser imports
  `calc.CalcLexer`). Options affect only how the modules are emitted and which
  ones, never the grammar the proofs are about; an unknown name is rejected.
- `name=symbol` binds an RHS value for the Lean semantic action.
- Rule and token constructors must agree with the declarations.
- An optional `%lexer { … }` block defines a tokenizer, so one CLI invocation
  generates the parser and the lexer together (LALRPOP-style). It carries
  `let name = <lexre>` definitions and `| <lexre> [as x] => { <action> } | skip`
  rules (with `enter`/`↓`, `leave`/`↱` mode transitions and an optional
  `eof => { … }`), where `<lexre>` is the regex sub-syntax parsed by
  `Frontend/File.lean` into `Lexer.Regex`
  (`"str"`, `'c'`, `_`, `ε`, `[ … ]`/`[^ … ]`, `*`, `+`, `?`, concatenation,
  `|`, grouping, and `let`-name references). Actions are captured verbatim like
  production actions. The primary CLI form infers every output from the `.lig`
  path and its `%option`s: `leanparsergenerator Foo.lig` writes `FooVerified.lean`,
  `FooParser.lean`, `FooLexer.lean` (when a `%lexer` block is present), and
  `FooLexerRoundtrip.lean` (when `%option roundtrip_lexer` is also set) next to the
  input. Explicit output paths and module names remain accepted as overrides
  (`leanparsergenerator Foo.lig FooVerified.lean FooParser.lean FooLexer.lean`, or
  `--lexer Foo.lig FooLexer.lean [Module]`). Either way it builds the DFA and
  validator certificate offline and writes an inspectable `FooLexer.lean` (§9).

The frontend preserves source spans so future `.lig` diagnostics can map errors
from generated Lean back to grammar locations.

### Parameterized-rule macros

A right-hand-side symbol may be a Menhir-style parameterized-rule application, which
`Frontend/Macros.lean` expands (before Pager construction) into a fresh concrete
nonterminal:

```text
top :: Prog
  | items=separated_list(COMMA, item) opt=option(trailer)  { Prog.mk items opt }
```

The built-ins are `list(X)`, `nonempty_list(X)`, `option(X)`,
`separated_list(sep, X)`, and `separated_nonempty_list(sep, X)`. Each distinct
application becomes one auto-named nonterminal (`separated_list_COMMA_item`) with the
usual alternatives and a result type derived from `X`'s declared type
(`List (…)` / `Option (…)`); `sep` is a terminal that carries no value. Repeated
identical applications share one generated nonterminal.

These are pure surface sugar: the expansion runs before `irOfSurface`, so the IR,
Pager tables, and proofs see only ordinary rules — the trust boundary is unchanged.
Expansion does **not** reduce the automaton's state count (a macro grammar and its
hand-written equivalent produce identical states); it only removes the boilerplate of
hand-writing recursive `list`/`separator` nonterminals, which matters for
list-heavy grammars.

## 9. Lexer

The lexer produces the token type declared by `%tokentype`, with
regular-expression definitions, maximal-munch matching, mode stacks, `skip`, and
an optional `eof => TOKEN` action. It is generated by the offline CLI, parallel to
the parser:

A `%lexer { … }` block in the `.lig` file (§8) is read by `leanparsergenerator`,
which builds the DFA and the validator certificate at generation time
(`Lexer.DFA.build?WithVecs`, ordinary compiled code, like Pager construction) and
writes an inspectable `FooLexer.lean` module: the tokenizer with its DFA tables
and certificate as literal data (a `Lexer.Compiled Tok`), the `native_decide`
validation theorem `FooLexer.validated⟨m⟩`, the maximal-munch soundness corollary
`FooLexer.scanSound⟨m⟩`, the flat `state × class` tables (`FooLexer.cflat`) with
their `native_decide` agreement theorem `FooLexer.flatValidated⟨m⟩`, and a
`FooLexer.tokenize` entry point that runs the fast flat scanner and returns
`List (Runtime.Positioned Tok)` — each token wrapped with its source `Span`
(`Lexer.tokenizeFlatStrPos`, §9.7 step 1, §9.8) (`Emit/CodegenLexer.lean`). The
bare `List Tok` path stays available as `FooLexer.tokenizeBare`
(`Lexer.tokenizeFlatStr`), used by the roundtrip theorems and the byte path;
`tokenizeFlatStrPos_val` proves the positioned tokens' values are exactly the bare
output, so `tokenize_sound` transfers unchanged. This is the
analogue of the parser's generated
modules — untrusted construction plus emission, with the emitted `native_decide`
the checked boundary.

The DFA construction, scanner, validator, and soundness proofs live in `Lexer/`
and are shared by every generated lexer; only the tables and certificate differ
per grammar. An earlier in-Lean DSL that built the same tables at Lean
*elaboration time* has been removed: there is one path, the CLI, and generated
lexers are written source files, not spliced definitions. `Compiled.ofTokenizer`
(`Lexer/Engine.lean`) still builds the tables at run time, but only as the
cross-check reference used by `test/cedar/CedarBench.lean`, not as a generation
path.

A verified bytes-to-tokens layer is later work and can remain independent of the
parser refinement.

### 9.1 Starting point and its cost

The lexer began (`Lexer/Regex.lean`, `Lexer/Engine.lean`, and an in-Lean DSL macro
since removed) as a
live Brzozowski-derivative interpreter. `Tokenizer` holds, per mode, an ordered
list of `Rule`s, each a `Regex` tree and an action. `tokenizeAux` scanned a
`List Char`; at every position `bestMatch` ran `Regex.longestMatch` for every
rule independently, and `longestMatch` took a derivative per character. There was
no offline construction and no table: the automaton was the regex term, walked at
scan time. This subsection records why that was replaced; §9.6 records the
measurements, and the interpreter tokenizer no longer exists.

This is slow, and the slowness is algorithmic, not a constant factor. On Cedar
policies the interpreter lexer measured about 800x slower than the Rust lexer,
while the generated parser was only a small constant factor slower than its Rust
counterpart (the current fused lex+parse is ~1.65x, §9.6.1). The causes of the
interpreter's slowness, in decreasing order of impact:

1. **`longestMatch` scans the whole remaining input.** Its `go` recurses to the
   end of `cs` even after the regex has derived to `never`, so matching a short
   token near the start of an `N`-character input still walks `N` characters. With
   `k` rules this is `O(N² · k)` over a file. This is the dominant term.
2. **No shared automaton across rules.** `bestMatch` re-derived the input against
   all `k` rules at every position; maximal munch was recomputed per rule from
   scratch.
3. **Derivatives are not simplified.** `deriv` builds `cat`/`alt`/`star` nodes
   without collapsing `never`/`epsilon`, so the regex term grows as the scan
   proceeds and `nullable`/`deriv` get slower per step.
4. **`List Char` with per-token `take`/`drop`/`ofList`.** The input is a linked
   list; each token does `O(len)` slicing and rebuilds a `String`.

Rust's lexer is a linear DFA scan, `O(N)` with a small constant. That gap
explains the 800x.

### 9.2 Target: a generated table, mirroring the parser's runtime split

The lexer adopted the *generator + flat-table + generic-runtime* half of the
parser architecture (§1, §6), which is what makes the parser fast:

- An untrusted construction step compiles each mode's rule set to a DFA. Brzozowski
  derivatives move from scan time to build time: derivative classes give the DFA
  states, so the existing `Regex` engine is reused, not discarded.
- An emitter writes a `LexerTables` value: a flat transition `Array` over a
  compressed alphabet (`Char → class id`), per-state accept information recording
  which rule accepts (ties broken by rule order, preserving current semantics),
  and the mode-stack action for each accepting rule.
- A generic `Runtime.Lexer.run` scans a `String` by index against the table,
  tracking the last accepting state for maximal munch, allocating nothing per
  token until it slices the lexeme. This is the lexer analog of
  `Runtime.Exec.run`.

The `.lig` `%lexer` block stays as the surface syntax; it feeds construction
instead of building a `Tokenizer` of live regexes. The table was at one point
built at Lean *elaboration time* inside an in-Lean `lexer` macro; that path was
later replaced by the generated *source file* route the parser backends use
(`Emit/CodegenLexer.lean`, §9), so the DFA and certificate are emitted as literal
data in `FooLexer.lean`.

### 9.3 Where a-posteriori validation does and does not apply

The parser uses untrusted construction plus a validated certificate because LR(1)
construction is hard to prove correct directly, so checking a witness is easier
than verifying the constructor. The lexer takes the same route, for the same
reason and with one structural difference.

The reason: the hard part of `Lexer/DFA.lean` is not the derivative theory, it is
the alphabet partitioning — `classIntervals`, `boundaries`, and the atom grouping
in `transitionsOf`. That code sorts, merges and complements interval lists and
groups atoms by successor vector. Proving it correct means proving all of that
correct. Checking its output does not: the construction already computes the only
certificate needed, namely each state's derivative vector, so annotating the
emitted tables with it is nearly free, and the conditions relating the vectors to
the edges are cheap to check.

The structural difference from the parser: the parser's validators enumerate the
alphabets, because terminals, states and productions are `Finite`. The lexer
cannot do that — its alphabet is the 1.1M Unicode scalar values. Every validation
condition therefore has to be *interval arithmetic* over `CharClass` (containment,
disjointness, coverage) rather than quantification over characters. §9.7 gives the
conditions in that form.

This is also why `CharClass.opaque` has to go before any of it (§9.7). An opaque
`Char → Bool` has no interval structure to check, which is the same reason it
defeats `DecidableEq` and makes the `opaqueWindow` assumption in `classIntervals`
unprovable.

§9.7 has since been carried out (steps 0, 2–5; §9.8): the emitted lexer tables are
validated by `native_decide` and the scanner's maximal-munch soundness is proved,
so the lexer's DFA scan is on the verified path. The token→character *frontend*
(the `lexre` → `Regex` translation) and the bytes-to-`Char` layer remain unverified
— see the §2 trust boundary and §9.7's "out of scope".

### 9.4 Properties to establish

The target properties, in the order §9.7 builds them:

- **Language agreement.** The DFA state reached after consuming a prefix accepts
  exactly when some rule's regex matches that prefix, i.e. the tables agree with
  `Regex.matchesFull`.
- **Maximal munch.** Each step consumes the longest prefix accepted by any rule,
  ties broken by rule order: `DFA.scan` agrees with `Regex.longestMatch` minimized
  over rule order. `matchesFull` and `longestMatch` are kept in `Lexer/Regex.lean`
  for exactly this purpose — they are the derivative-based statement of what the
  tables are supposed to compute, not an execution path.
- **Tokenization soundness and completeness.** `Lexer.tokenize` returns a token
  list precisely when a maximal-munch tokenization derivation exists, and returns
  that derivation's tokens (§9.7 step 2).
- **Unambiguity**, which unlike the parser's is a lemma rather than a separate
  obligation: maximal munch is deterministic, so the derivation is unique, and
  uniqueness gives unambiguity without a `Complete`-style hypothesis.
- **Round-trip (token fixed point).** Lex a source to tokens `T₁`, render `T₁`
  back to text, lex that text to `T₂`, and require `T₂ = T₁`. This is a fixed
  point on the *second* lex, not a text-identity round trip, and it is not
  unconditional. Some actions are lossy by design, and the Cedar lexer
  (`test/cedar/CedarLexer.lean`) shows every case:
    - keyword folding: `keywordOrIdentifier` maps `"if"` to `.IF`, dropping the
      surface text;
    - value normalization: `NUMBER value.toNat!` discards leading zeros and the
      original digit string;
    - text stripping: `stripStringQuotes` drops the surrounding quotes;
    - discarded tokens: whitespace and `//` comments `skip`, so they are gone
      after the first lex and cannot round-trip.
  The property therefore needs a defined token→text rendering and holds only up to
  re-lexing equality, and only for tokens whose rendering re-lexes to the same
  token. A correct rendering emits canonical surface text for each token
  constructor (for example, the keyword spelling for `.IF`, a canonical decimal
  for `.NUMBER n`, a re-quoted-and-escaped form for `.STRINGLIT`), and skipped
  tokens are simply absent from `T₁`. Stating and proving this cleanly is a reason
  to keep token payloads carrying enough information to reprint, or to accept the
  documented lossy cases explicitly.

### 9.5 Plan of work

The work was done in this order and is complete (§9.6 for timings, §9.7/§9.8 for
proofs): (1) baseline with `test/cedar/CedarBench.lean`; (2) cheap derivative fixes
keeping the interpreter shape (stop `longestMatch` at `never`, `never`/`epsilon`
smart constructors); (3) build the DFA construction/scan and emit the tables as data
in `FooLexer.lean`, removing the interpreter tokenizer; (4) verify per §9.7 (clear
the blockers, define the `Tokenization` derivation, validator conditions, generic
theorem, per-lexer `native_decide`), then the `String.Pos` runtime and the flat
`state × class` scanner, each carried across a-posteriori without re-proving
soundness. The round-trip rendering (§9.4) is independent and not yet done.

### 9.6 Measurements

Corpus: `cedar-spec/cedar-benchmarking/corpus` driven by `test/cedar/CedarBench.lean`.
Native-compiled; per-item
averages for before/after comparison, not absolute figures. Every step below keeps
the token output identical (checksums unchanged).

The lexer went from a live derivative interpreter to a validated flat-table scanner
in four stages, each removing a §9.1 cause:

| Stage | Cedar lex-only | What changed |
|---|---|---|
| Interpreter | ~92,000 us (1 KB file) | whole-input scan + unbounded derivative growth (§9.1 causes 1, 3) |
| Derivative fixes | 755 us/policy | stop `longestMatch` at `never`; `never`/`epsilon` smart constructors |
| DFA (`Compiled.ofTokenizer`) | ~210 us/policy | array-indexed `DFA.scan` shared across rules (§9.1 cause 2, at scan time) |
| `String.Pos` runtime | 143 us/policy | walk the `String` directly, `String.extract` lexemes, no `List Char` (§9.1 cause 4) |
| Flat `state × class` table | **66.8 us/policy** | one `classOf` + one flat table read per char, replacing `stepChar`'s edge-list search |

The tables are emitted as literal data in `FooLexer.lean` (`Emit/CodegenLexer.lean`),
not built at run time; a `.olean` grows by ~876 KB (in line with the parser tables).

The final flat scanner is the current runtime. After the `String.Pos` change a
profiler attributed ~87% of lex-only time to the DFA walk (`DState.stepChar`:
`Array.findSome?` over the state's edges, each a `List`-range `CharClass.mem`);
`Lexer/DFA.lean`'s `FlatDFA` replaces that with a `classOf : Char → classId` (binary
search over sorted class boundaries + a 128-entry ASCII fast path) and a flat
`state × classId → target` array, scanned over `String.Pos` by `DFA.flatScanStr`
(`Lexer/FlatTokenize.lean`'s `tokenizeFlatStr` is the emitted `FooLexer.tokenize`).
Soundness is a-posteriori (§9.7 step 1, §9.8): a Boolean `flatValidate`
(`Lexer/FlatValidator.lean`) checks the flat tables step/accept identically to the
DFA, discharged per lexer by `native_decide`, and `tokenizeFlatStr_eq_tokenize`
proves the emitted tokenize equals the spec `tokenize` (axioms only
`propext`/`Classical.choice`/`Quot.sound`), so `tokenize_sound` transfers unchanged.

Measured effect of the flat scanner vs the `List Char` and `String.Pos` runtimes
(2000 iterations; lex-only checksums identical throughout, so tokens are unchanged):

| Corpus | `List Char` | `String.Pos` | flat | speedup vs `List Char` |
|---|---|---|---|---|
| Cedar `generated/` (22) | 185.3 us/policy | 143 | 66.8 | ~2.2x |

A profiler decomposition of the flat path on Cedar: flat scan ~45 us/policy (~72%,
~29 ns/char), `String.extract` lexeme ~7 us, per-token semantic actions ~11 us
(user code the generator cannot speed up — keyword folding, `String.toNat!`,
token-list building), list building ~0. This is the ceiling for the
scan-representation lever: ~2.2x, sound, tokens identical, not an order of magnitude
because per-token user actions dominate the remainder.

Abandoned along the way, each for the stated reason:
- The `LexRefinement` plan (prove soundness on the fast flat object directly) was dropped once soundness was already proved against `DFA.scan`, leaving the a-posteriori validator as the simpler bridge.
- A linear `classOf` (scan 59 classes per char) regressed on Cedar, so `classOf` is a binary search with an ASCII fast path.
- Building the flat boundaries from complement-resolved `classIntervals` endpoints failed `flatValidate` on the calculator's negated classes, so boundaries are the raw edge-class endpoints (where `CharClass.mem` actually changes).
- A fused `state × 128` direct-ASCII transition table (one read per ASCII char) measured identical to `classOf`+table, so it was not adopted.
- The interim `test/LexerEmitAgreementTest.lean` (compare emitted tables against a run-time rebuild) was removed once the emitted tables are validated directly (§9.7 step 5).
- Against Rust `PolicySet::from_str` the end-to-end lex+parse is ~1.65x on the
  current flat+redv runtime (§9.6.1), down from ~2.4–2.9x on the pre-flat runtime.
  Cedar's Rust parser fuses lexing and parsing (`logos` DFA + LALRPOP) in one call,
  so there is no Rust lex-only figure to compare against; only the fused unit is
  comparable.

### 9.6.1 Rust comparison (lex+parse as one unit)

Cedar cannot separate lexing from parsing, so the comparison is against the fused
unit on both sides. Rust: the `cedar-benchmarking` `policy_parse` target
(`src/executor.rs`, `bench_policy_parsing`) times `src.parse::<PolicySet>()` — file
read once, 10 warmups, then timed trials with `black_box`. Lean: `CedarBench.lean`'s
`[lex+parse]` (`CedarLexer.tokenize` then `CedarParser.parse`). Both ran on the same
28-file corpus (`cedar-spec/cedar-benchmarking/corpus`: 22 `generated/`, 2
`clauses/`, `tinytodo`, 3 `oopsla/`), native/release, 4000–6000 iterations, all 28
policies accepted on both.

I could not build the `cedar-benchmarking` binary directly against this checkout:
`cedar-policy-generators` has drifted from `cedar` core 4.12.0 (5 × E0599, e.g.
`ExprKind::ExtHasAttr`/`Expr::extended_has_attr` removed from core). That crate is
only used for authorization request generation, not `policy_parse`, so I built a
standalone harness linking only `cedar-policy 4.12.0` that reproduces
`bench_policy_parsing`, recording per-trial time in nanoseconds (the shipped tool
truncates to whole microseconds, which would bias the fast policies; nanosecond
timing is if anything slightly more favorable to Rust).

Per-policy mean over the 28-policy corpus:

| Engine | per-policy mean | notes |
|---|---|---|
| Rust `policy_parse` (lex+parse) | ~117 us | 3 runs: 117.2, 116.3, 116.9 |
| Lean `[lex+parse]`, warm | ~195 us | 5 warm runs: 190.7–201.1 |
| Lean lex-only | ~72 us | matches §9.6 |
| Lean parse-only | ~120 us | `CedarBench` `[parse only]`, full 28-policy corpus |

So Lean lex+parse is **~1.65x slower than Rust** (≈195 vs ≈117 us). The first
Lean iteration paid a ~273 us warm-up cost that the steady state does not; the
warm figure is the fair one. The split is ~72 us lex + ~120 us parse (192 ≈ the
fused 195, so little slack between phases). Two boundaries keep this from being a
pure like-for-like constant factor: the bytes-to-`Char` decode is excluded on the
Lean side (§2), and Rust builds its validated `PolicySet` AST while Lean builds
`CedarAst`, so the parse-side allocation differs.

### 9.6.2 Fused lex+parse: measured, no gain found

Cedar's Rust parser fuses lexing and parsing into one driver (§9.6.1). I measured
whether a fused Lean lexer+parser recovers any of the ~1.65x gap, with a throwaway
harness (since removed) reusing the emitted flat lexer and parser tables so only the
handoff differed. Three fused drivers (log-fuel recursion + `List` stack; imperative
`while` + `List` stack; imperative `while` + `Array` stack) all agreed with the split
path on the 28-file corpus and all ran *slower* (0.95x, 0.88x, 0.47x). Removing the
intermediate `List Tok` recovers nothing here: the list is cheap (§9.6 put list
building at ~0), and each fused loop re-boxes a lookahead per parser step. The `Array`
stack was 2x slower because through `Id.run do`/`let mut` the array reference is not
provably unique, so `push`/`shrink` copy on nearly every step; a genuinely in-place
stack needs linearity (`ST` with a unique ref), not pursued once fusion showed no
benefit. Fusion is not made the primary spec anyway — if ever wanted it can be a
library-level equivalence `runFused = runRedv (tokenize |>.map decode)`, keeping the
`List Tok` theorems. The one regime not covered is a multi-GB single input file, where the
intermediate `List Tok` is one file-sized allocation; that is a
memory-residency question a 49 KB corpus cannot surface, and fusion there should be
re-measured before committing.

### 9.6.3 A byte-level scanner (implemented; proved-default pending)

The `~72 us` Lean lex figure and the `~1.65x` fused gap both *exclude* the
bytes-to-`Char` decode layer (§2, §9.6.1), which is a separate pass over the input
that Rust's `logos` does not pay — `logos` scans UTF-8 bytes directly. The flat
runtime (§9.6, §9.8) scans a `String` by `String.Pos`, i.e. over already-decoded
`Char`s, and the alphabet partition (`Lexer/DFA.lean`) is over Unicode scalar values.
A byte-level scanner moves the DFA alphabet to `UInt8`, scans the `ByteArray`
directly, and folds the decode into the same pass — removing the separate decode and
shrinking the per-char cost (a 256-wide byte table, no `String.Pos` `get`/`next` UTF-8
stepping). This is a structural lever on lex throughput orthogonal to the parser
refinement: the parser theorem still begins at tokens.

The scanner is implemented as a byte-expansion of the already-verified `FlatDFA`,
not a fresh automaton against `Regex` semantics, so the soundness chain
(`FlatDFA = DFA.scan = MatchStep`) is inherited rather than rebuilt. The runtime and
construction are done, the byte↔flat scan simulation is proved up to a Boolean
agreement, and the scanner is emitted into every lexer as a `native_decide`-validated
fast path; the one remaining piece is deriving that Boolean agreement for all `Char`,
so `tokenizeByte` can become the proved default. The details follow.

`Lexer/ByteScan.lean` defines `ByteDFA` (a flat `state × 256` byte-transition table
plus a boundary/intermediate state split — boundary states are the char-DFA states
and the only accepting ones; intermediate states thread the UTF-8 continuation bytes
of a multi-byte code point) and `ByteDFA.byteOfFlat`, which byte-expands a `FlatDFA`
per state per class via `Utf8Ranges.compile` (the standard code-point-interval →
UTF-8 byte-range-sequence construction, so the Unicode catch-all class compiles to 9
sequences, not a million code points). On Cedar's flat DFA this produces 71 byte
states (57 boundary + 14 intermediate), and the byte tokenizer produces byte-for-byte
identical tokens to `CedarLexer.tokenize` on sample policies. Construction is
untrusted, validated a-posteriori.

`Lexer/ByteValidator.lean` proves the byte walk simulates the flat char walk:
`byteScanListGo_consume` shows that from a boundary state, consuming one char's UTF-8
bytes lands on `FlatDFA.step` for that char while passing only through non-accepting
intermediate states (no mid-code-point accept), and `byteScanListGo_eq_flatScanCharGo`
lifts this by induction over the input to show the byte scan and the flat char scan
record the same rule. These are proved with no `sorry` and only the standard axiom
budget, up to `byteScan_rule_eq_flatScanArr`: given the agreements, the byte scan over
`s.toUTF8` records the same rule as the flat scan over `s.toList` (which
`flatScanArr_eq_scan` ties to `DFA.scan`). The remaining piece is a Boolean validator
deriving the abstract byte agreements (`ByteStepAgree`/`ByteNoMidAccept`, quantified
over all `Char`) that these theorems assume. The obstacle is real and is the "real
work" flagged above: a flat class holds code points with different UTF-8 byte
sequences, so a single class-representative check does not cover the class the way it
does for the char-level `FlatDFA`, and the byte run is not constant across a class at
the byte level. Full code-point enumeration is not a way out — validating
`runList = f.step` at every scalar value for every state measures ~250 s of native
evaluation on Cedar (57 states × ~1.1M code points), far past what `native_decide` can
discharge. The provable route is to certify the byte automaton recognizes each class's
UTF-8 byte ranges (`Utf8Ranges.compile` correctness). The ASCII fragment of this is
proved (`runList_utf8EncodeChar_ascii`: a single-byte code point's run is one validated
byte step); the multi-byte fragment (byte-range coverage of the non-ASCII classes — for
Cedar the single catch-all class) is what remains. The runtime `String.toUTF8`
input is bridged to the `encodeChars` list model by `toUTF8_size_eq`/`toUTF8_getElem_eq`
(via `String.utf8Encode_toList`), the one place `String`/`ByteArray` internals appear.

`Lexer/ByteTokenize.lean` is the runtime byte tokenizer (`CompiledByte` = a
`CompiledFlat` plus per-mode `ByteDFA`; `tokenizeByte` scans `input.toUTF8` by byte
index and slices lexemes with `ByteArray.extract`/`String.fromUTF8!`, reusing the
`needsText` skip). Measured lex-only, byte tokenizer vs the flat `String.Pos`
tokenizer, native/release (the `[byte lex]` phase of `cedar-bench`), tokens
byte-for-byte identical (Cedar 28/28):

| corpus | flat lex | byte lex | speedup |
|---|---|---|---|
| Cedar (28 files) | ~68 us/file | ~58 us/file | ~1.17x |

So folding the UTF-8 decode into the scan removes ~15% of lex time on these ASCII
corpora, where the `String.Pos` cursor's per-char UTF-8 stepping is pure overhead. The
win would be larger on multi-byte input (the byte scanner reads each byte once; the
`String.Pos` path decodes a code point per step). This is the throughput half of the
goal; the verified half (the byte validator deriving the agreements) is the remaining
work noted above.

The emitter (`Emit/CodegenLexer.lean`) now generates the byte scanner into every
lexer: per mode a `ByteDFA` (`FooLexer.cbyte = CompiledByte.ofFlat cflat`), a
`FooLexer.byteValidated{m} : byteValidate … = true := by native_decide` check, and a
`FooLexer.tokenizeByte` entry point. The proven `FooLexer.tokenize` stays on the flat
`String.Pos` scanner, so all existing guarantees are unchanged; the byte path is an
additional, per-lexer `native_decide`-validated fast path (the same a-posteriori
discharge the flat tables use). The generated lexers (calculator, Cedar,
CedarSchema, CedarEntities) regenerate, compile, and discharge `byteValidated{m}`, and their
`Verified` proofs (Cedar checked directly) still check. Making `tokenizeByte` the
proved default awaits `agreements_of_byteValidate` (the derivation noted above); until
then `tokenize` remains the proved path and `tokenizeByte` the validated fast path.

### 9.6.4 Further lexer optimization candidates

Fusion (§9.6.2) found no gain; the byte scanner (§9.6.3) is the one structural lever
that did, and is implemented. Two smaller lexer-side candidates were tried against the
*measured* hot spots (lex ~72 us: 45 us flat scan, 7 us `String.extract`, 11 us user
actions). Parser-side candidates are recorded separately in §13.

1. **Skip the lexeme copy for fixed-text tokens — done, retained.** `String.extract`
   (~7 us, ~9% of lex) copied the matched bytes for every token, but most tokens
   (`PLUS`, `LBRACE`, punctuation, and — where matched by literal rules — keywords)
   discard the text: the action ignores its `String` argument and emits a constant.
   The emitter now marks each rule text-dependent iff its action binds the lexeme and
   emits (`r.binder.isSome && r.emit.isSome`), recorded as `CompiledFlat.textDep`. The
   runtime (`tokenizeFlatStrAux`) passes `""` for text-independent rules and only
   `String.extract`s for the rest. Soundness: `tokenizeFlatStr_eq_tokenize` gained a
   hypothesis `htext` (a text-independent rule's action is constant in its argument,
   so `""` and the real lexeme give the same `Act`); the proof cases on `needsText`,
   the `false` case rewriting by `htext`. Measured: Cedar lex-only −5.6% (73.7→69.6
   us); tokens identical, `CedarVerified` unchanged.

2. **Reduce `Nat`/`String.Pos` arithmetic in the scan loop — non-optimizing.** At ~29
   ns/char the flat scan is the largest lex cost. `classOf` already routes code points
   `< 128` through an O(1) 128-entry ASCII table and only reaches `bsearch` for
   `n ≥ 128`. The Cedar corpus is 100% ASCII (0 bytes ≥ 128), so the fast
   path is hit on every character and `bsearch` is never entered — there is nothing to
   change. The remaining per-char cost is UTF-8 decode + machine-int arithmetic, which
   only the byte scanner (§9.6.3, deferred) removes.


### 9.7 Verification plan

This is the plan the verification follows; §9.8 records what is implemented (steps
0–5 are all done — step 1, the flat table, is the emitted runtime). It mirrors the
parser's architecture (§1, §6, §11)
rather than only borrowing its tactics: an untrusted construction, a Boolean
validator over an emitted certificate, one generic theorem turning validation into
the properties, and per-lexer `native_decide` to discharge the Boolean. The
differences from the parser are that the alphabet cannot be enumerated (§9.3), the
fuel bound is exact rather than logarithmic, and unambiguity is a lemma rather than
an obligation.

**Step 0 — clear three blockers.** None of the rest is worth starting first.

- Remove `CharClass.opaque`. It makes language agreement unprovable
  (`classIntervals` scans `[0, opaqueWindow)` and *assumes* the predicate is false
  above, which cannot be shown for an arbitrary `Char → Bool`), it merges DFA
  states wrongly (`CharClass.beq` compares opaque classes by name only, so two
  different predicates sharing a name are treated as equal), and it blocks
  `DecidableEq CharClass` and hence the validator. It is not needed: Lean's
  `Char.isWhitespace` resolves to exactly `[(9,10),(13,13),(32,32)]`, so
  `test/cedar/CedarLexer.lean` and `test/cedarschema/CedarSchemaLexer.lean` can use
  an explicit class. Note the separate finding that this exposed: Lean's
  `Char.isWhitespace` is false for U+0085, U+00A0, U+2028 and U+3000, where Rust's
  `char::is_whitespace` is true, so the Cedar fixtures may not match
  `grammar.lalrpop` on Unicode whitespace. That is a fixture-fidelity question to
  settle before differential testing against the Rust parser, independent of this
  plan.
- Make `DFA.build` signal failure. Its loop is
  `while !worklist.isEmpty && steps > 0`; on fuel exhaustion the unprocessed states
  keep `default`, which has no edges and no accept, so the lexer silently rejects
  valid input. It should return `Option DFA`/`Except`. The proof needs "the
  worklist emptied" as a hypothesis regardless.
- Decide the surrogate story. The atom partition covers `[0, maxCodePoint]`
  including `[0xD800, 0xDFFF]`, which contains no valid `Char`; `repOf` dodges the
  gap and `Char.ofNat` maps invalid values to U+FFFD. The theorem must quantify
  over valid scalar values only.

**Step 1 — the flat-table optimization (throughput; now implemented and sound).**
§9.6's `String.Pos` runtime still spent ~87% of lex-only time in the DFA walk
(`DState.stepChar`: `Array.findSome?` over the state's edges, each a `List`-range
`CharClass.mem`). A flat representation — a `classOf : Char → classId` map plus a
flat `state × classId → target` array — replaces that per-character search with two
array reads. The original plan was to do this *before* proving soundness, "in
refinement shape", with a `LexRefinement` tying the fast table to the
derivative-level DFA so the soundness theorem would be about the fast object. That
premise did not hold in the interim (soundness was proved directly against
`DFA.scan`, §9.8), so this became a pure throughput change carried across by an
a-posteriori validator — the parser's route, not a rewrite of the soundness proof.

Implemented in `Lexer/DFA.lean`, `Lexer/FlatScan.lean`, `Lexer/FlatValidator.lean`,
and `Lexer/FlatTokenize.lean`:

- `structure FlatDFA` holds `bounds` (sorted class boundaries, the raw endpoints of
  every edge class of every state), `nClasses`, `nStates`, a 128-entry `ascii`
  fast-path class table, a flat `trans : Array Nat` (`state*nClasses + classId ↦
  target+1`, 0 = dead), and `accept : Array Int` (rule, or −1). `classOf` is a
  binary search (`bsearch`) over `bounds` with the ASCII table for code points < 128.
  `DFA.flatOfDFA` builds it from the derivative-vector DFA (untrusted).
- `DFA.flatScanStr` walks a `String` by `String.Pos` with `FlatDFA.step`/`acceptOf`
  (the same shape as `scanStr`); `tokenizeFlatStr` (`Lexer/FlatTokenize.lean`) is the
  emitted `FooLexer.tokenize`, slicing lexemes with `String.extract`.
- Soundness is a-posteriori. `flatValidate f dfa : Bool` (`Lexer/FlatValidator.lean`)
  checks, per state and per flat class, that the flat step and accept agree with the
  DFA at the class representative, that `CharClass.mem` is constant on each flat class
  (`intervalConst`, no edge-class endpoint strictly inside the class — the interval
  form of the constancy `stepChar_congr` needs), that transition targets are in
  range, and the bounds/ascii shape. `flatScanArr_eq_scan_of_valid`/
  `flatScanStr_eq_scanStr` prove that when `flatValidate = true` the flat scanner
  equals `DFA.scan`/`scanStr`, and `tokenizeFlatStr_eq_tokenize` lifts that to the
  whole tokenizer for a single validated mode with stack-preserving actions. The key
  lemma is `bsearch_spec` (the binary search brackets each code point in its class
  interval). All carry only the `propext`/`Classical.choice`/`Quot.sound` budget; the
  per-lexer `flatValidate = … := by native_decide` adds one `native_decide` axiom, as
  the derivative-vector `validate` already does. So `DFA.scan`/`tokenizeAuxDFA` remain
  the specification, and the fast flat scanner is a verified-equal running object —
  exactly the `LexRefinement` role, discharged by a validator instead of a
  hand-proved constructor. Measured ~2.2x lex-only on Cedar (§9.6), tokens
  identical.

The related `List Char` removal (§9.1 cause 4) is also done: before the flat scanner,
the runtime already walked the `String` by `String.Pos` (`DFA.scanStr`/`tokenizeStr`,
`Lexer/StringScan.lean`), a sound ~1.3x; the flat scanner builds on that
`String.Pos` cursor.

**Step 2 — define the specification object.** The lexer has no analogue of
`ParseTree` yet, and every guarantee has to be stated against one. Because
tokenization is a linear scan with a mode stack, the derivation is a sequence, not
a tree: a `Tokenization` witness that a token list is a valid maximal-munch
tokenization of an input, each step recording the mode, the winning rule index, the
consumed length, and carrying
  * the rule's regex matches the consumed prefix (`matchesFull`),
  * no rule matches a longer prefix,
  * no earlier rule matches the same length (tie-break by rule order),
  * the length is non-zero,
  * the action's emit and mode-stack effect.
Its "size" is the input length, so unlike `ptSize` it needs no fuel bound. The
spec-level `bestMatch` over `longestMatch` belongs here too — it was removed from
`Engine.lean` as an execution path and should come back as a specification-only
definition.

**Step 3 — the validator conditions.** Emit, per mode and per state, the state's
derivative vector `vec : Array Regex`; the construction already computes it, so
this is an annotation, not new work. The conditions, all Boolean and all interval
arithmetic where the alphabet is involved:

| | Condition |
|---|---|
| `V0` | state 0's `vec` is the mode's rule regexes, in rule order |
| `V1` | each state's `accept` is `vec.findIdx? nullable` |
| `V2` | for each edge `(cls, tgt)` of state `s`: `states[tgt].vec = states[s].vec.map (deriv c)` for `c` a representative of `cls` |
| `V3` | for each edge class `cls` of state `s`, each component `r` of `states[s].vec`, and each `k ∈ classesOf r`: `cls ⊆ k` or `cls ∩ k = ∅` |
| `V4` | a state's edge classes are pairwise disjoint, and on the complement of their union every component's derivative is `never` (dead) |
| `V5` | the construction completed — no state left as the `default` placeholder |

`V3` is what replaces quantification over characters: it makes "every component
derives identically across `cls`" true, so checking one representative in `V2` is
sound. The supporting lemma is that if `c₁` and `c₂` agree on membership in every
class in `classesOf r`, then `deriv c₁ r = deriv c₂ r`, by induction on `Regex`.
`V4` is needed because `transitionsOf` drops dead successors, so "no edge" has to
mean "dead", not "unspecified".

**Step 4 — the generic theorem.** Prove once, for any tables satisfying `V0`–`V5`,
that `DFA.scan` returns the maximal-munch winner as defined in step 2, and then that
the tokenization loop returns a token list exactly when a `Tokenization` derivation
exists, with the same tokens. Uniqueness of the derivation follows from determinism
of maximal munch and gives unambiguity. This is the analogue of
`safe_of_safeValidator` composed with `parseCorrect`/`parseComplete`, and like them
it is proved in the library, not per lexer.

**Step 5 — validate the emitted tables, not a rebuild.** Run the validator on the
tables that actually run, discharged per lexer by `native_decide`, exactly as
`CalcVerified.lean:457` does for `safeValidator`. This subsumes
`test/LexerEmitAgreementTest.lean`: once the emitted tables are validated directly,
comparing them against `Compiled.ofTokenizer` is redundant, and
`Compiled.ofTokenizer` becomes purely untrusted scaffolding for the emitter. The
`lexer` command then emits the tables, the certificate, the validation theorem, and
the corollaries, the way the parser backend emits `parser_sound` and friends.

**Out of scope, and stated as such.** The `lexre` → `Regex` frontend stays
unverified, the same boundary as `.lig` for the parser: the theorem is about the
emitted regexes, not the author's intent. Semantic actions are arbitrary Lean
functions and are not constrained. Step 1 moved the scan to a `String.Pos` cursor
over Unicode code points (not UTF-8 byte positions), and `classOf`'s correctness
against the code point is discharged by `flatValidate` (§9.8), so the indexing is
inside the verified boundary; the bytes-to-`Char` decode that produces those code
points remains unverified, as for the `String.Pos` runtime generally.

### 9.8 What is implemented

Steps 0 and 2–5 are done and build; step 1 (the flat-table throughput
optimization) is now also done and is the emitted runtime (see the Step 1 bullet
below). The verified tokenizer is
validated end-to-end for the generated lexers (calculator, Cedar, CedarSchema,
and CedarEntities — their generated modules emit `validated⟨m⟩`/`scanSound⟨m⟩` and
`flatValidated⟨m⟩`, discharged by `native_decide`), with no `sorry` and the same
axiom budget as the parser (`propext`, `Classical.choice`, `Quot.sound`, and one
`native_decide` axiom per emitted Boolean). The scanner's maximal-munch soundness is stated against the
specification object `MatchStep` (`scan_matchStep` and its converse
`scan_of_matchStep`), and holds for `DFA.scan` — the scanner the emitted lexers
actually run — not only against the derivative-level `fusedScan`; see Step 4
below. The interval-refined `V2`/`V4` (§9.3) make Cedar's
Unicode-wide edge and leading classes tractable — 293 representatives, not 3.3M
code points — so no code-point budget gate is needed.

- **Step 0.** `CharClass` is now the ranges-only structure `⟨neg, rs⟩` with
  `DecidableEq` (`Lexer/Regex.lean`); the opaque predicate and `opaqueWindow` are
  gone, `Regex.asciiWhitespace` replaces `Char.isWhitespace` in the Cedar fixtures.
  `DFA.build?` returns `Option DFA`, `none` when the worklist did not empty
  (`Lexer/DFA.lean`). `DFA.repOf` documents that the theorem quantifies over valid
  scalar values, so the surrogate gap is never a match position.
- **Step 2.** `Lexer/Spec.lean` defines `bestMatch` (spec-only maximal munch over a
  rule array via `longestMatch`), the relational `MatchStep`, and the
  `Tokenization` sequence witness.
- **Step 3.** `Lexer/Validator.lean` defines the certificate `LexCert` (per-state
  derivative vectors, produced by `DFA.build?WithVecs`) and the Boolean `validate`.
  `V2` is **interval-refined** (§9.3): for each edge it tests one representative per
  *boundary cell* — a maximal sub-interval on which `deriv` is constant across the
  source vector, delimited by the raw endpoints of every class in every component
  (`cellReps`, `splitCells`, `vecEndpoints`), sound via `agreeOn_of_noEndpointBetween`
  + `deriv_congr` and covered by `splitCells_covers`. For Cedar this is 293
  representatives instead of 3.3M code points, so `native_decide` is tractable. `V4`
  (dead-complement coverage) is likewise interval-based and negation-aware
  (`coveredByEdges`/`coversInterval`, sound via `memRanges_of_coversInterval`),
  handling Cedar's `[^"\]`/`[^\n]` rules. Cell refinement replaced an earlier
  point-enumeration `V2` (exact but intractable for Unicode-wide edges) and the plan's
  `V3` edge-class-in-or-out condition (unsound because `transitionsOf` merges atoms
  across regex-class boundaries).
- **Step 4.** The generic theorem `scan_sound` proves that for validated tables
  `DFA.scan dfa cs = fusedScan rules cs 0 none` (the derivative-defined maximal
  munch), from the certificate step lemma `validate_step`; `scan_deterministic` is
  the unambiguity lemma and `tokenize_congr` (`Lexer/Tokenize.lean`) lifts it to the
  whole tokenizer. Soundness is stated against the specification object `MatchStep`
  (`Lexer/Spec.lean`), bridged from `fusedScan`'s derivative bookkeeping by the
  pure-regex fact `matchesFull r cs = nullable (derivs cs r)`: `scan_matchStep`
  (validated `DFA.scan … = some (rule, len)` with `0 < len` ⇒ `MatchStep`), its
  converse `scan_of_matchStep`, and `matchStep_unique` (the winner is unique). These
  lift to the tokenizer as `tokenizeAuxDFA_sound`/`tokenize_sound`: for a single-mode
  lexer whose start mode is validated and whose actions keep the mode stack put, a
  successful `tokenize` implies the input has a maximal-munch `Tokenization`
  derivation. All carry only the `propext`/`Classical.choice`/`Quot.sound` budget.
  Two items are deliberately deferred: the spec-only `bestMatch` is not proved equal
  to `fusedScan` (not needed — `MatchStep` is the spec object, and they differ only
  on the empty-match case, which is not a token), and the multi-mode lift (threading
  the mode stack through `Tokenization`) is the remaining generalization.
- **Step 5.** The CLI lexer backend (`Emit/CodegenLexer.lean`) emits, per mode,
  `⟨name⟩.rules⟨m⟩`, `⟨name⟩.dfa⟨m⟩`, `⟨name⟩.cert⟨m⟩` as data,
  `⟨name⟩.validated⟨m⟩ : Lexer.validate … = true := by native_decide`, and
  `⟨name⟩.scanSound⟨m⟩`. Because `V2`/`V4` are interval-based (§9.3), there is no
  code-point budget gate: the calculator, Cedar, and CedarSchema lexers all emit
  and discharge the validation and soundness theorems, with the same axiom budget
  as the parser (`propext`, `Classical.choice`, `Quot.sound`, and one per-lexer
  `native_decide` axiom). This subsumes the intent of
  `test/LexerEmitAgreementTest.lean` for the lexers that validate directly.
- **Step 1** (flat-table optimization) is done and is the emitted runtime. The
  derivative-vector `DFA.scan`/`tokenizeAuxDFA` remain the specification; the fast
  `FlatDFA` scanner is a verified-equal running object. `Lexer/FlatValidator.lean`'s
  `flatValidate f dfa : Bool` (discharged per lexer by `native_decide` as
  `FooLexer.flatValidated⟨m⟩`) implies the flat tables step and accept identically to
  the DFA (`StepAgree`/`AcceptAgree`/`StatesInRange`); `flatScanStr_eq_scanStr`
  (`Lexer/FlatScan.lean`) and `tokenizeFlatStr_eq_tokenize` (`Lexer/FlatTokenize.lean`)
  prove the emitted `FooLexer.tokenize := Lexer.tokenizeFlatStr FooLexer.cflat` equals
  the spec `tokenize`, so `tokenize_sound` transfers unchanged. Axioms are the same
  budget (`propext`/`Classical.choice`/`Quot.sound` + one per-lexer `native_decide`
  axiom). The generated lexers (calc, Cedar, CedarSchema, CedarEntities) emit `cflat`,
  `flatValidated⟨m⟩`, and the flat `tokenize`, and compile. Measured ~2.2x lex-only on
  Cedar (145.7 → 66.8 us/policy), tokens identical (§9.6). The `List Char` removal (`Lexer/StringScan.lean`,
  `tokenizeStr_eq_tokenize`) is the `String.Pos` cursor the flat scanner builds on.

- **Byte scanner (§9.6.3).** A `UInt8`/`ByteArray` scanner (`Lexer/ByteScan.lean`,
  `Lexer/ByteTokenize.lean`) is emitted into every lexer as `FooLexer.tokenizeByte`
  and validated per lexer by `FooLexer.byteValidated⟨m⟩` (`native_decide`, same axiom
  budget as `flatValidated⟨m⟩`). It is ~1.17x faster than the flat scanner on
  Cedar (tokens identical). The byte↔flat scan simulation is proved up to that
  Boolean (`byteScan_rule_eq_flatScanArr`, `Lexer/ByteValidator.lean`); the proved
  `tokenize` stays on the flat scanner and `tokenizeByte` is the validated fast path.
  Making it the proved default awaits `agreements_of_byteValidate` (§9.6.3).

## 10. Build and validation

```sh
lake build                 # library, CLI, verified smoke regressions (no heavy fixtures)
lake build parsers         # regenerate both backends for every non-heavy fixture
lake build heavyParsers    # regenerate the heavy fixtures (c99)
lake build Generated       # compile executable calc/IMP/Cedar/... modules
lake build VerifiedSmoke   # compile verified calc smoke and agreement tests (default)
lake build VerifiedMid     # compile + cache the non-heavy *Verified proof modules
lake build VerifiedHeavy   # compile + cache the heavy *Verified module (c99)
lake build ParserTests     # calc/imp end-to-end, span, error-message, and x_span tests
```

Lake 5.0.0 has no `-j` flag; bound build parallelism with the `LAKE_NUM_JOBS`
environment variable (e.g. `LAKE_NUM_JOBS=4 lake build VerifiedMid`). This matters
for the heavy fixtures: build `VerifiedHeavy` alone (see below).

The paired `*Verified` proof modules are split across two non-default
`lean_lib`s so plain `lake build` never pays their cost: `VerifiedMid` roots the
ones that fit comfortably in memory (calc, imp, cedar, cedarschema, cedarentities),
and `VerifiedHeavy` roots the heavy one (c99), reached only through
the separate `heavyParsers` regeneration target. Building either caches each
module's `native_decide` certificates to `.olean`, so an unchanged rebuild is a
Lake trace no-op (~0.9 s for Cedar) instead of the full re-check that
`lake env lean test/<g>/<G>Verified.lean` pays every time (~230 s for Cedar).
Neither is a default target — plain `lake build` (which builds `VerifiedSmoke`
only) must not pay the Cedar/c99 proof cost. Measured cold vs cached: Cedar
234 s → 0.9 s.

`c99` is split out for memory, not just time. `c99.C99Verified` checks
cold in ~18 min but peaks near the machine's physical RAM. Build the heavy fixture
one worker at a time on a host with enough RAM (or swap):
`LAKE_NUM_JOBS=1 lake build VerifiedHeavy`, or one module at a time.

The end-to-end functional tests are rooted in the `ParserTests` `lean_lib`
(`lake build ParserTests`): `calc`/`imp` acceptance, `test/calc/PositionTest.lean`
(span folding), `test/calc/ErrorMessageTest.lean` (diagnostics and `line:col`), and
`test/spanuse/` (an action reading `x_span`, and a sibling rule ignoring spans that
compiles without a linter warning).

Generated modules are committed for inspection. Lake targets regenerate them
when their `.lig` input or the generator executable is newer. See
[`test/README.md`](../test/README.md).

The default regression set exercises both validators, operational theorem
instantiation, Pager construction, generated parsing, calculator/IMP/Cedar
end-to-end behavior, rejection of a corrupted executable table, and expected
elaboration failure for a mismatched semantic dispatcher.

### Cold proof-compile cost: `Fin` bound proofs as terms, not tactics
Two levers cut proof-module compile time; they stack. Caching (`VerifiedMid`/
`VerifiedHeavy`, above) removes the *repeat* cost. The *cold* cost is dominated not by the
`native_decide` certificates but by elaborating the dependent tables (`actionTable'`,
`gotoTable'`) — enormous nested `match`-on-`Fin` functions. I measured this by
compiling each `*Verified` file truncated to just the tables, all `native_decide`
certificates removed: Cedar 186 s of its 231 s. So the
tables, not the certificates, are the cold-compile cost.

The tables are full of `Fin` literals `⟨n, proof⟩`. The emitter originally discharged
each bound with the `by decide` *tactic* — ~54 000 invocations in Cedar. Each pays the full tactic-elaboration overhead. Emitting the *proof term*
`of_decide_eq_true rfl` instead (same proposition; `decide (n < bound)` still reduces
to `true` and is kernel-checked, but no tactic framework spins up) cut CedarVerified
cold from 231 s to 143 s (−38 %), exit 0, with the axiom budget unchanged
(`#print axioms parser_sound` = `propext`, `Quot.sound`, and the safety + four
refinement `native_decide` axioms — no new axioms, no `sorry`). The change is in
`Emit/CodegenVerified.lean` (every emitted `Fin` literal); regeneration propagates it
to all grammars. This is why splitting the certificates into parallel modules
was *not* pursued: it would parallelize only the ~5 s certificate tail, while the
term-proof change attacks the dominant table-elaboration cost directly.

## 11. Parser refinement against the dependent specification

The dependent interpreter remains the specification; the parser engine is linked
to it rather than replacing its proofs.

`Runtime.Refinement.ExecRefinement` records each generated grammar's semantic encoding,
state/terminal/nonterminal/production numbering, decoder agreement, table
agreement, and semantic-action agreement. Structural obligations are finite
Boolean checks discharged with `native_decide`; semantic obligations are
per-production proofs that reduce by `rfl`.

The generic proof:

1. relates dependent heterogeneous values and stacks to executable `V` cells;
2. proves dependent `pop` agrees with executable `popN` and source-order action
   arguments;
3. simulates shifts, reductions, rejection, goto, and augmented-start acceptance;
4. lifts the simulation through the two structurally identical logarithmic-fuel
   `parseFix` functions;
5. relates complete `parse`/`run` results through `Runtime.Refinement.run_refines`.

Executable finite lists and dependent `NatStream`s both pad exhausted input with
the generated EOF token. Every paired specification module exports
`parserRunRefines` and `parse_eq_dependent`; calculator, IMP, and
Cedar compile these generated proofs. The existing `parseCorrect`,
`parseComplete`, `parse_err_free`, and `unambiguity` theorems remain unchanged and
transfer through this equality.

## 12. Inspectable verified grammar

The generated `semT'`, `prodContents'`, `tokenTerm'`, and `tokenSem'` definitions
are authoritative but their `Fin` matches are difficult to audit. Each dependent
specification module therefore also emits a readable `verifiedGrammarView` of
exactly the augmented grammar surrounding those definitions, rather than merely
pretty-printing the untrusted `.lig` parse.

`Runtime.VerifiedGrammarView` records:

- every terminal and nonterminal, including augmented `$` and `S'`, with indices
  and declared semantic type names;
- the augmented start nonterminal, original user start, and EOF token's mapping
  to `$`;
- every production in source order with a readable left-hand side and RHS,
  including the source binder attached to each symbol;
- the compact source action expression and stable `semanticActionN` declaration
  actually reused by `prodContents'`.

The generated `verifiedGrammarViewStructuralCheck` compares candidate metadata
with the emitted `GrammarSig`: terminal/nonterminal bounds, start symbol,
production indices/LHS/RHS, augmentation, EOF, and token-terminal bounds all
agree. `verifiedGrammarView_agrees` discharges that checker with `native_decide`,
checks that the view contains exactly the declared token-constructor names, and
proves by exhaustive token-constructor cases that every entry selected through
generated `tokenName'` agrees with `tokenTerm'`. A corrupted calculator view with
a missing production is a negative regression for the structural checker.

Users can inspect the value directly in generated source, call
`verifiedGrammarView.renderBNF` or `.renderMarkdown`, or render from the same
augmented generation data on demand. BNF keeps the source binders and action
expression compact while naming the generated Lean declaration as a comment:

```bnf
expr ::= e:expr PLUS t:term    { e + t }  -- semanticAction0
```

```sh
leanparsergenerator --print-grammar bnf grammar.lig
leanparsergenerator --print-grammar markdown grammar.lig
```

Normal generation does not print the view. Semantic type, binder, and source
action strings are presentation metadata because Lean cannot generally reflect a
`Type` or function back to trustworthy source text. The actual Lean definitions
remain authoritative: semantic actions have stable generated declarations, and
those declarations—not the strings—are what `prodContents'` uses.

Paired specification modules export direct `parser_sound`, `parser_err_free` /
`parser_ne_err`, `parser_complete`, and `parser_unambiguous` corollaries, so
callers do not assemble refinement or validator witnesses. Existing-repository
and automatic Lake generation workflows are documented in
[`INTEGRATION.md`](INTEGRATION.md). Later independent work includes a verified
lexer and `.lig` language-server diagnostics.

## 13. Executable parser throughput: the inline engine

The generated `ExecTable V` (§6) already stores the action, goto, default-reduce,
`prodLhs`, `prodRhsLen`, and semantic tables as flat `Array` literals — the LR table
lookup is one array read. But the six `ExecTable` fields are `fun` closures over
those arrays (`action := fun st t => actionData.getD (st * numT + t) .error`, and so
on), so each `Exec.step` performs several *indirect closure calls*. I profiled the
parser hot path of a generated parser to find where the time goes:

| Component | share |
|---|---|
| `decode` (`toks.map decode`) | ~8% |
| LR engine (steps, table reads, `popN`, stack) | ~77% |
| semantic actions + `V` allocation (user code) | ~15% |

Two measured facts ruled out the obvious levers. Switching the LR stack and input
cursor from `List` to `Array` did **not** help (within noise of the `List` baseline): `List.getD 0`/`drop 1` are O(1) and the `Array` version pays for
`shrink` and bounds-checked indexing, so the lexer's `List Char` story has no parser
analogue. A flat `while`-loop engine with an explicit step counter — no `Sum`
allocation per step, no logarithmic-fuel double recursion — also measured the same as
the shipped `parseFix`, so the `Sum`/`parseFix` structure is not the
cost either. The one lever that moved the number was **removing the `ExecTable`
closure indirection**: reading the raw arrays inline dropped parse-only time by about 12%.

`Runtime/Exec.lean` therefore adds a closure-free engine and proves it equal to the
closure engine, exactly the lexer's a-posteriori pattern (§9.8 step 1) — the
`ExecTable` `Exec.run` stays the specification the refinement theorem is stated
against, and the inline engine is a verified-equal running object:

- `structure FlatTable V` holds the raw arrays plus the two row widths
  (`actWidth`/`gotoWidth`), no closures. `FlatTable.toExecTable` wraps it in exactly
  the `getD` closures the emitter used to write, so it is *definitionally* the old
  `table`.
- `reduceInline`/`stepInline`/`parseFixInline`/`runInline` read the arrays inline.
  `FlatTable.topState` reads `startState` directly; an earlier version routed through
  `topState f.toExecTable`, which reconstructs the six-closure record on every step
  and made `runInline` 2x *slower* — the fix is the reason to keep a separate
  `topState`.
- `runInline_eq_run : runInline f input n = run f.toExecTable input n` (via
  `stepInline_eq`, `reduceInline_eq`, `parseFixInline_eq`) carries only
  `propext`/`Quot.sound`, no `native_decide`.

The emitter (`Emit/Codegen.lean`) now emits `def flat : FlatTable V := {…arrays…}`,
`def table : ExecTable V := flat.toExecTable`, and `run := Exec.runInline flat …`.
Because `table` is definitionally the same closures as before, every generated
`native_decide` agreement check (`refinementLookaheadCheck_ok`, etc.) and the
`refinementSemanticAgrees` `rfl` proofs are unchanged. The verified emitter
(`Emit/CodegenVerified.lean`) bridges `parserRunRefines` with one line —
`simp only [run, table, runInline_eq_run]` rewrites the emitted `run` to
`Exec.run table` — so `parse_eq_dependent` and the `parser_sound`/`parser_complete`/
`parser_err_free`/`parser_unambiguous` corollaries transfer with the **same axiom
budget** (`propext`, `Quot.sound`, and the per-grammar `native_decide` safety and
refinement axioms; no new axioms, no `sorry`).

Measured on Cedar: a direct A/B on the same tables (`Exec.run
CedarParser.table` vs `Exec.runInline CedarParser.flat`, `cedar-spec/cedar-benchmarking/corpus`,
0 output mismatches): the `generated/` corpus (22 policies) 146.9 → 130.0 µs/policy
(~11.5%), the full 28-policy corpus 195.1 → 168.9 (~13.4%), the `oopsla` real-world
set 79.3 → 69.8 (~12%). So the gain is ~11–13% across the corpora.

The remaining ~62 µs engine time was `popN`'s per-reduce args-list allocation, the
`sem : List V → V` dispatch (which forces that list), and per-token `V` payload
construction — the last is user semantic-action code the generator cannot speed up,
the parser analogue of the lexer's irreducible per-token actions (§9.6). The
generated grammars (calc, c99, cedar, cedarschema, cedarentities, imp) emit `flat`.

Abandoned, for the stated reason:
- An `Array` LR stack and `Array` input cursor measured no faster than `List` (the
  `List Char` lexer lever does not transfer), so the stack and input stay `List`.
- Rewriting the grammars' right-recursive list rules to left recursion (the classic
  Bison advice) was measured and rejected: it was ~3% *slower* on the corpus and only
  ~2% faster on a synthetic 2000-element list. The "left recursion saves stack" rule
  concerns fixed-size parser stacks that overflow; this runtime's stack is a heap
  `List`, so deep right-recursion costs proportional memory, not time, and the
  reverse-once wrapper offsets it.

### The direct-stack reduce (the `redv` engine; implemented and sound)

The second step attacks that per-reduce allocation directly. `reduceInline`
still does, per reduce, `popN` (which allocates a `List V` of the operands) and
then `sem p args` (which pattern-matches that list). Both go away if the emitted
code reads the operands off the stack in one match. I profiled the ceiling on
parse-only time: a no-op `sem` that reads the stack by RHS length without building
the list runs well below a no-op `sem` that still builds the `popN` list, so the
`List V` allocation and the `sem` list-match dispatch are a measurable share.

`Runtime/Exec.lean` adds `redv : Nat → Stack V → Option (V × Stack V)` as a
`FlatTable` field and a `runRedv` engine that uses it, following the same
a-posteriori pattern as the inline engine — `runInline` stays the intermediate
spec, `runRedv` is a verified-equal running object:

- The emitter (`Emit/Codegen.lean`, `emitRedv`) generates `redv` keyed on the
  production index first (a flat `Nat` match), then on the stack shape. For
  production `p` with RHS length `n`, the arm matches the top `n` stack cells in
  reverse RHS order (last symbol on top), binds and unwraps the operands, and
  returns `some (semantic-value, remaining-stack)` — no `List V` is built and no
  list is matched. A non-matching shape (and any other production index) falls to
  `(popN (lenData.getD p 0) stk).map (fun r => (sem p r.1, r.2))`, the `popN`+`sem`
  composite, computed from the top-level arrays (not through `flat`, which would be
  a definitional cycle).
- `Runtime.Exec.popNsem f p stk` names that composite; `reduceInline` is
  definitionally `reduceRedv` with `f.redv` replaced by `popNsem f`. So the emitted
  obligation is `redvMatches : flat.redv p stk = popNsem flat p stk`, proved by
  `fun_cases redv p <;> simp only [redv] <;> (first | rfl | (split <;> rfl))`. Keying
  `redv` on `p` first is what makes this cheap: `fun_cases` splits on the production
  index only (a flat `Nat` match), not the deeply nested stack shapes. Casing the
  merged nested match instead took ~2m36s on a 72-production grammar; the flat-on-`p`
  form is ~8 s. Because the fallback *is* `popN`+`sem`, `redvMatches` holds for
  matched shapes and fallbacks alike, so no arm is left over.
- Given `redvMatches`, the library proves `reduceRedv_eq`, `stepRedv_eq`,
  `parseFixRedv_eq`, `runRedv_eq_runInline`, and `runRedv_eq_run` generically. The
  emitter's `run` now calls `Exec.runRedv flat`, and `CodegenVerified.lean` bridges
  `parserRunRefines` with `runRedv_eq_run flat redvMatches`. All of this carries only
  `propext`/`Quot.sound` — **no new axioms** beyond the per-grammar `native_decide`
  already present, and no `sorry`. Verified end-to-end (full `parser_sound`/
  `parser_err_free`/`parser_complete`/`parser_unambiguous`/`parse_eq_dependent`, same
  axiom budget) for calc, imp, cedarschema, cedar, and c99.

Measured: across the
inline→redv steps, Cedar parse-only (full 28-policy corpus) 160.0 → ~151.5 µs/policy
(~5.5%). The A/B win is smaller than the no-op ceiling because the real per-
production `V` construction (user AST building) dominates and cannot be removed, and
because `redv`'s `Option (V × Stack V)` result still boxes one tuple per reduce; a
variant that fuses the `goto` into `redv` to drop that box measured ~55 µs but its
per-production equality proof was fragile, so it was not adopted.

The generated grammars emit `flat`, `redv`, `redvMatches`, and run `runRedv`.

Abandoned along the way:
- A fused reduce that returns `Result V ⊕ Stack V` directly (goto inlined per
  production, no intermediate `Option`) was ~11% faster than the `Option`-returning
  `redv` in a fair loop, but the per-arm `reduceRedv = reduceInline` proof had to
  reconstruct the `goto`/`topState`/array reads defeq-identically to `reduceInline`
  and was brittle; the clean `redvMatches` (equate `redv` to `popNsem`, not the whole
  reduce) was kept instead.

### Parser optimization candidates (untried)

Beyond the inline and `redv` engines above, three parser-side candidates target the
remaining hot spots (parse ~120 us on Cedar: AST construction + `sem` dispatch). None
is measured yet; recorded with expected effect and proof impact.

- **Unchecked table reads.** The state/goto/action tables are read with `Array.getD`,
  which bounds-checks every access. The validator already establishes the indices are
  in range (the `V3`/goto range condition), so an `Array.uget`/`getElem`-with-proof
  read would drop the per-step branch. Proof impact: `getD` → `uget` changes
  `FlatTable.toExecTable` and forces an in-range proof threaded through
  `step`/`parseFix`; the range fact exists but is not free to wire in. `Array.get!`
  is *not* the win — it still bounds-checks (panics instead of defaulting).

- **Specialize `V` with unboxed payloads.** `V` is a sum with one constructor per
  distinct semantic type (44 for Cedar); each reduce boxes a `V`. Carrying unboxed
  `UInt32` payloads where the AST does cuts per-reduce boxing. Touches the generated
  `V` and every `sem` arm, re-checked by the existing refinement `native_decide`
  (`parse_eq_dependent`) — no new theorem shape, but a large codegen change whose win
  depends on how many reduces carry currently-boxed payloads.

- **Default-reduction chain collapse.** `stepRedv` consults `defRedData` then
  `actionData` each step; a state with a default reduction still re-enters
  `parseFixRedv` through the `Result ⊕ (Stack × input)` sum. Collapsing a chain of
  default reductions into one loop iteration removes per-reduce fuel-recursion
  overhead. Proof impact: it changes `parseFixRedv`, so `runRedv_eq_run` must be
  re-proved for the collapsed loop (a bounded-unrolling lemma: `n` default reduces =
  `n` single steps). Only helps grammars with long default-reduce chains — worth
  profiling the Cedar default-reduce fraction first.

A fourth idea — an `Array`/`ST` parser stack — is not pursued: §9.6.2 measured the
naive array stack at 2x slower (non-unique reference, copy per push/shrink), and a
genuinely linear `ST` stack needs the mutable engine proved equal to pure `runRedv`,
more than the current thin `FlatTable` equivalences. The `redv` ceiling data show AST
construction dominates the remainder, so this is likely low payoff.

### `%option compress_tables`: compressed table literals for the executable parser

The generated *executable* parser (`FooParser.lean`) is itself expensive to compile
for large grammars, independent of the proofs. A parser file can be a few
thousand lines yet take many minutes and produce a large `.olean`. The cause is
`actionData`: a single flat `Array Runtime.Exec.Act` literal of `numStates ×
numTerminals` entries. Lean's compiler scales poorly generating C/IR for an array
literal that large; `gotoData` has the same problem.

Most of that literal is repetition: the large majority of action cells are `.error`
and of goto cells are `none`. The `%option compress_tables` directive (set in the `.lig`
before `%%`) exploits this. It does *not* change the tables — `actionData`/`gotoData` are
the same dense arrays with the same values either way. It changes only how they are
*written in source*: instead of one full literal with a cell per entry, it writes just
the non-default cells as `(index, value)` pairs and reconstructs the full array with
`buildDense`:

```lean
def buildDense {α} (n : Nat) (dflt : α) (cells : Array (Nat × α)) : Array α := Id.run do
  let mut a := Array.replicate n dflt
  for (i, v) in cells do a := a.set! i v
  return a
def actionCells : Array (Nat × Runtime.Exec.Act) := #[(2, .shift 4), (5, .shift 5), …]
def actionData : Array Runtime.Exec.Act := buildDense (numStates * numTerminals) .error actionCells
```

`gotoData` is written the same way over the `none` default. Only the ~10 % (action) /
~1 % (goto) non-default cells appear in the literal, so the literal the compiler must
process shrinks ~10–100x. The full array is rebuilt once at module load (`buildDense`),
so `actionData`/`gotoData` still have the *same value* and per-parse reads are still O(1)
`getD` array indexing — there is no runtime penalty.

**The proofs are unchanged, with no added `native_decide` cost.** This is the point of
compressing the *literal* rather than storing a sparse table: `actionData` is still a
dense `Array Act` value — `buildDense (numStates * numTerminals) .error actionCells` evaluates (by the native
compiler, which is what `native_decide` uses) to exactly the array the full literal would
have written. The refinement connects to the executable table only through
`table.action s t = f.actionData.getD (st*w+t) .error`; since `actionData` has the
identical value, `refinementLookaheadCheck` and the other `native_decide` agreement checks
see identical values and stay true, and the runtime `Runtime/Exec.lean` `FlatTable` is
untouched. A genuinely sparse *table* — a lookup with an `.error` default evaluated per
`native_decide` entry — would instead trade the executable-side win for a verified-side
cost (a binary search run ~57 000 times inside `native_decide`); compressing only the
source literal avoids that tension.

One interaction to know: `buildDense` is a normal recursive `def`, so code that forces
the *elaborator/kernel* to reduce the array (rather than the native compiler) can hit
`maximum recursion depth`. The generated specification modules do not — their checks are
`native_decide`, which uses compiled evaluation — but a hand-written test that elaborates
the table's type can (the calc `RefinementTest` negative test does, which is why calc, a
tiny grammar with no literal-size problem, is left uncompressed). A grammar that opts in
and has such a test should raise `set_option maxRecDepth` in that test. The option is
meant for large grammars whose table literal is the compile bottleneck; small grammars
gain nothing from it.

Measured (v4.34.0, this machine), full literal vs `%option compress_tables`, executable
backend:

| grammar | full compile | compressed compile | full `.olean` | compressed `.olean` |
|---|---|---|---|---|
| Cedar    | 67 s   | 39 s  | 54.1 MB  | 49.7 MB  |

Cedar's `.olean` shrinks modestly because it is dominated by the `V` sum type and
`sem` dispatch, not the tables; the compile-time win (≈1.7x) comes from the smaller
table literal. Grammars whose `.olean` is dominated by the tables benefit more. Runtime parse throughput is unchanged (Cedar parse-only 23.5 µs
full vs 22.8 µs compressed over the same corpus, within noise). The option is off by
default so existing grammars are byte-for-byte unaffected until they opt in.

Soundness was checked after enabling the option: `CalcVerified` and `CedarVerified`
both compile, and `#print axioms *.parser_sound` reports the unchanged set
(`propext`, `Quot.sound`, and the five safety/refinement `native_decide` certs; no new
axioms, no `Classical.choice`). `CedarVerified` took 147 s with `compress_tables` versus
~147–149 s without — no verified-side regression, because `actionData`/`gotoData` keep the
identical value and the compressed form exists only in the emitted source literal, not in
what `native_decide` evaluates. Note this does not
change the `*Verified` compile cost: that is the per-entry `native_decide` over
the dependent `actionTable'`, which is independent of how the *executable* `actionData`
literal is written.


## 14. Integration

We will need a good user experience for the tool. The `test/` folder shows how it
works today, but that only works because the library is local. A published version
of LPG (LeanParserGenerator) has to provide, for a downstream Lake package:

- a **generator tool** that emits the parser and lexer implementations from a `.lig`
  file, fetched as a build-time executable dependency, and
- a **runtime library** the generated parser and lexer link against directly.

The design must support automatic regeneration and build. Two mechanisms already in
this repository are the template for it:

- **Regenerate-on-stale.** The `parsers` Lake target (see the lakefile) fetches the
  generator executable, compares mtimes of each `.lig`, the generator, and the two
  committed outputs, and regenerates only stale pairs before the library compiles.
  A downstream package copies this target, pointing it at its own grammars. Committing
  the generated modules keeps them reviewable and makes a plain `lake build` enough on
  a clean checkout; a from-scratch checkout regenerates once before the first build.

- **Cache the proofs; do not re-check them.** The dependent-specification modules
  (`*Verified`) carry the expensive `native_decide` certificates — ~230 s for Cedar,
  minutes and multiple GB for the largest grammars. Re-running `lake env lean` on them every time is the
  wrong workflow. Instead they are rooted in a non-default `lean_lib`
  (`VerifiedMid`/`VerifiedHeavy` here) so Lake caches each certificate to `.olean`
  and an unchanged rebuild is a
  trace no-op (Cedar 234 s → 0.9 s; §10). A downstream package should
  likewise put its generated `*Verified` modules in a dedicated library so CI checks
  the proofs once per change, not once per invocation, and so the heavy grammars
  (Cedar/C99-scale) stay off the default build path while remaining one
  `lake build` away. This split — executable parser on the default path, proof modules
  in an opt-in cached library — is the intended integration shape.

A published version therefore ships (a) the generator as a Lake exe dependency,
(b) the runtime as a Lake lib dependency, and (c) a documented pair of Lake targets
(regenerate-on-stale + a cached verified library) that a consumer instantiates for its
own grammars. [`docs/INTEGRATION.md`](./INTEGRATION.md) carries the concrete setup.


## 15. The bootstrapped `.lig` frontend

The `.lig` frontend is split in two. The structure of a `.lig` file — the sequence of
`%`-directives, the rules, and the alternative/element shape of each rule — is parsed by
a parser LPG generates from a `.lig` grammar of its own. The embedded-Lean leaves —
`%header`, `%lexerheader`, `%lexer`, the `{ … }` action bodies, and the rest-of-line
`:: Type` — are read by a hand-written lexer. The leaves are brace-balanced Lean, not a
regular language, so a DFA cannot tokenize them; everything else is context-free and
LR(1), so it does not need to be hand-written.

The pieces:

- `LeanParserGenerator/Frontend/lig.lig` is the grammar for the `.lig` structure, 59
  lines. It uses the hand-written-lexer regime (no `%lexer`): its
  `%header` imports the token type and the `Surface` constructors, and its actions build
  `Frontend.Directive`s and `Frontend.Rule`s.
- `LeanParserGenerator/Frontend/LigLexer.lean` is the hand-written lexer. It turns
  `.lig` text into a `List LigTok`, capturing each embedded-Lean leaf verbatim into one
  string-carrying token with the same balanced-brace and rest-of-line code the old
  scanner used. It also holds `assembleSurface`, which folds the parsed directives and
  rules into a `Surface`, applying the same defaults and validation as `parseLig`.
- `LeanParserGenerator/Frontend/Generated/{LigParser,LigVerified}.lean` are generated by
  LPG from `lig.lig` and committed.
- `LeanParserGenerator/Frontend/LigParse.lean` exposes `parseLigGen`: tokenize with
  `LigLexer`, parse with the generated `LigParser`.

I did this for two reasons, in this order. The first is that the hand-written scanner
(`Frontend/File.lean`, ~950 lines of `Cursor` code) is hard to maintain and is where
misparse bugs hide: directive ordering, the rule/alternative/element structure, and
symbol-sequence parsing are all encoded in control flow rather than in a grammar. A
misparse there does not crash — it produces a `Surface` that is not what the file says,
LPG generates a parser for a different grammar than the author meant, and the only place
that shows up is `verifiedGrammarView` (§12), which the author has to read. A declared
grammar plus a focused lexer moves that structure out of control flow and into 59 lines
that state it directly. The second reason is that a generated parser comes with the same
proofs every generated parser gets — `LigVerified` proves `parser_sound`,
`parser_complete`, and `parser_unambiguous` for the `.lig` grammar, with the usual axiom
set (`propext`, `Classical.choice`, `Quot.sound`, and the safety/completeness/refinement
`native_decide` certs; no new axioms, no `sorry`).

That proof is a bonus, not the reason, and I want to be exact about what it does and does
not say. It is not a soundness claim about LPG. We do not make one, and the a-posteriori
architecture already makes a frontend bug unable to produce an unsound *user* parser — a
frontend bug can only produce a parser for a different grammar than intended, never one
that disagrees with its own emitted grammar. What the proof buys is an internal
consistency check: `LigParser` matches the `.lig` grammar written in `lig.lig`, and
`parser_unambiguous` shows that grammar is unambiguous.

The scope is the structure only. `%header`, `%lexerheader`, `%lexer`, and the `{ … }`
action bodies stay behind the `LigLexer` balanced-brace escape hatch, outside the
generated parser and its proof. So the part of `.lig` most prone to subtle bugs is now a
generated, declared-grammar parser, and the embedded free-text leaves are still
hand-written. This is not "the frontend is verified"; it is "the structural parser is
generated and the leaves are not."

`parseLig`, the hand-written frontend, is retained, and it is still what the generator
and the LSP call. Two reasons. The LSP diagnostics engine (`Frontend/Diagnostics.lean`)
reads `Surface` spans to place error markers, and the generated parser produces
`Span.dummy` because the `LigTok` stream carries no source positions. And a hand-written
frontend that does not depend on the generated `LigParser` avoids a build cycle and is
the known-good fallback for the bootstrap. `parseLigGen` is checked to agree with
`parseLig` up to spans on every `.lig` file in the repository — the seven fixtures,
and `lig.lig` itself — by `test/lig/BootstrapAgreementTest.lean` (`lake exe
lig-bootstrap-test`). Agreement up to spans is what code generation needs, because
codegen never reads spans: regenerating all the fixture grammars through `parseLigGen`
produces byte-identical output to the committed generated files.

### 15.1 Updating `lig.lig`

Once generated, `LigParser` and `LigVerified` are ordinary Lean modules over the LPG
runtime, so updating the `.lig` grammar is the same self-hosting loop LPG already runs
for the fixtures:

1. Edit `LeanParserGenerator/Frontend/lig.lig`. If the change adds a new token or a new
   leaf shape, also edit `Frontend/LigLexer.lean` — the `LigTok` type, the hand lexer,
   and `assembleSurface`.
2. `lake build parsers` regenerates `Frontend/Generated/{LigParser,LigVerified}.lean`
   (the `parsers` target lists `lig.lig` first). This needs a working generator, which
   is built from the hand-written `parseLig`, so it does not depend on the parser being
   regenerated.
3. `lake exe lig-bootstrap-test` confirms `parseLigGen` still agrees with `parseLig`, and
   `lake build LeanParserGenerator.Frontend.Generated.LigVerified` re-checks the proofs.
4. Commit `lig.lig`, the regenerated `Generated/*.lean`, and any `LigLexer.lean` change
   together.

This is the usual self-hosting-parser-generator situation, the one Menhir also has:
regenerating `LigParser` needs a working LPG, so a generation bug can brick the frontend
until you regenerate from a good `LigParser`. Version control handles it. The generated
modules are committed, so a clean checkout builds without bootstrapping, and the previous
commit is always a good generator to regenerate from. The rule is "always keep a valid
version of the generator," which is routine under version control. If `parseLig` is ever
retired in favor of `parseLigGen`, spans have to be threaded through `LigLexer` and
`lig.lig` first, or the LSP loses precise error locations.


## 16. Other Features Planned
### 16.1 Code generation

The emitters build the generated module as `Lean.Syntax` via quotation and pretty-print it, rather
than concatenating source `String`s. The point is that a malformed structural emission fails against
Lean's grammar when the generator runs, not later when the generated file is compiled or its proof
fails. This gives up byte-identical regeneration — the pretty-printer reflows to its own layout — so
it was done only once byte-equality was no longer required. The requirement is that regenerated
grammars still compile and their proofs still check.

`Emit/Quote.lean` holds the infrastructure: `EmitM = StateT (Array String) CommandElabM`,
`renderCmd`/`renderCmds` (via `PrettyPrinter.ppCommand`), and the leaf mechanism below. Emission runs
in `CommandElabM` over an `Init`-only environment, so the generator exe sets `supportInterpreter :=
true` (rendering runs the elaborator and pretty-printer at generator runtime). `Emit/Builder.lean`
still holds string combinators for the parts kept as raw text.

Two subtleties shape the design, both found by experiment:

- Every generated name (def names, types, constructors, binders) is built with `mkIdent`, never
  written literally inside a `` `(…) `` quotation. A literal name carries a macro scope that
  `ppCommand` renders as `sem✝`, which is invalid source. This applies to everything: `V`, `Array`,
  `some`/`none`, the `.shift`/`.reduce` constructors, the grammar binders in `sem` patterns.

- Verbatim embedded-Lean leaves (action bodies, `%type` strings, dependent `Fin` literals and types)
  are not parsed. `runParserCategory` has only the builtin term parsers, so it fails on ordinary
  notation (`+`, `if`, list literals), and the generator cannot know a user `%header`'s notation. Each
  leaf is spliced as a placeholder identifier (`__ligLeaf{n}__`) and, after pretty-printing,
  `substituteLeaves` replaces it with the leaf's exact source text and checks that every recorded leaf
  was emitted — a check the old `%%REDV%%` `String.replace` did not have. So the structure is
  grammar-checked `Syntax` and the opaque user text is copied through untouched. `substituteLeaves`
  makes one pass: it splits the rendered module once on the `__ligLeaf` marker and reassembles the
  segments, reading each placeholder's index and splicing its source. The earlier version called
  `String.replace` once per leaf, each a full scan and rebuild of the whole module — `O(leaves ×
  moduleLength)`, which was the dominant generation cost on large grammars (c99's dependent module has
  ~580 leaves in a ~3.4 MB string; that pass alone took ~205 s). The single pass is `O(moduleLength)`
  and brought it under 1 s.

The split is per-grammar structure to `Syntax`, fixed scaffolding to raw text. The executable backend
(`Emit/Codegen.lean`) puts `V`, `decode`, `sem`, and `redv` on `Syntax`. Its `flat`/`table` record and
the `redvMatches` proof stay raw text. The flat table array literals (`actionData`/`gotoData`, the
compressed `actionCells`/`gotoCells`, `defRedData`/`lhsData`/`lenData`) are also emitted as raw text,
by `emitTable`: they are literals of numbers and fixed nullary/unary constructors (`.shift n`,
`.reduce n`, `.error`, `some n`, `none`), so `Syntax` adds no real check, and routing them through
`ppCommand` is the generator's worst performance cliff. `ppCommand`'s parenthesizer is superlinear in
the size of a single array literal, and these literals reach tens of thousands of elements — c99's two
dense arrays alone cost ~21 s in `ppCommand` (the subsequent `Format.pretty` was ~25 ms). `emitTable`
instead renders the element text directly and lays it out with a greedy width-116 fill that reproduces
`ppCommand`'s array-literal formatting exactly (`#[` on a 2-space-indented line, 4-space continuation,
each line packed to ≤116 columns, closing `]` after the last element), verified byte-for-byte against
the committed fixtures. This is `O(total element text)` and dropped c99's executable emit from ~21 s to
under 1 s.

The verified backend
(`Emit/CodegenVerified.lean`) puts its per-grammar semantic defs on `Syntax` — `semT'`, the named
`semanticAction{n}`s, `prodContents'` and its projections, `tokenName'`/`tokenTerm'`/`tokenSem'`, and
the `Nat` code tables `laInit`/`laCodesNinit` — with dependent patterns, signatures, and bodies as
leaves. Its dependent `Automaton` match tables and the fixed refinement/validation proof scripts stay
raw text: proof-carrying dependent Lean whose content is nearly all opaque, so routing it through
`Syntax` would make everything a leaf and check nothing (the same reason the executable `flat` and
`redvMatches` are raw). The stopping point is where `Syntax` stops adding a real check.

One emitter stays string-based despite being pure data: `verifiedGrammarView`. An anonymous structure
instance `{ field := … }` rendered by `ppCommand` daggers its field names (`index✝`), and the record
has nothing (only `Nat`s and `reprStr` strings) that string emission gets wrong — so `Syntax` there is
net-negative.

This is verified end to end: all fixtures plus `lig.lig` regenerate through both backends with
zero `✝` daggers, `lake build` is green, and the verified proof modules (calc, imp,
cedarschema via the paired build, and cedar checked directly) discharge their `native_decide`
certificates against the regenerated output. Nothing here moves the trust boundary: emission is
untrusted, and the a-posteriori validator re-checks the output however it was produced (§2).

### 16.2 Module system

The library and the generated code use Lean 4.35's module system (`module` header,
`public`/`meta`/`import all` imports, `@[expose] public section`). Every `.lean` file
in the package is a `module`; a `module` file may only import other modules, so the
whole graph — the 48 library files, `Main`, the LSP server, the generated
parser/lexer/verified/roundtrip modules, and the hand-written test support — is ported
together. The port follows the reference recipe (`module` first; `public import`;
`@[expose] public section` for reasoned-about code, `public section` for programs) and
then tightens visibility where it is worth it.

The two rules that drove almost every decision:

- **`native_decide` and `#guard` run at the meta phase.** Any module they reduce must
  be `meta import`ed, not just `public import`ed. When a module is used both in ordinary
  definitions and by `native_decide`, it is imported *twice* — `public import X` for the
  ordinary use and `meta import X` for the reduction. The generated lexer therefore
  `meta import`s `Lexer.Validator`/`DFA`/`ByteScan`/`ByteTokenize`/`ByteValidator`/
  `FlatTokenize` (its `native_decide` validations reduce the tables) on top of the plain
  `public import`s its `cflat`/`cbyte` definitions need; the verified spec does the same
  for `Runtime.Validator.Safe`/`Complete`, `Runtime.GrammarView`, and the parser module;
  the roundtrip module for the lexer.

- **Def-eq unfolding across modules needs the body.** A `public` definition's body is
  private unless the definition is `@[expose]`d or the client uses `import all`. Proofs
  that unfold a definition by `rfl`/`simp`/`decide` fail otherwise.

Generated-code visibility is deliberate, not uniform:

- **Parser** (`Emit/Codegen.lean`): `public section`, not exposed. Its public API is the
  value type, `run`, and `parse`; the LR tables, `decode`, `sem`, and `redv` are internal
  (their bodies stay in the private scope). A plain `public import CalcParser` gives a
  caller only the API. The paired verified spec, which unfolds `decode`/`sem`/`table` in
  its refinement `rfl` proofs and `native_decide`s over the flat tables, reaches those
  internals with `import all CalcParser` (allowed because both are in this package) plus
  the meta import. The hand-written `RefinementTest`, which compares the executable parser
  to the spec, also `import all`s the parser, because that is exactly the internal-access
  use case `import all` exists for.

- **Lexer** (`Emit/CodegenLexer.lean`): `public section`, not exposed. Public API is the
  token type and `tokenize`/`tokenizeByte`; the DFA/flat/byte tables and validator
  certificates are internal. The lexer's own `native_decide` validation theorems reduce
  those tables through the meta imports (same-file visibility does not need `@[expose]`).

- **Verified spec** (`Emit/CodegenVerified.lean`): `@[expose] public section`. This is the
  dependent specification module: its `Grammar`, automaton, dependent semantic types,
  `verifiedGrammarView`, and the exported corollaries (`parser_sound`, `parser_complete`,
  …) *are* the public API that downstream proofs reference, and the validation/refinement
  proofs unfold them throughout. Exposing it is the right choice, not a fallback.

- **Roundtrip** (`Emit/CodegenLexer.lean`): `@[expose] public section`; the `native_decide`
  fixed points reduce `renderTok`/`tokenize`.

User `%header`/`%lexerheader` text is copied into generated modules, so `Emit.Builder.publicizeImports`
rewrites any bare `import X` in it to `public import X` (an unqualified `import` is rejected inside a
module). This port does not move the trust boundary or change any axiom budget: the generated
`native_decide` certificates still depend only on `propext`, `Classical.choice`, `Quot.sound`, and
their own per-`native_decide` axioms, with no `sorry` and no new custom axioms.

### 16.3 Nice Error Handling

We should work on providing nice error messages for when the lexer or parser fails. For the parser,
let us take inspiration from how Menhir handles error messages. See [ERROR_MESSAGES](./ERROR_MESSAGES.md).

### 16.4 Tokenizer Proofs

The current lexer/tokenizer is only proved sound, and this soundness result is not something that provides
high confidence in the resulting tokenizer. It does prove its correctness according to an idealized
executable version of the tokenizer. This is a good result, but it is too easy to write a bad lexer.
See [LEXER](./LEXER.md).

A first slice of the roundtrip (printer/lexer inverse) property is now proved, and
it is **generated**, not hand-written. The generator emits a `FooLexerRoundtrip.lean`
beside each `FooLexer.lean` (the `parsers` Lake target runs `--roundtrip` after the
lexer), containing a generated `renderTok`/`render` and, for each reachable constant
(valueless) token, the fixed point `tokenize (renderTok t ++ " ") = .ok [t, EOF]`,
discharged by `native_decide` at the lexer's usual axiom budget. `renderTok` is
inferred from each valueless token's rule: `Emit/CodegenLexer.lean`'s `regexLiteral?`
reads the literal string a rule matches (a `cat` chain of single-character classes),
so `%token PLUS` printing `"+"` is derived from the `"+"` rule, not written by hand.
Value-carrying tokens (Cedar `IDENTIFIER`, `NUMBER`, …) are out of scope — they need
the user's printer-inversion lemma (LEXER.md open question 1) — so `render` maps them
to the empty string and no theorem is emitted for them. On the test lexers this
generates 5 (calc), 15 (CedarSchema), and 29 (Cedar) constant-token
roundtrip theorems.

The lexer-independent proof core is in `LeanParserGenerator/Lexer/Roundtrip.lean`
(kernel checked, no `native_decide`, no `sorry`): `tokenizeAuxDFA_fuel_mono` (fuel
monotonicity), `tokenize_render_fold` (the general list roundtrip by induction on the
token list, from a per-token peel), and — the key fact for a *general* theorem —
`scan_go_append`: the scan walk stops at the first dead transition, so once the walk
over a prefix dies, the suffix is irrelevant. This is what makes the separator break
maximal munch regardless of the rest of the input, and reduces the per-token peel to a
finite, suffix-independent check on `renderTok t` and the separator character (which is
why it is generatable). What remains to reach the full generated `∀ reachable T,
tokenize (render T) = .ok (T ++ [EOF])` is the connective work wiring `scan_go_append`
and the peel into `tokenize_render_fold`, plus the user inversion lemma for value
tokens. See [LEXER](./LEXER.md) for the proved-versus-open breakdown.

The generated `FooLexerRoundtrip.lean` is hole-free. Its headline is the hole-free
`render_roundtrip_all` (the list of all constant tokens prints-and-lexes back to itself,
`native_decide`) alongside the per-constant-token fixed points and `coverage`. It also
emits `def guarantees : String` and `#eval guarantees`, so a reader sees exactly what the
module proves without reading the proofs. I dropped the earlier `∀ s`
`render_roundtrip_general` theorem: it was the one place that needed a `sorry` (the
unproved step is bridging `tokenizeBare`, the flat runtime, to the fold's
`tokenizeAuxDFA`), and a module that always carries a `sorry` is worse than one that
states precisely the sublanguage it proves. The library route for the general statement
(`tokenize_render_fold` + `peel_emit`/`peel_skip` + `scan_lit_sep_indep`) is still in
`Lexer/Roundtrip.lean` for when the bridge is done; the generated module no longer
asserts it.

### 16.5 Parser roundtrip (token-generation inverse), formatter idempotence, and the full roundtrip

The lexer roundtrip is a printer/lexer inverse on tokens. The parser roundtrip is the
same idea one level up, and it is deliberately *token-level*, not string-level: the
parser theorem begins at tokens (§1), so the clean inverse of `parse` is a token
generator, not a printer through the lexer. The user supplies `unparse : StartTy → List
Tok` and the module proves `parse (unparse t) = some t` for the ASTs it is asked about.
It is opt-in via `%option roundtrip_parser <unparse>` (the function's name, in scope
through the `<Base>Unparse` module below). The generator writes `FooParserRoundtrip.lean`
beside the parser (the `parsers` Lake target).

**Everything the module proves is hole-free; there is no `sorry`.** The guarantee is
quantified over a `corpus` of ASTs, not over all ASTs. A universal `∀ t, parse (unparse
t) = some t` is not provable by the generator — it would have to invert the LR
automaton, and it is in fact *false* for a partial `unparse` (the CST has forms the
example `unparse` does not cover) — so stating it as `by sorry` would be a hole that can
never be truthfully closed. Instead the module states exactly the testable, true slice,
the same way the lexer roundtrip is stated over reachable tokens. The module contains:

- `parseRoundtrip (t) := FooParser.parse ((unparse t).map Positioned.dummy) 30`;
- `abbrev corpus : List StartTy := <Base>Unparse.corpus` — the corpus lives in the
  user's module (next point), so regeneration never overwrites it;
- the hole-free `roundtrip_corpus : corpus.all (fun t => parseRoundtrip t == some t) =
  true := by native_decide` (stated with `BEq`/`= true` because the generated ASTs derive
  `BEq`, not `DecidableEq`);
- `def guarantees : String` and `#eval guarantees`, which print exactly what was proven,
  so the guarantee is visible without reading the proofs.

**Specification is one list.** `corpus` lives in the user's `<Base>Unparse` module
(`CedarUnparse.corpus`, `CedarSchemaUnparse.corpus`); adding an AST there — and nothing
else — extends every roundtrip theorem to cover it, and regeneration keeps it. The
`<Base>Unparse` module is also where `unparse` and `renderTok` live, because they
reference `Tok`, which the shared `%header` cannot (the header is spliced into the lexer
module *before* `Tok` is defined). It imports the generated lexer (for `Tok`) and the
AST; the generated roundtrip module imports it (no cycle) and `open`s its namespace so
the options may name the functions unqualified.

**Formatter idempotence.** A token stream is printed as source by inserting whitespace
between tokens, and we want to know that this formatting does not change what the lexer
recovers. `%option roundtrip_format <renderTok>` names a *complete* token renderer
`renderTok : Tok → String` (also in `<Base>Unparse`), and the module then emits
`format`/`relex` and the hole-free `formatter_idempotence`: for every AST in `corpus`,
formatting its token stream with a space, a newline, or a tab all re-lex to the same
tokens + EOF (`native_decide`). It holds because `renderTok` is complete (every token
renders to text that re-lexes to it — keywords to their spelling, value tokens to a
canonical form, not to `""` as the lexer-roundtrip's inferred `renderTok` does for
non-constant tokens) and the separator is whitespace the lexer skips. The generator
emits a warning into the module if the lexer's start mode has no `skip` rule.

**The full roundtrip.** With both options the module composes the two roundtrips:
`fullRoundtrip (sep) (t) := (relex sep (unparse t)).bind (parse ∘ map dummy)` — the full
AST → tokens → source → tokens → AST path — and the hole-free `full_roundtrip_corpus`
proves every corpus AST survives it, for a space and a newline separator
(`native_decide`).

`test/cedar/ParserRoundtripTest.lean` and `test/cedarschema/ParserRoundtripTest.lean`
confirm the corpora are non-empty (`0 < corpus.length`) and re-state the three proven
theorems, so the guarantees are not vacuous: 7 `Policies` and 5 `Schema` CST witnesses
(scope-only policies with annotations and a `when { true }` condition; type, entity, and
namespace declarations with `Set<…>` and record types). All carry only the standard
axiom budget plus their own `native_decide` axiom — no `sorryAx`.

The restriction is the same keyword-folding one as the lexer roundtrip, one level down:
a witness must use token constructors that re-lex to themselves. The Cedar example builds
`IDENTIFIER` tokens through `identTok s := if h : s ∉ keywords then .IDENTIFIER ⟨s, h⟩
else …` — a decidable guard, no `sorry` — so a keyword string does not masquerade as an
identifier. Both options are wired through both `.lig` frontends (`parseLig` and the
bootstrap `parseLigGen`, which agree on the fixtures), the inferred CLI form, and an
explicit `--roundtrip-parser` mode.
