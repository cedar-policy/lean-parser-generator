# Syntax-error messages (Menhir-style)

Generated parsers can now produce informative syntax-error messages, following
Menhir's declarative error-reporting model.

## Background: how Menhir does it

Menhir's [incremental API](https://gallium.inria.fr/~fpottier/menhir/manual.html)
exposes the **LR automaton state** at the point of an error. Its workflow
(F. Pottier, *Reachability and error diagnosis in LR(1) parsers*, 2016) is:

1. `menhir --list-errors` enumerates every state in which an error can occur,
   each shown with the set of terminals that would have been accepted there
   (`[ SEMI OR EOF ]`), producing a `.messages` template.
2. You edit the template, writing one message per error state.
3. `menhir --compile-errors` turns it into a `message : int -> string` function.
4. At runtime, on error the application reads the state number and calls
   `message state`.

## How this project does it

Our executable engine already surfaces the same primitive: `Runtime.Exec.run`
returns `Result.reject state terminal`, carrying the LR state and the offending
lookahead. The layer built on top lives in
[`LeanParserGenerator/Runtime/Diagnostic.lean`](../LeanParserGenerator/Runtime/Diagnostic.lean):

- `expectedAt tbl numTerminals state` — the terminals accepted in `state`
  (Menhir's `[ … ]` lookahead set).
- `ParseError { state, lookahead, position, expected }` — the structured error.
- `diagnose` — runs the parser and, on rejection, fills in the position and the
  expected set.
- `diagnoseSpanned spanOf` — like `diagnose`, but also recovers the offending
  token's source `Span` (via a `spanOf : V → Option Span` projection), so the
  error can be rendered as `line:col`.
- `ParseError.format terminalName messages` — renders a message from the token
  index, where `messages : Nat → Option String` is the analog of a compiled
  `.messages` file and overrides the auto-generated text.
- `ParseError.formatWithSource span source terminalName messages` — renders
  `line:col` from the offending token's span against the source string.

This layer is *unverified* (like the executable engine), but it is proved
**consistent** with the verified parser: `diagnose_run_agrees` shows `diagnose`
classifies accept/reject/timeout exactly as the verified `Runtime.Exec.run`, so a
syntax error is reported precisely when the parser genuinely rejects.

## Using it from a generated parser

The engine runs at `VP := Span × V`: every token carries a source span (the
generated lexer emits `List (Runtime.Positioned Tok)`, and a hand-written lexer
wraps its tokens the same way — `Runtime.Span.dummy` when there are no real
positions). Every generated parser module emits, alongside `parse` and `run`:

```lean
def terminalName (t : Nat) : String            -- readable terminal names
def diagnose (input : List (Runtime.Positioned Tok)) (logNSteps := 20)
  : Runtime.Exec.Diagnostic VP
def diagnoseSpanned (input : List (Runtime.Positioned Tok)) (logNSteps := 20)
  : Runtime.Exec.Diagnostic VP × Option Runtime.Span
def errorMessage (input : List (Runtime.Positioned Tok)) (source : String := "")
  (messages := fun _ => none) (logNSteps := 20) : Option String
```

`errorMessage` renders `line:col` when given the source string; without it, it
falls back to the token index. Example (from `test/calc/ErrorMessageTest.lean`,
where `spannedBad` is `1 1` with byte spans and the second `1` is at byte 2):

```lean
open Calc CalcParser Runtime

#eval errorMessage spannedBad "1 1"
-- some "1:3: unexpected NUM;
--       expected one of: PLUS, TIMES, RPAR, DIV, end of input (in parser state 2)"
```

Without a source string the location is the token index instead of `line:col`:

```lean
#eval errorMessage (dummy [.NUM 1, .PLUS])
-- some "token 2: unexpected end of input;
--       expected one of: LPAR, NUM (in parser state 6)"
```

`diagnose`/`diagnoseSpanned` return the structured `ParseError` (and, for the
spanned variant, the offending `Span`) if you want to build your own message.

## Custom per-state messages

To attach hand-written messages (Menhir's `.messages` step), first list the
error states:

```sh
lake exe leanparsergenerator --list-errors grammar/Calc.lig
```

```text
# Syntax-error states for this grammar (9 state(s) can reject).
...
## State 6
## expected one of: LPAR, NUM
## rejects: PLUS, TIMES, RPAR, DIV, EOF, end of input
<YOUR SYNTAX ERROR MESSAGE HERE>
```

The state numbers match the generated parser, so you supply them directly:

```lean
def messages : Nat → Option String
  | 6 => some "expected an operand (a number or '(') after '+'"
  | _ => none

#eval errorMessage input (messages := messages)
```

## Tests

- `test/calc/ErrorMessageTest.lean` — `terminalName`/`diagnose`/`diagnoseSpanned`/
  `errorMessage` behavior, the custom per-state message override, span-based
  `line:col` rendering, and agreement with `parse`.
- `Runtime/Diagnostic.lean` — the `diagnose_run_agrees` consistency theorem is
  checked whenever the module compiles.

`ErrorMessageTest` is rooted in the `ParserTests` library: `lake build ParserTests`.
