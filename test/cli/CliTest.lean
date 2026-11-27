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
`test/cli/CliTest.lean` — runs the `leanparsergenerator` binary on good and bad command
lines and checks the exit code, the messages, and the files written.

The binary is the one next to this executable, so build both first:

    lake build leanparsergenerator cli-test
    lake exe cli-test

Run from the repository root. Each case works in a fresh temporary directory.
-/

structure Res where
  code : UInt32
  out : String
  err : String

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- A grammar with a `%lexer` block. -/
private def lexerGrammar : String :=
"%tokentype Tok
%token <Nat> NUM
%token PLUS
%token EOF
%eof EOF
%lexer {
  let digit = ['0'-'9']
  | digit+ as s => { Tok.NUM s.toNat! }
  | \"+\"         => { Tok.PLUS }
  | (' ')+      => skip
  eof => { Tok.EOF }
}
%start expr
%%
expr :: Nat
  | l=expr PLUS r=NUM { l + r }
  | v=NUM             { v }
"

/-- The same grammar without a lexer: the tokens come from handwritten code. -/
private def noLexerGrammar : String :=
"%tokentype Tok
%token <Nat> NUM
%token PLUS
%token EOF
%eof EOF
%start expr
%%
expr :: Nat
  | l=expr PLUS r=NUM { l + r }
  | v=NUM             { v }
"

/-- A grammar with a reduce/reduce conflict. -/
private def conflictGrammar : String :=
"%tokentype Tok
%token A
%token EOF
%eof EOF
%start s
%%
s :: Nat
  | A { 1 }
  | A { 2 }
"

/-- A grammar whose syntax error is on line 3. -/
private def badOptionGrammar : String :=
"%tokentype Tok
%token EOF
%option bogus
%eof EOF
"

/-- A grammar around the given lexer rules. The rules start on line 8. -/
private def withLexerRules (rules : String) : String :=
  "%tokentype Tok\n%token <Nat> NUM\n%token ID\n%token KW\n%token EOF\n%eof EOF\n%lexer {\n" ++
  rules ++ "  eof => { Tok.EOF }\n}\n%start e\n%%\ne :: Nat\n  | v=NUM { v }\n"

private def numRule : String := "  | ['0'-'9']+ as s => { Tok.NUM s.toNat! }\n"

/-- A grammar around the given productions. The first rule head is on line 8. -/
private def withProductions (rules : String) : String :=
  "%tokentype Tok\n%token <Nat> NUM\n%token PLUS\n%token EOF\n%eof EOF\n%start e\n%%\n" ++ rules

/-- The version declared in `lakefile.lean`. -/
private def lakefileVersion : IO String := do
  let t ← IO.FS.readFile "lakefile.lean"
  match t.splitOn "version := v!\"" with
  | _ :: rest :: _ => return (rest.splitOn "\"").head!
  | _ => throw (IO.userError "no `version := v!\"…\"` in lakefile.lean")

def main : IO UInt32 := do
  let some dir := (← IO.appPath).parent
    | IO.eprintln "cannot find the directory of this executable"; return 1
  let bin := (dir / "leanparsergenerator").toString
  unless ← System.FilePath.pathExists bin do
    IO.eprintln s!"{bin} does not exist; run `lake build leanparsergenerator` first"
    return 1
  let failed ← IO.mkRef (0 : Nat)
  let check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
    if ok then IO.println s!"OK   {name}"
    else
      failed.modify (· + 1)
      IO.println s!"FAIL {name}{if detail.isEmpty then "" else "\n  " ++ detail}"
  let tmp ← IO.FS.createTempDir
  let counter ← IO.mkRef (0 : Nat)
  -- Run the binary in a fresh directory containing the given files.
  let run (cwd : System.FilePath) (args : List String) : IO Res := do
    let o ← IO.Process.output { cmd := bin, args := args.toArray, cwd := some cwd }
    return { code := o.exitCode, out := o.stdout, err := o.stderr }
  let fresh (files : List (String × String)) : IO System.FilePath := do
    counter.modify (· + 1)
    let d := tmp / s!"case{← counter.get}"
    IO.FS.createDirAll d
    for (n, c) in files do
      if let some parent := (d / n).parent then IO.FS.createDirAll parent
      IO.FS.writeFile (d / n) c
    return d
  let has (d : System.FilePath) (n : String) : IO Bool := System.FilePath.pathExists (d / n)

  -- Information flags.
  let d ← fresh []
  let r ← run d ["--help"]
  check "--help exits 0 and prints usage on stdout" (r.code == 0 && r.out.startsWith "usage:" && r.err.isEmpty)
  check "--help lists the exit codes" (contains r.out "LR(1) conflicts")
  let r ← run d ["-h"]
  check "-h is --help" (r.code == 0 && r.out.startsWith "usage:")
  let r ← run d ["--version"]
  let v ← lakefileVersion
  check "--version prints the version in lakefile.lean" (r.code == 0 && contains r.out v) s!"expected {v}, got {r.out}"

  -- Usage errors: exit 1, one `error:` line, and a pointer to --help.
  let usageErr (name : String) (args : List String) (msg : String) : IO Unit := do
    let d ← fresh [("a.lig", lexerGrammar)]
    let r ← run d args
    check name (r.code == 1 && contains r.err s!"error: {msg}" && contains r.err "--help" && r.out.isEmpty)
      s!"code {r.code}, stderr: {r.err}"
  usageErr "no arguments" [] "missing input file"
  usageErr "unknown option" ["--bogus", "a.lig"] "unknown option `--bogus`"
  usageErr "two input files" ["a.lig", "b.lig"] "expected one input file"
  usageErr "--only with an unknown output" ["--only", "foo", "a.lig"] "unknown output `foo`"
  usageErr "--print-grammar with an unknown format" ["--print-grammar", "xml", "a.lig"] "unknown format `xml`"
  usageErr "a flag without its value" ["a.lig", "--out-dir"] "`--out-dir` needs a value"
  usageErr "-v without --rust-report" ["-v", "a.lig"] "`-v` is only meaningful with `--rust-report`"
  usageErr "--print-grammar with --rust-report" ["--print-grammar", "bnf", "--rust-report", "a.lig"] "`--print-grammar` and `--rust-report` cannot be combined"

  -- Input errors: exit 1 and no uncaught exception.
  let d ← fresh [("sub/x", "")]
  let r ← run d ["missing.lig"]
  check "a missing file" (r.code == 1 && contains r.err "error: cannot read `missing.lig`" && !contains r.err "uncaught") r.err
  let r ← run d ["sub"]
  check "a directory as input" (r.code == 1 && contains r.err "it is a directory") r.err
  let d ← fresh [("bad.lig", badOptionGrammar)]
  let r ← run d ["bad.lig"]
  check "a syntax error is reported as file:line:col" (r.code == 1 && contains r.err "bad.lig:3:" && !contains r.err "at byte") r.err
  check "a syntax error writes nothing" (!(← has d "BadParser.lean"))

  -- Default generation.
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["expr.lig"]
  check "generation succeeds" (r.code == 0 && r.err.isEmpty) r.err
  check "it writes the verified, parser and lexer modules next to the .lig"
    ((← has d "ExprVerified.lean") && (← has d "ExprParser.lean") && (← has d "ExprLexer.lean"))
  check "it reports each file on stdout" (contains r.out "wrote ExprParser.lean" && contains r.out "wrote ExprLexer.lean")
  check "it writes no Rust without an option" (!(← has d "expr.rs"))
  let parserText ← IO.FS.readFile (d / "ExprParser.lean")
  check "the parser imports a top-level lexer" (contains parserText "public import ExprLexer")

  let d ← fresh [("expr.lig", noLexerGrammar)]
  let r ← run d ["expr.lig"]
  check "without a %lexer block no lexer module is written"
    (r.code == 0 && (← has d "ExprParser.lean") && !(← has d "ExprLexer.lean"))

  -- Flags.
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["--out-dir", "gen/out", "--module-prefix", "Foo.Bar", "expr.lig"]
  check "--out-dir and --module-prefix" (r.code == 0 && (← has d "gen/out/ExprParser.lean") && !(← has d "ExprParser.lean")) r.err
  let p ← IO.FS.readFile (d / "gen/out/ExprParser.lean")
  check "--module-prefix qualifies the lexer import" (contains p "public import Foo.Bar.ExprLexer")
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["--out-dir=o", "--module-prefix=Baz", "expr.lig"]
  check "--flag=value form" (r.code == 0 && (← has d "o/ExprParser.lean"))
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["--only", "parser", "expr.lig"]
  check "--only parser writes only the parser"
    (r.code == 0 && (← has d "ExprParser.lean") && !(← has d "ExprVerified.lean") && !(← has d "ExprLexer.lean"))
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["--only", "lexer", "--only", "verified", "expr.lig"]
  check "--only can be repeated"
    (r.code == 0 && (← has d "ExprLexer.lean") && (← has d "ExprVerified.lean") && !(← has d "ExprParser.lean"))
  let d ← fresh [("expr.lig", noLexerGrammar)]
  let r ← run d ["--only", "lexer", "expr.lig"]
  check "--only lexer needs a %lexer block" (r.code == 1 && contains r.err "needs a `%lexer` block") r.err
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["--only", "rust", "expr.lig"]
  check "--only rust needs an output path" (r.code == 1 && contains r.err "no Rust output path") r.err
  let r ← run d ["--only", "rust", "--rust-out", "r/x.rs", "expr.lig"]
  check "--only rust --rust-out writes only the Rust file"
    (r.code == 0 && (← has d "r/x.rs") && !(← has d "ExprParser.lean")) r.err
  let rs ← IO.FS.readFile (d / "r/x.rs")
  check "the Rust file says where it came from" (contains rs "Generated by LeanParserGenerator")

  -- The Rust path from `%option gen_rust` is relative to the .lig.
  let d ← fresh [("sub/expr.lig", "%option gen_rust rust/gen.rs\n" ++ lexerGrammar)]
  let r ← run d ["sub/expr.lig"]
  check "%option gen_rust is relative to the .lig" (r.code == 0 && (← has d "sub/rust/gen.rs") && (← has d "sub/ExprParser.lean")) r.err

  -- Grammar inspection writes no files.
  let d ← fresh [("expr.lig", lexerGrammar)]
  let r ← run d ["--print-grammar", "bnf", "expr.lig"]
  check "--print-grammar bnf prints productions and writes nothing"
    (r.code == 0 && contains r.out "expr" && contains r.out "PLUS" && !(← has d "ExprParser.lean")) r.err
  let r ← run d ["--print-grammar", "markdown", "expr.lig"]
  check "--print-grammar markdown" (r.code == 0 && r.out.length > 0 && !(← has d "ExprParser.lean")) r.err

  -- A `.lig` file name has to give valid module names.
  for bad in ["my-grammar.lig", "two words.lig", "1calc.lig", "calc.v2.lig", ".lig", "ünï.lig"] do
    let d ← fresh [(bad, lexerGrammar)]
    let r ← run d [bad]
    let written := (← (d.readDir)).size
    check s!"file name `{bad}` is rejected"
      (r.code == 1 && contains r.err "cannot infer module names from the file name" && r.out.isEmpty && written == 1)
      s!"code {r.code}, stderr: {r.err}, {written} files"
  let d ← fresh [("my-grammar.lig", lexerGrammar)]
  let r ← run d ["my-grammar.lig"]
  check "the error suggests a valid file name" (contains r.err "for example to `my_grammar.lig`") r.err
  for good in ["my_grammar.lig", "_x.lig", "Calc2.lig"] do
    let d ← fresh [(good, lexerGrammar)]
    let r ← run d [good]
    check s!"file name `{good}` is accepted" (r.code == 0) r.err
  let d ← fresh [("my-grammar.lig", lexerGrammar)]
  let r ← run d ["--only", "rust", "--rust-out", "x.rs", "my-grammar.lig"]
  check "--only rust does not need a valid file name" (r.code == 0 && (← has d "x.rs")) r.err
  for bad in ["Foo Bar", "Foo..Bar", ".Foo", "Foo.", "1Foo"] do
    let d ← fresh [("expr.lig", lexerGrammar)]
    let r ← run d ["--module-prefix", bad, "expr.lig"]
    check s!"module prefix `{bad}` is rejected"
      (r.code == 1 && contains r.err "invalid module prefix" && !(← has d "ExprParser.lean")) r.err
  let d ← fresh [("expr.lig", "%option module_prefix Foo.\n" ++ lexerGrammar)]
  let r ← run d ["expr.lig"]
  check "a bad %option module_prefix is rejected" (r.code == 1 && contains r.err "invalid module prefix" && contains r.err "%option module_prefix") r.err

  -- Grammar checks. Errors stop the generation and write nothing. Warnings are printed
  -- and the generation goes on. Every message carries file:line:col.
  let checkError (name : String) (src : String) (needle : String) (loc : String) : IO Unit := do
    let d ← fresh [("g.lig", src)]
    let r ← run d ["g.lig"]
    check name
      (r.code == 1 && contains r.err needle && contains r.err s!"g.lig:{loc}" && !(← has d "GParser.lean"))
      s!"code {r.code}, stderr: {r.err}"
  let checkWarning (name : String) (src : String) (needle : String) (loc : String) : IO Unit := do
    let d ← fresh [("g.lig", src)]
    let r ← run d ["g.lig"]
    check name
      (r.code == 0 && contains r.err s!"warning: g.lig:{loc}" && contains r.err needle && (← has d "GParser.lean"))
      s!"code {r.code}, stderr: {r.err}"
  checkError "a duplicate binder" (withProductions "e :: Nat\n  | v=NUM PLUS v=NUM { v }\n")
    "binder `v` is used more than once" "9:"
  checkError "the EOF token in a production" (withProductions "e :: Nat\n  | v=NUM EOF { v }\n")
    "end-of-input token `EOF` must not appear inside a production" "9:"
  checkError "an undefined symbol" (withProductions "e :: Nat\n  | v=NUM { v }\n  | l=e PLUS r=zzz { l }\n")
    "symbol `zzz` in rule `e` is neither a declared token nor a nonterminal" "10:"
  checkError "a reversed character range" (withLexerRules "  | ['9'-'0']+ => { Tok.ID }\n")
    "empty character range" "8:"
  checkError "a regex shorthand escape" (withLexerRules "  | '\\d'+ => { Tok.ID }\n")
    "unknown escape `\\d`" "8:"
  checkError "a pattern that matches nothing"
    (withLexerRules (numRule ++ "  | [^ '\\u0000'-'" ++ String.singleton (Char.ofNat 0x10FFFF) ++ "'] => { Tok.ID }\n"))
    "can never match" "9:"
  checkWarning "a lexer rule that matches the empty string"
    (withLexerRules "  | ['0'-'9']* as s => { Tok.NUM s.length }\n") "matches the empty string" "8:"
  checkWarning "a keyword rule after the identifier rule"
    (withLexerRules (numRule ++ "  | ['a'-'z']+ => { Tok.ID }\n  | \"if\" => { Tok.KW }\n"))
    "can never win" "10:"
  -- Rules in a good order, and a backslash before punctuation, give no diagnostics.
  let d ← fresh [("g.lig", withLexerRules (numRule ++ "  | \"if\" => { Tok.KW }\n  | ['a'-'z']+ => { Tok.ID }\n  | '\\.' => { Tok.ID }\n"))]
  let r ← run d ["g.lig"]
  check "a lexer with its rules in a good order gives no diagnostics" (r.code == 0 && r.err.isEmpty) r.err
  -- All errors are reported, not only the first.
  let d ← fresh [("g.lig", withProductions "e :: Nat\n  | v=NUM PLUS v=NUM { v }\n  | v=NUM EOF { v }\n")]
  let r ← run d ["g.lig"]
  check "all errors are reported" (r.code == 1 && contains r.err "used more than once" && contains r.err "end-of-input token") r.err

  -- LR(1) conflicts: exit 2, with the output still written.
  let d ← fresh [("c.lig", conflictGrammar)]
  let r ← run d ["c.lig"]
  check "LR(1) conflicts exit 2 and are listed on stderr" (r.code == 2 && contains r.err "conflict") r.err
  check "LR(1) conflicts still write the output" ((← has d "CParser.lean") && (← has d "CVerified.lean"))

  IO.FS.removeDirAll tmp
  let n ← failed.get
  if n == 0 then
    IO.println "cli test: all checks passed"
    return 0
  else
    IO.eprintln s!"cli test FAILED: {n} check(s)"
    return 1
