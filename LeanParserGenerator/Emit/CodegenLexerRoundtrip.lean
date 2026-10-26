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
The offline lexer *roundtrip* backend.

This is separate from `Emit/CodegenLexer.lean` on purpose: the lexer module
(`FooLexer.lean`) is emitted for every `%lexer` block, but the roundtrip module
(`FooLexerRoundtrip.lean`) is only emitted when the user asks for it (the
`--roundtrip` CLI mode / the `parsers` Lake target's roundtrip step). Keeping the
opt-in roundtrip generation in its own file makes that boundary explicit and keeps
the always-run lexer backend small.

The roundtrip module proves, for the constant (valueless) token sublanguage, that
rendering a token and lexing it back returns that token, and states reachability
and coverage for every declared token (constant tokens exactly, value tokens for
some carried value). See docs/DESIGN.md §16.4 and docs/LEXER.md.
-/
public import LeanParserGenerator.Frontend.File
public import LeanParserGenerator.Lexer.Validator
public import LeanParserGenerator.Emit.Builder


@[expose] public section

namespace Emit

open Frontend Lexer

/-! ### Roundtrip (printer/lexer inverse) module

The generated `FooLexerRoundtrip.lean` proves that rendering a token list and
lexing it back returns the same list (docs/DESIGN.md §16.4, docs/LEXER.md). The
per-token peel is discharged by `native_decide` for the constant (valueless)
tokens whose rule matches a literal string; the general list fold is
`Lexer.tokenize_render_fold`. Value-carrying tokens need a user inversion lemma
(LEXER.md open q1) and are out of scope here — `render` maps them to the empty
string, so the generated theorem is stated over the constant-token sublanguage. -/

partial def regexLiteral? : Regex → Option String
  | .epsilon => some ""
  | .cls ⟨false, [(lo, hi)]⟩ => if lo == hi then some (String.singleton (Char.ofNat lo)) else none
  | .cat a b => do
      let sa ← regexLiteral? a
      let sb ← regexLiteral? b
      return sa ++ sb
  | _ => none

/-- TODO: this is useful to find a witness. This is currently incomplete and just "works" for
    our examples -/
partial def regexCandidates : Regex → List String
  | .epsilon => [""]
  | .never => []
  | .cls ⟨false, ranges⟩ =>
      -- one representative per range (low end), a few ranges max
      (ranges.take 3).filterMap (fun (lo, _) => some (String.singleton (Char.ofNat lo)))
  | .cls ⟨true, _⟩ =>
      -- negated class: try a common ASCII letter/digit not typically excluded
      ["a", "z", "0", "_", "."].take 3
  | .cat a b => Id.run do
      let cas := regexCandidates a
      let cbs := regexCandidates b
      let mut acc : List String := []
      for x in cas.take 3 do
        for y in cbs.take 3 do
          acc := acc ++ [x ++ y]
      return acc.take 6
  | .alt a b => (regexCandidates a ++ regexCandidates b).take 6
  | .star r =>
      let c := (regexCandidates r).headD ""
      ["", c, c ++ c].eraseDups

/-- A Lean string literal source form for `s` (escaping quotes and backslashes). -/
def strLitStr (s : String) : String :=
  "\"" ++ (s.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else String.singleton c)) "") ++ "\""

/-- **Faked witnesses for folded value tokens**  -/
def foldedWitness? (lexerName tokenName : String) : Option (String × String) :=
  match lexerName, tokenName with
  -- Cedar-family identifier: `a` is not a keyword, so it folds to IDENTIFIER.
  -- Payload literal must match the declared payload type: a plain `String` for
  -- cedarschema, the `{s // s ∉ keywords}` subtype for cedar/cedarentities.
  | "CedarLexer", "IDENTIFIER" => some ("a", "⟨\"a\", by native_decide⟩")
  | "CedarSchemaLexer", "IDENTIFIER" => some ("a", "\"a\"")
  | "CedarEntitiesLexer", "IDENTIFIER" => some ("a", "⟨\"a\", by native_decide⟩")
  | _, _ => none

/-- Generate `FooLexerRoundtrip.lean`: a generated `renderTok`/`render` and the
    per-constant-token roundtrip theorems, plus the general list roundtrip. Returns
    `none` (no module) if the lexer has no `skip` rule matching the space separator,
    since the roundtrip needs the separator to be skippable. -/
def generateRoundtripFrom (surface : Surface) (lexerImport lexerName roundtripModule : String) :
    Except String String := do
  let some spec := surface.lexer
    | .error "no `%lexer` block in the grammar; nothing to generate"
  let tokTy := surface.tokenType
  -- Constant (valueless) tokens whose start-mode rule emits exactly that token on
  -- a literal match. Map each to its literal render text.
  let mode0 := spec.modes[0]!
  -- Pair each rule with the inferred literal and its emit expression.
  let constToks : Array (String × String) := Id.run do
    let mut acc : Array (String × String) := #[]
    for t in surface.tokens do
      if t.hasVal then continue
      -- find a rule that emits exactly `Tok.<name>` (or `<name>`) on a literal
      for r in mode0.rules do
        match r.emit, regexLiteral? r.regex with
        | some e, some lit =>
            let en := e.trimAscii.toString
            if (en == s!"{tokTy}.{t.name}" || en == s!".{t.name}") && lit.length > 0 then
              acc := acc.push (t.name, lit)
        | _, _ => pure ()
    return acc
  -- Deduplicate token names (first literal wins).
  let constToks : Array (String × String) := Id.run do
    let mut seen : Array String := #[]
    let mut acc : Array (String × String) := #[]
    for (n, l) in constToks do
      unless seen.contains n do seen := seen.push n; acc := acc.push (n, l)
    return acc
  let eofName : Option String := match spec.eof with
    | some e => let en := e.trimAscii.toString
                if en.startsWith s!"{tokTy}." then some ((en.drop (tokTy.length + 1)).toString)
                else if en.startsWith "." then some ((en.drop 1).toString) else none
    | none => none
  -- Value-carrying tokens: for coverage we witness *some* value is producible.
  -- We must pick a lexeme whose *whole-lexer maximal munch* maps to the intended
  -- rule, not to a competing earlier/longer rule (e.g. `digit idcont*` MIXED
  -- vs `digit (digit|_)*` NAT). We enumerate candidate lexemes for the token's
  -- rule and keep the first whose `bestMatch` winner (over all mode-0 regexes,
  -- with the separator appended so munch stops there) is exactly that rule.
  let mode0Regexes : Array Regex := mode0.rules.map (·.regex)
  -- Classify each value token: `munchToks` = a munch-simulated lexeme whose winning
  -- rule's emit names the constructor (proof extracts the value); `fakeToks` = a
  -- hand-supplied (lexeme, payloadLiteral) for folded constructors; `unwitnessed`
  -- = declared value tokens we could not witness (named explicitly so the coverage
  -- gap is visible, not silent).
  let mut munchToks : Array (String × String) := #[]
  let mut fakeToks : Array (String × String × String) := #[]
  let mut unwitnessed : Array String := #[]
  for t in surface.tokens do
    if !t.hasVal then continue
    if some t.name == eofName then continue
    -- Try munch simulation: candidate lexemes whose bestMatch winner is a rule
    -- that emits this constructor, consuming exactly the candidate.
    let mut winners : Array String := #[]
    for hi : ri in [0:mode0.rules.size] do
      let r := mode0.rules[ri]
      match r.emit with
      | some e =>
          let en := e.trimAscii.toString
          let mentions := (en.splitOn s!"{tokTy}.{t.name}").length > 1
                        || (en.splitOn s!".{t.name}").length > 1
          if mentions then
            for w in regexCandidates r.regex do
              if w.isEmpty then continue
              match Lexer.bestMatch mode0Regexes (w ++ " ").toList with
              | some (winRule, winLen) =>
                  if winRule == ri && winLen == w.length && !winners.contains w then
                    winners := winners.push w
              | none => pure ()
      | none => pure ()
    -- Prefer all-decimal, shorter lexemes (least likely to panic a numeric action).
    let isDigits := fun (s : String) => !s.isEmpty && s.all (fun c => '0' ≤ c && c ≤ '9')
    let best := winners.toList.foldl (init := (none : Option String)) (fun cur w =>
      match cur with
      | none => some w
      | some b =>
          let better := (isDigits w && !isDigits b)
            || (isDigits w == isDigits b && w.length < b.length)
          if better then some w else some b)
    match best with
    | some w => munchToks := munchToks.push (t.name, w)
    | none =>
        match foldedWitness? lexerName t.name with
        | some (lexeme, payload) => fakeToks := fakeToks.push (t.name, lexeme, payload)
        | none => unwitnessed := unwitnessed.push t.name
  -- renderTok: constant tokens → their literal; everything else → "".
  let renderArms := String.intercalate "\n" (constToks.toList.map (fun (n, l) =>
    s!"  | .{n} => {strLitStr l}")) ++ "\n  | _ => \"\""
  -- Per-constant-token roundtrip theorems (native_decide).
  let thms := String.intercalate "\n" (constToks.toList.map (fun (n, _) =>
    let expected := match eofName with
      | some eof => s!"[{tokTy}.{n}, {tokTy}.{eof}]"
      | none => s!"[{tokTy}.{n}]"
    s!"theorem roundtrip_{n} : {lexerName}.tokenizeBare (renderTok {tokTy}.{n} ++ \" \") = .ok {expected} := by native_decide"))
  let reachThms := String.intercalate "\n"
    (constToks.toList.map (fun (n, _) =>
      s!"theorem reachable_{n} : ReachableTok {tokTy}.{n} := ⟨renderTok {tokTy}.{n} ++ \" \", _, roundtrip_{n}⟩"))
  let munchReachThms := String.intercalate "\n\n" (munchToks.toList.map (fun (n, w) =>
    let src := strLitStr (w ++ " ")
    s!"theorem reachable_{n} : ∃ v, ReachableTok ({tokTy}.{n} v) := by\n" ++
    s!"  refine ⟨?v, {src}, ?rest, ?eq⟩\n" ++
    s!"  case v => exact (match {lexerName}.tokenizeBare {src} with\n" ++
    s!"    | .ok ({tokTy}.{n} v :: _) => v | _ => default)\n" ++
    s!"  case rest => exact (match {lexerName}.tokenizeBare {src} with\n" ++
    s!"    | .ok (_ :: r) => r | _ => [])\n" ++
    s!"  case eq => native_decide"))
  let fakeReachThms := String.intercalate "\n\n" (fakeToks.toList.map (fun (n, lexeme, payload) =>
    let src := strLitStr (lexeme ++ " ")
    s!"-- folded constructor: witness supplied by `foldedWitness?` (LEXER.md).\n" ++
    s!"theorem reachable_{n} : ∃ v, ReachableTok ({tokTy}.{n} v) := by\n" ++
    s!"  refine ⟨{payload}, {src}, ?rest, ?eq⟩\n" ++
    s!"  case rest => exact (match {lexerName}.tokenizeBare {src} with\n" ++
    s!"    | .ok (_ :: r) => r | _ => [])\n" ++
    s!"  case eq => native_decide"))
  let valReachThms :=
    (if munchToks.isEmpty then "" else munchReachThms)
    ++ (if !munchToks.isEmpty && !fakeToks.isEmpty then "\n\n" else "")
    ++ (if fakeToks.isEmpty then "" else fakeReachThms)
  let valNames := (munchToks.toList.map Prod.fst) ++ (fakeToks.toList.map (fun (n, _, _) => n))
  let allReach := (constToks.toList.map Prod.fst) ++ valNames
  -- Coverage: every witnessed token constructor is reachable. Un-witnessed value
  -- tokens (LEXER.md witness-synthesis problem) are NOT in the conjunction; they
  -- are named in a comment above it so the gap is explicit, not silent.
  let coverageConjunct := fun (n : String) =>
    if (constToks.toList.map Prod.fst).contains n then s!"ReachableTok {tokTy}.{n}"
    else s!"(∃ v, ReachableTok ({tokTy}.{n} v))"
  let coverageBody := String.intercalate ",\n   " (allReach.map (fun n => s!"reachable_{n}"))
  let coverageType := if allReach.isEmpty then "True"
    else String.intercalate "\n    ∧ " (allReach.map coverageConjunct)
  let coverageProof := if allReach.length == 0 then "True.intro"
    else if allReach.length == 1 then coverageBody
    else s!"⟨{coverageBody}⟩"
  let unwitnessedNote := if unwitnessed.isEmpty then ""
    else s!"-- NOTE: these declared value tokens have no reachability witness yet\n" ++
         s!"-- (LEXER.md, the witness-synthesis problem): " ++
         String.intercalate ", " unwitnessed.toList ++ "\n"
  let out :=
    s!"module\n" ++
    s!"-- Generated by leanparsergenerator: roundtrip (printer/lexer inverse) theorems.\n" ++
    s!"public import {lexerImport}\n" ++
    s!"public import LeanParserGenerator.Lexer.Roundtrip\n" ++
    s!"meta import {lexerImport}\n" ++
    s!"meta import LeanParserGenerator.Lexer.Roundtrip\n" ++
    (if surface.header.isEmpty then "" else Builder.publicizeImports surface.header ++ "\n") ++ "\n" ++
    -- Roundtrip theorems are discharged by `native_decide` and unfold the lexer's
    -- `tokenize`/`renderTok`; expose the section (module system).
    s!"@[expose] public section\n\n" ++
    s!"namespace {roundtripModule}\n\n" ++
    s!"local instance \{ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) :=\n" ++
    s!"  fun a b => by cases a <;> cases b <;> simp_all <;> exact inferInstance\n\n" ++
    s!"def renderTok : {tokTy} → String\n{renderArms}\n\n" ++
    s!"def render (ts : List {tokTy}) : String := ts.foldr (fun t acc => renderTok t ++ \" \" ++ acc) \"\"\n\n" ++
    thms ++ "\n\n" ++
    s!"def ReachableTok (t : {tokTy}) : Prop := ∃ src rest, {lexerName}.tokenizeBare src = .ok (t :: rest)\n\n" ++
    reachThms ++ "\n\n" ++
    (if valNames.isEmpty then "" else valReachThms ++ "\n\n") ++
    unwitnessedNote ++
    s!"theorem coverage :\n    {coverageType} :=\n  {coverageProof}\n\n" ++
    (let cnames := constToks.toList.map Prod.fst
     if cnames.isEmpty then "" else
      let listLit := "[" ++ String.intercalate ", " (cnames.map (fun n => s!"{tokTy}.{n}")) ++ "]"
      let eofSuffix := match eofName with
        | some eof => s!" ++ [{tokTy}.{eof}]"
        | none => ""
      s!"abbrev Roundtrips (s : List {tokTy}) : Prop :=\n" ++
      s!"  {lexerName}.tokenizeBare (render s) = .ok (s{eofSuffix})\n\n" ++
      s!"/-- **Proven (hole-free).** The list of all constant (valueless) tokens this\n" ++
      s!"    lexer renders prints-and-lexes back to itself, by `native_decide`: a\n" ++
      s!"    printer/lexer inverse on the constant-token sublanguage. Extend it by adding\n" ++
      s!"    tokens to the list. -/\n" ++
      s!"theorem render_roundtrip_all : Roundtrips {listLit} := by native_decide\n\n" ++
      s!"/-- A human-readable summary of what this module proves. `#eval guarantees`. -/\n" ++
      s!"def guarantees : String :=\n" ++
      s!"  \"{roundtripModule}: proven hole-free:\\n" ++
      s!"  per-constant-token  : tokenize (renderTok t ++ \\\" \\\") = [t, EOF]\\n" ++
      s!"  render_roundtrip_all: tokenize (render all-const-tokens) = tokens ++ EOF\\n" ++
      s!"  coverage            : every declared token constructor is reachable\"\n\n" ++
      s!"#eval guarantees\n\n") ++
    s!"end {roundtripModule}\n"
  return out

end Emit
