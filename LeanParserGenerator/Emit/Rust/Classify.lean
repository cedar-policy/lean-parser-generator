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
Decide whether a semantic action can be emitted as Rust (docs/RUST_PARSER.md).

`analyze` walks an `AExpr` and records which emission rules it needs (`Used`) and what
stops it (`Blocker`). An action with no blockers is emittable; an action with blockers
needs a hand-written Rust hook (decision D4). The set of rules is the `Used`
datatype plus `Rules.knownFns`, and the set of blockers is the `Blocker` datatype,
so this file is the whole answer to "what does the Rust backend emit".
-/
public import LeanParserGenerator.Emit.Rust.Action
public import LeanParserGenerator.Emit.Rust.Rules


@[expose] public section

namespace Emit.Rust

/-- Why an action cannot be emitted. -/
inductive Blocker where
  /-- Syntax outside the action subset (`Action.lean`). -/
  | syntax (what : String)
  /-- A lambda (D4: no closures in the output). -/
  | lambda
  /-- A name the resolver does not know. -/
  | unresolved (name : String)
  /-- A name defined in the `.lig` header text, which the resolver cannot see. -/
  | headerDefinition (name : String)
  /-- A function that is not in `Rules.knownFns`. -/
  | unknownFunction (full : String)
  /-- A bound variable applied to arguments. -/
  | localFunction (x : String)
  /-- `.c` where the expected type is not known. -/
  | noExpectedType (c : String)
  /-- A constructor or known function applied to the wrong number of arguments. -/
  | arity (full : String) (want got : Nat)
  /-- `e.f` where the type of `e` is not known. -/
  | unknownReceiver (f : String)
  /-- A function used as a value, or an application with a non-name head. -/
  | notApplicable (what : String)
  deriving Repr, BEq, Inhabited

def Blocker.describe : Blocker → String
  | .syntax w => s!"syntax outside the action subset ({w})"
  | .lambda => "lambda"
  | .unresolved n => s!"unresolved name `{n}`"
  | .headerDefinition n => s!"`{n}` is defined in the .lig header"
  | .unknownFunction f => s!"function `{f}` is not a known function"
  | .localFunction x => s!"application of bound variable `{x}`"
  | .noExpectedType c => s!"`.{c}` without a known expected type"
  | .arity f w g => s!"`{f}` takes {w} arguments, given {g}"
  | .unknownReceiver f => s!"`.{f}` on an expression of unknown type"
  | .notApplicable w => s!"{w}"

/-- A short label for counting blockers of the same kind. -/
def Blocker.kind : Blocker → String
  | .syntax _ => "syntax"
  | .lambda => "lambda"
  | .unresolved _ => "unresolved name"
  | .headerDefinition _ => "defined in header"
  | .unknownFunction _ => "unknown function"
  | .localFunction _ => "local function"
  | .noExpectedType _ => "no expected type"
  | .arity .. => "arity"
  | .unknownReceiver _ => "unknown receiver"
  | .notApplicable _ => "not applicable"

/-- An emission rule that an action used. -/
inductive Used where
  | var | lit | unit | tuple | list | cons | append | proj
  /-- A constructor, by full name. -/
  | ctor (full : String)
  /-- A structure projection function, by full name. -/
  | field (full : String)
  /-- A function from `Rules.knownFns`. -/
  | known (full : String)
  deriving Repr, BEq, Inhabited

def Used.describe : Used → String
  | .var => "variable" | .lit => "literal" | .unit => "unit" | .tuple => "tuple"
  | .list => "list literal" | .cons => "cons" | .append => "append" | .proj => "projection"
  | .ctor n => s!"constructor {n}" | .field n => s!"field {n}" | .known n => s!"known function {n}"

/-- The result of analysing one action. -/
structure Analysis where
  used : Array Used := #[]
  blockers : Array Blocker := #[]
  /-- Calls of known functions, with the receiver or first argument (for domain checks). -/
  calls : Array (String × AExpr) := #[]
  /-- Variables used more than once. Rust moves values, so these need a copy (D5). -/
  clones : Array String := #[]
  deriving Repr, Inhabited

def Analysis.emittable (a : Analysis) : Bool := a.blockers.isEmpty

/-- What the analysis knows about names. -/
structure Ctx where
  res : Resolver
  /-- Namespaces opened by the header. -/
  opens : List String := []
  /-- Bound variables with their types. -/
  vars : List (String × Ty) := []
  /-- Names of functions defined in the header text. -/
  headerDefs : List String := []

abbrev M := StateM Analysis

def use (u : Used) : M Unit :=
  modify fun a => { a with used := if a.used.contains u then a.used else a.used.push u }

def recordCall (fn : String) (recv : AExpr) : M Unit :=
  modify fun a => { a with calls := a.calls.push (fn, recv) }

def block (b : Blocker) : M Unit :=
  modify fun a => { a with blockers := a.blockers.push b }

/-- Look a global name up: `Init` aliases first, then the resolver. -/
def lookup (ctx : Ctx) (name : String) : Option Resolved :=
  let name := (builtinAliases.lookup name).getD name
  ctx.res.find ctx.opens name

def knownFn? (full : String) : Option KnownFn := knownFns.find? (·.name == full)

/-- The type of a variable or of a projection of one. -/
def typeOf (ctx : Ctx) : AExpr → Option Ty
  | .var x => ctx.vars.lookup x
  | .proj e i =>
    match typeOf ctx e with
    | some (.prod a b) => if i == 1 then some a else if i == 2 then some b else none
    | _ => none
  | .field x f =>
    match typeOf ctx x with
    | some ty => ty.head?.bind fun h => (knownFn? (h ++ "." ++ f)).bind (·.ret)
    | none => none
  | .app (.field x f) _ =>
    match typeOf ctx x with
    | some ty => ty.head?.bind fun h => (knownFn? (h ++ "." ++ f)).bind (·.ret)
    | none => none
  | _ => none

/-- Explain a name the resolver cannot find. -/
def unresolvedBlocker (ctx : Ctx) (name : String) : Blocker :=
  if ctx.headerDefs.contains name then .headerDefinition name else .unresolved name

/-- The constructor `T.c` for an expected type `T`. -/
def dotCtor (ctx : Ctx) (expected : Option Ty) (c : String) : Option Resolved :=
  match expected.bind Ty.head? with
  | none => none
  | some t =>
    match ctx.res.find ctx.opens t with
    | none => none
    | some r =>
      match ctx.res.find [] (r.full ++ "." ++ c) with
      | some ({ kind := .ctor .., .. } : Resolved) => ctx.res.find [] (r.full ++ "." ++ c)
      | _ => none

mutual

/-- Check an application of a resolved constructor/function to `args`. -/
partial def analyzeApp (ctx : Ctx) (r : Resolved) (args : Array AExpr) : M Unit := do
  match r.kind with
  | .ctor _ fields =>
    use (.ctor r.full)
    if fields.size != args.size then block (.arity r.full fields.size args.size)
    for h : i in [0:args.size] do
      analyze ctx args[i] (fields[i]?)
  | .fn _ =>
    match knownFn? r.full with
    | some k =>
      use (.known r.full)
      if let some a0 := args[0]? then recordCall r.full a0
      if k.arity != args.size then block (.arity r.full k.arity args.size)
      for a in args do analyze ctx a none
    | none => block (.unknownFunction r.full)
  | .proj =>
    use (.field r.full)
    if args.size != 1 then block (.arity r.full 1 args.size)
    for a in args do analyze ctx a none
  | _ => block (.notApplicable s!"`{r.full}` is not a constructor or function")

/-- Analyse `e` against the expected type, if known. -/
partial def analyze (ctx : Ctx) (e : AExpr) (expected : Option Ty) : M Unit := do
  match e with
  | .var _ => use .var
  | .nat _ | .str _ => use .lit
  | .unit => use .unit
  | .other w => block (.syntax w)
  | .lam .. => block .lambda
  | .tuple es =>
    use .tuple
    for h : i in [0:es.size] do
      let ty := match expected with
        | some (.prod a b) => if i == 0 then some a else if i == 1 && es.size == 2 then some b else none
        | _ => none
      analyze ctx es[i] ty
  | .list es =>
    use .list
    let elemTy := match expected with
      | some (.con "List" #[t]) => some t
      | _ => none
    for x in es do analyze ctx x elemTy
  | .cons h t =>
    use .cons
    let elemTy := match expected with
      | some (.con "List" #[x]) => some x
      | _ => none
    analyze ctx h elemTy
    analyze ctx t expected
  | .append a b =>
    use .append
    analyze ctx a expected
    analyze ctx b expected
  | .proj x _ =>
    use .proj
    analyze ctx x none
  | .field x f =>
    match typeOf ctx x with
    | none => block (.unknownReceiver f)
    | some ty =>
      match ty.head? with
      | none => block (.unknownReceiver f)
      | some t =>
        analyze ctx x none
        let full := t ++ "." ++ f
        match knownFn? full with
        | some _ => use (.known full); recordCall full x
        | none =>
          match lookup ctx full with
          | some r => analyzeApp ctx r #[]
          | none => block (unresolvedBlocker ctx full)
  | .structInst fs =>
    -- `{ f := e, … }` against a structure type: the fields must be exactly the
    -- structure's, and each is analysed at its declared type.
    match expected.bind Ty.head? with
    | none => block (.noExpectedType "{ … }")
    | some t =>
      match ctx.res.find ctx.opens t with
      | none => block (unresolvedBlocker ctx t)
      | some r =>
        match ctx.res.fields r.full, ctx.res.find [] (r.full ++ ".mk") with
        | some names, some ({ kind := .ctor _ ftys, .. } : Resolved) =>
          use (.ctor (r.full ++ ".mk"))
          let given := fs.map (·.1)
          if names.any (!given.contains ·) || given.any (!names.contains ·) then
            block (.notApplicable s!"structure instance fields {given.toList} do not match {names.toList}")
          for (f, x) in fs do
            let idx := names.findIdx? (· == f)
            analyze ctx x (idx.bind fun i => ftys[i]?)
        | _, _ => block (.notApplicable s!"`{r.full}` is not a structure")
  | .anon es =>
    -- `⟨…⟩` is the structure constructor of the expected type.
    match dotCtor ctx expected "mk" with
    | some r => analyzeApp ctx r es
    | none => block (.noExpectedType "⟨…⟩")
  | .dotIdent c =>
    match dotCtor ctx expected c with
    | some r => analyzeApp ctx r #[]
    | none => block (.noExpectedType c)
  | .global n =>
    match lookup ctx n with
    | some r =>
      match r.kind with
      | .ctor _ fields =>
        use (.ctor r.full)
        if fields.size != 0 then block (.arity r.full fields.size 0)
      | _ => block (.notApplicable s!"`{r.full}` used as a value")
    | none => block (unresolvedBlocker ctx n)
  | .app f args =>
    match f with
    | .global n =>
      -- `some x` against `Option T` passes `T` down; every other constructor takes its
      -- field types from the environment.
      if n == "some" && args.size == 1 then
        use (.ctor "Option.some")
        let inner := match expected with
          | some (.con "Option" #[t]) => some t
          | _ => none
        analyze ctx args[0]! inner
      else
        match lookup ctx n with
        | some r => analyzeApp ctx r args
        | none => block (unresolvedBlocker ctx n)
    | .dotIdent c =>
      match dotCtor ctx expected c with
      | some r => analyzeApp ctx r args
      | none => block (.noExpectedType c)
    | .var x => block (.localFunction x)
    | .field x fn =>
      -- A method call `x.f a`: the receiver is the first argument.
      match typeOf ctx x with
      | none => block (.unknownReceiver fn)
      | some ty =>
        match ty.head? with
        | none => block (.unknownReceiver fn)
        | some t =>
          let full := t ++ "." ++ fn
          match knownFn? full with
          | some k =>
            use (.known full)
            recordCall full x
            analyze ctx x none
            if k.arity != args.size + 1 then block (.arity full k.arity (args.size + 1))
            for a in args do analyze ctx a none
          | none =>
            match lookup ctx full with
            | some r => block (.unknownFunction r.full)
            | none => block (unresolvedBlocker ctx full)
    | _ => block (.notApplicable "application of a non-name")

end

/-- The variables an expression mentions, with repetition. -/
partial def varUses : AExpr → List String
  | .var x => [x]
  | .app f args => varUses f ++ (args.toList.flatMap varUses)
  | .tuple es | .list es | .anon es => es.toList.flatMap varUses
  | .structInst fs => fs.toList.flatMap fun (_, x) => varUses x
  | .cons a b | .append a b => varUses a ++ varUses b
  | .proj e _ | .field e _ => varUses e
  | .lam ps b => (varUses b).filter (fun x => !ps.contains x)
  | _ => []

/-- Analyse the action text `src`. `vars` are the bound variables and their types, and
    `expected` is the type the action must produce. -/
def analyzeAction (ctx : Ctx) (src : String) (expected : Option Ty) : Analysis :=
  let e := Action.parse (ctx.vars.map (·.1)) src
  let (_, a) := (analyze ctx e expected).run {}
  let uses := varUses e
  let dup := (uses.eraseDups).filter fun x =>
    uses.count x > 1 && !x.endsWith "_span"
  { a with clones := dup.toArray }

end Emit.Rust
