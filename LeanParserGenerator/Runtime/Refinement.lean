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
public import LeanParserGenerator.Runtime.Exec
public import LeanParserGenerator.Runtime.Safety


@[expose] public section

namespace Runtime.Refinement

open Runtime Grammar

variable [G : Grammar] [A : Automaton]
variable {V : Type}

/-- A heterogeneous list of semantic values indexed by grammar symbols. -/
inductive Values : List Grammar.Sym → Type
  | nil : Values []
  | cons {symbol : Grammar.Sym} {symbols : List Grammar.Sym}
      (value : G.semT symbol) (rest : Values symbols) : Values (symbol :: symbols)

namespace Values

/-- Apply a curried dependent action to a heterogeneous value list. -/
def apply {Result : Type} : {symbols : List Grammar.Sym} →
    Values symbols → arrowsRight Result (symbols.map G.semT) → Result
  | [], .nil, action => action
  | s :: _, .cons value rest, action =>
      have action' : G.semT s → arrowsRight Result _ := action
      rest.apply (action' value)

/-- Encode a heterogeneous value list into executable values, top first. -/
def encode (encodeValue : (symbol : Grammar.Sym) → G.semT symbol → V) :
    {symbols : List Grammar.Sym} → Values symbols → List V
  | [], .nil => []
  | symbol :: _, .cons value rest => encodeValue symbol value :: rest.encode encodeValue

end Values

/-- Per-grammar evidence connecting a dependent automaton to an executable table. -/
structure ExecRefinement (V : Type) where
  table : Exec.ExecTable V
  decode : G.Token → Nat × V
  eof : G.Token
  encodeValue : (symbol : Grammar.Sym) → G.semT symbol → V
  stateIndex : AState → Nat
  terminalIndex : G.Terminal → Nat
  nonterminalIndex : G.NonTerminal → Nat
  productionIndex : G.Production → Nat
  start_agrees : ∀ init, table.startState = stateIndex (.Init init)
  eof_agrees : table.eof = decode eof
  decode_agrees : ∀ token,
    decode token =
      (terminalIndex (G.tokenTerm token), encodeValue (.T (G.tokenTerm token)) (G.tokenSem token))
  default_agrees : ∀ state,
    table.defaultReduce (stateIndex state) =
      match A.actionTable state with
      | .DefaultReduce production => some (productionIndex production)
      | .Lookahead _ => none
  lookahead_agrees : ∀ state actions,
    A.actionTable state = .Lookahead actions → ∀ terminal,
      table.action (stateIndex state) (terminalIndex terminal) =
        match actions terminal with
        | .Shift target _ => .shift (stateIndex (.Ninit target))
        | .Reduce production => .reduce (productionIndex production)
        | .Fail => .error
  goto_agrees : ∀ state nonterminal,
    table.goto (stateIndex state) (nonterminalIndex nonterminal) =
      (A.gotoTable state nonterminal).map fun target => stateIndex (.Ninit target.1)
  production_lhs_agrees : ∀ production,
    table.prodLhs (productionIndex production) =
      nonterminalIndex (G.prodLhs production)
  production_length_agrees : ∀ production,
    table.prodRhsLen (productionIndex production) = (G.prodRhsRev production).length
  semantic_agrees : ∀ production (values : Values (G.prodRhsRev production)),
    table.sem (productionIndex production) (values.encode encodeValue).reverse =
      encodeValue (.NT (G.prodLhs production)) (values.apply (G.prodAction production))

/-- A finite token list viewed as the verified runtime's total EOF-padded stream. -/
def listStream (refinement : ExecRefinement V) (input : List G.Token) : NatStream G.Token :=
  fun index => input.getD index refinement.eof

/-- Erase the dependent parser stack into executable state/value cells. -/
def eraseStack (refinement : ExecRefinement V) : Runtime.Stack → Exec.Stack V
  | [] => []
  | ⟨state, value⟩ :: rest =>
      (refinement.stateIndex (.Ninit state), refinement.encodeValue (A.lastSymb state) value) ::
        eraseStack refinement rest

private theorem encode_cast (refinement : ExecRefinement V) {left right : Grammar.Sym}
    (equality : left = right) (value : G.semT left) :
    refinement.encodeValue right (castSem equality value) = refinement.encodeValue left value := by
  subst right
  rfl

private inductive Pops : (symbols : List Grammar.Sym) → Runtime.Stack →
    Runtime.Stack → Values symbols → Prop
  | nil (stack : Runtime.Stack) : Pops [] stack stack .nil
  | cons {symbol : Grammar.Sym} {symbols : List Grammar.Sym}
      {state : A.NonInitState} {value : G.semT (A.lastSymb state)}
      {stack rest : Runtime.Stack} {values : Values symbols}
      (head : A.lastSymb state = symbol) (tail : Pops symbols stack rest values) :
      Pops (symbol :: symbols) (⟨state, value⟩ :: stack) rest
        (.cons (castSem head value) values)

private theorem pop_of_pops {Result : Type} {symbols : List Grammar.Sym}
    {stack rest : Runtime.Stack} {values : Values symbols}
    (pops : Pops symbols stack rest values)
    (action : arrowsRight Result (symbols.map G.semT)) :
    Runtime.pop symbols stack action = some (rest, values.apply action) := by
  induction pops generalizing Result with
  | nil => rfl
  | @cons symbol symbols state value stack rest values head tail ih =>
      simp only [Runtime.pop]
      split
      next equality =>
        have : equality = head := Subsingleton.elim _ _
        subst equality
        exact ih (action (castSem head value))
      next mismatch => exact (mismatch head).elim

private theorem Exec.popNGo_of_pops (refinement : ExecRefinement V) {symbols : List Grammar.Sym}
    {stack rest : Runtime.Stack} {values : Values symbols}
    (pops : Pops symbols stack rest values) (accumulator : List V) :
    Exec.popN.go symbols.length (eraseStack refinement stack) accumulator =
      some ((values.encode refinement.encodeValue).reverse ++ accumulator,
        eraseStack refinement rest) := by
  induction pops generalizing accumulator with
  | nil => rfl
  | @cons symbol symbols state value stack rest values head tail ih =>
      simp only [List.length_cons, eraseStack, Exec.popN.go]
      rw [ih (refinement.encodeValue (A.lastSymb state) value :: accumulator)]
      simp only [Values.encode, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [encode_cast refinement head]

private theorem Exec.popN_of_pops (refinement : ExecRefinement V) {symbols : List Grammar.Sym}
    {stack rest : Runtime.Stack} {values : Values symbols}
    (pops : Pops symbols stack rest values) :
    Exec.popN symbols.length (eraseStack refinement stack) =
      some ((values.encode refinement.encodeValue).reverse, eraseStack refinement rest) := by
  unfold Exec.popN
  simpa using popNGo_of_pops refinement pops []

private theorem pops_of_prefix : ∀ (symbols : List Grammar.Sym) (stack : Runtime.Stack),
    Prefix symbols (symbStackOfStack stack) →
      ∃ (rest : Runtime.Stack) (values : Values symbols), Pops symbols stack rest values := by
  intro symbols
  induction symbols with
  | nil =>
      intro stack _
      exact ⟨stack, .nil, .nil stack⟩
  | cons symbol symbols ih =>
      intro stack hPrefix
      cases stack with
      | nil => exact (by cases hPrefix)
      | cons cell stack =>
          obtain ⟨state, value⟩ := cell
          obtain ⟨head, tail⟩ := hPrefix.cons_inv
          obtain ⟨rest, values, pops⟩ := ih stack tail
          exact ⟨rest, .cons (castSem head.symm value) values, .cons head.symm pops⟩

private theorem top_state_agrees (refinement : ExecRefinement V) (init : A.InitState)
    (stack : Runtime.Stack) :
    Exec.topState refinement.table (eraseStack refinement stack) =
      refinement.stateIndex (stateOfStack init stack) := by
  cases stack with
  | nil => exact refinement.start_agrees init
  | cons cell _ => cases cell; rfl

private def eraseReductionResult (refinement : ExecRefinement V) (init : A.InitState) :
    StepResult (NatStream G.Token) init → Exec.Result V ⊕ Exec.Stack V
  | .Fail state token =>
      .inl (.reject (refinement.stateIndex state) (refinement.terminalIndex (G.tokenTerm token)))
  | .Accept value _ => .inl (.ok (refinement.encodeValue (.NT (A.startNt init)) value))
  | .Progress stack _ => .inr (eraseStack refinement stack)
  | .Err message => .inl (.err message)

private theorem reduce_agrees (refinement : ExecRefinement V)
    (init : A.InitState) (stack : Runtime.Stack) (input : List G.Token)
    (production : G.Production) (invariant : StackInvariant init stack)
    (valid : ValidForReduce (stateOfStack init stack) production) :
    Exec.reduce refinement.table (refinement.productionIndex production) (eraseStack refinement stack) =
      eraseReductionResult refinement init
        (Runtime.reduceStep init stack production (listStream refinement input)) := by
  have hPrefix := valid.1.trans invariant.symbs
  obtain ⟨rest, values, pops⟩ := pops_of_prefix _ _ hPrefix
  have dependentPop := pop_of_pops pops (G.prodAction production)
  have executablePop := Exec.popN_of_pops refinement pops
  obtain ⟨safeRest, safeValue, safePop, _, stateValid⟩ :=
    pop_safe init (G.prodRhsRev production) stack (G.prodAction production)
      (headStates (stateOfStack init stack)) invariant hPrefix invariant.states
  rw [dependentPop] at safePop
  have pairEq := Option.some.inj safePop
  have restEq : rest = safeRest := congrArg Prod.fst pairEq
  subst safeRest
  unfold Exec.reduce Runtime.reduceStep
  rw [refinement.production_length_agrees, executablePop]
  simp only
  rw [refinement.semantic_agrees, refinement.production_lhs_agrees, dependentPop]
  simp only
  rw [top_state_agrees refinement init rest, refinement.goto_agrees]
  cases gotoResult : A.gotoTable (stateOfStack init rest) (G.prodLhs production) with
  | some target =>
      obtain ⟨target, equality⟩ := target
      simp only [Option.map_some, eraseReductionResult, eraseStack]
      rw [encode_cast refinement equality]
  | none =>
      have missing := valid.2 (stateOfStack init rest) stateValid
      rw [gotoResult] at missing
      simp only [Option.map_none]
      cases rest with
      | nil =>
          have startEq : G.prodLhs production = A.startNt init := by
            simpa only [stateOfStack] using missing
          simp only [startEq, eraseReductionResult]
          congr 2
          exact (encode_cast refinement
            (congrArg (fun nt => (Symbol.NT nt : Grammar.Sym)) startEq)
            (values.apply (G.prodAction production))).symm
      | cons cell tail =>
          obtain ⟨state, value⟩ := cell
          exact missing.elim

/-- Relation between one dependent result and one executable result/configuration. -/
inductive StepRel (refinement : ExecRefinement V) (init : A.InitState) :
    (input : List G.Token) → StepResult (NatStream G.Token) init →
      Exec.Result V ⊕ (Exec.Stack V × List (Nat × V)) → Prop
  | fail (input : List G.Token) (state : AState) (token : G.Token) :
      StepRel refinement init input (.Fail state token)
        (.inl (.reject (refinement.stateIndex state) (refinement.terminalIndex (G.tokenTerm token))))
  | accept (input : List G.Token) (value : G.semT (.NT (A.startNt init)))
      (stream : NatStream G.Token) :
      StepRel refinement init input (.Accept value stream)
        (.inl (.ok (refinement.encodeValue (.NT (A.startNt init)) value)))
  | same (input : List G.Token) (stack : Runtime.Stack) :
      StepRel refinement init input (.Progress stack (listStream refinement input))
        (.inr (eraseStack refinement stack, input.map refinement.decode))
  | shift (input : List G.Token) (stack : Runtime.Stack) :
      StepRel refinement init input (.Progress stack (listStream refinement (input.drop 1)))
        (.inr (eraseStack refinement stack, (input.drop 1).map refinement.decode))
  | error (input : List G.Token) (message : String) :
      StepRel refinement init input (.Err message) (.inl (.err message))

private def liftReduction (refinement : ExecRefinement V) (input : List G.Token) :
    Exec.Result V ⊕ Exec.Stack V → Exec.Result V ⊕ (Exec.Stack V × List (Nat × V))
  | .inl result => .inl result
  | .inr stack => .inr (stack, input.map refinement.decode)

private theorem reduceStep_preserves_stream (init : A.InitState)
    (stack : Runtime.Stack) (production : G.Production) (stream : NatStream G.Token) :
    match Runtime.reduceStep init stack production stream with
    | .Progress _ next => next = stream
    | .Accept _ next => next = stream
    | _ => True := by
  unfold Runtime.reduceStep
  cases hpop : Runtime.pop (G.prodRhsRev production) stack (G.prodAction production) with
  | none => simp
  | some popped =>
      obtain ⟨rest, value⟩ := popped
      simp only
      cases hgoto : A.gotoTable (stateOfStack init rest) (G.prodLhs production) with
      | some target => simp only
      | none =>
          simp only
          cases rest with
          | nil =>
              by_cases start : G.prodLhs production = A.startNt init
              · simp [start]
              · simp [start]
          | cons _ _ => simp only

private theorem reduction_related (refinement : ExecRefinement V)
    (init : A.InitState) (stack : Runtime.Stack) (input : List G.Token)
    (production : G.Production) (invariant : StackInvariant init stack)
    (valid : ValidForReduce (stateOfStack init stack) production) :
    StepRel refinement init input
      (Runtime.reduceStep init stack production (listStream refinement input))
      (liftReduction refinement input
        (Exec.reduce refinement.table (refinement.productionIndex production)
          (eraseStack refinement stack))) := by
  have agreement := reduce_agrees refinement init stack input production invariant valid
  rw [agreement]
  have streamAgreement := reduceStep_preserves_stream init stack production
    (listStream refinement input)
  cases result : Runtime.reduceStep init stack production (listStream refinement input) with
  | Fail state token =>
      simp only [eraseReductionResult, liftReduction]
      exact .fail input state token
  | Accept value stream =>
      simp only [eraseReductionResult, liftReduction]
      exact .accept input value stream
  | Progress next stream =>
      rw [result] at streamAgreement
      subst stream
      simp only [eraseReductionResult, liftReduction]
      exact .same input next
  | Err message =>
      simp only [eraseReductionResult, liftReduction]
      exact .error input message

private theorem listStream_head (refinement : ExecRefinement V) (input : List G.Token) :
    TokenStream.head (listStream refinement input) = input.getD 0 refinement.eof := by
  rfl

private theorem listStream_tail (refinement : ExecRefinement V) (input : List G.Token) :
    TokenStream.tail (listStream refinement input) = listStream refinement (input.drop 1) := by
  funext index
  cases input <;> rfl

private theorem decoded_head (refinement : ExecRefinement V) (input : List G.Token) :
    (input.map refinement.decode).getD 0 refinement.table.eof =
      (refinement.terminalIndex (G.tokenTerm (input.getD 0 refinement.eof)),
        refinement.encodeValue (.T (G.tokenTerm (input.getD 0 refinement.eof)))
          (G.tokenSem (input.getD 0 refinement.eof))) := by
  cases input with
  | nil =>
      rw [refinement.eof_agrees]
      change refinement.decode refinement.eof = _
      exact refinement.decode_agrees refinement.eof
  | cons token rest => exact refinement.decode_agrees token

private theorem decoded_tail (refinement : ExecRefinement V) (input : List G.Token) :
    (input.map refinement.decode).drop 1 = (input.drop 1).map refinement.decode := by
  cases input <;> rfl

/-- One executable parser step simulates the dependent step on an EOF-padded finite list. -/
theorem step_refines (refinement : ExecRefinement V) (hSafe : Safe) (init : A.InitState)
    (stack : Runtime.Stack) (input : List G.Token) (invariant : StackInvariant init stack) :
    StepRel refinement init input
      (Runtime.step init stack (listStream refinement input))
      (Exec.step refinement.table (eraseStack refinement stack) (input.map refinement.decode)) := by
  let current := stateOfStack init stack
  have top := top_state_agrees refinement init stack
  cases actionEq : A.actionTable current with
  | DefaultReduce production =>
      have defaultEq := refinement.default_agrees current
      rw [actionEq] at defaultEq
      have valid := hSafe.2.2.2.2 current
      rw [actionEq] at valid
      unfold Runtime.step Exec.step
      rw [show stateOfStack init stack = current from rfl, actionEq, top]
      simp only
      rw [defaultEq]
      simp only
      have related := reduction_related refinement init stack input production invariant valid
      unfold liftReduction at related
      cases reduction : Exec.reduce refinement.table (refinement.productionIndex production)
          (eraseStack refinement stack) with
      | inl result =>
          rw [reduction] at related
          simp only at related ⊢
          exact related
      | inr next =>
          rw [reduction] at related
          simp only at related ⊢
          exact related
  | Lookahead actions =>
      have defaultEq := refinement.default_agrees current
      rw [actionEq] at defaultEq
      let token := input.getD 0 refinement.eof
      have executableAction := refinement.lookahead_agrees current actions actionEq (G.tokenTerm token)
      have headEq := decoded_head refinement input
      cases lookEq : actions (G.tokenTerm token) with
      | Shift target equality =>
          have encoded := encode_cast refinement equality (G.tokenSem token)
          unfold Runtime.step Exec.step
          rw [show stateOfStack init stack = current from rfl, actionEq,
            listStream_head, top]
          simp only
          rw [defaultEq, headEq, executableAction]
          rw [lookEq]
          rw [listStream_tail, decoded_tail]
          have related := StepRel.shift (refinement := refinement) (init := init) input
            (⟨target, castSem equality (G.tokenSem token)⟩ :: stack)
          simp only [eraseStack] at related
          rw [encoded] at related
          exact related
      | Reduce production =>
          have valid := hSafe.2.2.2.2 current
          rw [actionEq] at valid
          have validProduction := valid (G.tokenTerm token)
          rw [lookEq] at validProduction
          unfold Runtime.step Exec.step
          rw [show stateOfStack init stack = current from rfl, actionEq,
            listStream_head, top]
          simp only
          rw [defaultEq, headEq, executableAction]
          rw [lookEq]
          simp only
          have related := reduction_related refinement init stack input production invariant
            validProduction
          unfold liftReduction at related
          cases reduction : Exec.reduce refinement.table (refinement.productionIndex production)
              (eraseStack refinement stack) with
          | inl result =>
              rw [reduction] at related
              simp only at related ⊢
              exact related
          | inr next =>
              rw [reduction] at related
              simp only at related ⊢
              exact related
      | Fail =>
          unfold Runtime.step Exec.step
          rw [show stateOfStack init stack = current from rfl, actionEq,
            listStream_head, top]
          simp only
          rw [defaultEq, headEq, executableAction]
          rw [lookEq]
          exact .fail input current token

/-- Relation used after iteration has consumed an unknown finite prefix. -/
inductive FixRel (refinement : ExecRefinement V) (init : A.InitState) :
    StepResult (NatStream G.Token) init →
      Exec.Result V ⊕ (Exec.Stack V × List (Nat × V)) → Prop
  | fail (state : AState) (token : G.Token) :
      FixRel refinement init (.Fail state token)
        (.inl (.reject (refinement.stateIndex state) (refinement.terminalIndex (G.tokenTerm token))))
  | accept (value : G.semT (.NT (A.startNt init))) (stream : NatStream G.Token) :
      FixRel refinement init (.Accept value stream)
        (.inl (.ok (refinement.encodeValue (.NT (A.startNt init)) value)))
  | progress (input : List G.Token) (stack : Runtime.Stack) :
      FixRel refinement init (.Progress stack (listStream refinement input))
        (.inr (eraseStack refinement stack, input.map refinement.decode))
  | error (message : String) :
      FixRel refinement init (.Err message) (.inl (.err message))

private theorem fixRel_of_stepRel (refinement : ExecRefinement V) (init : A.InitState)
    {input : List G.Token} {dependent executable}
    (related : StepRel refinement init input dependent executable) :
    FixRel refinement init dependent executable := by
  cases related with
  | fail state token => exact .fail state token
  | accept value stream => exact .accept value stream
  | same stack => exact .progress input stack
  | shift stack => exact .progress (input.drop 1) stack
  | error message => exact .error message

/-- Matching logarithmic fuel preserves the parser configuration relation. -/
theorem parseFix_refines (refinement : ExecRefinement V) (hSafe : Safe) (init : A.InitState) :
    ∀ (logN : Nat) (stack : Runtime.Stack) (input : List G.Token),
      StackInvariant init stack →
      FixRel refinement init
        (Runtime.parseFix init stack (listStream refinement input) logN)
        (Exec.parseFix refinement.table (eraseStack refinement stack) (input.map refinement.decode) logN) := by
  intro logN
  induction logN with
  | zero =>
      intro stack input invariant
      exact fixRel_of_stepRel refinement init (step_refines refinement hSafe init stack input invariant)
  | succ logN ih =>
      intro stack input invariant
      have first := ih stack input invariant
      have firstSafe := parseFix_safe hSafe init logN stack (listStream refinement input) invariant
      generalize hDep : Runtime.parseFix init stack (listStream refinement input) logN = dep
        at first firstSafe ⊢
      generalize hExec : Exec.parseFix refinement.table (eraseStack refinement stack)
        (input.map refinement.decode) logN = exec at first ⊢
      cases first with
      | fail state token =>
          simp only [Runtime.parseFix, Exec.parseFix, hDep, hExec]
          exact .fail state token
      | accept value stream =>
          simp only [Runtime.parseFix, Exec.parseFix, hDep, hExec]
          exact .accept value stream
      | error message =>
          simp only [Runtime.parseFix, Exec.parseFix, hDep, hExec]
          exact .error message
      | progress suffix next =>
          have nextInvariant : StackInvariant init next := by
            simpa only [StepResultInvariant] using firstSafe
          simpa only [Runtime.parseFix, Exec.parseFix, hDep, hExec] using
            ih next suffix nextInvariant

/-- Relation between complete dependent and executable parser results. -/
inductive ResultRel (refinement : ExecRefinement V) (init : A.InitState) :
    ParseResult (NatStream G.Token) init → Exec.Result V → Prop
  | fail (state : AState) (token : G.Token) :
      ResultRel refinement init (.Fail state token)
        (.reject (refinement.stateIndex state) (refinement.terminalIndex (G.tokenTerm token)))
  | parsed (value : G.semT (.NT (A.startNt init))) (stream : NatStream G.Token) :
      ResultRel refinement init (.Parsed value stream)
        (.ok (refinement.encodeValue (.NT (A.startNt init)) value))
  | timeout : ResultRel refinement init .Timeout .timeout
  | error (message : String) : ResultRel refinement init (.Err message) (.err message)

/-- The executable runner refines the dependent parser at the same logarithmic fuel. -/
theorem run_refines (refinement : ExecRefinement V) (hSafe : Safe) (init : A.InitState)
    (input : List G.Token) (logN : Nat) :
    ResultRel refinement init
      (Runtime.parse init (listStream refinement input) logN)
      (Exec.run refinement.table (input.map refinement.decode) logN) := by
  have related := parseFix_refines refinement hSafe init logN [] input (stackInvariant_nil init)
  simp only [eraseStack] at related
  unfold Runtime.parse Exec.run
  generalize hDep : Runtime.parseFix init [] (listStream refinement input) logN = dep
    at related ⊢
  generalize hExec : Exec.parseFix refinement.table [] (input.map refinement.decode) logN = exec
    at related ⊢
  cases related with
  | fail state token => exact .fail state token
  | accept value stream => exact .parsed value stream
  | progress suffix stack => exact .timeout
  | error message => exact .error message

end Runtime.Refinement
