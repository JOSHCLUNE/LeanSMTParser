import QuerySMT

open Lean Meta Parser Elab Tactic Auto Duper QuerySMT

initialize Lean.registerTraceClass `hammer.debug

namespace Hammer

declare_syntax_cat Hammer.solverOption (behavior := symbol)
syntax "zipperposition" : Hammer.solverOption
syntax "cvc5" : Hammer.solverOption

def elabSolverOption [Monad m] [MonadError m] (stx : TSyntax `Hammer.solverOption) : m String :=
  withRef stx do
    match stx with
    | `(solverOption| zipperposition) => return "zipperposition"
    | `(solverOption| cvc5) => return "cvc5"
    | _ => Elab.throwUnsupportedSyntax

declare_syntax_cat Hammer.configOption (behavior := symbol)
syntax (&"solver" " := " Hammer.solverOption) : Hammer.configOption
syntax (&"goalHypPrefix" " := " strLit) : Hammer.configOption
syntax (&"negGoalLemmaName" " := " strLit) : Hammer.configOption

structure ConfigurationOptions where
  solver : String
  goalHypPrefix : String
  negGoalLemmaName : String

syntax hammerStar := "*"
syntax (name := hammer) "hammer" (ppSpace "[" (hammerStar <|> term),* "]")? (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

macro_rules
| `(tactic| hammer) => `(tactic| hammer [] {}) -- Missing both facts and config options
| `(tactic| hammer [$facts,*]) => `(tactic| hammer [$facts,*] {}) -- Mising just config options
| `(tactic| hammer {$configOptions,*}) => `(tactic| hammer [] {$configOptions,*}) -- Missing just facts

/-- Given a Syntax.TSepArray of facts provided by the user (which may include `*` to indicate that hammer should read in the
    full local context) `removeHammerStar` returns the Syntax.TSepArray with `*` removed and a boolean that indicates whether `*`
    was included in the original input. -/
def removeHammerStar (facts : Syntax.TSepArray [`Hammer.hammerStar, `term] ",") : Bool × Syntax.TSepArray `term "," := Id.run do
  let factsArr := facts.elemsAndSeps -- factsArr contains both the elements of facts and separators, ordered like `#[e1, s1, e2, s2, e3]`
  let mut newFactsArr : Array Syntax := #[]
  let mut removedHammerStar := false
  let mut needToRemoveSeparator := false -- If `*` is removed, its comma also needs to be removed to preserve the elemsAndSeps ordering
  for fact in factsArr do
    match fact with
    | `(hammerStar| *) =>
      removedHammerStar := true
      needToRemoveSeparator := true
    | _ =>
      if needToRemoveSeparator then needToRemoveSeparator := false -- Don't push current separator onto newFactsArr
      else newFactsArr := newFactsArr.push fact
  if removedHammerStar && needToRemoveSeparator then -- This can occur if `*` was the last or only element of facts
    return (removedHammerStar, {elemsAndSeps := newFactsArr.pop}) -- Remove the last extra separator in newFactsArr, if it exists
  else
    return (removedHammerStar, {elemsAndSeps := newFactsArr})

set_option pp.rawOnError true in
def parseConfigOptions (configOptionsStx : TSyntaxArray `Hammer.configOption) : TacticM ConfigurationOptions := do
  let mut solver := ""
  let mut goalHypPrefix := ""
  let mut negGoalLemmaName := ""
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(Hammer.configOption| solver := $solverName:Hammer.solverOption) =>
      if solver.isEmpty then solver ← elabSolverOption solverName
      else throwError "Erroneous invocation of hammer: The solver option has been specified multiple times"
    | `(Hammer.configOption| goalHypPrefix := $userGoalHypPrefix:str) =>
      if goalHypPrefix.isEmpty then goalHypPrefix := userGoalHypPrefix.getString
      else throwError "Erroneous invocation of hammer: The goalHypPrefix option has been specified multiple times"
    | `(Hammer.configOption| negGoalLemmaName := $userNegGoalLemmaName:str) =>
      if negGoalLemmaName.isEmpty then negGoalLemmaName := userNegGoalLemmaName.getString
      else throwError "Erroneous invocation of hammer: The negGoalLemmaName option has been specified multiple times"
    | _ => throwUnsupportedSyntax
  -- Set default values for options that were not specified
  if solver.isEmpty then solver := "zipperposition"
  if goalHypPrefix.isEmpty then goalHypPrefix := "h"
  if negGoalLemmaName.isEmpty then negGoalLemmaName := "negGoal"
  return {solver := solver, goalHypPrefix := goalHypPrefix, negGoalLemmaName := negGoalLemmaName}

def withSolverOptions [Monad m] [MonadError m] [MonadWithOptions m] (configOptions : ConfigurationOptions) (x : m α) : m α :=
  if configOptions.solver == "zipperposition" then
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition"
        o.set `auto.native true
      ) x
  else if configOptions.solver == "cvc5" then
    throwError "cvc5 hammer support not implemented yet"
  else
    throwError "Hammer solver must be set to either zipperposition or cvc5"

@[rebind Auto.Native.solverFunc]
def duperNativeSolverFunc (lemmas : Array Lemma) : MetaM Expr := do
  let formulas ← autoLemmasToFormulas lemmas
  let formulas := formulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  trace[hammer.debug] "Formulas passed to Duper after filtering: {formulas.map (fun x => x.1)}"
  Duper.runDuperPortfolioMode formulas .none
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      preprocessing := Duper.PreprocessingOption.NoPreprocessing, -- It would be redundant to enable Auto's preprocessing for Auto calls
      includeExpensiveRules := none,
      selFunction := none
    }
    .none

def throwTranslationError (e : Exception) : TacticM α :=
  throwError "hammer failed to preprocess facts for translation. Error: {e.toMessageData}"

def throwExternalSolverError (e : Exception) : TacticM α :=
  throwError "hammer successfully translated the problem to TPTP, but the external prover was unable to solve it. Error: {e.toMessageData}"

def throwDuperError (e : Exception) : TacticM α :=
  throwError "hammer successfully translated the problem to TPTP and obtained an unsat core from an external prover, but was unable to reconstruct the proof. Error: {e.toMessageData}"

def throwProofFitError (e : Exception) : TacticM α :=
  throwError "hammer successfully translated the problem and reconstructed an external prover's proof, but encountered an issue in applying said proof. Error: {e.toMessageData}"

/-- A function to determine whether an error thrown by `hammer` was generated by `throwTranslationError` -/
def hammerErrorIsTranslationError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer failed to preprocess facts for translation.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwExternalSolverError` -/
def hammerErrorIsExternalSolverError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer successfully translated the problem to TPTP, but the external prover was unable to solve it.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwDuperError` -/
def hammerErrorIsDuperSolverError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer successfully translated the problem to TPTP and obtained an unsat core from an external prover, but was unable to reconstruct the proof.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwProofFitError` -/
def hammerErrorIsProofFitError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer successfully translated the problem and reconstructed an external prover's proof, but encountered an issue in applying said proof.".isPrefixOf eStr

@[tactic hammer]
def evalHammer : Tactic
| `(tactic| hammer%$stxRef [$facts,*] {$configOptions,*}) => withMainContext do
  let configOptions ← parseConfigOptions configOptions
  let (factsContainsHammerStar, facts) := removeHammerStar facts
  let lctxBeforeIntros ← getLCtx
  let originalMainGoal ← getMainGoal
  let goalType ← originalMainGoal.getType
  let goalType ← instantiateMVars goalType
  -- If `goalType` has the form `∀ x1 : t1, … ∀ xn : tn, b`, first apply `intros` to put `x1 … xn` in the local context
  let numBinders := getIntrosSize goalType
  let mut introNCoreNames : Array Name := #[]
  let mut numGoalHyps := 0
  /- Assuming `goal` has the form `∀ x1 : t1, ∀ x2 : t2, … ∀ xn : tn, b`, `goalPropHyps` is
     an array of size `n` where the mth element in `goalPropHyps` indicates whether the mth forall
     binder has a `Prop` type. This is used to help create `introNCoreNames` which should use existing
     binder names for nonProp arguments and newly created names (based on `goalHypPrefix`) for Prop arguments -/
  let goalPropHyps ← forallTelescope goalType fun xs _ => do xs.mapM (fun x => do pure (← inferType (← inferType x)).isProp)
  for b in goalPropHyps do
    if b then
      introNCoreNames := introNCoreNames.push (.str .anonymous (configOptions.goalHypPrefix ++ numGoalHyps.repr))
      numGoalHyps := numGoalHyps + 1
    else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
      introNCoreNames := introNCoreNames.push `_ -- `introNCore` will overwrite this with the existing binder name
  let (goalBinders, newGoal) ← introNCore originalMainGoal numBinders introNCoreNames.toList true true
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "querySMT :: Unexpected result after applying Classical.byContradiction"
  let (_, absurd) ← MVarId.intro nngoal (.str .anonymous configOptions.negGoalLemmaName)
  replaceMainGoal [absurd]
  withMainContext do
    let lctxAfterIntros ← getLCtx
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let formulas ← collectAssumptions facts factsContainsHammerStar goalDecls
    withSolverOptions configOptions do
      let lemmas ← formulasToAutoLemmas formulas
      -- Calling Auto.unfoldConstAndPreprocessLemma is an essential step for the monomorphization procedure
      let lemmas ←
        try
          lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[])
        catch e =>
          throwTranslationError e
      let inhFacts ←
        try
          Auto.Inhabitation.getInhFactsFromLCtx
        catch e =>
          throwTranslationError e
      let hints ←
        try
          runAutoGetHints lemmas inhFacts
        catch e =>
          if (← e.toMessageData.toString) ==  "runAutoGetHints :: External TPTP solver unable to solve the goal" then
            throwExternalSolverError e
          else
            throwTranslationError e
      if configOptions.solver == "zipperposition" then
        let mut tacticsArr := #[] -- The array of tactics that will be suggested to the user
        let unsatCoreDerivLeafStrings := hints.1
        let duperConfigOptions := -- We set preprocessing to `NoPreprocessing` because repreprocessing the lemmas would be redundant
          { portfolioMode := true, portfolioInstance := none, inhabitationReasoning := none, includeExpensiveRules := none,
            preprocessing := Duper.PreprocessingOption.NoPreprocessing, selFunction := none }
        let (_, _, coreLctxLemmas, coreUserInputFacts, duperProof) ←
          try
            getDuperCoreSMTLemmas unsatCoreDerivLeafStrings #[] [] lemmas facts duperConfigOptions
          catch e =>
            throwDuperError e
        -- Build the `intros ...` tactic with appropriate names
        let mut introsNames := #[] -- Can't just use `introNCoreNames` because `introNCoreNames` uses `_ as a placeholder
        let mut numGoalHyps := 0
        for fvarId in goalBinders do
          let localDecl := lctxAfterIntros.fvarIdToDecl.find! fvarId
          let ty := localDecl.type
          if (← inferType ty).isProp then
            introsNames := introsNames.push (.str .anonymous (configOptions.goalHypPrefix ++ numGoalHyps.repr))
            numGoalHyps := numGoalHyps + 1
          else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
            introsNames := introsNames.push $ Name.eraseMacroScopes localDecl.userName
        let ids : TSyntaxArray [`ident, `Lean.Parser.Term.hole] := introsNames.map (fun n => mkIdent n)
        if ids.size > 0 then
          tacticsArr := tacticsArr.push $ ← `(tactic| intros $ids*)
        -- Add `apply Classical.byContradiction` so that the unsat core can determine whether the target needs to be included in the call
        let byContradictionConst : TSyntax `term ← PrettyPrinter.delab $ mkConst ``Classical.byContradiction
        tacticsArr := tacticsArr.push $ ← `(tactic| apply $byContradictionConst)
        -- Introduce the negated hypothesis (again, so that the unsat core can determine whether the target needs to be included in the call)
        tacticsArr := tacticsArr.push $ ← `(tactic| intro $(mkIdent (.str .anonymous configOptions.negGoalLemmaName)):term)
        -- Build a Duper call using each coreLctxLemma and each coreUserInputFact
        let coreLctxLemmaIds ← coreLctxLemmas.mapM
          (fun lemFVarId => withOptions ppOptionsSetting $ PrettyPrinter.delab (.fvar lemFVarId))
        tacticsArr := tacticsArr.push $ ← `(tactic| duper [$(coreLctxLemmaIds ++ coreUserInputFacts),*] {preprocessing := full})
        -- Add tactic sequence suggestion
        let tacticSeq ← `(tacticSeq| $tacticsArr*)
        -- **TODO** Add a warning if anything gets inadvertently shadowed (e.g. by `negGoal` or an introduced goal hypothesis)
        addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
        try
          absurd.assign duperProof
        catch e =>
          throwProofFitError e
      else if configOptions.solver == "cvc5" then
        throwError "evalHammer :: cvc5 support not yet implemented"
      else
        throwError "evalHammer :: Unknown solver: {configOptions.solver}"
| _ => throwUnsupportedSyntax

end Hammer
