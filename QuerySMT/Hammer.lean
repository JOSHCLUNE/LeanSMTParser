import QuerySMT
import PremiseSelection

open Lean Meta Parser Elab Tactic Auto Duper QuerySMT Syntax

initialize Lean.registerTraceClass `hammer.debug

namespace Hammer

-- An option to specify the external prover that `hammer` uses
declare_syntax_cat Hammer.solverOption (behavior := symbol)
syntax "zipperposition" : Hammer.solverOption
syntax "cvc5" : Hammer.solverOption

-- An option to specify the set of facts targeted by the preprocessing `simp` call
declare_syntax_cat Hammer.simpTarget (behavior := symbol)
syntax "target" : Hammer.simpTarget -- Corresponds to `simp`
syntax "all" : Hammer.simpTarget -- Corresponds to `simp_all`
syntax "no_target" : Hammer.simpTarget -- Corresponds to skipping the preprocessing `simp` call

inductive Solver where
| zipperposition
| cvc5

inductive SimpTarget where
| target
| all
| no_target

open Solver SimpTarget

def elabSolverOption [Monad m] [MonadError m] (stx : TSyntax `Hammer.solverOption) : m Solver :=
  withRef stx do
    match stx with
    | `(solverOption| zipperposition) => return zipperposition
    | `(solverOption| cvc5) => return cvc5
    | _ => Elab.throwUnsupportedSyntax

def elabSimpTarget [Monad m] [MonadError m] (stx : TSyntax `Hammer.simpTarget) : m SimpTarget :=
  withRef stx do
    match stx with
    | `(simpTarget| target) => return target
    | `(simpTarget| all) => return all
    | `(simpTarget| no_target) => return no_target
    | _ => Elab.throwUnsupportedSyntax

declare_syntax_cat Hammer.configOption (behavior := symbol)
syntax (&"solver" " := " Hammer.solverOption) : Hammer.configOption
syntax (&"goalHypPrefix" " := " strLit) : Hammer.configOption
syntax (&"negGoalLemmaName" " := " strLit) : Hammer.configOption
syntax (&"simpTarget" " := " Hammer.simpTarget) : Hammer.configOption
syntax (&"premiseRetrievalK" " := " numLit) : Hammer.configOption

structure ConfigurationOptions where
  solver : Solver
  goalHypPrefix : String
  negGoalLemmaName : String
  simpTarget : SimpTarget
  premiseRetrievalK : Nat

syntax hammerStar := "*"
syntax (name := hammerCore) "hammerCore"
  (ppSpace "[" ((simpErase <|> simpLemma),*,?)  "]")
  (ppSpace "[" (hammerStar <|> term),* "]")
  (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

syntax (name := hammer) "hammer" (ppSpace "{"Hammer.configOption,*,?"}")? : tactic

macro_rules
| `(tactic| hammerCore [$simpLemmas,*] [$facts,*]) => `(tactic| hammerCore [$simpLemmas,*] [$facts,*] {})
| `(tactic| hammer) => `(tactic| hammer {})

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

def parseConfigOptions (configOptionsStx : TSyntaxArray `Hammer.configOption) : TacticM ConfigurationOptions := do
  let mut solverOpt := none
  let mut goalHypPrefix := ""
  let mut negGoalLemmaName := ""
  let mut simpTargetOpt := none
  let mut premiseRetrievalKOpt := none
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(Hammer.configOption| solver := $solverName:Hammer.solverOption) =>
      if solverOpt.isNone then solverOpt ← elabSolverOption solverName
      else throwError "Erroneous invocation of hammer: The solver option has been specified multiple times"
    | `(Hammer.configOption| goalHypPrefix := $userGoalHypPrefix:str) =>
      if goalHypPrefix.isEmpty then goalHypPrefix := userGoalHypPrefix.getString
      else throwError "Erroneous invocation of hammer: The goalHypPrefix option has been specified multiple times"
    | `(Hammer.configOption| negGoalLemmaName := $userNegGoalLemmaName:str) =>
      if negGoalLemmaName.isEmpty then negGoalLemmaName := userNegGoalLemmaName.getString
      else throwError "Erroneous invocation of hammer: The negGoalLemmaName option has been specified multiple times"
    | `(Hammer.configOption| simpTarget := $simpTarget:Hammer.simpTarget) =>
      if simpTargetOpt.isNone then simpTargetOpt ← elabSimpTarget simpTarget
      else throwError "Erroneous invocation of hammer: The simpMode option has been specified multiple times"
    | `(Hammer.configOption| premiseRetrievalK := $premiseRetrievalK:num) =>
      if premiseRetrievalKOpt.isNone then premiseRetrievalKOpt := some (TSyntax.getNat premiseRetrievalK)
      else throwError "Erroneous invocation of hammer: The premisesRetrievalK option has been specified multiple times"
    | _ => throwUnsupportedSyntax
  -- Set default values for options that were not specified
  let solver :=
    match solverOpt with
    | none => zipperposition
    | some solver => solver
  if goalHypPrefix.isEmpty then goalHypPrefix := "h"
  if negGoalLemmaName.isEmpty then negGoalLemmaName := "negGoal"
  let simpTarget :=
    match simpTargetOpt with
    | none => all
    | some simpTarget => simpTarget
  let premiseRetrievalK :=
    match premiseRetrievalKOpt with
    | none => 16
    | some premiseRetrievalK => premiseRetrievalK
  return {solver := solver, goalHypPrefix := goalHypPrefix, negGoalLemmaName := negGoalLemmaName, simpTarget := simpTarget, premiseRetrievalK := premiseRetrievalK}

def withSolverOptions [Monad m] [MonadError m] [MonadWithOptions m] (configOptions : ConfigurationOptions) (x : m α) : m α :=
  match configOptions.solver with
  | zipperposition =>
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition"
        let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
        o.set `auto.native true
      ) x
  | cvc5 => throwError "cvc5 hammer support not implemented yet"

def withDuperOptions [Monad m] [MonadError m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions
    (fun o =>
      let o := o.set `duper.ignoreUnusableFacts true
      o.set `auto.mono.ignoreNonQuasiHigherOrder true
    ) x

@[rebind Auto.Native.solverFunc]
def duperNativeSolverFunc (lemmas : Array Lemma) (inhLemmas : Array Lemma) : MetaM Expr := do
  let formulas ← autoLemmasToFormulas lemmas
  let formulas := formulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  trace[hammer.debug] "Formulas passed to Duper after filtering: {formulas.map (fun x => x.1)}"
  Duper.runDuperPortfolioMode formulas .none
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      preprocessing := none,
      includeExpensiveRules := none,
      selFunction := none
    }
    .none

def throwSimpPreprocessingError (e : Exception) : TacticM α :=
  throwError "hammer encountered an error during simp preprocessing. Try calling hammer with the simpTarget option set to no_target. Error: {e.toMessageData}"

def throwTranslationError (e : Exception) : TacticM α :=
  throwError "hammer failed to preprocess facts for translation. Error: {e.toMessageData}"

def throwExternalSolverError (e : Exception) : TacticM α :=
  throwError "hammer successfully translated the problem to TPTP, but the external prover was unable to solve it. Error: {e.toMessageData}"

def throwDuperError (e : Exception) : TacticM α :=
  throwError "hammer successfully translated the problem to TPTP and obtained an unsat core from an external prover, but was unable to reconstruct the proof. Error: {e.toMessageData}"

def throwProofFitError (e : Exception) : TacticM α :=
  throwError "hammer successfully translated the problem and reconstructed an external prover's proof, but encountered an issue in applying said proof. Error: {e.toMessageData}"

/-- A function to determine whether an error thrown by `hammer` was generated by `throwSimpPreprocessingError` -/
def errorIsSimpPreprocessingError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer encountered an error during simp preprocessing. Try calling hammer with the simpTarget option set to no_target.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwTranslationError` -/
def errorIsTranslationError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer failed to preprocess facts for translation.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwExternalSolverError` -/
def errorIsExternalSolverError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer successfully translated the problem to TPTP, but the external prover was unable to solve it.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwDuperError` -/
def errorIsDuperSolverError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer successfully translated the problem to TPTP and obtained an unsat core from an external prover, but was unable to reconstruct the proof.".isPrefixOf eStr

/-- A function to determine whether an error thrown by `hammer` was generated by `throwProofFitError` -/
def errorIsProofFitError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "hammer successfully translated the problem and reconstructed an external prover's proof, but encountered an issue in applying said proof.".isPrefixOf eStr

def runHammerCore (stxRef : Syntax) (simpLemmas : Syntax.TSepArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] ",")
  (facts : TSepArray `term ",") (includeLCtx : Bool) (configOptions : ConfigurationOptions) : TacticM Unit := withMainContext do
  let simpPreprocessingSuggestion ←
    tryCatchRuntimeEx (do
      match configOptions.simpTarget with
      | no_target => pure #[] -- No simp preprocessing
      | target =>
        let goalsBeforeSimpCall ← getGoals
        evalTactic (← `(tactic| simp [$simpLemmas,*]))
        let goalsAfterSimpCall ← getGoals
        if goalsBeforeSimpCall != goalsAfterSimpCall then -- Only add `simp` call to suggestion if it affected the goal state
          pure #[(← `(tactic| simp [$simpLemmas,*]))]
        else
          pure #[]
      | all =>
        let goalsBeforeSimpCall ← getGoals
        evalTactic (← `(tactic| simp_all [$simpLemmas,*]))
        let goalsAfterSimpCall ← getGoals
        if goalsBeforeSimpCall != goalsAfterSimpCall then -- Only add `simp_all` call to suggestion if it affected the goal state
          pure #[(← `(tactic| simp_all [$simpLemmas,*]))]
        else
          pure #[]
      )
      (fun e => do
        let eStr ← e.toMessageData.toString
        if eStr == "simp made no progress" || eStr == "simp_all made no progress" then pure #[]
        else throwSimpPreprocessingError e
      )

  if (← getUnsolvedGoals).isEmpty then
    let tacticSeq ← `(tacticSeq| $simpPreprocessingSuggestion*)
    addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
    return -- The simp preprocessing call is sufficient to close all goals, so no more work needs to be done

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
    | throwError "evalHammer :: Unexpected result after applying Classical.byContradiction"
  let (_, absurd) ← MVarId.intro nngoal (.str .anonymous configOptions.negGoalLemmaName)
  replaceMainGoal [absurd]
  withMainContext do
    let lctxAfterIntros ← getLCtx
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    -- **NOTE** We collect `formulas` using `Duper.collectAssumptions` rather than `Auto.collectAllLemmas` because `Auto.collectAllLemmas`
    -- does not currently support a mode where unusable facts are ignored.
    let formulas ← withDuperOptions $ collectAssumptions facts includeLCtx goalDecls
    withSolverOptions configOptions do
      let lemmas ← formulasToAutoLemmas formulas
      -- Calling `Auto.unfoldConstAndPreprocessLemma` is an essential step for the monomorphization procedure
      let lemmas ←
        tryCatchRuntimeEx
          (lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[]))
          throwTranslationError
      let inhFacts ←
        tryCatchRuntimeEx
          Auto.Inhabitation.getInhFactsFromLCtx
          throwTranslationError
      let solverHints ←
        tryCatchRuntimeEx (do
          trace[hammer.debug] "Lemmas passed to runAutoGetHints {lemmas}"
          trace[hammer.debug] "inhFacts passed to runAutoGetHints {inhFacts}"
          runAutoGetHints lemmas inhFacts
          )
          (fun e => do
            if (← e.toMessageData.toString) ==  "runAutoGetHints :: External TPTP solver unable to solve the goal" then
              throwExternalSolverError e
            else
              throwTranslationError e
          )
      match configOptions.solver with
      | zipperposition =>
        let mut tacticsArr := simpPreprocessingSuggestion -- The array of tactics that will be suggested to the user
        let unsatCoreDerivLeafStrings := solverHints.1
        trace[hammer.debug] "unsatCoreDerivLeafStrings: {unsatCoreDerivLeafStrings}"
        let duperConfigOptions :=
          { portfolioMode := true, portfolioInstance := none, inhabitationReasoning := none, includeExpensiveRules := none,
            preprocessing := some PreprocessingOption.FullPreprocessing, selFunction := none }
        let (_, _, coreLctxLemmas, coreUserInputFacts, duperProof) ←
          tryCatchRuntimeEx
            (getDuperCoreSMTLemmas unsatCoreDerivLeafStrings facts goalDecls #[] [] includeLCtx (fun _ => false) duperConfigOptions)
            throwDuperError
        -- Build the `intros ...` tactic with appropriate names
        let mut introsNames := #[] -- Can't just use `introNCoreNames` because `introNCoreNames` uses `_ as a placeholder
        let mut numGoalHyps := 0
        for fvarId in goalBinders do
          let some localDecl := lctxAfterIntros.fvarIdToDecl.find? fvarId
            | throwProofFitError $ ← throwError "Unable to find fvarId {Expr.fvar fvarId} in local context (after intros)"
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
        let coreUserInputFacts := coreUserInputFacts.filter (fun x => !coreLctxLemmaIds.contains x)
        tacticsArr := tacticsArr.push $ ← `(tactic| duper [$(coreLctxLemmaIds ++ coreUserInputFacts),*] {preprocessing := full})
        -- Add tactic sequence suggestion
        let tacticSeq ← `(tacticSeq| $tacticsArr*)
        -- **TODO** Add a warning if anything gets inadvertently shadowed (e.g. by `negGoal` or an introduced goal hypothesis)
        addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
        tryCatchRuntimeEx
          (absurd.assign duperProof)
          throwProofFitError
      | cvc5 => throwError "evalHammer :: cvc5 support not yet implemented"

@[tactic hammerCore]
def evalHammerCore : Tactic
| `(tactic| hammerCore%$stxRef [$simpLemmas,*] [$facts,*] {$configOptions,*}) => do
  let configOptions ← parseConfigOptions configOptions
  let (includeLCtx, facts) := removeHammerStar facts
  runHammerCore stxRef simpLemmas facts includeLCtx configOptions
| _ => throwUnsupportedSyntax

open PremiseSelection in
@[tactic hammer]
def evalHammer : Tactic
| `(tactic| hammer%$stxRef {$configOptions,*}) => withMainContext do
  let goal ← getMainGoal
  let configOptions ← parseConfigOptions configOptions
  let premiseSelectionConfig : PremiseSelection.Config := {
    maxSuggestions := configOptions.premiseRetrievalK,
    caller := `hammer
  }
  -- Get the registered premise selector for premise selection.
  -- If none registered, then use the cloud premise selector by default.
  let selector := premiseSelectorExt.getState (← getEnv)
  let selector := selector.getD Cloud.premiseSelector
  let premises ← selector goal premiseSelectionConfig

  let premises := premises.map (fun p => p.name)
  let premises ← premises.mapM (fun p => return (← `(term| $(mkIdent p))))
  runHammerCore stxRef ∅ premises true configOptions
| _ => throwUnsupportedSyntax

end Hammer
