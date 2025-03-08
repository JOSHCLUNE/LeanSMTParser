import Duper
-- import QuerySMT.UtilTactics -- Removing this dependency so I can enable precompileModules
import QuerySMT.SkolemizeAll

open Lean Meta Auto Elab Tactic Parser Tactic Duper

initialize Lean.registerTraceClass `querySMT.debug

register_option querySMT.ignoreHints : Bool := {
  defValue := false
  descr := "Ignores all hints provided from cvc5 and just uses the unsat core"
}

declare_syntax_cat QuerySMT.configOption (behavior := symbol)

namespace QuerySMT

def getIgnoreHints (opts : Options) : Bool :=
  querySMT.ignoreHints.get opts

def getIgnoreHintsM : CoreM Bool := do
  let opts ← getOptions
  return getIgnoreHints opts

syntax (&"lemmaPrefix" " := " strLit) : QuerySMT.configOption
syntax (&"skolemPrefix" " := " strLit) : QuerySMT.configOption
syntax (&"goalHypPrefix" " := " strLit) : QuerySMT.configOption
syntax (&"negGoalLemmaName" " := " strLit) : QuerySMT.configOption

syntax querySMTStar := "*"
syntax (name := querySMT) "querySMT" (ppSpace "[" (querySMTStar <|> term),* "]")? (ppSpace "{"QuerySMT.configOption,*,?"}")? : tactic

def getLemmaPrefixFromConfigOptions (configOptionsStx : TSyntaxArray `QuerySMT.configOption) : Option String := Id.run do
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(configOption| lemmaPrefix := $lemmaPrefixSyntax:str) => return some lemmaPrefixSyntax.getString
    | _ => continue
  return none

def getSkolemPrefixFromConfigOptions (configOptionsStx : TSyntaxArray `QuerySMT.configOption) : Option String := Id.run do
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(configOption| skolemPrefix := $skolemPrefixSyntax:str) => return some skolemPrefixSyntax.getString
    | _ => continue
  return none

def getGoalHypPrefixFromConfigOptions (configOptionsStx : TSyntaxArray `QuerySMT.configOption) : Option String := Id.run do
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(configOption| goalHypPrefix := $goalHypPrefixSyntax:str) => return some goalHypPrefixSyntax.getString
    | _ => continue
  return none

def getNegGoalLemmaNameFromConfigOptions (configOptionsStx : TSyntaxArray `QuerySMT.configOption) : Option String := Id.run do
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(configOption| negGoalLemmaName := $negGoalLemmaNameSyntax:str) => return some negGoalLemmaNameSyntax.getString
    | _ => continue
  return none

def throwSkolemizationError (e : Exception) : TacticM α :=
  throwError "querySMT encountered an error during skolemization. Error: {e.toMessageData}"

def throwTranslationError (e : Exception) : TacticM α :=
  throwError "querySMT encountered an error translating the inital goal to the SMT format. Error: {e.toMessageData}"

def throwSolverError (e : Exception) : TacticM α :=
  throwError "querySMT's external solver was unable to find a proof. Error: {e.toMessageData}"

def throwHintParsingError (e : Exception) : TacticM α :=
  throwError "querySMT encountered an error parsing the hints output by the external solver. Error: {e.toMessageData}"

def throwSelectorConstructionError (e : Exception) : TacticM α :=
  throwError "querySMT encountered an error constructing a datatype's selectors. Error: {e.toMessageData}"

def throwDuperError (e : Exception) : TacticM α :=
  throwError "querySMT encountered an error using Duper to reconstruct the external solver's proof. Error: {e.toMessageData}"

def throwProofFitError (e : Exception) : TacticM α :=
  throwError "querySMT successfully translated the problem and reconstructed an external prover's proof, but encountered an issue in applying said proof. Error: {e.toMessageData}"

def errorIsSkolemizationError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT encountered an error during skolemization.".isPrefixOf eStr

def errorIsTranslationError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT encountered an error translating the inital goal to the SMT format.".isPrefixOf eStr

def errorIsSolverError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT's external solver was unable to find a proof.".isPrefixOf eStr

def errorIsHintParsingError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT encountered an error parsing the hints output by the external solver.".isPrefixOf eStr

def errorIsSelectorConstructionError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT encountered an error constructing a datatype's selectors.".isPrefixOf eStr

def errorIsDuperError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT encountered an error using Duper to reconstruct the external solver's proof.".isPrefixOf eStr

def errorIsProofFitError (e : Exception) : IO Bool := do
  let eStr ← e.toMessageData.toString
  return "querySMT successfully translated the problem and reconstructed an external prover's proof, but encountered an issue in applying said proof.".isPrefixOf eStr

/-- Sets the `auto.smt` options necessary to call `runAutoGetHints` without error -/
def withAutoOptions {m : Type → Type} [MonadWithOptions m] {α : Type} (x : m α) : m α :=
  withOptions
    (fun o =>
      let o := o.set `auto.smt true
      let o := o.set `auto.smt.trust true
      let o := o.set `auto.smt.solver.name "cvc5"
      let o := o.set `auto.smt.dumpHints true
      let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
      o.set `auto.smt.dumpHints.limitedRws true
    ) x

def withDuperOptions [Monad m] [MonadError m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions
    (fun o =>
      let o := o.set `duper.ignoreUnusableFacts true
      o.set `auto.mono.ignoreNonQuasiHigherOrder true
    ) x

macro_rules
| `(tactic| querySMT) => `(tactic| querySMT [*] {}) -- Missing both facts and config options
| `(tactic| querySMT [$facts,*]) => `(tactic| querySMT [$facts,*] {}) -- Mising just config options
| `(tactic| querySMT {$configOptions,*}) => `(tactic| querySMT [*] {$configOptions,*}) -- Missing just facts

/-- Given a Syntax.TSepArray of facts provided by the user (which may include `*` to indicate that `querySMT` should read in the
    full local context) `removeQuerySMTStar` returns the Syntax.TSepArray with `*` removed and a boolean that indicates whether `*`
    was included in the original input. -/
def removeQuerySMTStar (facts : Syntax.TSepArray [`QuerySMT.querySMTStar, `term] ",") : Bool × Syntax.TSepArray `term "," := Id.run do
  let factsArr := facts.elemsAndSeps -- factsArr contains both the elements of facts and separators, ordered like `#[e1, s1, e2, s2, e3]`
  let mut newFactsArr : Array Syntax := #[]
  let mut removedQuerySMTStar := false
  let mut needToRemoveSeparator := false -- If `*` is removed, its comma also needs to be removed to preserve the elemsAndSeps ordering
  for fact in factsArr do
    match fact with
    | `(querySMTStar| *) =>
      removedQuerySMTStar := true
      needToRemoveSeparator := true
    | _ =>
      if needToRemoveSeparator then needToRemoveSeparator := false -- Don't push current separator onto newFactsArr
      else newFactsArr := newFactsArr.push fact
  if removedQuerySMTStar && needToRemoveSeparator then -- This can occur if `*` was the last or only element of facts
    return (removedQuerySMTStar, {elemsAndSeps := newFactsArr.pop}) -- Remove the last extra separator in newFactsArr, if it exists
  else
    return (removedQuerySMTStar, {elemsAndSeps := newFactsArr})

/-- Given `userFacts`, `goalDecls`, `selectorInfos`, and `smtLemmas`, `getDuperCoreSMTLemmas` calls Duper and returns:
    - The SMT lemmas that appear in the final proof
    - The SMT selectors that appear in the final proof (as Strings)
    - The hypotheses from the local context that were included by `unsatCoreDerivLeafStrings` (as FVarIds)
    - The facts from `userInputFacts` passed into `querySMT` or `hammer` that were not from the local context
    - The proof the Duper produces -/
def getDuperCoreSMTLemmas (unsatCoreDerivLeafStrings : Array String) (userFacts : Syntax.TSepArray `term ",") (goalDecls : Array LocalDecl)
  (selectorInfos : Array (String × Expr × Nat × Expr)) (smtLemmas : List Expr) (includeAllLctx : Bool) (alwaysInclude : Term → Bool)
  (duperConfigOptions : Duper.ConfigurationOptions) : TacticM (Array Expr × Array String × Array FVarId × Array Term × Expr) := do
  Core.checkSystem "querySMT :: getDuperCoreSMTLemmas"
  let lctx ← getLCtx
  -- Filter `userFacts` to only include facts that appear in the SMT solver's unsat core (and facts that `alwaysInclude` says to include)
  let userFacts : Array Term := userFacts
  let mut coreUserFacts := #[]
  for factStx in userFacts do
    -- **TODO** Modify `Duper.collectAssumptions` to output a leaf containing `s!"❰{factStx}❱"` so that we only need to check `factStr1`
    let factStr1 := s!"❰{factStx}❱" -- This `factStr` is based on the leaf that `Auto.collectUserLemmas` generates for `fact`
    let factStr2 := s!"false, {factStx}" -- This `factStr` is based on the leaf that `Duper.collectAssumptions` generates for `fact`
    let factStr1InUnsatCore := unsatCoreDerivLeafStrings.contains factStr1
    let factStr2InUnsatCore := unsatCoreDerivLeafStrings.contains factStr2
    if factStr1InUnsatCore || factStr2InUnsatCore || alwaysInclude factStx then
      coreUserFacts := coreUserFacts.push factStx
  -- Build `smtDeclInfos` from `smtLemmas` (after instantiating loose bound variables corresponding to selectors)
  let mut selectorFVars := #[]
  for (selUserName, _, _, _) in selectorInfos do
    match lctx.findFromUserName? (.str .anonymous selUserName) with
    | some decl => selectorFVars := selectorFVars.push (.fvar decl.fvarId)
    | none => throwError "{decl_name%} :: Error in trying to access selector definition for {selUserName}"
  let smtLemmas := smtLemmas.map (fun lem => lem.instantiateRev selectorFVars)
  /- Preprocess `smtLemmas` to zetaReduce let expressions
     We don't need to preprocess `lemmas` because `Auto.collectAllLemmas` already zetaReduces -/
  let smtLemmas ← smtLemmas.mapM (fun lem => Duper.preprocessFact lem)
  let smtDeclInfos : Array (Name × (Array Expr → TacticM Expr)) ← do
    let mut declInfos := #[]
    let mut declCounter := 0
    let baseName := `h
    for lem in smtLemmas do
      let lemName := Name.num baseName declCounter
      let lemConstructor : Array Expr → TacticM Expr := (fun _ => pure lem)
      declInfos := declInfos.push (lemName, lemConstructor)
      declCounter := declCounter + 1
    pure declInfos
  -- Continue with local decls corresponding to `smtDeclInfos`
  withLocalDeclsD smtDeclInfos $ fun xs => do
    -- Build `formulas` to pass into `runDuperPortfolioMode`
    trace[querySMT.debug] "{decl_name%} :: Collecting assumptions. coreUserFacts: {coreUserFacts}"
    let mut formulas := (← collectAssumptions coreUserFacts includeAllLctx goalDecls).toArray
    -- Add selector facts to `formulas`
    for (selName, _selCtor, _argIdx, _selType) in selectorInfos do
      let selFactName := selName ++ "Fact"
      let some selFactDecl := lctx.findFromUserName? (.str .anonymous selFactName)
        | throwError "getDuperCoreSMTLemmas :: Unable to find selector fact {selFactName}"
      formulas := formulas.push (selFactDecl.type, ← mkAppM ``eq_true #[.fvar selFactDecl.fvarId], #[], false, none)
    -- Add `smtLemmas` to `extraFormulas` (to indicate that these should not be added to the set of support)
    let mut extraFormulas := #[]
    let mut lemCounter := 0
    for lem in smtLemmas do
      extraFormulas := extraFormulas.push (lem, ← mkAppM ``eq_true #[xs[lemCounter]!], #[], false, none)
      lemCounter := lemCounter + 1
    -- Try to reconstruct the proof using `runDuperPortfolioMode`
    let prf ←
      try
        Core.checkSystem "querySMT :: runDuperPortfolioMode"
        trace[querySMT.debug] "getDuperCoreSMTLemmas :: Calling runDuperPortfolioMode with formulas: {formulas}"
        runDuperPortfolioMode formulas.toList extraFormulas.toList none duperConfigOptions none
      catch e =>
        throwError m!"getDuperCoreSMTLemmas :: Unable to use hints from external solver to reconstruct proof. " ++
                   m!"Duper threw the following error:\n\n{e.toMessageData}"
    -- Find `smtLemmasInPrf`
    -- **TODO** This procedure does not appear to always work (see Even/Odd example in issues.lean). Look into a better method
    let mut smtLemmasInPrf := #[]
    let mut smtDeclIndex := 0
    for x in xs do
      if prf.containsFVar x.fvarId! then
        trace[querySMT.debug] "{smtLemmas[smtDeclIndex]!} appears in the proof (index: {smtDeclIndex})"
        smtLemmasInPrf := smtLemmasInPrf.push (smtLemmas[smtDeclIndex]!)
      else
        trace[querySMT.debug] "{smtLemmas[smtDeclIndex]!} does not appear in the proof (index: {smtDeclIndex})"
      smtDeclIndex := smtDeclIndex + 1
    -- Find `necessarySelectors`
    let mut necessarySelectors := #[]
    for (selName, _, _, _) in selectorInfos do
      let some selDecl := lctx.findFromUserName? (.str .anonymous selName)
        | throwError "getDuperCoreSMTLemmas :: Unable to find selector {selName}"
      if prf.containsFVar selDecl.fvarId then
        necessarySelectors := necessarySelectors.push selName
    -- Find `lctxFactsInProof`
    let mut lctxFactsInProof := #[]
    for declOpt in lctx.decls do
      match declOpt with
      | none => continue
      | some decl =>
        if xs.contains (.fvar decl.fvarId) then continue -- Don't add SMT lemmas to `lctxFactsInProof`
        if selectorInfos.any (fun (selName, _, _, _) => (.str .anonymous (selName ++ "Fact")) == decl.userName) then continue -- Don't add selector facts to `lctxFactsInProof`
        if (← inferType decl.type).isProp && prf.containsFVar decl.fvarId then
          lctxFactsInProof := lctxFactsInProof.push decl.fvarId
    -- Determine which of the non-lctx facts that were passed into `querySMT`/`hammer` appear in `prf`
    let mut userInputFactsInProof := #[]
    for factStx in userFacts do
      let factName := factStx.raw.getId
      if prf.containsConst (fun n => n == factName) then
        userInputFactsInProof := userInputFactsInProof.push factStx
    pure (smtLemmasInPrf, necessarySelectors, lctxFactsInProof, userInputFactsInProof, prf)

/-- `makeShadowWarning` is to be called if the final tactic suggestion produced by `querySMT` contains a shadowed hypothesis.
    Checks whether `n` has a format that would allow it to be shadowed by one of the free variables generated by `querySMT`
    and uses that information to craft the appropriate warning (which is returned as MessageData) -/
def makeShadowWarning (n : Name) (smtLemmaCount : Nat) (smtLemmaPrefix : String)
  (numGoalHyps : Nat) (goalHypPrefix : String) (negGoalLemmaName : String) (skolemPrefix : String) : MessageData := Id.run do
  -- **TODO** Update makeShadowWarning to also give a more specific error message when selectors shadow something from the local context
  let generalWarning :=
    m!"Warning: The name {n} has been shadowed, which may cause the tactic suggestion to be inaccurate. " ++
    m!"To correct this, we recommend changing the shadowing or shadowed declaration prior to calling querySMT."
  let s := n.toString
  match s.splitOn smtLemmaPrefix with
  | ["", idxStr] =>
    let some idx := idxStr.toNat?
      | pure () -- Do nothing
    if idx < smtLemmaCount then
      let smtLemmaWarning :=
        m!" This can be done by calling querySMT while setting the lemmaPrefix option " ++
        m!"(e.g. querySMT \{lemmaPrefix := \"mySMTLemmaPrefix\"})"
      return generalWarning ++ smtLemmaWarning
  | _ => pure () -- Do nothing
  match s.splitOn goalHypPrefix with
  | ["", idxStr] =>
    let some idx := idxStr.toNat?
      | pure () -- Do nothing
    if idx < numGoalHyps then
      let goalHypWarning :=
        m!" This can be done by calling querySMT while setting the goalHypPrefix option " ++
        m!"(e.g. querySMT \{goalHypPrefix := \"myGoalHypPrefix\"})"
      return generalWarning ++ goalHypWarning
  | _ => pure () -- Do nothing
  match s.splitOn skolemPrefix with
  | ["", idxStr] =>
    if idxStr.isNat then
      let skolemPrefixWarning :=
        m!" This can be done by calling querySMT while setting the skolemPrefix option " ++
        m!"(e.g. querySMT \{skolemPrefix := \"mySkolemPrefix\"})"
      return generalWarning ++ skolemPrefixWarning
  | _ => pure () -- Do nothing
  if s == negGoalLemmaName then
    let negGoalWarning :=
      m!" This can be done by calling querySMT while setting the negGoalLemmaName option " ++
      m!"(e.g. querySMT \{negGoalLemmaName := \"myNegGoalLemmaName\"})"
    return generalWarning ++ negGoalWarning
  return generalWarning

-- **TODO** Experiment with ideal set of additionalFacts once we have a proper evaluation set up. Currently, I am
-- trying to include only additionalFacts that evaluate to unit clauses
def getAdditionalFacts : CoreM (Array Term) := do
  return #[(← `(term| $(mkIdent ``Nat.zero_le))), (← `(term| $(mkIdent ``Int.ofNat_nonneg))),
    (← `(term| $(mkIdent ``ge_iff_le))), (← `(term| $(mkIdent ``gt_iff_lt))),
    (← `(term| $(mkIdent ``lt_iff_not_ge))),
    -- (← `(term| $(mkIdent ``le_iff_lt_or_eq))),
    (← `(term| $(mkIdent ``Int.ofNat_inj))), (← `(term| $(mkIdent ``Int.natAbs_ofNat))),
    -- (← `(term| $(mkIdent ``Int.natAbs_eq))),
    -- (← `(term| $(mkIdent ``Int.natAbs_eq_natAbs_iff))),
    (← `(term| $(mkIdent ``Int.ofNat_le))), (← `(term| $(mkIdent ``Int.ofNat_lt))),
    (← `(term| $(mkIdent ``Int.ofNat_eq_coe))), (← `(term| $(mkIdent ``Int.zero_sub))),
    -- (← `(term| $(mkIdent ``Int.natAbs_of_nonneg))), (← `(term| $(mkIdent ``Int.ofNat_natAbs_of_nonpos))),
    -- (← `(term| $(mkIdent ``Int.nonpos_of_neg_nonneg))), (← `(term| $(mkIdent ``Int.nonneg_of_neg_nonpos))),
    (← `(term| $(mkIdent ``Int.natCast_add))), (← `(term| $(mkIdent ``Int.natCast_mul))),
    (← `(term| $(mkIdent ``Int.natAbs_mul))),
    (← `(term| $(mkIdent ``Int.natCast_one))), (← `(term| $(mkIdent ``Int.natCast_zero))),
    (← `(term| $(mkIdent ``Int.natAbs_zero))), (← `(term| $(mkIdent ``Int.natAbs_one))),
    (← `(term| $(mkIdent ``Int.ofNat_zero))), (← `(term| $(mkIdent ``Int.ofNat_one)))]
    -- (← `(term| $(mkIdent ``Int.mul_assoc))), (← `(term| $(mkIdent ``Int.mul_comm))),
    -- (← `(term| $(mkIdent ``Int.add_assoc))), (← `(term| $(mkIdent ``Int.add_comm))),
    -- (← `(term| $(mkIdent ``Nat.mul_assoc))), (← `(term| $(mkIdent ``Nat.mul_comm))),
    -- (← `(term| $(mkIdent ``Nat.add_assoc))), (← `(term| $(mkIdent ``Nat.add_comm)))

def addAdditionalFacts (facts : Array Term) : CoreM (Array Term) := do
  let mut facts := facts
  for additionalFact in ← getAdditionalFacts do
    facts := facts.push additionalFact
  pure facts

def isAdditionalFact : CoreM (Term → Bool) := do
  let additionalFacts ← getAdditionalFacts
  return additionalFacts.contains

@[tactic querySMT]
def evalQuerySMT : Tactic
| `(querySMT | querySMT%$stxRef [$facts,*] {$configOptions,*}) => withMainContext do
  let (includeLCtx, facts) := removeQuerySMTStar facts
  let lctxBeforeIntros ← getLCtx
  let originalMainGoal ← getMainGoal
  let goalType ← originalMainGoal.getType
  let goalType ← instantiateMVars goalType
  -- If `goalType` has the form `∀ x1 : t1, … ∀ xn : tn, b`, first apply `intros` to put `x1 … xn` in the local context
  let numBinders := getIntrosSize goalType
  let mut introNCoreNames : Array Name := #[]
  let mut numGoalHyps := 0
  let goalHypPrefix :=
    match getGoalHypPrefixFromConfigOptions configOptions with
    | some goalHypPrefix => goalHypPrefix
    | none => "h"
  /- Assuming `goal` has the form `∀ x1 : t1, ∀ x2 : t2, … ∀ xn : tn, b`, `goalPropHyps` is
     an array of size `n` where the mth element in `goalPropHyps` indicates whether the mth forall
     binder has a `Prop` type. This is used to help create `introNCoreNames` which should use existing
     binder names for nonProp arguments and newly created names (based on `goalHypPrefix`) for Prop arguments -/
  let goalPropHyps ← forallTelescope goalType fun xs _ => do xs.mapM (fun x => do pure (← inferType (← inferType x)).isProp)
  for b in goalPropHyps do
    if b then
      introNCoreNames := introNCoreNames.push (.str .anonymous (goalHypPrefix ++ numGoalHyps.repr))
      numGoalHyps := numGoalHyps + 1
    else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
      introNCoreNames := introNCoreNames.push `_ -- `introNCore` will overwrite this with the existing binder name
  let (goalBinders, newGoal) ← introNCore originalMainGoal numBinders introNCoreNames.toList true true
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "querySMT :: Unexpected result after applying Classical.byContradiction"
  let negGoalLemmaName :=
    match getNegGoalLemmaNameFromConfigOptions configOptions with
    | some n => n
    | none => "negGoal"
  let (_, absurd) ← MVarId.intro nngoal (.str .anonymous negGoalLemmaName)
  replaceMainGoal [absurd]
  withMainContext do
    let lctxAfterIntros ← getLCtx
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let goalsBeforeSkolemization ← getGoals
    tryCatchRuntimeEx
      (match getSkolemPrefixFromConfigOptions configOptions with
      | some skolemPrefix => do evalTactic (← `(tactic| skolemizeAll {prefix := $(Syntax.mkStrLit skolemPrefix)}))
      | none => do evalTactic (← `(tactic| skolemizeAll)))
      throwSkolemizationError
    let goalsAfterSkolemization ← getGoals
    withMainContext do -- Use updated main context so that `collectAllLemmas` collects from the appropriate context
      let lctxAfterSkolemization ← getLCtx
      -- **NOTE** We collect `formulas` using `Duper.collectAssumptions` rather than `Auto.collectAllLemmas` because `Auto.collectAllLemmas`
      -- does not currently support a mode where unusable facts are ignored.
      let formulas ← withDuperOptions $ collectAssumptions facts includeLCtx goalDecls
      trace[querySMT.debug] "formulas: {(formulas.map (fun x => x.1))}"
      withAutoOptions do
        let lemmas ← formulasToAutoLemmas formulas (includeInSetOfSupport := true)
        -- Calling `Auto.unfoldConstAndPreprocessLemma` is an essential step for the monomorphization procedure
        let lemmas ←
          tryCatchRuntimeEx
            (do Core.checkSystem "querySMT :: Auto.unfoldConstAndPreprocessLemma"; lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[]))
            throwTranslationError
        let inhFacts ←
          tryCatchRuntimeEx
            (do Core.checkSystem "querySMT :: Auto.Inhabitation.getInhFactsFromLCtx"; Auto.Inhabitation.getInhFactsFromLCtx)
            throwTranslationError
        let SMTHints ←
          tryCatchRuntimeEx (do
            Core.checkSystem "querySMT :: runAutoGetHints"
            trace[querySMT.debug] "Lemmas passed to runAutoGetHints {lemmas}"
            trace[querySMT.debug] "inhFacts passed to runAutoGetHints {inhFacts}"
            runAutoGetHints lemmas inhFacts)
            (fun e => do
              let eStr ← e.toMessageData.toString
              if eStr == "runAutoGetHints :: SMT solver was unable to find a proof" then throwSolverError e
              else if "querySMTForHints :: Encountered error trying to parse SMT solver's hints.".isPrefixOf eStr then throwHintParsingError e
              else throwTranslationError e -- If an error isn't explicitly identified as a solver or parsing error, interpret it as a translation error
            )
        let (unsatCoreDerivLeafStrings, selectorInfos, allSMTLemmas) := SMTHints
        let (preprocessFacts, theoryLemmas, _instantiations, computationLemmas, polynomialLemmas, rewriteFacts) := allSMTLemmas
        let smtLemmas :=
          if ← getIgnoreHintsM then
            []
          else
            preprocessFacts ++ theoryLemmas ++ computationLemmas ++ polynomialLemmas ++ -- instantiations are intentionally ignored
              (rewriteFacts.foldl (fun acc rwFacts => acc ++ rwFacts) [])
        tryCatchRuntimeEx
          (for (selName, selCtor, argIdx, selType) in selectorInfos do
            Core.checkSystem "querySMT :: buildSelectors"
            let selFactName := selName ++ "Fact"
            let selector ← buildSelector selCtor argIdx
            let selectorStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selector
            let selectorFact ← buildSelectorFact selName selCtor selType argIdx
            let selectorFactStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selectorFact
            let existsIntroStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab (mkConst ``Exists.intro)
            evalTactic $ -- Eval to add selector and its corresponding fact to lctx
              ← `(tactic|
                  obtain ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                    apply $existsIntroStx:term $selectorStx:term
                    intros
                    rfl
                )
          )
          throwSelectorConstructionError
        withMainContext do -- Use updated main context so that newly added selectors are accessible
          trace[querySMT.debug] "Number of lemmas before filter: {smtLemmas.length}"
          let duperConfigOptions :=
            { portfolioMode := true, portfolioInstance := none, inhabitationReasoning := none,
              preprocessing := none, includeExpensiveRules := none, selFunction := none }
          let (smtLemmas, necessarySelectors, coreLctxLemmas, coreUserProvidedLemmas, _) ←
            tryCatchRuntimeEx
              (getDuperCoreSMTLemmas unsatCoreDerivLeafStrings (← addAdditionalFacts facts) goalDecls selectorInfos smtLemmas includeLCtx (← isAdditionalFact) duperConfigOptions)
              throwDuperError
          trace[querySMT.debug] "Number of lemmas after filter: {smtLemmas.size}"
          let smtLemmasStx ← smtLemmas.mapM
            (fun lemExp => withOptions ppOptionsSetting $ PrettyPrinter.delab lemExp)
          let mut tacticsArr := #[] -- The array of tactics that will be suggested to the user
          -- Build the `intros ...` tactic with appropriate names
          let mut introsNames := #[] -- Can't just use `introNCoreNames` because `introNCoreNames` uses `_ as a placeholder
          let mut numGoalHyps := 0
          for fvarId in goalBinders do
            -- Use `lctxAfterIntros` instead of `lctxAfterSkolemization` because `goalBinders` was generated prior to skolemization
            let localDecl := lctxAfterIntros.fvarIdToDecl.find! fvarId
            let ty := localDecl.type
            if (← inferType ty).isProp then
              introsNames := introsNames.push (.str .anonymous (goalHypPrefix ++ numGoalHyps.repr))
              numGoalHyps := numGoalHyps + 1
            else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
              introsNames := introsNames.push $ Name.eraseMacroScopes localDecl.userName
          let ids : TSyntaxArray [`ident, `Lean.Parser.Term.hole] := introsNames.map (fun n => mkIdent n)
          if ids.size > 0 then
            tacticsArr := tacticsArr.push $ ← `(tactic| intros $ids*)
          -- Add `apply Classical.byContradiction` so that SMT lemmas can depend on the negated goal
          let byContradictionConst : TSyntax `term ← PrettyPrinter.delab $ mkConst ``Classical.byContradiction
          tacticsArr := tacticsArr.push $ ← `(tactic| apply $byContradictionConst)
          -- Introduce the negated hypothesis (again, so that SMT lemmas can depend on the negated goal)
          tacticsArr := tacticsArr.push $ ← `(tactic| intro $(mkIdent (.str .anonymous negGoalLemmaName)):term)
          -- Add `skolemizeAll` tactic iff there is something to skolemize
          if goalsBeforeSkolemization != goalsAfterSkolemization then
            match getSkolemPrefixFromConfigOptions configOptions with
            | some skolemPrefix => tacticsArr := tacticsArr.push $ ← `(tactic| skolemizeAll {prefix := $(Syntax.mkStrLit skolemPrefix)})
            | none => tacticsArr := tacticsArr.push $ ← `(tactic| skolemizeAll)
          -- Create each of the necessary selectors
          for (selName, selCtor, argIdx, selType) in selectorInfos do
            if necessarySelectors.contains selName then
              let selFactName := selName ++ "Fact"
              let selector ← buildSelector selCtor argIdx
              let selectorStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selector
              let selectorFact ← buildSelectorFact selName selCtor selType argIdx
              let selectorFactStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selectorFact
              let existsIntroStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab (mkConst ``Exists.intro)
              tacticsArr := tacticsArr.push $
                ← `(tactic|
                    obtain ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                      apply $existsIntroStx:term $selectorStx:term
                      intros
                      rfl
                  )
          -- Create each of the SMT lemmas
          let mut smtLemmaCount := 0
          let smtLemmaPrefix :=
            match getLemmaPrefixFromConfigOptions configOptions with
            | some lemmaPrefix => lemmaPrefix
            | none => "smtLemma"
          for smtLemmaStx in smtLemmasStx do
            let lemmaName := smtLemmaPrefix ++ smtLemmaCount.repr
            -- tacticsArr := tacticsArr.push $ ← `(tactic| have $(mkIdent (.str .anonymous lemmaName)) : $smtLemmaStx := by proveSMTLemma)
            tacticsArr := tacticsArr.push $ ← `(tactic| have $(mkIdent (.str .anonymous lemmaName)) : $smtLemmaStx := by sorry)
            smtLemmaCount := smtLemmaCount + 1
          -- Build a Duper call using each coreLctxLemma, necessary selector fact, and necessary SMT lemma
          let coreLctxLemmaIds ← coreLctxLemmas.mapM
            (fun lemFVarId => withOptions ppOptionsSetting $ PrettyPrinter.delab (.fvar lemFVarId))
          let mut smtLemmaIds : Array Term := #[]
          for i in [:smtLemmaCount] do
            let lemmaName := smtLemmaPrefix ++ i.repr
            smtLemmaIds := smtLemmaIds.push $ mkIdent (.str .anonymous lemmaName)
          let mut necessarySelectorFactIds : Array Term := #[]
          for necessarySelectorName in necessarySelectors do
            let necessarySelectorFactName := necessarySelectorName ++ "Fact"
            necessarySelectorFactIds := necessarySelectorFactIds.push $ mkIdent (.str .anonymous necessarySelectorFactName)
          let coreUserProvidedLemmas := coreUserProvidedLemmas.filter (fun x => !coreLctxLemmaIds.contains x)
          tacticsArr := tacticsArr.push $ ← `(tactic| duper [$(coreLctxLemmaIds ++ coreUserProvidedLemmas ++ necessarySelectorFactIds),*] [$(smtLemmaIds),*])
          let tacticSeq ← `(tacticSeq| $tacticsArr*)
          -- Check if any of the ids in `coreLctxLemmaIds` are shadowed. If they are, print a warning that the tactic suggestion may fail
          for coreLctxLemmaFVarId in coreLctxLemmas do
            match lctxAfterSkolemization.find? coreLctxLemmaFVarId with
            | some decl1 =>
              match lctxAfterSkolemization.findFromUserName? decl1.userName with
              | some decl2 =>
                if decl1.fvarId != decl2.fvarId then -- `decl1` is shadowed by `decl2`
                  let skolemPrefix :=
                    match getSkolemPrefixFromConfigOptions configOptions with
                    | some skolemPrefix => skolemPrefix
                    | none => "sk"
                  let warning := makeShadowWarning decl1.userName smtLemmaCount smtLemmaPrefix numGoalHyps goalHypPrefix negGoalLemmaName skolemPrefix
                  logWarning warning
                else if let ["", idxStr] := decl1.userName.toString.splitOn smtLemmaPrefix then -- Check whether `decl1.userName` will be shadowed by an SMT lemma
                  match idxStr.toNat? with
                  | some idx =>
                    if idx < smtLemmaCount then -- `decl1.userName` will be shadowed by an SMT lemma
                      let skolemPrefix :=
                        match getSkolemPrefixFromConfigOptions configOptions with
                        | some skolemPrefix => skolemPrefix
                        | none => "sk"
                      let warning := makeShadowWarning decl1.userName smtLemmaCount smtLemmaPrefix numGoalHyps goalHypPrefix negGoalLemmaName skolemPrefix
                      logWarning warning
                  | none => continue
              | none => throwError "querySMT :: Unable to find a necessary fact in the local context"
            | none => throwError "querySMT :: Unable to find a necessary fact in the local context"
          -- Create the suggestion
          addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
          let proof ← mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
          let newAbsurd ← getMainGoal -- Main goal changed by `skolemizeAll` and selector creation
          tryCatchRuntimeEx
            (newAbsurd.assign proof)
            throwProofFitError
| _ => throwUnsupportedSyntax

end QuerySMT
