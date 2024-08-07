import Auto
import Duper
import Mathlib.Tactic
import SMTParser.UtilTactics

open Lean Meta Auto Elab Tactic Parser Tactic

initialize Lean.registerTraceClass `querySMT.debug

namespace QuerySMT

/-- Checks whether the expression `e` can already be proven by `duper` -/
def uselessLemma (e : Expr) : TacticM Bool := do
  withoutModifyingState do
    let goalMVar ← mkFreshExprMVar e
    let goal := goalMVar.mvarId!
    setGoals [goal]
    tryCatch
      (do let _ ← evalTactic (← `(tactic| duper)); pure true)
      (fun _ => pure false)

/-- Checks whether the expression `e` can already be proven by `tauto` -/
def isTautology (e : Expr) : TacticM Bool := do
  withoutModifyingState do
    let goalMVar ← mkFreshExprMVar e
    let goal := goalMVar.mvarId!
    setGoals [goal]
    tryCatch
      (do let _ ← evalTactic (← `(tactic| tauto)); pure true)
      (fun _ => pure false)

declare_syntax_cat QuerySMT.configOption (behavior := symbol)

syntax (&"lemmaPrefix" " := " strLit) : QuerySMT.configOption
syntax (&"skolemPrefix" " := " strLit) : QuerySMT.configOption
syntax (&"goalHypPrefix" " := " strLit) : QuerySMT.configOption
syntax (&"negGoalLemmaName" " := " strLit) : QuerySMT.configOption

syntax (name := querySMT) "querySMT" hints (uord)* (ppSpace "{"QuerySMT.configOption,*,?"}")? : tactic

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

macro_rules
| `(tactic| querySMT) => `(tactic| querySMT {})

/-- Given `selectorInfos` and `smtLemmas` output by the SMT solver, and `lemmas` which is output by
    `Auto.collectAllLemmas`, `getDuperCoreSMTLemmas` calls Duper and returns:
    - The selectorInfos corresponding to selectors that appear in the final proof
    - The SMT lemmas that appear in the final proof
    - The hypotheses from the local context that were included by `unsatCoreDerivLeafStrings` (as FVarIds) -/
def getDuperCoreSMTLemmas (unsatCoreDerivLeafStrings : Array String) (selectorInfos : Array (String × Expr × Nat × Expr)) (smtLemmas : List Expr)
  (lemmas : Array Auto.Lemma) : TacticM (Array Expr × Array FVarId) := do
  -- Use `unsatCoreDerivLeafStrings` to filter `lemmas` so that it only contains `lemmas` in the SMT solver's unsat core
  let mut coreLemmas := #[]
  for lem in lemmas do
    let lemLeafStrings := lem.deriv.collectLeafStrings
    -- Add `lem` to `coreLemmas` iff all strings in `lemLeafStrings` appear in `unsatCoreDerivLeafStrings`
    let mut allLemLeafStringsInUnsatCore := true
    for lemLeafString in lemLeafStrings do
      if !unsatCoreDerivLeafStrings.contains lemLeafString then
        allLemLeafStringsInUnsatCore := false
        break
    if allLemLeafStringsInUnsatCore then
      coreLemmas := coreLemmas.push lem
  /- **TODO** Incorporate `selectorInfos`
  -- Add selectors to the local context and instantiate `smtLemmas` with them
  for (selName, selCtor, argIdx, selType) in selectorInfos do
    let selTypeStx ← withOptions (fun o => (o.set `pp.analyze true).set `pp.proofs true) $ PrettyPrinter.delab selType
    let selector ← buildSelector selCtor argIdx
    let selectorStx ← withOptions (fun o => (o.set `pp.analyze true).set `pp.proofs true) $ PrettyPrinter.delab selector
    evalTactic $ ← `(tactic| let $(mkIdent (.str .anonymous selName)) : $selTypeStx := $selectorStx) -- Add selector to lctx
  -/
  withMainContext do -- Use updated main context so that newly added selectors are accessible
    /- **TODO** Incorporate `selectorInfos`
    let lctx ← getLCtx
    let mut selectorFVars := #[]
    for (selUserName, _, _, _) in selectorInfos do
      match lctx.findFromUserName? (.str .anonymous selUserName) with
      | some decl => selectorFVars := selectorFVars.push (.fvar decl.fvarId)
      | none => throwError "getDuperCoreSMTLemmas :: Error in trying to access selector definition for {selUserName}"
    let smtLemmas := smtLemmas.map (fun lem => lem.instantiateRev selectorFVars)
    -/
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
    withLocalDeclsD smtDeclInfos $ fun xs => do
      let formulas ← do
        let mut formulas := #[]
        let mut lemCounter := 0
        for lem in smtLemmas do -- Add SMT lemmas
          formulas := formulas.push (lem, ← mkAppM ``eq_true #[xs[lemCounter]!], #[], false)
          lemCounter := lemCounter + 1
        for lem in coreLemmas do -- Add lemmas from ordinary lctx that appear in the SMT solver's unsat core
          let isFromGoal := false -- **TODO**: Figure out how to correctly compute this using `goalDecls`
          formulas := formulas.push (lem.type, ← mkAppM ``eq_true #[lem.proof], lem.params, isFromGoal)
        /- **TODO** Incorporate `selectorInfos`
        for ((selName, selCtor, argIdx, selType), selectorFVar) in selectorInfos.zip selectorFVars do
          /- Add Duper-friendly facts about the selectors (Each selector corresponding to argument `i`
            of constructor `c` returns the `i`th argument of `c` when given `c`) -/
          let selCtorType ← inferType selCtor
          let selCtorFieldTypes := getForallArgumentTypes selCtorType
          let selCtorDeclInfos : Array (Name × (Array Expr → TacticM Expr)) ← do
            let mut declInfos := #[]
            let mut declCounter := 0
            let baseName := `arg
            for selCtorFieldType in selCtorFieldTypes do
              let argName := Name.num baseName declCounter
              let argConstructor : Array Expr → TacticM Expr := (fun _ => pure selCtorFieldType)
              declInfos := declInfos.push (argName, argConstructor)
              declCounter := declCounter + 1
            pure declInfos
          let selectorHyp ←
            withLocalDeclsD selCtorDeclInfos $ fun selCtorArgFVars => do
              let selCtorWithFields ← mkAppM' selCtor selCtorArgFVars
              let selectedArg := selCtorArgFVars[argIdx]!
              mkForallFVars selCtorArgFVars $ ← mkAppM ``Eq #[← mkAppM' selectorFVar #[selCtorWithFields], selectedArg]
          trace[querySMT.debug] "Adding selectorHyp: {selectorHyp} to formulas"
          formulas := formulas.push (selectorHyp, ← mkSorry (← mkAppM ``Eq #[selectorHyp, mkConst ``True]) false, #[], false)
        -/
        pure formulas.toList
      let duperConfigOptions :=
        { portfolioMode := true, portfolioInstance := none, inhabitationReasoning := none,
          preprocessing := none, includeExpensiveRules := none, selFunction := none }
      let prf ← runDuperPortfolioMode formulas none duperConfigOptions none
      let mut smtLemmasInPrf := #[]
      let mut smtDeclIndex := 0
      for x in xs do
        if prf.containsFVar x.fvarId! then
          trace[querySMT.debug] "{smtLemmas[smtDeclIndex]!} appears in the proof (index: {smtDeclIndex})"
          smtLemmasInPrf := smtLemmasInPrf.push (smtLemmas[smtDeclIndex]!)
        smtDeclIndex := smtDeclIndex + 1
      let mut lctxFactsInProof := #[]
      for declOpt in (← getLCtx).decls do
        match declOpt with
        | none => continue
        | some decl =>
          if xs.contains (.fvar decl.fvarId) then continue -- Don't add SMT lemmas to `lctxFactsInProof`
          if (← inferType decl.type).isProp && prf.containsFVar decl.fvarId then
            lctxFactsInProof := lctxFactsInProof.push decl.fvarId
      pure (smtLemmasInPrf, lctxFactsInProof)

/-- Copied from Lean.Meta.Tactic.Intro.lean -/
private partial def getIntrosSize : Expr → Nat
  | .forallE _ _ b _ => getIntrosSize b + 1
  | .letE _ _ _ b _  => getIntrosSize b + 1
  | .mdata _ b       => getIntrosSize b
  | e                =>
    if let some (_, _, _, b) := e.letFun? then getIntrosSize b + 1
    else 0

/-- `makeShadowWarning` is to be called if the final tactic suggestion produced by `querySMT` contains a shadowed hypothesis.
    Checks whether `n` has a format that would allow it to be shadowed by one of the free variables generated by `querySMT`
    and uses that information to craft the appropriate warning (which is returned as MessageData) -/
def makeShadowWarning (n : Name) (smtLemmaCount : Nat) (smtLemmaPrefix : String)
  (numGoalHyps : Nat) (goalHypPrefix : String) (negGoalLemmaName : String) (skolemPrefix : String) : MessageData := Id.run do
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

@[tactic querySMT]
def evalQuerySMT : Tactic
| `(querySMT | querySMT%$stxRef $[$uords]* {$configOptions,*}) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let lctxBeforeIntros ← getLCtx
  let originalMainGoal ← getMainGoal
  let goalType ← originalMainGoal.getType
  let goalType ← instantiateMVars goalType
  let numBinders := getIntrosSize goalType
  let goalForallArgs := getForallArgumentTypes goalType
  let mut introNCoreNames : Array Name := #[]
  let mut numGoalHyps := 0
  let goalHypPrefix :=
    match getGoalHypPrefixFromConfigOptions configOptions with
    | some goalHypPrefix => goalHypPrefix
    | none => "h"
  for goalArg in goalForallArgs do
    if (← inferType goalArg).isProp then
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
    -- **TODO**: Figure out how to properly propagate `goalDecls` in getDuperCoreSMTLemmas
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let goalsBeforeSkolemization ← getGoals
    match getSkolemPrefixFromConfigOptions configOptions with
    | some skolemPrefix => evalTactic (← `(tactic| skolemizeAll {prefix := $(Syntax.mkStrLit skolemPrefix)}))
    | none => evalTactic (← `(tactic| skolemizeAll))
    let goalsAfterSkolemization ← getGoals
    withMainContext do
      let lctxAfterSkolemization ← getLCtx
      let (lemmas, inhFacts) ← collectAllLemmas (← `(hints| [*])) uords #[]
      let SMTHints ← runAutoGetHints lemmas inhFacts
      let (unsatCoreDerivLeafStrings, selectorInfos, allSMTLemmas) := SMTHints
      let (preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts) := allSMTLemmas
      let smtLemmas := preprocessFacts ++ theoryLemmas ++ computationLemmas ++ polynomialLemmas ++ -- instantiations are intentionally ignored
        (rewriteFacts.foldl (fun acc rwFacts => acc ++ rwFacts) [])
      trace[querySMT.debug] "Number of lemmas before filter: {smtLemmas.length}"
      let (smtLemmas, coreLctxLemmas) ← getDuperCoreSMTLemmas unsatCoreDerivLeafStrings selectorInfos smtLemmas lemmas
      trace[querySMT.debug] "Number of lemmas after filter: {smtLemmas.size}"
      -- **TODO** Make syntax for creating selectors and their corresponding facts
      let smtLemmasStx ← smtLemmas.mapM
        (fun lemExp => withOptions (fun o => (o.set `pp.analyze true).set `pp.proofs true) $ PrettyPrinter.delab lemExp)
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
      -- Create each of the SMT lemmas
      let mut smtLemmaCount := 0
      let smtLemmaPrefix :=
        match getLemmaPrefixFromConfigOptions configOptions with
        | some lemmaPrefix => lemmaPrefix
        | none => "smtLemma"
      for smtLemmaStx in smtLemmasStx do
        let lemmaName := smtLemmaPrefix ++ smtLemmaCount.repr
        tacticsArr := tacticsArr.push $ ← `(tactic| have $(mkIdent (.str .anonymous lemmaName)) : $smtLemmaStx := by proveSMTLemma)
        smtLemmaCount := smtLemmaCount + 1
      -- Build a Duper call using each coreLctxLemma and necessary SMT lemma
      -- **TODO** Include relevant selector facts
      let coreLctxLemmaIds ← coreLctxLemmas.mapM
        (fun lemFVarId => withOptions (fun o => (o.set `pp.analyze true).set `pp.proofs true) $ PrettyPrinter.delab (.fvar lemFVarId))
      let mut smtLemmaIds : Array Term := #[]
      for i in [:smtLemmaCount] do
        let lemmaName := smtLemmaPrefix ++ i.repr
        smtLemmaIds := smtLemmaIds.push $ mkIdent (.str .anonymous lemmaName)
      tacticsArr := tacticsArr.push $ ← `(tactic| duper [$(coreLctxLemmaIds ++ smtLemmaIds),*])
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
      newAbsurd.assign proof
| _ => throwUnsupportedSyntax

end QuerySMT
