import Auto
import Duper
import Mathlib.Tactic
import SMTParser.UtilTactics

open Lean Meta Auto Elab Tactic Parser Tactic

initialize Lean.registerTraceClass `querySMT.debug

namespace QuerySMT

inductive filterOptTy where
| noFilter
| tautoFilter
| duperFilter
| duperCore
deriving Inhabited

open filterOptTy DataValue

def filterOptToDataValue : filterOptTy → DataValue
  | noFilter => ofNat 0
  | tautoFilter => ofNat 1
  | duperFilter => ofNat 2
  | duperCore => ofNat 3

def dataValueToFilterOpt : DataValue → Option filterOptTy
  | ofNat 0 => some noFilter
  | ofNat 1 => some tautoFilter
  | ofNat 2 => some duperFilter
  | ofNat 3 => some duperCore
  | _ => none

instance : KVMap.Value filterOptTy := ⟨filterOptToDataValue, dataValueToFilterOpt⟩

register_option querySMT.filterOpt : filterOptTy := {
  defValue := noFilter
  descr := ""
}

def querySMT.getFilterOpt (opts : Options) : filterOptTy :=
  querySMT.filterOpt.get opts

def querySMT.getFilterOptM : CoreM filterOptTy := do
  let opts ← getOptions
  return querySMT.getFilterOpt opts

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

macro_rules
| `(tactic| querySMT) => `(tactic| querySMT {})

/-- Given `smtLemmas` output by the SMT solver and `lemmas` which is output by `Auto.collectAllLemmas`,
    `getDuperCoreSMTLemmas` calls Duper and returns just the SMT lemmas that appear in the final proof -/
def getDuperCoreSMTLemmas (smtLemmas : List Expr) (lemmas : Array Auto.Lemma) : TacticM (List Expr) := do
  -- Preprocess `smtLemmas` to zetaReduce let expressions
  -- Note: We don't need to preprocess `lemmas` because `Auto.collectAllLemmas` already zetaReduces
  let smtLemmas ← smtLemmas.mapM (fun lem => Duper.preprocessFact lem)
  let smtDeclInfos : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
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
      for lem in lemmas do -- Add lemmas from ordinary lctx (including the negated goal)
        let isFromGoal := false -- TODO: Figure out how to correctly compute this using `goalDecls`
        formulas := formulas.push (lem.type, ← mkAppM ``eq_true #[lem.proof], lem.params, isFromGoal)
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
    pure smtLemmasInPrf.toList

/-- Copied from Lean.Meta.Tactic.Intro.lean -/
private partial def getIntrosSize : Expr → Nat
  | .forallE _ _ b _ => getIntrosSize b + 1
  | .letE _ _ _ b _  => getIntrosSize b + 1
  | .mdata _ b       => getIntrosSize b
  | e                =>
    if let some (_, _, _, b) := e.letFun? then getIntrosSize b + 1
    else 0

@[tactic querySMT]
def evalQuerySMT : Tactic
| `(querySMT | querySMT%$stxRef $hints $[$uords]* {$configOptions,*}) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let lctxBeforeIntros ← getLCtx
  let originalMainGoal ← getMainGoal
  let goalType ← originalMainGoal.getType
  let goalType ← instantiateMVars goalType
  let numBinders := getIntrosSize goalType
  let (goalBinders, newGoal) ← introNCore originalMainGoal numBinders [] true true
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let lctxAfterIntros ← getLCtx
    -- **TODO**: Figure out how to properly propagate `goalDecls` in getDuperCoreSMTLemmas
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let allSMTLemmas ← runAutoGetHints lemmas inhFacts
    let (preprocessFacts, theoryLemmas, instantiations, rewriteFacts) := allSMTLemmas
    let smtLemmas := preprocessFacts ++ theoryLemmas ++ -- instantiations
      (rewriteFacts.foldl (fun acc rwFacts => acc ++ rwFacts) [])
    trace[querySMT.debug] "Number of lemmas before filter: {smtLemmas.length}"
    let smtLemmas ←
      match ← querySMT.getFilterOptM with
      | noFilter => pure smtLemmas
      | tautoFilter => smtLemmas.filterM (fun lem => return !(← isTautology lem))
      | duperFilter => smtLemmas.filterM (fun lem => return !(← uselessLemma lem))
      | duperCore => getDuperCoreSMTLemmas smtLemmas lemmas
    trace[querySMT.debug] "Number of lemmas after filter: {smtLemmas.length}"
    let lemmasStx ← smtLemmas.mapM (fun lemExp => PrettyPrinter.delab lemExp)
    let mut tacticsArr := #[] -- The array of tactics that will be suggested to the user
    -- Build the `intros ...` tactic with appropriate names
    let mut introsNames : Array Name := #[]
    let mut needIntrosTactic := false -- We only need the `intros` tactic if there is at least one non-proof binder
    let mut numTrailingUnderscores := 0 -- Info to remove trailing underscores at the end of `intros` tactic
    for fvarId in goalBinders do
      let localDecl := lctxAfterIntros.fvarIdToDecl.find! fvarId
      let ty := localDecl.type
      if (← inferType ty).isProp then
        introsNames := introsNames.push `_
        numTrailingUnderscores := numTrailingUnderscores + 1
      else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
        introsNames := introsNames.push $ Name.eraseMacroScopes localDecl.userName
        needIntrosTactic := true
        numTrailingUnderscores := 0
    if needIntrosTactic then -- Include `intros ...` tactic only if there is at least one non-proof binder to introduce
      introsNames := introsNames.toSubarray 0 (introsNames.size - numTrailingUnderscores)
      let ids : TSyntaxArray [`ident, `Lean.Parser.Term.hole] := introsNames.map (fun n => mkIdent n)
      tacticsArr := tacticsArr.push $ ← `(tactic| intros $ids*)
    -- Create each of the SMT lemmas
    let mut lemmaCount := 0
    let lemmaPrefix :=
      match getLemmaPrefixFromConfigOptions configOptions with
      | some lemmaPrefix => lemmaPrefix
      | none => "smtLemma"
    for lemmaStx in lemmasStx do
      let lemmaName := lemmaPrefix ++ lemmaCount.repr
      tacticsArr := tacticsArr.push $ ← `(tactic| have $(mkIdent (.str .anonymous lemmaName)) : $lemmaStx := by proveSMTLemma)
      lemmaCount := lemmaCount + 1
    tacticsArr := tacticsArr.push $ ← `(tactic| duper [*])
    let tacticSeq ← `(tacticSeq| $tacticsArr*)
    -- Create the suggestion
    withOptions (fun o => (o.set `pp.analyze true).set `pp.funBinderTypes true) $
      addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
    let proof ← mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
    absurd.assign proof
| _ => throwUnsupportedSyntax

end QuerySMT
