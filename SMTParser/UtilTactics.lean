import Auto
import Duper
import Mathlib.Tactic

open Lean Meta Auto Elab Tactic Parser Tactic

namespace ProveSMTLemma

syntax (name := proveSMTLemma) "proveSMTLemma" : tactic

@[tactic proveSMTLemma]
def evalProveSMTLemma : Tactic
| `(proveSMTLemma | proveSMTLemma%$stxRef) => withMainContext do
  let tacList := [
    ← `(tactic| simp),
    ← `(tactic| rfl),
    ← `(tactic| tauto),
    ← `(tactic| linarith only),
    ← `(tactic| omega),
    ← `(tactic| aesop)
  ]
  -- `loop` iterates through `allTacs`, collecting the tactics that made any progress in `usedTacs`, then
  -- returns the sublist of tactics that can be used to close the goal (if there exists one)
  let rec loop (allTacs : List Syntax.Tactic) (usedTacs : Array Syntax.Tactic)
    : TacticM (Option (Array Syntax.Tactic)) := do
    match allTacs with
    | [tac] =>
      let tacSucceeded ←
        tryCatch
          (do let _ ← evalTactic tac; pure true)
          (fun _ => pure false)
      if tacSucceeded then return some (usedTacs.push tac)
      else return none
    | tac :: tacs =>
      let tacSucceeded ←
        tryCatch
          (do let _ ← evalTactic tac; pure true)
          (fun _ => pure false)
      if tacSucceeded then
        if (← getGoals).isEmpty then return usedTacs.push tac
        else loop tacs (usedTacs.push tac)
      else loop tacs usedTacs
    | [] => throwError "loop error in proveSMTLemma" -- Should never occur because [tac] is base case
  match ← loop tacList #[] with
  | some tacsUsed =>
    let tacticSeq ← `(tacticSeq| $tacsUsed*)
    addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
  | none => throwError "proveSMTLemma was unable to prove this goal"
| _ => throwUnsupportedSyntax

end ProveSMTLemma

namespace SkolemizeOne

#check Meta.withLocalDecls

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, it produces and returns:
    - A list of types for new skolem functions
    - A list of names and types for new skolemized lemmas
    - A list of expressions whose types correspond with the skolem functions
    - A list of expressions whose types correspond with the skolemized lemmas

    So for example, if `skolemizeOneHelper` is given an `fVarId` with type `∃ x : Int, P x`, the output should be:
    - [`Int`]
    - [`∀ x : Int, P x`]
    - [An Int `c` that satisfies `P c`]
    - [A proof of `P c`] -/
partial def skolemizeOneHelper (fVarId : FVarId) : TacticM (Option (List Expr × List (Name × Expr) × List Expr × List Expr)) := do
  let ldecl ← Lean.FVarId.getDecl fVarId
  let ty ← instantiateMVars ldecl.type
  trace[skolemizeAll.debug] "Calling skolemizeOneHelper on ty: {ty}"
  match ty with
  | Expr.app (Expr.app (Expr.const ``Exists _) ty) b => do
    -- Introduce skolem symbol
    let tyChoice ← mkAppOptM ``Classical.choose #[some ty, none, some (.fvar fVarId)]
    let tyChoiceSpec ← mkAppM ``Classical.choose_spec #[.fvar fVarId]
    Meta.withLocalDeclD `_ ty fun skolemFVar => do
      let b :=
        match b with
        | .lam _ _ b _ => b
        | _ => mkApp b (.bvar 0)
      let b := b.instantiate1 skolemFVar
      let bWithBinder ←  Meta.mkForallFVars #[skolemFVar] b
      Meta.withLocalDeclD `_ b fun skolemizedLemmaFVar => do
        let some (skolemTypes, newLemmas, skolemWitnesses, lemmaProofs) ← skolemizeOneHelper skolemizedLemmaFVar.fvarId!
          | return some ([ty], [(ldecl.userName, bWithBinder)], [tyChoice], [tyChoiceSpec])
        return (ty :: skolemTypes, (ldecl.userName, bWithBinder) :: newLemmas, tyChoice :: skolemWitnesses, tyChoiceSpec :: lemmaProofs)
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 => return none -- Nontrivial skolemization not implemented yet
  | _ => return none -- Nontrivial skolemization not implemented yet

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, then `skolemizeOne` will generate a
    new goal which does not include `fVarId`, but does include a skolemized version of the hypothesis. Additionally,
    `skolemizeOne` will assign to `mvarId` and generate a new mvarId which is returned (along with an updated skolemIdx) -/
def skolemizeOne (fVarId : FVarId) (mvarId : MVarId) (skolemPrefix : String) (skolemIdx : Nat) : TacticM (MVarId × Nat) :=
  mvarId.withContext do
    trace[skolemizeAll.debug] "Calling skolemizeOne on fvar: {Expr.fvar fVarId}"
    let some (skolemTypes, newLemmas, skolemWitnesses, lemmaProofs) ← skolemizeOneHelper fVarId
      | return (mvarId, skolemIdx)
    trace[skolemizeAll.debug] "skolemTypes: {skolemTypes}"
    trace[skolemizeAll.debug] "newLemmas: {newLemmas}"
    trace[skolemizeAll.debug] "skolemWitnesses: {skolemWitnesses}"
    trace[skolemizeAll.debug] "lemmaProofs: {lemmaProofs}"
    let mvarTarget ← instantiateMVars (← mvarId.getType)
    let mvarTag ← mvarId.getTag
    let skolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
      let mut curSkolemIdx := skolemIdx
      let mut res := #[]
      for skolemType in skolemTypes do
        let skolemName := skolemPrefix ++ curSkolemIdx.repr
        let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemType
        res := res.push (.str .anonymous skolemName, skolemTypeConstructor)
        curSkolemIdx := curSkolemIdx + 1
      return res
    let newGoal ←
      withLocalDeclsD skolemTypesDeclInfo fun skolemFVars => do
        let newLemmasDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
          let mut res := #[]
          for (_, newLemma) in newLemmas do
            let newLemmaConstructor : Array Expr → TacticM Expr := fun _ => instantiateForall newLemma skolemFVars
            res := res.push (`_, newLemmaConstructor)
          return res
        withLocalDeclsD newLemmasDeclInfo fun newLemmaFVars => do
          mkForallFVars (skolemFVars ++ newLemmaFVars) mvarTarget
    let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoal mvarTag
    mvarId.assign (← mkAppM' newGoalMVar (skolemWitnesses.toArray ++ lemmaProofs.toArray))
    let newGoalMVarId := newGoalMVar.mvarId!
    trace[skolemizeAll.debug] "newGoalMVar before intros: {newGoalMVar}"
    let numSkolems := skolemTypes.length
    let numNewLemmas := newLemmas.length
    let skolemNames := Id.run do
      let mut skolemIdx := skolemIdx
      let mut skolemNames := #[]
      for _ in skolemTypes do
        skolemNames := skolemNames.push (.str .anonymous (skolemPrefix ++ skolemIdx.repr))
        skolemIdx := skolemIdx + 1
      return skolemNames.toList
    let newLemmaNames := newLemmas.map (fun (name, _) => name)
    let (_, newGoalMVarId) ← newGoalMVarId.introN (numSkolems + numNewLemmas) (skolemNames ++ newLemmaNames)
    trace[skolemizeAll.debug] "newGoalMVar after intros: {newGoalMVar}"
    let newGoalMVarId ← newGoalMVarId.clear fVarId
    return (newGoalMVarId, skolemIdx + numSkolems)

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, then `skolemizeOne` will generate a
    new goal which does not include `fVarId`, but does include a skolemized version of the hypothesis. Additionally,
    `skolemizeOne` will assign to `mvarId` and generate a new mvarId which is returned (along with an updated skolemIdx) -/
partial def skolemizeOneOld (fVarId : FVarId) (mvarId : MVarId) (skolemPrefix : String) (skolemIdx : Nat) : TacticM (MVarId × Nat) :=
  mvarId.withContext do
    let ldecl ← Lean.FVarId.getDecl fVarId
    let ty ← instantiateMVars ldecl.type
    trace[skolemizeAll.debug] "Skolemizing ty: {ty}"
    let mvarTarget ← instantiateMVars (← mvarId.getType)
    let mvarTag ← mvarId.getTag
    match ty with
    | Expr.app (Expr.app (Expr.const ``Exists _) ty) b => do
      -- Introduce skolem symbol
      let tyChoice ← mkAppOptM ``Classical.choose #[some ty, none, some (.fvar fVarId)]
      let tyChoiceSpec ← mkAppM ``Classical.choose_spec #[.fvar fVarId]
      let newGoal ←
        Meta.withLocalDeclD `_ ty fun skolemFVar => do
          let b :=
            match b with
            | .lam _ _ b _ => b
            | _ => mkApp b (.bvar 0)
          let b := b.instantiate1 skolemFVar
          Meta.withLocalDeclD `_ b fun skolemizedLemmaFVar => Meta.mkForallFVars #[skolemFVar, skolemizedLemmaFVar] mvarTarget
      let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoal mvarTag
      mvarId.assign (← mkAppM' newGoalMVar #[tyChoice, tyChoiceSpec])
      let newGoalMVarId := newGoalMVar.mvarId!
      let skolemName := skolemPrefix ++ skolemIdx.repr
      let (newFVars, newGoalMVarId) ← newGoalMVarId.introN 2 [.str .anonymous skolemName, ldecl.userName]
      -- Clear the old declaration
      let newGoalMVarId ← newGoalMVarId.clear fVarId
      -- If `ty` has a form like `∃ x, ∃ y, ...` then we need to continue skolemizing. So we recurse rather than return
      let newFVarId := newFVars[1]!
      skolemizeOneOld newFVarId newGoalMVarId skolemPrefix (skolemIdx + 1)
    | _ => return (mvarId, skolemIdx) -- Nontrivial skolemization not implemented yet

end SkolemizeOne

namespace SkolemizeAll

initialize Lean.registerTraceClass `skolemizeAll.debug

declare_syntax_cat SkolemizeAll.configOption (behavior := symbol)
syntax (&"prefix" " := " strLit) : SkolemizeAll.configOption
syntax (name := skolemizeAll) "skolemizeAll" (ppSpace "{"SkolemizeAll.configOption,*,?"}")? : tactic

macro_rules
| `(tactic| skolemizeAll) => `(tactic| skolemizeAll {})

def getPrefixFromConfigOptions (configOptionsStx : TSyntaxArray `SkolemizeAll.configOption) : Option String := Id.run do
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(configOption| prefix := $skolemPrefixSyntax:str) => return some skolemPrefixSyntax.getString
    | _ => continue
  return none

@[tactic skolemizeAll]
def evalSkolemizeAll : Tactic
| `(skolemizeAll | skolemizeAll {$configOptions,*}) => withMainContext do
  let skolemPrefix :=
    match getPrefixFromConfigOptions configOptions with
    | some skolemPrefix => skolemPrefix
    | none => "sk"
  let mut skolemIdx := 0
  let mut mainGoal ← getMainGoal
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← Lean.FVarId.getDecl fVarId
    unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
      let (newMainGoal, newSkolemIdx) ← SkolemizeOne.skolemizeOne fVarId mainGoal skolemPrefix skolemIdx
      skolemIdx := newSkolemIdx
      mainGoal := newMainGoal
  replaceMainGoal [mainGoal]
| _ => throwUnsupportedSyntax

end SkolemizeAll
