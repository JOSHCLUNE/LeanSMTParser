import Lean

open Lean Meta Elab Tactic Parser Tactic

namespace SkolemizeOne

mutual

partial def skolemizeAnd (fVarId : FVarId) (generatedSkolems : Array Expr) (forallFVars: Array Expr) (e1 e2 : Expr)
  (lvls : List Level) : TacticM (Option (List Expr × Expr × List Expr × Expr)) := do
  withLocalDeclD `_ e1 fun e1FVar =>
    withLocalDeclD `_ e2 fun e2FVar => do
      let e1RecursiveResult ← skolemizeOneHelper e1FVar.fvarId! generatedSkolems forallFVars
      let e2RecursiveResult ← skolemizeOneHelper e2FVar.fvarId! generatedSkolems forallFVars
      match e1RecursiveResult, e2RecursiveResult with
      | none, none => return none -- There is no skolemization to be done in either `e1` or `e2`
      | none, some (e2SkolemTypes, newE2, e2SkolemWitnesses, newE2Proof) =>
        let e2Proof ← mkAppM ``And.right #[.fvar fVarId]
        let abstractedNewE2Proof ← mkLambdaFVars #[e2FVar] newE2Proof
        let newE2Proof ← instantiateLambda abstractedNewE2Proof #[e2Proof]
        let abstractedE2SkolemWitnesses ← e2SkolemWitnesses.mapM (fun skolemWitness => mkLambdaFVars #[e2FVar] skolemWitness)
        let e2SkolemWitnesses ← abstractedE2SkolemWitnesses.mapM (fun abstractedSkolemWitness => instantiateLambda abstractedSkolemWitness #[e2Proof])
        let e2SkolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
          let mut res := #[]
          for skolemType in e2SkolemTypes do
            let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemType
            res := res.push (`_, skolemTypeConstructor)
          return res
        let newLemma ←
          withLocalDeclsD e2SkolemTypesDeclInfo fun e2SkolemFVars => do
            let instantiatedNewE2 ← instantiateForall newE2 (generatedSkolems ++ e2SkolemFVars)
            mkForallFVars (generatedSkolems ++ e2SkolemFVars) $ Expr.app (Expr.app (Expr.const ``And lvls) e1) instantiatedNewE2
        let e1Proof ← mkAppM ``And.left #[.fvar fVarId]
        let newLemmaProof ← mkAppM ``And.intro #[e1Proof, newE2Proof]
        return some (e2SkolemTypes, newLemma, e2SkolemWitnesses, newLemmaProof)
      | some (e1SkolemTypes, newE1, e1SkolemWitnesses, newE1Proof), none =>
        let e1Proof ← mkAppM ``And.left #[.fvar fVarId]
        let abstractedNewE1Proof ← mkLambdaFVars #[e1FVar] newE1Proof
        let newE1Proof ← instantiateLambda abstractedNewE1Proof #[e1Proof]
        let abstractedE1SkolemWitnesses ← e1SkolemWitnesses.mapM (fun skolemWitness => mkLambdaFVars #[e1FVar] skolemWitness)
        let e1SkolemWitnesses ← abstractedE1SkolemWitnesses.mapM (fun abstractedSkolemWitness => instantiateLambda abstractedSkolemWitness #[e1Proof])
        let e1SkolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
          let mut res := #[]
          for skolemType in e1SkolemTypes do
            let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemType
            res := res.push (`_, skolemTypeConstructor)
          return res
        let newLemma ←
          withLocalDeclsD e1SkolemTypesDeclInfo fun e1SkolemFVars => do
            let instantiatedNewE1 ← instantiateForall newE1 (generatedSkolems ++ e1SkolemFVars)
            mkForallFVars (generatedSkolems ++ e1SkolemFVars) $ Expr.app (Expr.app (Expr.const ``And lvls) instantiatedNewE1) e2
        let e2Proof ← mkAppM ``And.right #[.fvar fVarId]
        let newLemmaProof ← mkAppM ``And.intro #[newE1Proof, e2Proof]
        return some (e1SkolemTypes, newLemma, e1SkolemWitnesses, newLemmaProof)
      | some (e1SkolemTypes, newE1, e1SkolemWitnesses, newE1Proof), some (e2SkolemTypes, newE2, e2SkolemWitnesses, newE2Proof) =>
        let e1Proof ← mkAppM ``And.left #[.fvar fVarId]
        let abstractedNewE1Proof ← mkLambdaFVars #[e1FVar] newE1Proof
        let newE1Proof ← instantiateLambda abstractedNewE1Proof #[e1Proof]
        let abstractedE1SkolemWitnesses ← e1SkolemWitnesses.mapM (fun skolemWitness => mkLambdaFVars #[e1FVar] skolemWitness)
        let e1SkolemWitnesses ← abstractedE1SkolemWitnesses.mapM (fun abstractedSkolemWitness => instantiateLambda abstractedSkolemWitness #[e1Proof])
        let e1SkolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
          let mut res := #[]
          for skolemType in e1SkolemTypes do
            let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemType
            res := res.push (`_, skolemTypeConstructor)
          return res
        let e2Proof ← mkAppM ``And.right #[.fvar fVarId]
        let abstractedNewE2Proof ← mkLambdaFVars #[e2FVar] newE2Proof
        let newE2Proof ← instantiateLambda abstractedNewE2Proof #[e2Proof]
        let abstractedE2SkolemWitnesses ← e2SkolemWitnesses.mapM (fun skolemWitness => mkLambdaFVars #[e2FVar] skolemWitness)
        let e2SkolemWitnesses ← abstractedE2SkolemWitnesses.mapM (fun abstractedSkolemWitness => instantiateLambda abstractedSkolemWitness #[e2Proof])
        let e2SkolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
          let mut res := #[]
          for skolemType in e2SkolemTypes do
            let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemType
            res := res.push (`_, skolemTypeConstructor)
          return res
        let newLemma ←
          withLocalDeclsD e1SkolemTypesDeclInfo fun e1SkolemFVars => do
            withLocalDeclsD e2SkolemTypesDeclInfo fun e2SkolemFVars => do
              let instantiatedNewE1 ← instantiateForall newE1 (generatedSkolems ++ e1SkolemFVars)
              let instantiatedNewE2 ← instantiateForall newE2 (generatedSkolems ++ e2SkolemFVars)
              mkForallFVars (generatedSkolems ++ e1SkolemFVars ++ e2SkolemFVars) $ Expr.app (Expr.app (Expr.const ``And lvls) instantiatedNewE1) instantiatedNewE2
        let newLemmaProof ← mkAppM ``And.intro #[newE1Proof, newE2Proof]
        return some (e1SkolemTypes ++ e2SkolemTypes, newLemma, e1SkolemWitnesses ++ e2SkolemWitnesses, newLemmaProof)


/-- Given an `fVarId` whose type has the form `∃ x : α, p x`, and `forallFVars` of types `forallFVarTys`, generalizes the existential statement
    to produce `p (f forallFVar1 forallFVar2 ...)` where `f : forallFVarTy1 → forallFVarTy2 → ... α`. Returns:
    - A generalized type for the skolem symbol `∀ [[forallFVars]] → α`
    - A skolemWitness `λ [[forallFVars]] → f forallFVars` which has the type described in bullet 1
    - A proof of `p (f forallFVar1 forallFVar2 ...)` -/
partial def generalizeExists (fVarId : FVarId) (forallFVars : Array Expr) (ty b : Expr) : TacticM (Expr × Expr × Expr) := do
  let generalizedTy ← mkForallFVars forallFVars ty
  -- `fVarId : ∃ x : α, p x`
  -- `originalSkolemWitness : α`
  let originalSkolemWitness ← mkAppOptM ``Classical.choose #[some ty, some b, some (.fvar fVarId)]
  -- `originalSkolemWitnessSpec : p originalSkolemWitness`
  let originalSkolemWitnessSpec ← mkAppM ``Classical.choose_spec #[.fvar fVarId]
  -- `generalizedSkolemWitness : [[forallFVars]] → α`
  let generalizedSkolemWitness ← mkLambdaFVars forallFVars originalSkolemWitness
  return (generalizedTy, generalizedSkolemWitness, originalSkolemWitnessSpec)

partial def skolemizeExists (fVarId : FVarId) (generatedSkolems : Array Expr) (forallFVars : Array Expr) (ty b : Expr)
  : TacticM (Option (List Expr × Expr × List Expr × Expr)) := do
  let (generalizedTy, skolemWitness, skolemWitnessSpec) ← generalizeExists fVarId forallFVars ty b
  withLocalDeclD `generalizedSkolem generalizedTy fun skolemFVar => do
    let generatedSkolems := generatedSkolems.push skolemFVar
    let b :=
      match b with
      | .lam _ _ b _ => b
      | _ => mkApp b (.bvar 0)
    let b := b.instantiate1 $ ← mkAppM' skolemFVar forallFVars
    let bWithBinder ← mkForallFVars generatedSkolems b
    withLocalDeclD `_ b fun skolemizedLemmaFVar => do
      let some (skolemTypes, newLemma, skolemWitnesses, lemmaProof) ← skolemizeOneHelper skolemizedLemmaFVar.fvarId! generatedSkolems forallFVars
        | return some ([generalizedTy], bWithBinder, [skolemWitness], skolemWitnessSpec)
      let abstractedLemmaProof ← mkLambdaFVars #[skolemizedLemmaFVar, skolemFVar] lemmaProof
      let lemmaProof ← instantiateLambda abstractedLemmaProof #[skolemWitnessSpec, skolemWitness]
      let abstractedSkolemWitnesses ← skolemWitnesses.mapM (fun witness => mkLambdaFVars #[skolemizedLemmaFVar, skolemFVar] witness)
      let skolemWitnesses ← abstractedSkolemWitnesses.mapM (fun abstractedSkolemWitness => instantiateLambda abstractedSkolemWitness #[skolemWitnessSpec, skolemWitness])
      return some (generalizedTy :: skolemTypes, newLemma, skolemWitness :: skolemWitnesses, lemmaProof)

partial def skolemizeForall (fVarId : FVarId) (generatedSkolems : Array Expr) (forallFVars : Array Expr) (ty b : Expr)
  : TacticM (Option (List Expr × Expr × List Expr × Expr)) :=
  withLocalDeclD `forallBinder ty fun tyFVar => do
    let b := b.instantiate1 tyFVar
    withLocalDeclD `_ b fun bFVar => do
      let forallFVars := forallFVars.push tyFVar
      let some (skolemTypes, newLemma, skolemWitnesses, lemmaProof) ← skolemizeOneHelper bFVar.fvarId! generatedSkolems forallFVars
        | return none
      -- Skolem symbols should be universally bound at the front, so we need to move `tyFVar`'s binder
      -- below the skolem binders but not below other universal binders
      let skolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
        let mut res := #[]
        for skolemType in skolemTypes do
          let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemType
          res := res.push (`skolemBinder, skolemTypeConstructor)
        return res
      let newLemma ←
        withLocalDeclsD skolemTypesDeclInfo fun skolemFVars => do
          let instantiatedNewLemma ← instantiateForall newLemma skolemFVars
          mkForallFVars (skolemFVars.push tyFVar) instantiatedNewLemma
      let lemmaProof ← mkLambdaFVars #[bFVar] lemmaProof
      let lemmaProof ← mkAppM' lemmaProof #[← mkAppM' (.fvar fVarId) #[tyFVar]]
      let lemmaProof ← whnf lemmaProof
      let lemmaProof ← mkLambdaFVars #[tyFVar] lemmaProof

      let skolemWitnesses ← skolemWitnesses.mapM
        (fun skolemWitness => do
          let skolemWitness ← mkAppM' skolemWitness forallFVars
          let skolemWitness ← whnf skolemWitness
          let skolemWitness ← mkLambdaFVars forallFVars skolemWitness
          let skolemWitness ← mkLambdaFVars #[bFVar] skolemWitness
          let skolemWitness ← mkAppM' skolemWitness #[← mkAppM' (.fvar fVarId) #[tyFVar]]
          let skolemWitness ← mkAppM' skolemWitness forallFVars -- This + last line might cancel. Experiment with just returning skolemWitness here
          let skolemWitness ← whnf skolemWitness
          mkLambdaFVars forallFVars skolemWitness
        )
      return some (skolemTypes, newLemma, skolemWitnesses, lemmaProof)

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, it produces and returns:
    - A list of types for new skolem functions
    - The new skolemized lemma (with its skolem symbols abstracted away)
    - A list of expressions whose types correspond with the skolem functions
    - An expression whose type corresponds with the skolemized lemma

    So for example, if `skolemizeOneHelper` is given an `fVarId` with type `∃ x : Int, P x`, the output should be:
    - [`Int`]
    - `∀ x : Int, P x`
    - [An Int `c` that satisfies `P c`]
    - A proof of `P c` -/
partial def skolemizeOneHelper (fVarId : FVarId) (generatedSkolems : Array Expr) (forallFVars : Array Expr)
  : TacticM (Option (List Expr × Expr × List Expr × Expr)) := do
  let ldecl ← Lean.FVarId.getDecl fVarId
  let ty ← instantiateMVars ldecl.type
  match ty with
  | Expr.app (Expr.app (Expr.const ``Exists _) ty) b => skolemizeExists fVarId generatedSkolems forallFVars ty b
  | Expr.forallE _ ty b _ => -- **TODO** Distinguish between genuine forall and implication
    skolemizeForall fVarId generatedSkolems forallFVars ty b
  | Expr.app (Expr.app (Expr.const ``And lvls) e1) e2 => skolemizeAnd fVarId generatedSkolems forallFVars e1 e2 lvls
  | Expr.app (Expr.app (Expr.const ``Or lvls) e1) e2 => return none -- **TODO** Or support
  | _ => return none -- **TODO** Negation support

end

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, then `skolemizeOne` will generate a
    new goal which does not include `fVarId`, but does include a skolemized version of the hypothesis. Additionally,
    `skolemizeOne` will assign to `mvarId` and generate a new mvarId which is returned (along with an updated skolemIdx) -/
def skolemizeOne (fVarId : FVarId) (mvarId : MVarId) (skolemPrefix : String) (skolemIdx : Nat) : TacticM (MVarId × Nat) :=
  mvarId.withContext do
    let some (skolemTypes, newLemma, skolemWitnesses, lemmaProof) ← skolemizeOneHelper fVarId #[] #[]
      | return (mvarId, skolemIdx)
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
        let instantiatedNewLemma ← instantiateForall newLemma skolemFVars
        withLocalDeclD `_ instantiatedNewLemma fun newLemmaFVar =>
          mkForallFVars (skolemFVars.push newLemmaFVar) mvarTarget
    let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoal mvarTag
    mvarId.assign (← reduceAll (← mkAppM' newGoalMVar (skolemWitnesses.toArray ++ #[lemmaProof])))
    let newGoalMVarId := newGoalMVar.mvarId!
    let numSkolems := skolemTypes.length
    let skolemNames := Id.run do
      let mut skolemIdx := skolemIdx
      let mut skolemNames := #[]
      for _ in skolemTypes do
        skolemNames := skolemNames.push (.str .anonymous (skolemPrefix ++ skolemIdx.repr))
        skolemIdx := skolemIdx + 1
      return skolemNames.toList
    let (_, newGoalMVarId) ← newGoalMVarId.introN (numSkolems + 1) (skolemNames ++ [(← FVarId.getDecl fVarId).userName])
    let newGoalMVarId ← newGoalMVarId.clear fVarId
    return (newGoalMVarId, skolemIdx + numSkolems)

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
