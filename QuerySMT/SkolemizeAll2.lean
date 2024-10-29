import Lean
import Mathlib.Tactic.PushNeg

open Lean Meta Elab Tactic Parser Tactic Core Mathlib.Tactic.PushNeg

namespace Skolemize

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

noncomputable def Skolem.some (p : α → Prop) (x : α) : α :=
  let _ : Decidable (∃ a, p a) := Classical.propDecidable _
  if hp : ∃ a, p a then Classical.choose hp else x

theorem Skolem.spec {p : α → Prop} (x : α) (hp : ∃ a, p a) :
  p (Skolem.some p x) := by
  simp only [Skolem.some, hp]
  exact Classical.choose_spec _

/-- `skolemizeExists` takes as input:
    - `e` a term whose type has the form `∃ x : α, p x` where:
      - `α : Prop`
      - `p : α → Prop`
    - `forallFVars` which contains all universally quantified free variables in `e`, `α`, and `p`

    `skolemizeExists` returns:
    - A skolem function `f : ∀ [forallFVars] → α`
    - A proof of `p (f [forallFVars])`

    **NOTE** The `Skolem.some` approach isn't compatible with types not known to be inhabited, and
     the fallback `Classical.choose` approach isn't compatible with the `Or` case of `skolemizeOne`.
     So this can fail when we need to skolemize a type not known to be inhabited inside of an `Or` expression. -/
def skolemizeExists (e : Expr) (forallFVars : Array Expr) (α p : Expr) : TacticM (Expr × Expr) := do
  try -- Try to use the `Skolem.some` approach first since it's compatible with Or
    -- `defaultValue : α`
    let defaultValue ← mkAppOptM ``Inhabited.default #[some α, none]
    -- `originalSkolemWitness : α`
    let originalSkolemWitness ← mkAppOptM ``Skolem.some #[some α, some p, some defaultValue]
    -- `originalSkolemWitnessSpec : p originalSkolemWitness`
    let originalSkolemWitnessSpec ← mkAppM ``Skolem.spec #[defaultValue, e]
    -- `generalizedSkolemWitness : ∀ [forallFVars] → α`
    let generalizedSkolemWitness ← mkLambdaFVars forallFVars originalSkolemWitness
    return (generalizedSkolemWitness, originalSkolemWitnessSpec)
  catch _ => -- If `Skolem.some` fails, use `Classical.choose` directly even though it's not compatible with `Or`
     -- `originalSkolemWitness : α`
    let originalSkolemWitness ← mkAppOptM ``Classical.choose #[some α, some p, some e]
    -- `originalSkolemWitnessSpec : p originalSkolemWitness`
    let originalSkolemWitnessSpec ← mkAppM ``Classical.choose_spec #[e]
    -- `generalizedSkolemWitness : ∀ [forallFVars] → α`
    let generalizedSkolemWitness ← mkLambdaFVars forallFVars originalSkolemWitness
    return (generalizedSkolemWitness, originalSkolemWitnessSpec)

/-- `skolemizeOne` takes as input:
    - `e` of type `t` (where `t : Prop` has had all of its metavariables instantiated). It is assumed that `push_neg`
      has already been called to ensure that when `Not` is encountered, no binders will appear in its argument
    - `generatedSkolems` which is a running array of generated skolem functions along with the types of the original
      existential binders that were skolemized
    - `forallFVars` which is a running array of universally quantified free variables that may appear in `e`.

    `skolemizeOne` checks whether `t` can be skolemized, and if it can, produces and returns:
    - The array of skolem functions generated throughout the process of skolemizing `t` (i.e. `generatedSkolems`)
    - A proof `e'` whose type is the skolemized version of `t`

    So for example, if `skolemizeOneHelper` is given `e : ∀ x : α, ∃ y : β, p x y`, the output should be:
    - [(`f : α → β`, `β`)]
    - `e'` which has the type `∀ x : α, p x (f x)`  -/
partial def skolemizeOne (e : Expr) (generatedSkolems : Array (Expr × Expr)) (forallFVars : Array Expr)
  : TacticM (Array (Expr × Expr) × Expr) := do
  let t ← instantiateMVars $ ← inferType e
  match t with
  | Expr.app (Expr.app (Expr.const ``Exists _) ty) b =>
    let (skolemFunction, e') ← skolemizeExists e forallFVars ty b
    skolemizeOne e' (generatedSkolems.push (skolemFunction, ty)) forallFVars
  | Expr.forallE n ty b _ =>
    if (← inferType ty).isProp && !b.hasLooseBVars then -- Interpret `t` is an implication rather than as a forall statement
      -- Translate `p → q` into `q ∨ ¬p` and recurse. Only use the result if the recursive call skolemized anything
      let e' ← mkAppM ``or_not_of_imp #[e]
      let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
      if generatedSkolems == generatedSkolems' then
        return (generatedSkolems, e) -- No need to call `or_not_of_imp` on `e` if no further skolemization will be done
      else
        return (generatedSkolems', e')
    else -- `t` must be interpreted as a forall statement
      withLocalDeclD n ty fun tyFVar => do
        let e' ← mkAppM' e #[tyFVar]
        let (generatedSkolems, e') ← skolemizeOne e' generatedSkolems (forallFVars.push tyFVar)
        let e' ← mkLambdaFVars #[tyFVar] e'
        return (generatedSkolems, e')
  | Expr.app (Expr.app (Expr.const ``And _) _) _ =>
    let e1 ← mkAppM ``And.left #[e]
    let e2 ← mkAppM ``And.right #[e]
    let (generatedSkolems, e1') ← skolemizeOne e1 generatedSkolems forallFVars
    let (generatedSkolems, e2') ← skolemizeOne e2 generatedSkolems forallFVars
    return (generatedSkolems, ← mkAppM ``And.intro #[e1', e2'])
  | Expr.app (Expr.app (Expr.const ``Or _) t1) t2 =>
    withLocalDeclD `e1Hyp t1 fun e1 => do
      withLocalDeclD `e2Hyp t2 fun e2 => do
        let (generatedSkolemsE1, e1') ← skolemizeOne e1 generatedSkolems forallFVars
        let (generatedSkolemsE2, e2') ← skolemizeOne e2 generatedSkolems forallFVars
        let newE1Skolems := generatedSkolemsE1.filter (fun x => !generatedSkolems.contains x)
        let newE2Skolems := generatedSkolemsE2.filter (fun x => !generatedSkolems.contains x)
        let newE1Skolems ← newE1Skolems.mapM $
          fun (skFunction, t) =>
            pure (skFunction, t)
        let t1' ← inferType e1'
        let t2' ← inferType e2'
        let skolemizedOr ← mkAppM ``Or #[t1', t2']
        let left ← mkLambdaFVars #[e1] $ ← mkAppM ``Or.intro_left #[t2', e1']
        let right ← mkLambdaFVars #[e2] $ ← mkAppM ``Or.intro_right #[t1', e2']
        return (generatedSkolems ++ newE1Skolems ++ newE2Skolems, ← mkAppOptM ``Or.elim #[none, none, skolemizedOr, e, left, right])
  | Expr.app (Expr.const ``Not _) _ =>
    -- throwError "Still figuring out not case (need to handle negations missed by push_neg that come from translated implications)"
    return (generatedSkolems, e) -- `push_neg` ensured that `e` has no binders
  | _ => return (generatedSkolems, e)

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, then `skolemizeOne` will generate a
    new goal which does not include `fVarId`, but does include a skolemized version of the hypothesis. Additionally,
    `skolemizeOne` will assign to `mvarId` and generate a new mvarId which is returned (along with an updated skolemIdx) -/
def skolemizeAndReplace (fVarId : FVarId) (mvarId : MVarId) (skolemPrefix : String) (skolemStartIdx : Nat) : TacticM (MVarId × Nat) := do
  let s ← Tactic.saveState
  let originalMVarId := mvarId
  mvarId.withContext do
    let fvarType ← instantiateMVars (← inferType (.fvar fVarId))
    let pushNegRes ← withOptions (fun o => o.set `push_neg.use_distrib true) $ pushNegCore fvarType
    let some (fVarId, mvarId) ← applySimpResultToLocalDecl mvarId fVarId pushNegRes False | failure
    mvarId.withContext do -- Enter `mvarId`'s context because `mvarId` was changed by `push_neg` call
      let (skolemFunctions, newLemmaProof) ← skolemizeOne (.fvar fVarId) #[] #[]
      if skolemFunctions.isEmpty then
        restoreState s -- Don't call `push_neg` on `fVarId` if it does not lead to skolemizing anything
        return (originalMVarId, skolemStartIdx)
      let numSkolems := skolemFunctions.size
      let skolemFunctionTys ← skolemFunctions.mapM (fun (f, _) => inferType f)
      let newLemma ← inferType newLemmaProof
      let mvarTarget ← instantiateMVars (← mvarId.getType)
      let mvarTag ← mvarId.getTag
      let skolemTypesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) := Id.run do
        let mut curSkolemIdx := skolemStartIdx
        let mut res := #[]
        for skolemFunctionTy in skolemFunctionTys do
          let skolemName := skolemPrefix ++ curSkolemIdx.repr
          let skolemTypeConstructor : Array Expr → TacticM Expr := fun _ => pure skolemFunctionTy
          res := res.push (.str .anonymous skolemName, skolemTypeConstructor)
          curSkolemIdx := curSkolemIdx + 1
        return res
      let newGoal ←
        withLocalDeclsD skolemTypesDeclInfo fun skolemFVars => do
          let skolemEqualitiesDeclInfo : Array (Name × (Array Expr → TacticM Expr)) ← do
            let mut curSkolemIdx := skolemStartIdx
            let mut res := #[]
            for (skolemFVarsIdx, (skolemFunction, originalBinderType)) in skolemFunctions.mapIdx (fun idx f => (idx, f)) do
              let skolemFunctionTy := skolemFunctionTys[skolemFVarsIdx]!
              let numForallBindersInOriginalType ← forallTelescope originalBinderType $ fun xs _ => do pure xs.size
              let maxTelescopeBinders ← forallTelescope skolemFunctionTy $ fun xs _ => do pure (xs.size - numForallBindersInOriginalType)
              let equalityName := skolemPrefix ++ curSkolemIdx.repr ++ "_def"
              let equalityConstructor : Array Expr → TacticM Expr := fun _ =>
                forallBoundedTelescope skolemFunctionTy maxTelescopeBinders $ fun xs _ => do
                  let skolemFVarWithArgs ← mkAppM' skolemFVars[skolemFVarsIdx]! xs
                  let skolemFVarWithArgs :=
                    match (← betaReduce skolemFVarWithArgs).etaExpanded? with
                    | some skolemFVarWithArgs => skolemFVarWithArgs
                    | none => skolemFVarWithArgs
                  let instantiatedSkolemFunction ← mkAppM' skolemFunction xs
                  let instantiatedSkolemFunction :=
                    match (← betaReduce instantiatedSkolemFunction).etaExpanded? with
                    | some instantiatedSkolemFunction => instantiatedSkolemFunction
                    | none => instantiatedSkolemFunction
                  mkForallFVars xs $ ← mkAppM ``Eq #[skolemFVarWithArgs, instantiatedSkolemFunction]
              res := res.push (.str .anonymous equalityName, equalityConstructor)
              curSkolemIdx := curSkolemIdx + 1
            pure res
          withLocalDeclsD skolemEqualitiesDeclInfo fun skolemDefFVars => do
            withLocalDeclD `_ newLemma fun newLemmaFVar =>
              mkForallFVars ((skolemFVars ++ skolemDefFVars).push newLemmaFVar) mvarTarget
      let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoal mvarTag
      let mut rflArray : Array Expr := #[]
      for ((skolemFunction, originalBinderType), skolemFunctionTy) in skolemFunctions.zip skolemFunctionTys do
        let numForallBindersInOriginalType ← forallTelescope originalBinderType $ fun xs _ => do pure xs.size
        let maxTelescopeBinders ← forallTelescope skolemFunctionTy $ fun xs _ => do pure (xs.size - numForallBindersInOriginalType)
        let skolemRfl ←
          forallBoundedTelescope skolemFunctionTy maxTelescopeBinders $ fun xs _ => do
            let instantiatedSkolemFunction ← mkAppM' skolemFunction xs
            let instantiatedSkolemFunction :=
              match (← betaReduce instantiatedSkolemFunction).etaExpanded? with
              | some instantiatedSkolemFunction => instantiatedSkolemFunction
              | none => instantiatedSkolemFunction
            mkLambdaFVars xs $ ← mkAppOptM ``rfl #[none, some instantiatedSkolemFunction]
        rflArray := rflArray.push skolemRfl
      mvarId.assign (← reduceAll (← mkAppM' newGoalMVar (((skolemFunctions.map Prod.fst) ++ rflArray).push newLemmaProof)))
      let newGoalMVarId := newGoalMVar.mvarId!
      let (skolemNames, skolemDefNames) := Id.run do
        let mut skolemNames := #[]
        let mut skolemDefNames := #[]
        for skolemIdx in [skolemStartIdx:skolemStartIdx + skolemFunctions.size] do
          skolemNames := skolemNames.push (.str .anonymous (skolemPrefix ++ skolemIdx.repr))
          skolemDefNames := skolemDefNames.push (.str .anonymous (skolemPrefix ++ skolemIdx.repr ++ "_def"))
        pure (skolemNames.toList, skolemDefNames.toList)
      let (introducedFVars, newGoalMVarId) ←
        newGoalMVarId.introN (2 * numSkolems + 1) (skolemNames ++ skolemDefNames ++ [(← FVarId.getDecl fVarId).userName])
      let newGoalMVarIds ← Tactic.run newGoalMVarId $
        do
          let skolemizedLemmaFVar := introducedFVars[2 * numSkolems]!
          let skolemizedLemmaTerm ← PrettyPrinter.delab (.fvar skolemizedLemmaFVar)
          -- Iterate backwards so that the most recent skolem function (which has the fewest dependencies) is rewritten first
          for skolemIdx in (List.range skolemFunctions.size).reverse do
            let skolemDefFVar := introducedFVars[skolemIdx + numSkolems]!
            let skolemDefTerm ← PrettyPrinter.delab (.fvar skolemDefFVar)
            evalTactic $ ← `(tactic| try simp only [← $skolemDefTerm:term] at ($skolemizedLemmaTerm:term))
            evalTactic $ ← `(tactic| clear $skolemDefTerm) -- Clear skolemDef because it was only created for the above rewrite
      let [newGoalMVarId] := newGoalMVarIds
        | throwError "skolemizeAndReplace :: Failed to skolemize {Expr.fvar fVarId}"
      let newGoalMVarId ← newGoalMVarId.clear fVarId
      return (newGoalMVarId, skolemStartIdx + numSkolems)

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
      let (newMainGoal, newSkolemIdx) ← skolemizeAndReplace fVarId mainGoal skolemPrefix skolemIdx
      skolemIdx := newSkolemIdx
      mainGoal := newMainGoal
  replaceMainGoal [mainGoal]
| _ => throwUnsupportedSyntax

end Skolemize

example (P : Int → Prop) (Q : Nat → Prop) (h : ∃ x : Int, P x) (h2 : ∃ y : Nat, Q y) : ∃ y : Int, P y := by
  skolemizeAll
  apply Exists.intro sk0
  assumption

example (P : Int → Nat → Prop) (h : ∃ x : Int, ∃ y : Nat, P x y) : ∃ x : Int, ∃ y : Nat, P x y := by
  skolemizeAll
  apply Exists.intro sk0
  apply Exists.intro sk1
  assumption

example (P : Nat → Int → Prop) (h : ∀ x : Nat, ∃ y : Int, P x y) (x : Nat) : ∃ y : Int, P x y := by
  skolemizeAll
  apply Exists.intro (sk0 x)
  exact h x

example (A B C D : Type) (P : A → B → C → D → Prop) (h : ∀ a : A, ∃ b : B, ∀ c : C, ∃ d : D, P a b c d)
  : ∀ a : A, ∃ b : B, ∀ c : C, ∃ d : D, P a b c d := by
  skolemizeAll
  intro a
  apply Exists.intro (sk0 a)
  intro c
  apply Exists.intro (sk1 a c)
  exact h a c

set_option pp.proofs true
example (h : ∀ f : α → β, ∃ f' : α → β, f = f') : ∀ f : α → β, ∃ f' : α → β, f = f' := by
  skolemizeAll
  intro f
  apply Exists.intro (sk0 f)
  exact h f

example (f : b → a → Prop) (h : (∀ y : b, ∃ x : a, f y x)) : ∀ y : b, ∃ x : a, f y x := by
  skolemizeAll
  intro y
  apply Exists.intro (sk0 y)
  exact h y

example (f : Nat → Prop) (h : ¬(∀ x : Nat, f x)) : ¬(∀ x : Nat, f x) := by
  skolemizeAll
  intro h2
  exact h $ h2 sk0

example (p q : Prop) (h : ¬(p ∨ q)) : ¬(p ∨ q) := by
  skolemizeAll -- It is correct that skolemizeAll does nothing since there isn't anything to skolemize
  exact h

example (p q : Prop) (h : (p → q)) : p → q := by
  skolemizeAll -- It is correct that skolemizeAll does nothing since there isn't anything to skolemize
  exact h

example (p q : Prop) (f : Nat → Prop) (h : p ∨ (q ∧ ∃ x : Nat, f x)) : p ∨ (q ∧ ∃ x : Nat, f x) := by
  skolemizeAll
  rcases h with h | ⟨h1, h2⟩
  . exact Or.inl h
  . right
    constructor
    . exact h1
    . apply Exists.intro sk0
      exact h2

example (p : Prop) (f : Nat → Prop) (h : p → ∃ x : Nat, f x) : p → ∃ x : Nat, f x := by
  skolemizeAll
  intro hp
  rcases h with h | h
  . exact Exists.intro sk0 h
  . exfalso
    exact h hp

example (p : Prop) (f : Nat → Prop) (h : (∀ x : Nat, f x) → p) : (∀ x : Nat, f x) → p := by
  -- **TODO** We should skolemize `h` but we don't because we don't push the Not that results from clausifying the implication
  skolemizeAll
  sorry
