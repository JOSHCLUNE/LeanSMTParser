import Lean
import QuerySMT.RecomputeGetElem
import Mathlib.Tactic.Push

open Lean Meta Elab Tactic Parser Tactic Core Mathlib.Tactic

register_option skolemizeAll.fakeWitness : Bool := {
  defValue := false
  descr := "Fakes witnesses for non-Prop types (for testing only)"
}
namespace Skolemize

def getFakeWitness (opts : Options) : Bool :=
  skolemizeAll.fakeWitness.get opts

def getFakeWitnessM : CoreM Bool := do
  let opts ← getOptions
  return getFakeWitness opts

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

noncomputable def choice {α : Sort u} [h : Nonempty α] : α := Classical.choice h

noncomputable def Skolem.some (p : α → Prop) (x : α) : α :=
  let _ : Decidable (∃ a, p a) := Classical.propDecidable _
  if hp : ∃ a, p a then Classical.choose hp else x

theorem Skolem.spec {p : α → Prop} (x : α) (hp : ∃ a, p a) :
  p (Skolem.some p x) := by
  simp only [Skolem.some, hp]
  exact Classical.choose_spec _

theorem or_of_or {a b a' b' : Prop} (h : a ∨ b) (left : a → a') (right : b → b') : a' ∨ b' :=
  Or.casesOn h (fun h => Or.inl (left h)) fun h => Or.inr (right h)

theorem both_or_neither_of_iff {p q : Prop} (h : p ↔ q) : (p ∧ q) ∨ (¬p ∧ ¬q) := by
  rw [h, and_self, and_self]
  exact em q

theorem one_or_other_of_ne {p q : Prop} (h : p ≠ q) : (p ∧ ¬q) ∨ (¬p ∧ q) := by
  by_cases hp : p
  . simp only [eq_true hp, ne_eq, eq_iff_iff, true_iff] at h
    simp only [eq_true hp, h, not_false_eq_true, and_self, not_true_eq_false, or_false]
  . simp only [eq_false hp, ne_eq, eq_iff_iff, false_iff, not_not] at h
    simp only [eq_false hp, h, not_true_eq_false, and_self, not_false_eq_true, or_true]

theorem exists_of_not_forall {p : α → Prop} : (¬∀ x, p x) → ∃ x, ¬p x := Iff.mp not_forall
theorem not_imp_forward {p q : Prop} : (¬(p → q)) → (p ∧ ¬q) := Iff.mp Classical.not_imp
theorem not_and_or_forward {a : Prop} {b : Prop} : ¬(a ∧ b) → ¬a ∨ ¬b := Iff.mp not_and_or
theorem not_or_forward {p : Prop} {q : Prop} : ¬(p ∨ q) → ¬p ∧ ¬q := Iff.mp not_or
theorem not_iff_forward {a b : Prop} : ¬(a ↔ b) → (¬a ↔ b) := Iff.mp not_iff
theorem of_prop_not_eq {p : Prop} {q : Prop} : ¬(p = q) → (¬p) = q := by
  by_cases hp : p
  . simp only [eq_true hp, eq_iff_iff, true_iff, not_true_eq_false, false_iff, imp_self]
  . simp only [eq_false hp, eq_iff_iff, false_iff, not_not, not_false_eq_true, true_iff, imp_self]
theorem not_ne_iff_forward {α : Sort u_1} {a : α} {b : α} : ¬a ≠ b → a = b := Iff.mp not_ne_iff
theorem and_of_exists_prop {p q : Prop} : (∃ _ : p, q) → p ∧ q := exists_prop.mp
theorem and_of_exists_prop_dep {p : Prop} {q : p → Prop} : (∃ x : p, q x) → p ∧ ∀ x : p, q x := by
  simp only [forall_exists_index]
  intros hp hqp
  constructor
  . exact hp
  . intro hp'
    have hp_eq_hp' : hp = hp' := rfl
    rw [← hp_eq_hp']
    exact hqp

/-- Attempts to find a witness for `α`. Succeeds if `α` is `Inhabited`, `Nonempty`, appears in the types of `forallFVars`,
    or if any witness of type `α` is already in the local context. -/
def tryToFindWitness (α : Expr) (forallFVars : Array Expr) : TacticM (Option Expr) := do
  try
    if ← getFakeWitnessM then
      return some (← mkAppOptM ``sorryAx #[some α, some (mkConst ``false)])
    else
      return some (← mkAppOptM ``Inhabited.default #[some α, none])
  catch _ =>
    try
      return some (← mkAppOptM ``Skolemize.choice #[some α, none])
    catch _ =>
      let forallFvarsWithTypes ← forallFVars.mapM (fun fvar => do pure (fvar, ← inferType fvar))
      trace[skolemizeAll.debug] "tryToFindWitness :: forallFvarsWithTypes: {forallFvarsWithTypes}, α: {α}"
      trace[skolemizeAll.debug] "forallTypes.find? (fun ty => ty == α) : {forallFvarsWithTypes.find? (fun (_, ty) => ty == α)}"
      match forallFvarsWithTypes.find? (fun (_, ty) => ty == α) with
      | some (fvar, _) => return some fvar
      | none =>
        let lctx ← getLCtx
        let localDecls := lctx.decls.toArray.filterMap id
        for localDecl in localDecls do
          if localDecl.type == α then
            return some $ Expr.fvar localDecl.fvarId
        logWarning "Failed to find a witness for {α}"
        return none

/-- `skolemizeExists` takes as input:
    - `e` a term whose type has the form `∃ x : α, p x` where `p : α → Prop`
    - `forallFVars` which contains a superset of all universally quantified free variables in `e`, `α`, and `p`

    `skolemizeExists` returns:
    - A skolem function `f : ∀ [forallFVars'] → α`
    - A proof of `p (f [forallFVars'])`
    where `forallFVars'` is the subset of `forallFVars` that actually appear in `p` and `α`

    **NOTE** The `Skolem.some` approach isn't compatible with types not known to be inhabited, and
     the fallback `Classical.choose` approach isn't compatible with the `Or` case of `skolemizeOne`.
     So this can fail when we need to skolemize a type not known to be inhabited inside of an `Or` expression.

     **TODO** Modify how `skolemizeExists` interacts with `skolemizeOne` and `skolemizeAndReplace` so that
     if both approaches fail, a new goal for the user to fill can be created. -/
def skolemizeExists (e : Expr) (forallFVars : Array Expr) (α p : Expr) : TacticM (Expr × Expr) := do
  try -- Try to use the `Skolem.some` approach first since it's compatible with Or
    -- `defaultValue : α`
    let some defaultValue ← tryToFindWitness α forallFVars
      | throwError "Failed to find a witness for {α}"
    -- `originalSkolemWitness : α`
    let originalSkolemWitness ← mkAppOptM ``Skolem.some #[some α, some p, some defaultValue]
    -- `originalSkolemWitnessSpec : p originalSkolemWitness`
    let originalSkolemWitnessSpec ← mkAppM ``Skolem.spec #[defaultValue, e]
    -- `forallFVars'` is the subset of `forallFVars` that actually appear in `e`, `α`, `p`, and `defaultValue`
    let forallFVars' := forallFVars.filter
      (fun fvar => p.containsFVar fvar.fvarId! || α.containsFVar fvar.fvarId! || defaultValue.containsFVar fvar.fvarId!)
    -- `generalizedSkolemWitness : ∀ [forallFVars'] → α`
    let generalizedSkolemWitness ← mkLambdaFVars forallFVars' originalSkolemWitness
    return (generalizedSkolemWitness, originalSkolemWitnessSpec)
  catch _ => -- If `Skolem.some` fails, use `Classical.choose` directly even though it's not compatible with `Or`
     -- `originalSkolemWitness : α`
    let originalSkolemWitness ← mkAppOptM ``Classical.choose #[some α, some p, some e]
    -- `originalSkolemWitnessSpec : p originalSkolemWitness`
    let originalSkolemWitnessSpec ← mkAppM ``Classical.choose_spec #[e]
    -- `generalizedSkolemWitness : ∀ [forallFVars] → α`
    let generalizedSkolemWitness ← mkLambdaFVars forallFVars originalSkolemWitness
    return (generalizedSkolemWitness, originalSkolemWitnessSpec)

/-- `pushNegation` takes `e : ¬t` and checks if `t` has a logical symbol at its head that the negation can be
    pushed down into (e.g. if `t` = `p ∧ q`, then `¬t` can be transformed into `¬p ∨ ¬q`). If so, then `pushNegation`
    returns `e' : t'` where `t'` is equivalent to `t` but has had its negation pushed inwards. -/
def pushNegation (e : Expr) : TacticM (Option Expr) := do
  let t ← instantiateMVars $ ← inferType e
  match t with
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.const ``Exists _) _) _) => mkAppM ``forall_not_of_not_exists #[e]
  | Expr.app (Expr.const ``Not _) (Expr.forallE _ ty b _) =>
    if (← inferType ty).isProp && !b.hasLooseBVars then mkAppM ``not_imp_forward #[e]
    else mkAppM ``Skolemize.exists_of_not_forall #[e]
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.const ``And _) _) _) => mkAppM ``not_and_or_forward #[e]
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.const ``Or _) _) _) => mkAppM ``not_or_forward #[e]
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.const ``Iff _) _) _)  => mkAppM ``not_iff_forward #[e]
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) eqType) _) _) =>
    if eqType.isProp then mkAppM ``of_prop_not_eq #[e]
    else return none
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _) _) _) => mkAppM ``not_ne_iff_forward #[e]
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.const ``Not _) _) => mkAppM ``of_not_not #[e]
  | _ => return none

/-- `skolemizeOne` takes as input:
    - `e` of type `t` (where `t : Prop` has had all of its metavariables instantiated). It is assumed that `push_neg`
      has already been called to ensure that when `Not` is encountered, no binders will appear in its argument
    - `generatedSkolems` which is a running array of generated skolem functions along with the types of the original
      existential binders that were skolemized
    - `forallFVars` which is a running array of universally quantified free variables that may appear in `e`. Each
      free variable is paired with a boolean indicating whether it actually appears in `e`.

    `skolemizeOne` checks whether `t` can be skolemized, and if it can, produces and returns:
    - The array of skolem functions generated throughout the process of skolemizing `t` (i.e. `generatedSkolems`)
    - A proof `e'` whose type is the skolemized version of `t`

    So for example, if `skolemizeOneHelper` is given `e : ∀ x : α, ∃ y : β, p x y`, the output should be:
    - [(`f : α → β`, `β`)]
    - `e'` which has the type `∀ x : α, p x (f x)`  -/
partial def skolemizeOne (e : Expr) (generatedSkolems : Array (Expr × Expr)) (forallFVars : Array Expr)
  : TacticM (Array (Expr × Expr) × Expr) := do
  let t ← instantiateMVars $ ← inferType e
  trace[skolemizeAll.debug] "Calling skolemizeOne on {e} of type {t}"
  match t with
  | Expr.app (Expr.app (Expr.const ``Exists _) ty) (Expr.lam n t b bi) =>
    if (← inferType ty).isProp && !b.hasLooseBVars then
      let e' ← mkAppM ``and_of_exists_prop #[e]
      let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
      if generatedSkolems == generatedSkolems' then
        return (generatedSkolems, e) -- No need to perform `and_of_exists_prop` transformation if no further skolemization will be done
      else
        return (generatedSkolems', e')
    else if (← inferType ty).isProp && b.hasLooseBVars then
      let e' ← mkAppM ``and_of_exists_prop_dep #[e]
      let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
      if generatedSkolems == generatedSkolems' then
        return (generatedSkolems, e) -- No need to perform `and_of_exists_prop_ep` transformation if no further skolemization will be done
      else
        return (generatedSkolems', e')
    else
      let etaReducedBody :=
        match (Expr.lam n t b bi).etaExpanded? with
        | some etaReducedBody => etaReducedBody
        | none => Expr.lam n t b bi
      let (skolemFunction, e') ← skolemizeExists e forallFVars ty etaReducedBody
      skolemizeOne e' (generatedSkolems.push (skolemFunction, ty)) forallFVars
  | Expr.app (Expr.app (Expr.const ``Exists _) ty) b => -- Any existential quantifiers not covered by the previous case should be skolemized
    let etaReducedBody :=
      match b.etaExpanded? with
      | some etaReducedBody => etaReducedBody
      | none => b
    let (skolemFunction, e') ← skolemizeExists e forallFVars ty etaReducedBody
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
        let e' ← mkAppOptM' e #[some tyFVar]
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
        let t1' ← inferType e1'
        let t2' ← inferType e2'
        let left ← mkLambdaFVars #[e1] e1'
        let right ← mkLambdaFVars #[e2] e2'
        return (generatedSkolems ++ newE1Skolems ++ newE2Skolems, ← mkAppOptM ``or_of_or #[t1, t2, t1', t2', e, left, right])
  | Expr.app (Expr.app (Expr.const ``Iff _) _) _  =>
    let e' ← mkAppM ``Skolemize.both_or_neither_of_iff #[e]
    let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
    if generatedSkolems == generatedSkolems' then
      return (generatedSkolems, e) -- No need to transform `iff` if no further skolemization will be done
    else
      return (generatedSkolems', e')
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) eqType) _) _ =>
    if eqType.isProp then -- Treat `=` like `iff` when possible
      let e' ← mkAppM ``iff_of_eq #[e]
      let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
      if generatedSkolems == generatedSkolems' then
        return (generatedSkolems, e) -- No need to transform `Eq` if no further skolemization will be done
      else
        return (generatedSkolems', e')
    else
      return (generatedSkolems, e)
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) neType) _) _ =>
    if neType.isProp then -- Replace `≠` if possible
      let e' ← mkAppM ``one_or_other_of_ne #[e]
      let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
      if generatedSkolems == generatedSkolems' then
        return (generatedSkolems, e) -- No need to transform `Ne` if no further skolemization will be done
      else
        return (generatedSkolems', e')
    else
      return (generatedSkolems, e)
  | Expr.app (Expr.const ``Not _) _ =>
    match ← pushNegation e with
    | some e' =>
      let (generatedSkolems', e') ← skolemizeOne e' generatedSkolems forallFVars
      if generatedSkolems == generatedSkolems' then
        return (generatedSkolems, e) -- No need to push negation inward if no further skolemization will be done
      else
        return (generatedSkolems', e')
    | none => return (generatedSkolems, e)
  | _ => return (generatedSkolems, e)

/-- Given `fVarId` which is part of the local context of `mvarId`, finds the `ldecl` corresponding to `fVarId` and checks
    if `(← instantiateMVars (← inferType ldecl.type))` can be skolemized. If it can, then `skolemizeOne` will generate a
    new goal which does not include `fVarId`, but does include a skolemized version of the hypothesis. Additionally,
    `skolemizeOne` will assign to `mvarId` and generate a new mvarId which is returned (along with an updated skolemIdx) -/
def skolemizeAndReplace (fVarId : FVarId) (mvarId : MVarId) (skolemPrefix : String) (skolemStartIdx : Nat) : TacticM (MVarId × Nat) := do
  mvarId.withContext do
    let (skolemFunctions, newLemmaProof) ← skolemizeOne (.fvar fVarId) #[] #[]
    if skolemFunctions.isEmpty then return (mvarId, skolemStartIdx)
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
                let skolemFVarWithArgs ← mkAppOptM' skolemFVars[skolemFVarsIdx]! (xs.map some)
                let skolemFVarWithArgs :=
                  match (← betaReduce skolemFVarWithArgs).etaExpanded? with
                  | some skolemFVarWithArgs => skolemFVarWithArgs
                  | none => skolemFVarWithArgs
                let instantiatedSkolemFunction ← mkAppOptM' skolemFunction (xs.map some)
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
          let instantiatedSkolemFunction ← mkAppOptM' skolemFunction (xs.map some)
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
    let newGoalMVarIds ← Tactic.run newGoalMVarId
      do
        let skolemizedLemmaFVar := introducedFVars[2 * numSkolems]!
        let skolemizedLemmaTerm ← PrettyPrinter.delab (.fvar skolemizedLemmaFVar)
        -- Iterate backwards so that the most recent skolem function (which has the fewest dependencies) is rewritten first
        for skolemIdx in (List.range skolemFunctions.size).reverse do
          let skolemDefFVar := introducedFVars[skolemIdx + numSkolems]!
          let skolemDefTerm ← PrettyPrinter.delab (.fvar skolemDefFVar)
          let skolemDefType ← inferType (.fvar skolemDefFVar)
          /- If `skolemDefType` has the form `∀ xs, skX xs = Skolemize.some ...` then `relevanceArr` has the size of `xs` and all values set to `true`.
             If `skolemDefType` has the form `∀ xs, skX xs = Classical.choose ...` then `relevanceArr` indicates for each `x ∈ xs` whether `x` appears
             in the type of the last argument passed to `Classical.choose`. This determines whether this binder should be inferred by unification (`_`)
             or by assumption (`(by assumption)`) in the final `simp only [← skolemDefTerm args]` call. -/
          let relevanceArr : Array Bool ←
            forallTelescope skolemDefType $ fun xs skolemDefBody => do
              match skolemDefBody.getAppFn with
              | Expr.const ``Eq _ =>
                let skolemDefArgs := skolemDefBody.getAppArgs
                if h : skolemDefArgs.size ≠ 3 then
                  throwError "{decl_name%} :: Invalid skolem definition {Expr.fvar skolemDefFVar} (Eq has wrong number of arguments)"
                else
                  let instantiatedSkolemFunction := skolemDefArgs[2]
                  let instantiatedSkolemFunctionHead := instantiatedSkolemFunction.getAppFn
                  let instantiatedSkolemFunctionArgs := instantiatedSkolemFunction.getAppArgs
                  match instantiatedSkolemFunctionHead with
                  | Expr.const ``Classical.choose _ =>
                    if h : instantiatedSkolemFunctionArgs.size ≠ 3 then
                      throwError "{decl_name%} :: Found Classical.choose with wrong number of arguments (args: {instantiatedSkolemFunctionArgs})"
                    else
                      xs.mapM (fun x => do return (← inferType instantiatedSkolemFunctionArgs[2]).containsFVar (Expr.fvarId! x))
                  | _ =>
                    pure $ xs.map (fun _ => true)
              | _ => throwError "{decl_name%} :: Invalid skolem definition {Expr.fvar skolemDefFVar} (head symbol is not Eq)"
          let skolemizedLemmaIdent : Ident := mkIdent $ (← FVarId.getDecl fVarId).userName
          let mut innerConvTacticArr ← relevanceArr.mapM (fun b => `(conv| intro))
          let skolemDefTermArgs ← relevanceArr.mapM (fun (b : Bool) => if b then `(term| _) else `(term| (by assumption)))
          innerConvTacticArr := innerConvTacticArr.push $ ← `(conv| simp only [← $skolemDefTerm:term $skolemDefTermArgs*])
          evalTactic $ ← `(tacticSeq| conv at $skolemizedLemmaIdent:ident => $innerConvTacticArr*)
        withMainContext $ RecomputeGetElem.recomputeGetElem skolemizedLemmaTerm
        withMainContext do
          for skolemIdx in (List.range skolemFunctions.size).reverse do
            let skolemDefFVar := introducedFVars[skolemIdx + numSkolems]!
            let skolemDefTerm ← PrettyPrinter.delab (.fvar skolemDefFVar)
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
