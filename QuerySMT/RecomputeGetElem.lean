import Lean

open Lean Meta Elab Tactic Parser Tactic Core

namespace RecomputeGetElem

partial def recomputeGetElemHelper (e : Expr) : TacticM Expr := do
  match e with
  | .app f a         =>
    match e.getAppFn with
    | .const ``GetElem.getElem _ =>
      let args := e.getAppArgs
      if h : args.size ≠ 8 then
        throwError "{decl_name%} :: Found GetElem.getElem with wrong number of arguments (args: {args})"
      else
        let proofToRecompute := args[7]
        let proofGoal ← inferType proofToRecompute
        let m ← mkFreshExprMVar proofGoal
        let [] ← Tactic.run m.mvarId! $ evalTactic $ ← `(tactic| get_elem_tactic)
          | throwError "{decl_name%} Unable to use get_elem_tactic to discover a new proof of {proofGoal} to replace {proofToRecompute}"
        let m ← instantiateMVars m
        let newArgs := args.set 7 m
        mkAppOptM ``GetElem.getElem $ newArgs.map some
    | _ => return e.updateApp! (← recomputeGetElemHelper f) (← recomputeGetElemHelper a)
  | .mdata _ b       => return e.updateMData! (← recomputeGetElemHelper b)
  | .proj _ _ b      => return e.updateProj! (← recomputeGetElemHelper b)
  | .letE declName t v b nonDep  =>
    -- `visit` needs to go inside binders (so local facts are accessible to `visit b`)
    let e' := e.updateLet! (← recomputeGetElemHelper t) (← recomputeGetElemHelper v) b nonDep
    -- `lambdaLetBoundedTelescope` doesn't exist so I just use `lambdaLetTelescope`
    lambdaLetTelescope e' $ fun xs body => do
      let body' ← recomputeGetElemHelper body
      mkLetFVars xs body'
  | .lam _ d b _     =>
    -- return e.updateLambdaE! (← recomputeGetElemHelper d) (← recomputeGetElemHelper b) **TODO** Delete
    -- `visit` needs to go inside binders (so local facts are accessible to `visit b`)
    let e' := e.updateLambdaE! (← recomputeGetElemHelper d) b
    lambdaBoundedTelescope e' 1 $ fun xs body => do
      let body' ← recomputeGetElemHelper body
      mkLambdaFVars xs body'
  | .forallE _ d b _ =>
    -- return e.updateForallE! (← recomputeGetElemHelper d) (← recomputeGetElemHelper b) **TODO** Delete
    -- `visit` needs to go inside binders (so local facts are accessible to `visit b`)
    let e' := e.updateForallE! (← recomputeGetElemHelper d) b
    forallBoundedTelescope e' (some 1) $ fun xs body => do
      let body' ← recomputeGetElemHelper body
      mkForallFVars xs body'
  | e                => return e

-- **TODO** Add doc string
-- Explain that recomputeGetElem takes a term as input rather than an fvar because `simp only` changes the relevant fvar
def recomputeGetElem (id : Term) : TacticM Unit := do
  let some e ← Term.resolveId? id
    | throwError "{decl_name%} :: Unable to resolve the term {id}"
  let some fvar := e.fvarId?
    | throwError "{decl_name%} :: Term {id} resolved to {e} which is not an fvar"
  let lctx ← getLCtx
  let some fvarDecl := lctx.find? fvar
    | throwError "{decl_name%} :: Unable to find {Expr.fvar fvar}"
  let fvarType := fvarDecl.type
  let newFVarType ← recomputeGetElemHelper fvarType
  let newMainGoal ← (← getMainGoal).replaceLocalDeclDefEq fvar newFVarType
  replaceMainGoal [newMainGoal]
  setGoals $ ← getUnsolvedGoals

end RecomputeGetElem
