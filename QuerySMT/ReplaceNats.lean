import Lean
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Rename

open Lean Meta Elab Tactic Parser Tactic Core Mathlib.Tactic.PushNeg

namespace ReplaceNats

initialize Lean.registerTraceClass `replaceNats.debug

syntax (name := replaceNats) "replaceNats" : tactic

instance : CanLift Nat Int Int.natAbs (fun _ => True) :=
  { prf := (fun x _ => Exists.intro ↑x (Int.natAbs_ofNat x)) }

@[tactic replaceNats]
def evalReplaceNats : Tactic
| `(replaceNats | replaceNats) => do
  evalTactic $ ← `(tactic| try zify at *)
  withMainContext do
    for fVarId in (← getLCtx).getFVarIds do
      let ldecl ← Lean.FVarId.getDecl fVarId
      let ldeclType ← instantiateMVars ldecl.type
      if ldeclType == mkConst ``Nat then
        let fvarStx ← PrettyPrinter.delab (.fvar fVarId)
        let n := s!"{ldecl.userName}"
        let nOld := n ++ "_old"
        let zeroLeFact := "zero_le_" ++ n
        let eqFact := nOld ++ "_eq_" ++ n
        let castEqFact := "cast_" ++ nOld ++ "_eq_cast_" ++ n
        let nIdent := mkIdent (.str .anonymous n)
        let nOldIdent := mkIdent (.str .anonymous nOld)
        let zeroLeFactIdent := mkIdent (.str .anonymous zeroLeFact)
        let eqFactIdent := mkIdent (.str .anonymous eqFact)
        let castEqFactIdent := mkIdent (.str .anonymous castEqFact)
        evalTactic $ ← `(tactic| rename' $fvarStx => $nOldIdent)
        evalTactic $ ← `(tactic| have $zeroLeFactIdent : (0 : Int) ≤ $nOldIdent := Int.ofNat_le.mpr (Nat.zero_le $nOldIdent))
        evalTactic $
          ← `(tactic|
              obtain ⟨$nIdent, ⟨$eqFactIdent, $castEqFactIdent⟩⟩ :
                ∃ a : Int, (↑($nOldIdent:term) = a ∧ $nOldIdent:term = Int.natAbs a) :=
                Exists.intro ↑$nOldIdent (And.intro rfl rfl)
            )
        evalTactic $ ← `(tactic| lift $nOldIdent to Int using True.intro)
        evalTactic $ ← `(tactic| simp_rw [$eqFactIdent:term, $castEqFactIdent:term] at *)
        evalTactic $ ← `(tactic| clear $eqFactIdent)
        evalTactic $ ← `(tactic| clear $castEqFactIdent)
        evalTactic $ ← `(tactic| clear $nOldIdent)
| _ => throwUnsupportedSyntax

example (x : Nat) (y : Nat) (z : Int) (h : z = x + y) : z = x + y := by
  replaceNats
  exact h

example (f : Nat → Prop) (x : Nat) (h : f 0) (x_eq_zero : x = 0) : f x := by
  replaceNats
  simp only [x_eq_zero, Int.natAbs_zero, h]

end ReplaceNats
