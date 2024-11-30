import Lean
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Rename
import Mathlib.Data.Real.Basic
import Duper

open Lean Meta Elab Tactic Parser Tactic Core Mathlib.Tactic.PushNeg

namespace ReplaceNats

initialize Lean.registerTraceClass `replaceNats.debug

syntax (name := replaceNats) "replaceNats" : tactic

instance : CanLift Nat Int Int.natAbs (fun _ => True) :=
  { prf := (fun x _ => Exists.intro ↑x (Int.natAbs_ofNat x)) }

def intFunToNatFun (g : Int → Int) (n : Nat) : Nat := (g (Int.ofNat n)).natAbs
def natFunToIntFun (f : Nat → Nat) (z : Int) : Int := Int.ofNat (f z.natAbs)
def intFunNatFunInv (f : Nat → Nat) : intFunToNatFun (natFunToIntFun f) = f := by
  unfold intFunToNatFun natFunToIntFun
  simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat]

instance : CanLift (Nat → Nat) (Int → Int) intFunToNatFun (fun _ => True) :=
  { prf := (fun f _ => Exists.intro (natFunToIntFun f) (intFunNatFunInv f)) }

def intInputToNatInput (g : Int → α) (n : Nat) : α := g (Int.ofNat n)
def natInputToIntInput (f : Nat → α) (z : Int) : α := f z.natAbs
def intInputNatInputInv (f : Nat → α) : intInputToNatInput (natInputToIntInput f) = f := by
  unfold intInputToNatInput natInputToIntInput
  simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat]

instance (α) : CanLift (Nat → α) (Int → α) intInputToNatInput (fun _ => True) :=
  { prf := (fun f _ => Exists.intro (natInputToIntInput f) (intInputNatInputInv f)) }

def intOutputToNatOutput (g : α → Int) (a : α) : Nat := (g a).natAbs
def natOutputToIntOutput (f : α → Nat) (a : α) : Int := Int.ofNat (f a)
def intOutputNatOutputInv (f : α → Nat) : intOutputToNatOutput (natOutputToIntOutput f) = f := by
  unfold intOutputToNatOutput natOutputToIntOutput
  simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat]

instance (α) : CanLift (α → Nat) (α → Int) intOutputToNatOutput (fun _ => True) :=
  { prf := (fun f _ => Exists.intro (natOutputToIntOutput f) (intOutputNatOutputInv f)) }

def intProdToNatProd (x : Int × Int) : Nat × Nat := (x.1.natAbs, x.2.natAbs)
def natProdToIntProd (x : Nat × Nat) : Int × Int := (Int.ofNat x.1, Int.ofNat x.2)
def intProdNatProdInv (x : Nat × Nat) : intProdToNatProd (natProdToIntProd x) = x := by
  unfold intProdToNatProd natProdToIntProd
  simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat]

instance : CanLift (Nat × Nat) (Int × Int) intProdToNatProd (fun _ => True) :=
  { prf := (fun x _ => Exists.intro (natProdToIntProd x) (intProdNatProdInv x)) }

def intProd1ToNatProd1 (x : Int × α) : Nat × α := (x.1.natAbs, x.2)
def natProd1ToIntProd1 (x : Nat × α) : Int × α := (Int.ofNat x.1, x.2)
def intProd1NatProd1Inv (x : Nat × α) : intProd1ToNatProd1 (natProd1ToIntProd1 x) = x := by
  unfold intProd1ToNatProd1 natProd1ToIntProd1
  simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat]

instance (α) : CanLift (Nat × α) (Int × α) intProd1ToNatProd1 (fun _ => True) :=
  { prf := (fun x _ => Exists.intro (natProd1ToIntProd1 x) (intProd1NatProd1Inv x)) }

def intProd2ToNatProd2 (x : α × Int) : α × Nat := (x.1, x.2.natAbs)
def natProd2ToIntProd2 (x : α × Nat) : α × Int := (x.1, Int.ofNat x.2)
def intProd2NatProd2Inv (x : α × Nat) : intProd2ToNatProd2 (natProd2ToIntProd2 x) = x := by
  unfold intProd2ToNatProd2 natProd2ToIntProd2
  simp only [Int.ofNat_eq_coe, Int.natAbs_ofNat]

instance (α) : CanLift (α × Nat) (α × Int) intProd2ToNatProd2 (fun _ => True) :=
  { prf := (fun x _ => Exists.intro (natProd2ToIntProd2 x) (intProd2NatProd2Inv x)) }

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
    evalTactic $ ← `(tactic| try simp only [Nat.cast, NatCast.natCast] at *)
| _ => throwUnsupportedSyntax

example (x : Nat) (y : Nat) (z : Int) (h : z = x + y) : z = x + y := by
  replaceNats
  exact h

example (f : Nat → Prop) (x : Nat) (h : f 0) (x_eq_zero : x = 0) : f x := by
  replaceNats
  simp only [x_eq_zero, Int.natAbs_zero, h]

example (f : Nat → Prop) (x : Nat × Nat) (h : f 0) (x_eq_zero : x.1 = 0) : f x.1 := by
  /- Current tests suggest I can only lift `x` to `Int × Int` when I directly define
     `CanLift (Nat × Nat) (Int × Int)`. It doesn't appear to be sufficient to define
     `CanLift (Nat × α) (Int × α)` and `CanLift (α × Nat) (α × Int)`. Though it's
     possible I'm doing something wrong since lift's documentation here
     (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Lift.html#Mathlib.Tactic.lift)
     appears to suggest that `CanLift` will automatically generate transitive instances -/
  zify at *
  lift x to Int × Int using True.intro
  unfold intProdToNatProd
  simp only
  unfold intProdToNatProd at x_eq_zero
  simp only at x_eq_zero
  /- I can't get rid of the casting because I don't know that `x.1` is always nonnegative
     (even though it definitely is since I lifted `x` from `Nat × Nat`) -/
  sorry

example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) : f = g := by
  /- Current tests suggest I can only lift f to Int → Int when I directly define
     `CanLift (Nat → Nat) (Int → Int)`. It doesn't appear to be sufficient to define
     `CanLift (Nat → α) (Int → α)` and `CanLift (α → Nat) (α → Int)`. Though it's
     possible I'm doing something wrong since lift's documentation here
     (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Lift.html#Mathlib.Tactic.lift)
     appears to suggest that `CanLift` will automatically generate transitive instances -/
  zify at *
  lift f to Int → Int using True.intro
  lift g to Int → Int using True.intro
  unfold intFunToNatFun
  simp only [Int.ofNat_eq_coe]
  unfold intFunToNatFun at h
  simp only [Int.ofNat_eq_coe] at h
  /- I can't get rid of the casting because I don't know that `f` and `g` always output nonnegative
     results (even though they definitely do since I lifted them from `Nat → Nat`) -/
  sorry

example (x : Int) (h : x ≥ 0) : |x| = x := by
  simp [h]

example : ∀ x : Int, x = 5 → |x| = 5 := by
  simp only [forall_eq, Nat.abs_ofNat]

example : ∃ x : Int, x = 5 ∧ |x| = 5 := by
  simp only [exists_eq_left, Nat.abs_ofNat]

example : ∃ x : Int, x ≥ 0 ∧ |x| = 5 := by
  simp? (config := { contextual := true })
  sorry

example (P : Int → Prop) (h : ∀ x : Int, x ≥ 0 → P x) : ∀ x : Int, x ≥ 0 → P x := by
  simp (config := { contextual := true }) only [ge_iff_le, implies_true, h]
  -- contextual := true is necessary for simp to solve the above

example (x : Nat × Nat) : x.1 ≥ 0 := by
  zify
  lift x to Int × Int using True.intro
  unfold intProdToNatProd
  simp only [Int.natCast_natAbs, abs_nonneg]

#check Int.natAbs_cast

theorem Int.cast_natAbs_cancel (z : Int) (h : z ≥ 0) : ↑(z.natAbs) = z := by
  simp only [Int.natCast_natAbs, abs_eq_self, h]

example (P Q : Nat → Prop) (n : Nat)
  (h1 : ∀ x : Int, x ≥ 0 → P x.natAbs → Q x.natAbs)
  (h2 : P n) : Q n := by
  exact h1 ↑n (by simp only [ge_iff_le, Nat.cast_nonneg]) h2

example (P Q : Nat → Prop) (n : Nat)
  (h1 : ∀ x : Int, x ≥ 0 → P x.natAbs → Q x.natAbs)
  (h2 : P n) : Q n := by
  duper [*, Int.natAbs_cast, Int.cast_natAbs_cancel, Nat.cast_nonneg]

set_option trace.duper.saturate.debug true in
example (P Q : Nat → Prop) (R : Nat × Nat → Prop) (y : Nat × Nat)
  (h1 : ∀ x : Int × Int, R (x.1.natAbs, x.2.natAbs) → x.1 ≥ 0 → x.2 ≥ 0 → P x.1.natAbs → Q x.2.natAbs)
  (h2 : P y.1) (h3 : R y) : Q y.2 := by
  duper [*, Int.natAbs_cast, Int.cast_natAbs_cancel, Nat.cast_nonneg] {portfolioInstance := 1}
  -- Fails because current monomorphization procedure kills datatype reasoning

set_option trace.duper.saturate.debug true in
example (P Q : Nat → Prop) (R : Nat × Nat → Prop) (y : Nat × Nat)
  (h1 : ∀ x : Int × Int, R (x.1.natAbs, x.2.natAbs) → x.1 ≥ 0 → x.2 ≥ 0 → P x.1.natAbs → Q x.2.natAbs)
  (h2 : P y.1) (h3 : R y) : Q y.2 := by
  duper [*, Int.natAbs_cast, Int.cast_natAbs_cancel, Nat.cast_nonneg, ge_iff_le, Nat.zero_le] {portfolioInstance := 1}

#check Int.natAbs_cast
#check Int.cast_natAbs_cancel
#check Nat.cast_nonneg
#check Nat.zero_le
#check ge_iff_le

example (P Q : Int → Prop) (R : Nat × Nat → Prop) (y : Nat × Nat)
  (h1 : ∀ x : Nat × Nat, R x → x.1 ≥ 0 → x.2 ≥ 0 → P x.1 → Q x.2)
  (h2 : P ↑y.1) (h3 : R y) : Q ↑y.2 := by
  duper [*, ge_iff_le, Nat.zero_le, Int.natAbs_cast, Int.cast_natAbs_cancel, Nat.cast_nonneg]

end ReplaceNats
