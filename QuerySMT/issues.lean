import QuerySMT
import Hammer
import Aesop
import Mathlib.Tactic.Linarith

set_option auto.smt true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/joshClune/Desktop/temp.smt"

-- This option gets rid of warnings associated with trace options when Mathlib is imported
-- set_option linter.setOption false

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true
set_option trace.auto.smt.parseTermErrors true
set_option auto.getHints.failOnParseError true
set_option trace.auto.smt.stderr true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors false

set_option duper.collectDatatypes true

-------------------------------------------------------------------------------------------
-- `cvc5` doesn't get these

example (l : List Int) : l = [] ∨ ∃ x : Int, ∃ l' : List Int, l = x :: l' := by
  sorry -- querySMT -- `cvc5` times out

example : ∀ x : Int × Int, ∃ y : Int, ∃ z : Int, x = (y, z) := by
  sorry -- querySMT -- `cvc5` times out

-------------------------------------------------------------------------------------------
-- Currently, Duper's portfolio mode doesn't toggle duper.collectDatatypes

-- The example works only when duper.collectDatatypes is disabled
set_option maxHeartbeats 400000 in
set_option duper.collectDatatypes false in
example (x y z a b : Int) : (x < y → y < z → x < z) ∧ (a < b ∨ b ≤ a) := by
  sorry -- querySMT used to work, it now times out

-- Only works when duper.collectDatatypes is enabled
set_option duper.collectDatatypes true in
theorem Bool.or_eq_true2 (a b : Bool) : ((a || b) = true) = (a = true ∨ b = true) := by
  sorry

-------------------------------------------------------------------------------------------
-- cvc5 can solve these but Duper can't reconstruct the proof

example (x y : Int) (h : x ≥ 0) (h2 : x < y) : x * x < y * y := by
  -- autoGetHints works
  sorry -- `querySMT` fails because Duper can't reconstruct the proof

example (x : Int) (h : x * x = 1) : x = 1 ∨ x = -1 := by
  -- autoGetHints works
  sorry -- `querySMT` fails because Duper can't reconstruct the proof

-------------------------------------------------------------------------------------------
/-
example (x y : Real) : x < y ∨ y ≤ x := by
  querySMT -- Fails because lean-auto doesn't depend on Mathlib and therefore doesn't know about Reals
-/

-------------------------------------------------------------------------------------------
-- `querySMT` itself succeeds, but the tactic it suggests doesn't. We can see that calling `duper`
-- after `autoGetHints` succeeds, so the issue is that when filtering the Duper core, we're eliminating
-- some `smtLemma`s that are actually needed.

set_option trace.auto.inspectMVarAssignments true in
set_option trace.auto.printLemmas true in
set_option trace.auto.runAuto.printLemmas true in
set_option trace.auto.lamReif.printProofs true in
set_option trace.duper.printProof true in
set_option trace.duper.proofReconstruction true in
example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  /-
  have : Int.ofNat 32 + Int.ofNat 28 = Int.ofNat 60 := sorry
  have : Int.ofNat 14 + Int.ofNat 14 = Int.ofNat 28 := sorry
  have : Int.ofNat 21 + Int.ofNat 11 = Int.ofNat 32 := sorry
  have : Int.ofNat 1 + Int.ofNat 1 = Int.ofNat 2 := sorry
  have : Int.ofNat 10 + Int.ofNat 10 = Int.ofNat 20 := sorry
  have : Int.ofNat 10 + Int.ofNat 20 = Int.ofNat 30 := sorry
  have : Int.ofNat 1 + Int.ofNat 20 = Int.ofNat 21 := sorry
  have : Int.ofNat 1 + Int.ofNat 2 = Int.ofNat 3 := sorry
  have : Int.ofNat 30 + Int.ofNat 30 = Int.ofNat 60 := sorry
  have : Int.ofNat 1 + Int.ofNat 10 = Int.ofNat 11 := sorry
  have : Int.ofNat 3 + Int.ofNat 11 = Int.ofNat 14 := sorry
  duper? [*] {preprocessing := monomorphization, includeExpensiveRules := false}
  -/
  sorry -- querySMT

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Pos 2 := by
  sorry -- querySMT -- `querySMT` succeeds but the tactic suggestion fails

-------------------------------------------------------------------------------------------
-- `querySMT` thinks it succeeded but there is an error in the proof that Duper produces

example : ∀ x : Nat, ∀ y : Nat, x * y ≠ 0 → x ≠ 0 ∧ y ≠ 0 := by
  -- Below is the output of `querySMT`
  intros x y h0
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 : Int.ofNat y = Int.ofNat 0 → Int.ofNat x * Int.ofNat y = Int.ofNat 0 := by sorry
  have smtLemma1 : Int.ofNat x = Int.ofNat 0 → Int.ofNat x * Int.ofNat y = Int.ofNat 0 := by sorry
  duper [h0, negGoal, Int.natCast_mul, smtLemma0, smtLemma1]

example (x z : Nat) (hxz : x + z < 2) (f : Nat → Nat)
  (hz : 0 < z) : ∀ y : Nat, f (x + y) = f y := by
  intros y
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 : Int.ofNat 0 < Int.ofNat z → Int.ofNat z ≥ Int.ofNat 1 := by sorry
  have smtLemma1 : Int.ofNat x = Int.ofNat 0 → Int.ofNat (f (x + y)) = Int.ofNat (f y) := by sorry
  have smtLemma2 :
    ((Int.ofNat x + Int.ofNat z ≥ Int.ofNat 2 ∨ ¬Int.ofNat z ≥ Int.ofNat 1) ∨ ¬Int.ofNat x ≥ Int.ofNat 0) ∨
      Int.ofNat x = Int.ofNat 0 :=
    by sorry
  duper [hxz, hz, negGoal, Int.ofNat_nonneg, lt_iff_not_ge, Int.ofNat_le, Int.ofNat_lt, Int.natCast_add, smtLemma0,
    smtLemma1, smtLemma2]

-------------------------------------------------------------------------------------------
-- Both `autoGetHints` and `querySMT` appear to hang on this example (it's not clear why yet)

set_option auto.smt.save true in
set_option trace.auto.smt.printCommands true in
set_option trace.auto.smt.result true in
set_option trace.auto.smt.proof true in
example (P : Nat × Int → Prop) (h : ∀ x : Nat, ∀ y : Int, P (x, y)) :
  ∃ z : Nat × Int, P z := by
  sorry -- autoGetHints

example (Even Odd : Nat → Prop)
  (h1 : ∀ x : Nat, ∀ y : Nat, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Nat, ∀ y : Nat, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Nat, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  sorry -- querySMT

-------------------------------------------------------------------------------------------
-- Translation does not appear to include information about `MyEven` and `MyOdd`'s constructors

mutual
  inductive MyEven : Nat → Prop where
    | even_zero : MyEven 0
    | even_succ : (n : Nat) → MyOdd n → MyEven (n + 1)

  inductive MyOdd : Nat → Prop where
    | odd_succ : (n : Nat) → MyEven n → MyOdd (n + 1)
end

example (n : Nat) : MyEven n ↔ MyOdd (n + 1) := by
  sorry
