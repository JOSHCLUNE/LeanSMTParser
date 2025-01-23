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
-- Issue: Adding the fact `h7` causes Duper to stop succeeding and start saturating
-- Update: The reason for this is the same as the issue below. Duper doesn't know that `-x` = `0 - x`

set_option pp.rawOnError true in
set_option trace.duper.printProof true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1) : Pos 2 := by
  querySMT [*, h4, h5] -- This problem works without `h7`

set_option trace.duper.saturate.debug true in
set_option trace.querySMT.debug true in
set_option pp.rawOnError true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Pos 2 := by
  sorry -- querySMT -- Duper saturates when `h7` is added

set_option trace.duper.saturate.debug true in
set_option trace.querySMT.debug true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Pos 2 := by
  have neededFact : ∀ x : Int, -x = 0 - x := sorry
  sorry -- querySMT -- `querySMT` currently fails even with neededFact, but only because the unsatCore reasoning filters out neededFact

-------------------------------------------------------------------------------------------
-- Issue: Duper doesn't natively know that `-x` = `0 - x`. So when `-x` appears in the initial
-- problem but is then translated to `0 - x` by the SMT parser, duper can wind up missing an essential fact

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1)) : Neg (-2) := by
  querySMT -- This problem works with `h4` in this simpler form

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg (- x) → Neg (-(x + 1)))
  (h5 : Neg (-1)) : Neg (- 2) := by
  have neededFact : ∀ x : Int, -x = 0 - x := sorry
  sorry -- querySMT -- `querySMT` currently fails even with neededFact, but only because the unsatCore reasoning filters out neededFact

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg (- x) → Neg ((- x) - 1))
  (h5 : Neg (-1)) : Neg (- 2) := by
  have neededFact : ∀ x : Int, -x = 0 - x := sorry
  sorry -- querySMT -- `querySMT` currently fails even with neededFact, but only because the unsatCore reasoning filters out neededFact

-------------------------------------------------------------------------------------------
-- `cvc5` doesn't get these

example (l : List Int) : l = [] ∨ ∃ x : Int, ∃ l' : List Int, l = x :: l' := by
 sorry -- querySMT -- `cvc5` times out

example : ∀ x : Int × Int, ∃ y : Int, ∃ z : Int, x = (y, z) := by
  sorry -- querySMT -- `cvc5` times out

-------------------------------------------------------------------------------------------
-- The example works only when duper.collectDatatypes is disabled

set_option duper.collectDatatypes false in
example (x y z a b : Int) : (x < y → y < z → x < z) ∧ (a < b ∨ b ≤ a) := by
  querySMT

-- Only works when duper.collectDatatypes is enabled
set_option duper.collectDatatypes true in
@[simp] theorem Bool.or_eq_true2 (a b : Bool) : ((a || b) = true) = (a = true ∨ b = true) := by
  querySMT

-------------------------------------------------------------------------------------------
-- cvc5 can solve these but Duper can't reconstruct the proof (presumably because of <, ≥, and negative stuff)

set_option auto.smt true in
set_option auto.smt.dumpHints true in
set_option auto.smt.solver.name "cvc5" in
example (x y : Int) (h : x ≥ 0) (h2 : x < y) : x * x < y * y := by
  -- autoGetHints works
  sorry -- `querySMT` fails because Duper can't reconstruct the proof

set_option auto.smt true in
set_option auto.smt.dumpHints true in
set_option auto.smt.solver.name "cvc5" in
example (x : Int) (h : x * x = 1) : x = 1 ∨ x = -1 := by
  -- autoGetHints workds
  sorry -- `querySMT` fails because Duper can't reconstruct the proof

-------------------------------------------------------------------------------------------
/-
example (x y : Real) : x < y ∨ y ≤ x := by
  querySMT -- Fails because lean-auto doesn't depend on Mathlib and therefore doesn't know about Reals

example (x y z : Nat) : x < y → y < z → x < z := by
  querySMT -- TODO: Look into incorporating `zify` in the preprocessing (or a better version of it)
-/

-- **TODO** Investigate whether `a < b` and `b > a` are equally usable
-- for querySMT (there might be a world where GT appears in the problem but lean-auto
-- and/or cvc5 normalize it to LT, resulting in an issue)

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
theorem test (Even Odd : Int → Prop)
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
  querySMT

-------------------------------------------------------------------------------------------
-- `Nat` proof reconstruction not yet supported
set_option auto.smt true in
set_option auto.smt.solver.name "cvc5" in
set_option auto.smt.dumpHints true in
example (x y z : Nat) : x ≤ y → y ≤ z → x ≤ z := by
  have : Int.ofNat y ≤ Int.ofNat z → ¬Int.ofNat y + -Int.ofNat 1 * Int.ofNat z ≥ Int.ofNat 1 := sorry
  have : ¬Int.ofNat x ≤ Int.ofNat z → Int.ofNat x + -Int.ofNat 1 * Int.ofNat z ≥ Int.ofNat 1 := sorry
  have : Int.ofNat x ≤ Int.ofNat y → ¬Int.ofNat x + -Int.ofNat 1 * Int.ofNat y ≥ Int.ofNat 1 := sorry
  have :
    let _let_1 := -Int.ofNat 1 * Int.ofNat z;
    (Int.ofNat x + -Int.ofNat 1 * Int.ofNat y ≥ Int.ofNat 1 ∨ Int.ofNat y + _let_1 ≥ Int.ofNat 1) ∨
      ¬Int.ofNat x + _let_1 ≥ Int.ofNat 1 :=
    sorry
  have :
    let _let_1 := Int.ofNat y + -Int.ofNat 1 * Int.ofNat z;
    _let_1 < Int.ofNat 1 → _let_1 ≤ Int.ofNat 0 :=
    sorry
  zify at * -- This line is necessary to get `duper` to work **TODO** Add this to `querySMT`
  duper [*]
