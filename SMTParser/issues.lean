import SMTParser.QuerySMT

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true
set_option auto.smt.dumpHints.limitedRws true

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/joshClune/Desktop/temp.smt"

set_option linter.setOption false

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

set_option trace.duper.printProof true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1) : Pos 2 := by
  querySMT -- This problem works without `h7`

set_option trace.duper.saturate.debug true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Pos 2 := by
  sorry -- querySMT -- Duper saturates when `h7` is added
  -- Temporary fix: Only pass unsat core to duper
  -- Long term fix: Fix this behavior so duper can handle being given `h7`

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
  querySMT

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg (- x) → Neg ((- x) - 1))
  (h5 : Neg (-1)) : Neg (- 2) := by
  have neededFact : ∀ x : Int, -x = 0 - x := sorry
  querySMT

-------------------------------------------------------------------------------------------
-- `cvc5` doesn't get these

example (l : List Int) : l = [] ∨ ∃ x : Int, ∃ l' : List Int, l = x :: l' := by
 sorry -- querySMT -- `cvc5` times out

example : ∀ x : Int × Int, ∃ y : Int, ∃ z : Int, x = (y, z) := by
  sorry -- querySMT -- `cvc5` times out

-------------------------------------------------------------------------------------------
-- Currently the lean-auto/cvc5 connection can't handle selectors

whatsnew in
inductive myType2 (t : Type)
| const3 : t → myType2 t
| const4 : t → myType2 t

open myType2

example (t : Type) (x : myType2 t) : ∃ y : t, x = const3 y ∨ x = const4 y := by
  duper

example (t : Type) (x : myType2 t) : ∃ y : t, x = const3 y ∨ x = const4 y := by
  sorry -- querySMT

-------------------------------------------------------------------------------------------
-- Bug in lean-auto's monomorphization procedure that causes preprocessing to fail for myProd

structure myStructure where
  field1 : Int
  field2 : Int

open myStructure

-- This example works because `myStructure` is actually a structure (and hence has projections, meaning
-- it does not require handmade selector functions)
example (sum : myStructure → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myStructure) : ∃ y : myStructure, sum y > sum x := by
  querySMT

inductive myProd (t1 t2 : Type _)
| mk : t1 → t2 → myProd t1 t2

open myProd

-- This example can be processing without the have statement, but with the have statement, we get
-- an error from lean-auto
example (sum : myProd Int Int → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myProd Int Int) : ∃ y : myProd Int Int, sum x < sum y := by
  let _mk_sel0 : myProd ℤ ℤ → ℤ := myProd.rec (motive := fun _ => ℤ) fun arg0 arg1 => arg0
  let _mk_sel1 : myProd ℤ ℤ → ℤ := myProd.rec (motive := fun _ => ℤ) fun arg0 arg1 => arg1
  have test : _mk_sel0 x = 0 := sorry -- This triggers `unfoldProj :: myProd is not a structure`
  duper [*] {portfolioInstance := 1}
  -- When I fix this issue, send a PR or issue to lean-auto main since this is something that should be fixed in main too

set_option maxHeartbeats 400000 in
set_option trace.duper.timeout.debug true in
set_option duper.throwPortfolioErrors true in
example (sum : myProd Int Int → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myProd Int Int) : ∃ y : myProd Int Int, sum x < sum y := by
  sorry -- querySMT -- unfoldProj :: myProd is not a structure

-------------------------------------------------------------------------------------------
-- The example works only when duper.collectDatatypes is disabled

set_option duper.collectDatatypes false in
example (x y z a b : Int) : (x < y → y < z → x < z) ∧ (a < b ∨ b ≤ a) := by
  querySMT

-------------------------------------------------------------------------------------------
-- cvc5 yields lemmas containing approximate (`?`) types

example (y : Bool) (myNot : Bool → Bool) (not_not : ∀ x : Bool, myNot (myNot x) = x)
  : y = myNot (myNot y) := by
  querySMT

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
