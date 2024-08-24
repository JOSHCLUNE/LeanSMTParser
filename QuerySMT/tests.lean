import QuerySMT

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/joshClune/Desktop/temp.smt"

-- This option lets us ignore warnings about trace options when Mathlib is imported
-- set_option linter.setOption false

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true
set_option trace.auto.smt.parseTermErrors true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors false

set_option duper.collectDatatypes true

example (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  querySMT

example (x y z : Int) : x < y → y < z → x < z := by
  querySMT

example {a b c d e f : Int} (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  querySMT -- `proveSMTLemma` is insufficient to prove the theory lemma returned by cvc5

example : True → ∀ x : Int, ∀ y : Int, ∀ z : Int, x ≤ y → y ≤ z → x ≤ z := by
  querySMT

example : ∀ x : Int × Int × Int, x.1 ≤ x.2.1 → x.2.1 ≤ x.2.2 → x.1 ≤ x.2.2 := by
  querySMT

example (x : Int) : ∃ y : Int, y < x := by
  querySMT -- `proveSMTLemma` is insufficient to prove the lemma returned by cvc5 (basically just double-negated goal)

example (x : Int) (h : ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT

example (x : Int) (h : True ∧ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT

example (x : Int) (h : False ∨ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT

example (x y : Int) (h : x * y ≠ 0) : x ≠ 0 ∧ y ≠ 0 := by
  querySMT

example : ∀ x : Int, ∀ y : Int, x * y ≠ 0 → x ≠ 0 ∧ y ≠ 0 := by
  querySMT

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∃ z : Int × Int, P z := by
  querySMT

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ x : Int, ∀ y : Int, P (x, y) := by
  querySMT

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ z : Int × Int, P z := by
  querySMT -- Note this requires duper.collectDatatypes be set to true

example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1) : Pos 2 := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1)) : Neg (-2) := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1))
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Neg (-2) := by
  querySMT -- `proveSMTLemma` is not able to prove `smtLemma0`

example : ∀ x : Int, ∃ y : Int, x ≤ y := by
  querySMT

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∃ z : Int × Int, P z := by
  querySMT

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ x : Int, ∀ y : Int, P (x, y) := by
  querySMT

set_option duper.collectDatatypes true in
example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ z : Int × Int, P z := by
  querySMT

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ x : Int, ∀ y : Int, P (x, y) := by
  querySMT

inductive myType
| const1 : myType
| const2 : myType

open myType

-- Note, zipperposition can't solve this with lean-auto's current encoding
set_option duper.collectDatatypes true in
example : ∀ x : myType, x = const1 ∨ x = const2 := by
  querySMT

structure myStructure where
  field1 : Int
  field2 : Int

open myStructure

example : myStructure.mk 0 (1 + 1) = myStructure.mk 0 2 := by
  querySMT

example : { field1 := 0, field2 := 0 : myStructure } ≠ ⟨0, 1⟩ := by
  querySMT

example : ∀ l : List Int, ∃ l' : List Int, l' = 0 :: l := by
  querySMT

mutual
  inductive IntTree where
    | node : Int → IntTreeList → IntTree

  inductive IntTreeList where
    | nil  : IntTreeList
    | cons : IntTree → IntTreeList → IntTreeList
end

open IntTree IntTreeList

example (contains1 : IntTree → Int → Prop) (contains2 : IntTreeList → Int → Prop)
  (h1 : ∀ l : IntTreeList, ∀ x : Int, ∀ y : Int, contains1 (node x l) y ↔ (x = y ∨ contains2 l y))
  (h2 : ∀ t : IntTree, ∀ l : IntTreeList, ∀ x : Int, contains2 (cons t l) x ↔ (contains1 t x ∨ contains2 l x))
  (h3 : ∀ x : Int, ¬contains2 nil x) :
  contains1 (node a (cons (node b nil) (cons (node c nil) nil))) x ↔ (x = a ∨ x = b ∨ x = c) := by
  duper [*]

set_option maxHeartbeats 1000000 in
example (contains1 : IntTree → Int → Prop) (contains2 : IntTreeList → Int → Prop)
  (h1 : ∀ l : IntTreeList, ∀ x : Int, ∀ y : Int, contains1 (node x l) y ↔ (x = y ∨ contains2 l y))
  (h2 : ∀ t : IntTree, ∀ l : IntTreeList, ∀ x : Int, contains2 (cons t l) x ↔ (contains1 t x ∨ contains2 l x))
  (h3 : ∀ x : Int, ¬contains2 nil x) :
  contains1 (node a (cons (node b nil) (cons (node c nil) nil))) x ↔ (x = a ∨ x = b ∨ x = c) := by
  querySMT

example (l : List Int) (contains : List Int → Int → Prop)
  (h1 : ∀ x : Int, contains l x → x ≥ 0)
  (h2 : ∃ x : Int, ∃ y : Int, contains l x ∧ contains l y ∧ x + y < 0) : False := by
  querySMT

example (l : List Int) (h1 : ∀ x : Int, l.contains x → x ≥ 0)
  (h2 : ∃ x : Int, ∃ y : Int, l.contains x ∧ l.contains y ∧ x + y < 0) : False := by
  querySMT

example (y : Bool) (p : Prop) (myAnd : Bool → Prop → Prop)
  (hMyAnd : ∀ x : Bool, ∀ q : Prop, myAnd x q = ((x = true) ∧ q)) :
  myAnd true True := by
  querySMT

inductive myType2 (t : Type)
| const3 : t → myType2 t
| const4 : t → myType2 t

inductive myType3
| const5 : Unit → myType3

open myType2 myType3

example (x : myType3) : ∃ y : Unit, x = const5 y := by
  querySMT

example (P : Int → Prop) (h : ∃ x : Int, P x) : ∃ y : Int, P (y + 0) := by
  querySMT

example (x : Int) (h : ∃ y : Int, y + y = x) : ∃ y : Int, y = x / 2 := by
  querySMT

example (y : Bool) (myNot : Bool → Bool) (not_not : ∀ x : Bool, myNot (myNot x) = x)
  : y = myNot (myNot y) := by
  querySMT

example (x : Int) : x * x - 1 = (x + 1) * (x - 1) := by
  querySMT

-- Tests to make sure `h2` is not included in the final duper call
example (p q unrelatedFact : Prop) (h1 : p → q) (h2 : unrelatedFact) (h3 : p) : q := by
  querySMT

-- Tests shadowing behavior (`querySMT` should emit a warning since `h1` is both shadowed and needed)
example (p q unrelatedFact : Prop) (h1 : p → q) (h2 : unrelatedFact) (h1 : p) : q := by
  querySMT

-- Tests shadowing behavior (`querySMT` shouldn't emit a warning since the shadowed `h2` isn't needed)
example (p q unrelatedFact : Prop) (h1 : p → q) (h2 : unrelatedFact) (h2 : p) : q := by
  querySMT

-- Testing that I can introduce and skolemize a fact and still pass it to Duper without issue
example (t1 t2 : Type) (f : t1 → t2) (P : t2 → Prop) (z : t2) (h : P z)
  : (∀ y : t2, ∃ x : t1, f x = y) → ∃ x : t1, P (f x) := by
  querySMT

inductive myProd (t1 t2 : Type _)
| mk : t1 → t2 → myProd t1 t2

open myProd

example (sum : myStructure → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myStructure) : ∃ y : myStructure, sum y > sum x := by
  querySMT

-- Same as above example but uses a structure-like inductive type rather than a structure
example (sum : myProd Int Int → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myProd Int Int) : ∃ y : myProd Int Int, sum x < sum y := by
  querySMT

example (t : Type) (x : myType2 t) : ∃ y : t, x = const3 y ∨ x = const4 y := by
  querySMT

-- Checking to make sure `querySMT` can handle dependencies in initial forall arguments
example : ∀ α : Type, ∀ x : α, x = x := by
  querySMT
