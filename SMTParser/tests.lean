import SMTParser.QuerySMT

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true
set_option auto.smt.dumpHints.limitedRws true

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/joshClune/Desktop/temp.smt"

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true
set_option trace.auto.smt.parseTermErrors true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors false
set_option querySMT.filterOpt 3

set_option duper.collectDatatypes true

-- This is needed to produce suggestions with type annotations in ∀ and ∃ binders
set_option pp.analyze true

example (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  querySMT

example (x y z : Int) : x < y → y < z → x < z := by
  querySMT

example (x y z a b : Int) : (x < y → y < z → x < z) ∧ (a < b ∨ b ≤ a) := by
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
  skolemizeAll
  querySMT

example (x : Int) (h : True ∧ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  skolemizeAll
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

set_option duper.collectDatatypes true in
example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ z : Int × Int, P z := by
  querySMT

example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  querySMT

set_option trace.duper.printProof true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1) : Pos 2 := by
  have smtLemma0 : Int.ofNat 1 + Int.ofNat 1 = Int.ofNat 2 := by proveSMTLemma
  duper [*]

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1)) : Neg (-2) := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1))
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Neg (-2) := by
  querySMT

theorem forallExists : ∀ x : Int, ∃ y : Int, x ≤ y := by
  intros x
  have smtLemma0 : (¬∃ smtd_0, x ≤ smtd_0) → False := by proveSMTLemma
  duper [*]

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
