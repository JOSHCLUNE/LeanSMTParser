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
set_option duper.throwPortfolioErrors true
set_option querySMT.filterOpt 3

example (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  querySMT

set_option auto.smt.dumpHints.limitedRws false in
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
  querySMT -- varName: smti_0 maps to an atom other than term

example (P : Int × Int → Prop) (h : ∀ x : Int, ∀ y : Int, P (x, y)) :
  ∀ z : Int × Int, P z := by
  querySMT

-- set_option trace.duper.printProof true in
example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  -- (h0 : ∀ x : Int, Pos x → ¬ Zero x)
  -- (h1 : ∀ x : Int, Neg x → ¬ Zero x)
  -- (h2 : ∀ x : Int, Zero x → (¬ Pos x) ∧ (¬ Neg x))
  -- (h3 : ∀ x : Int, Pos x ∨ Neg x ∨ Zero x)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  -- (h6 : Zero 0)
  /- (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) -/ : Pos 2 := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  -- (h0 : ∀ x : Int, Pos x → ¬ Zero x)
  -- (h1 : ∀ x : Int, Neg x → ¬ Zero x)
  -- (h2 : ∀ x : Int, Zero x → (¬ Pos x) ∧ (¬ Neg x))
  -- (h3 : ∀ x : Int, Pos x ∨ Neg x ∨ Zero x)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  -- (h6 : Zero 0)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Pos 2 := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  -- (h0 : ∀ x : Int, Pos x → ¬ Zero x)
  -- (h1 : ∀ x : Int, Neg x → ¬ Zero x)
  -- (h2 : ∀ x : Int, Zero x → (¬ Pos x) ∧ (¬ Neg x))
  -- (h3 : ∀ x : Int, Pos x ∨ Neg x ∨ Zero x)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1))
  -- (h6 : Zero 0)
  /- (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) -/ : Neg (-2) := by
  querySMT

-- set_option auto.smt.save true in
example (Pos Neg Zero : Int → Prop)
  -- (h0 : ∀ x : Int, Pos x → ¬ Zero x)
  -- (h1 : ∀ x : Int, Neg x → ¬ Zero x)
  -- (h2 : ∀ x : Int, Zero x → (¬ Pos x) ∧ (¬ Neg x))
  -- (h3 : ∀ x : Int, Pos x ∨ Neg x ∨ Zero x)
  (h4 : ∀ x : Int, Neg x → Neg (x - 1))
  (h5 : Neg (-1))
  -- (h6 : Zero 0)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Neg (-2) := by
  querySMT

example (Pos Neg Zero : Int → Prop)
  -- (h0 : ∀ x : Int, Pos x → ¬ Zero x)
  -- (h1 : ∀ x : Int, Neg x → ¬ Zero x)
  -- (h2 : ∀ x : Int, Zero x → (¬ Pos x) ∧ (¬ Neg x))
  -- (h3 : ∀ x : Int, Pos x ∨ Neg x ∨ Zero x)
  (h4 : ∀ x : Int, Neg (- x) → Neg (-(x + 1)))
  (h5 : Neg (-1))
  -- (h6 : Zero 0)
  /- (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) -/ : Neg (- 2) := by
  querySMT

-- set_option auto.smt.save true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Neg (- x) → Neg ((- x) - 1))
  (h5 : Neg (-1)) : Neg (- 2) := by
  querySMT

/-
example (x y : Real) : x < y ∨ y ≤ x := by
  querySMT -- Fails because lean-auto doesn't depend on Mathlib and therefore doesn't know about Reals

example (x y z : Nat) : x < y → y < z → x < z := by
  querySMT -- TODO: Look into incorporating `zify` in the preprocessing (or a better version of it)
-/

theorem forallExists : ∀ x : Int, ∃ y : Int, x ≤ y := by
  intros x
  have smtLemma0 : (¬∃ smtd_0, x ≤ smtd_0) → False := by proveSMTLemma
  duper [*]
