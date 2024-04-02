import SMTParser.QuerySMT

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true

example (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  querySMT -- Succeeds

example (x y z a b : Int) : (x < y → y < z → x < z) ∧ (a < b ∨ b ≤ a) := by
  querySMT -- Succeeds but the result is longer

example {a b c d e f : Int} (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  querySMT -- Lemma reconstruction fails for one of the lemmas

example : ∀ x : Int, ∀ y : Int, ∀ z : Int, x ≤ y → y ≤ z → x ≤ z := by
  querySMT -- Fails because I don't apply intros first and because of `✝` issue

example (x y z : Nat) : x < y → y < z → x < z := by
  querySMT -- Fails because I don't have `Nat` support right now

example (x : Int) : ∃ y : Int, y < x := by
  querySMT -- This problem is (essentially) considered to be a preprocessing step

example (x : Int) (h : ∃ y : Int, y * y = x) : x ≥ 0 := by
  querySMT -- Fails because I haven't implemented the mapping for constructs other than variables

example (x y : Int) (h : x * y ≠ 0) : x ≠ 0 ∧ y ≠ 0 := by
  querySMT -- Lemmas provided by cvc5 appear to be insufficient (also, the second lemma is useless)

example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (4) := by
  have : (1 : Int) + 1 = 2 := by rfl
  have : (1 : Int) + 2 = 3 := by rfl
  have : (1 : Int) + 3 = 4 := by rfl
  duper [*] -- Duper can solve this with the right lemmas

example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (4) := by
  querySMT -- But not with the lemmas provided by cvc5
