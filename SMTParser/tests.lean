import SMTParser.QuerySMT

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true

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

example (x y z : Int) : x < y → y < z → x < z := by
  querySMT

example (x y z a b : Int) : (x < y → y < z → x < z) ∧ (a < b ∨ b ≤ a) := by
  querySMT

example {a b c d e f : Int} (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  querySMT -- `proveSMTLemma` is insufficient to prove the theory lemma returned by cvc5

example : True → ∀ x : Int, ∀ y : Int, ∀ z : Int, x ≤ y → y ≤ z → x ≤ z := by
  intros _ x y z
  have smtLemma0 : ¬x ≤ z → x + -Int.ofNat 1 * z ≥ Int.ofNat 1 := by proveSMTLemma
  have smtLemma1 : y ≤ z → ¬y + -Int.ofNat 1 * z ≥ Int.ofNat 1 := by proveSMTLemma
  have smtLemma2 : x ≤ y → ¬x + -Int.ofNat 1 * y ≥ Int.ofNat 1 := by proveSMTLemma
  have smtLemma3 :
    (x + -Int.ofNat 1 * y ≥ Int.ofNat 1 ∨ y + -Int.ofNat 1 * z ≥ Int.ofNat 1) ∨ ¬x + -Int.ofNat 1 * z ≥ Int.ofNat 1 :=
    by proveSMTLemma
  duper [*]

example : ∀ x : Int × Int × Int, x.1 ≤ x.2.1 → x.2.1 ≤ x.2.2 → x.1 ≤ x.2.2 := by
  intros x
  have smtLemma0 : ¬x.1 ≤ x.2.2 → x.1 + -Int.ofNat 1 * x.2.2 ≥ Int.ofNat 1 := by proveSMTLemma
  have smtLemma1 : x.2.1 ≤ x.2.2 → ¬x.2.1 + -Int.ofNat 1 * x.2.2 ≥ Int.ofNat 1 := by proveSMTLemma
  have smtLemma2 : x.1 ≤ x.2.1 → ¬x.1 + -Int.ofNat 1 * x.2.1 ≥ Int.ofNat 1 := by proveSMTLemma
  have smtLemma3 :
    (x.1 + -Int.ofNat 1 * x.2.1 ≥ Int.ofNat 1 ∨ x.2.1 + -Int.ofNat 1 * x.2.2 ≥ Int.ofNat 1) ∨
      ¬x.1 + -Int.ofNat 1 * x.2.2 ≥ Int.ofNat 1 :=
    by proveSMTLemma
  duper [*]

example (x y z : Nat) : x < y → y < z → x < z := by
  querySMT -- TODO: Look into incorporating `zify` in the preprocessing (or a better version of it)

example (x : Int) : ∃ y : Int, y < x := by
  querySMT -- `proveSMTLemma` is insufficient to prove the lemma returned by cvc5 (basically just double-negated goal)

example (x : Int) (h : ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT -- Fails because of skolemization issue

example (x : Int) (h : True ∧ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT -- Fails because of skolemization issue
  -- This example is one in which lean-auto doesn't skolemize but cvc5 does. So I need
  -- to be pretty general with my skolemization
  -- cvc5 will skolemize "top-level" existential quantifiers, though based on this
  -- example, that's presumably "top-level" after some preprocessing/normalization

example (x : Int) (h : False ∨ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT

example (x y : Int) (h : x * y ≠ 0) : x ≠ 0 ∧ y ≠ 0 := by
  querySMT

example : ∀ x : Int, ∀ y : Int, x * y ≠ 0 → x ≠ 0 ∧ y ≠ 0 := by
  intros x y
  have smtLemma0 : y = Int.ofNat 0 → x * y = Int.ofNat 0 := by proveSMTLemma
  have smtLemma1 : x = Int.ofNat 0 → x * y = Int.ofNat 0 := by proveSMTLemma
  duper [*]

-- set_option trace.duper.printProof true in
example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  querySMT

example (x y : Real) : x < y ∨ y ≤ x := by
  querySMT -- Fails because lean-auto doesn't depend on Mathlib and therefore doesn't know about Reals
