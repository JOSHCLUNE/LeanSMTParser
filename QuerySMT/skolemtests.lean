import QuerySMT

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/joshClune/Desktop/temp.smt"

-- set_option linter.setOption false

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true
set_option trace.auto.smt.parseTermErrors true
set_option auto.getHints.failOnParseError true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors true

set_option trace.skolemizeAll.debug false
set_option pp.proofs true

example (P : Int → Prop) (h : ∃ x : Int, P x) : ∃ y : Int, P y := by
  skolemizeAll
  apply Exists.intro sk0
  assumption

example (P : Int → Prop) (Q : Int → Prop)
  (h1 : ∃ x : Int, P x) (h2 : ∃ x : Int, Q x) : ∃ x : Int × Int, (P x.1) ∧ (Q x.2) := by
  skolemizeAll
  apply Exists.intro (sk0, sk1)
  exact ⟨h1, h2⟩

example (P : Int → Prop) (Q : Int → Prop)
  (h1 : ∃ x : Int, ∃ y : Int, P x ∧ Q y) : ∃ x : Int × Int, (P x.1) ∧ (Q x.2) := by
  skolemizeAll
  apply Exists.intro (sk0, sk1)
  exact h1

example (P : Int → Prop) (Q : Int → Prop) (R : Int → Prop)
  (h : ∃ s : String, ∃ x : Int, ∃ y : Int, ∃ z : Int, P x → Q y ∧ R z) :
  ∃ a : Int × Int × Int, P a.1 → Q a.2.1 ∧ R a.2.2 := by
  skolemizeAll
  apply Exists.intro (sk1, sk2, sk3)
  exact h

example (x : Int) (h : ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  skolemizeAll
  have smtLemma0 : ¬¬Int.ofNat 2 * sk0 = Int.ofNat 1 → False := by
    simp
    omega
  duper [*]

example (x : Int) (h : True ∧ ∃ y : Int, 2 * y = x) : ∃ y : Int, 2 * y = x := by
  skolemizeAll
  apply Exists.intro sk0
  exact h.2

example (h : ∃ x : Int, True ∧ ∃ y : Int, 2 * y = x) : ∃ x : Int, ∃ y : Int, 2 * y = x := by
  skolemizeAll
  apply Exists.intro sk0
  apply Exists.intro sk1
  exact h.2

example (h : ∃ x : Int, (∃ y : Int, ∃ z : Int, z * y = x) ∧ True) :
  ∃ x : Int, ∃ y : Int, ∃ z : Int, z * y = x := by
  skolemizeAll
  apply Exists.intro sk0
  apply Exists.intro sk1
  apply Exists.intro sk2
  exact h.1

example (h : ∃ x : Int, True ∧ ∃ y : Int, True ∧ ∃ z : Int, z * y = x) :
  ∃ x : Int, ∃ y : Int, ∃ z : Int, z * y = x := by
  skolemizeAll
  apply Exists.intro sk0
  apply Exists.intro sk1
  apply Exists.intro sk2
  exact h.2.2

example (h : ∃ x : Int, (∃ y : Int, x = y) ∧ (∃ z : Int, x ≠ z)) :
  ∃ x : Int, (∃ y : Int, x = y) ∧ (∃ z : Int, x ≠ z) := by
  skolemizeAll
  apply Exists.intro sk0
  constructor
  . apply Exists.intro sk1
    exact h.1
  . apply Exists.intro sk2
    exact h.2

example (h : ∀ x : Int, ∃ y : Int, x = y) :
  ∀ x : Int, ∃ y : Int, x = y := by
  skolemizeAll
  intro x
  apply Exists.intro (sk0 x)
  specialize h x
  exact h

example (h : ∀ x : Int, ∀ y : Int, ∃ z : Int, (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x)) :
  ∀ x : Int, ∀ y : Int, ∃ z : Int, (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x) := by
  skolemizeAll
  intros x y
  specialize h x y
  apply Exists.intro (sk0 x y)
  exact h

example (h : ∀ x : Int, (∃ y : Int, y < x) ∧ (∃ y : Int, y > x)) :
  ∀ x : Int, (∃ y : Int, y < x) ∧ (∃ y : Int, y > x) := by
  skolemizeAll
  intro x
  specialize h x
  constructor
  . apply Exists.intro (sk0 x)
    exact h.1
  . apply Exists.intro (sk1 x)
    exact h.2

example (h : ∀ x : Int, (∀ y : Int, ∃ z : Int, z = x + y) ∧ (∀ y : Int, ∃ z : Int, x = z + y)) :
  ∀ x : Int, (∀ y : Int, ∃ z : Int, z = x + y) ∧ (∀ y : Int, ∃ z : Int, x = z + y) := by
  skolemizeAll
  intro x
  specialize h x
  constructor
  . intro y
    apply Exists.intro (sk0 x y)
    exact h.1 y
  . intro y
    apply Exists.intro (sk1 x y)
    exact h.2 y

example (h : ∀ x : Int, ∃ y : Int, x = y) :
  ∀ x : Int, ∃ y : Int, x = y := by
  skolemizeAll
  intro x
  apply Exists.intro (sk0 x)
  specialize h x
  exact h

example (h : ∀ x : Int, ∃ y : Int, ∃ z : Int, y < x ∧ x < z) :
  ∀ x : Int, ∃ y : Int, ∃ z : Int, y < x ∧ x < z := by
  skolemizeAll
  intro x
  apply Exists.intro (sk0 x)
  apply Exists.intro (sk1 x)
  exact h x

example (h : ∀ x : Int, ∃ y : Int, ∃ z : Int, y < x ∧ x < z) :
  ∀ x : Int, ∃ y : Int, ∃ z : Int, y < x ∧ x < z := by
  skolemizeAll
  intro x
  apply Exists.intro (x - 1)
  apply Exists.intro (x + 1)
  omega

example (h : ∀ x : Int, ∃ y : Int, y < x) : ∃ z : Int, z < 0 := by
  skolemizeAll
  have smtLemma0 : (¬∃ smtd_2, smtd_2 < Int.ofNat 0) → False := by
    simp
    exact ⟨-1, by decide⟩
  duper [*]

example (P : Int → Prop) (Q : Prop) (h : Q ∧ ∃ x : Int, P x) :
  Q ∨ ∃ x : Int, P x := by
  skolemizeAll
  right
  apply Exists.intro sk0
  exact h.2

example (h : ∀ x : Int, ∀ y : Int, ∃ x' : Int, ∃ y' : Int, x' = x + 1 ∧ y' = y + 1) :
  ∀ x : Int, ∀ y : Int, ∃ x' : Int, ∃ y' : Int, x' = x + 1 ∧ y' = y + 1 := by
  skolemizeAll
  intro x y
  apply Exists.intro (sk0 x y)
  apply Exists.intro (sk1 x y)
  exact h x y

set_option trace.skolemizeAll.debug true in
example (P : Int → Prop) (Q : Prop) (h : Q ∨ ∃ x : Int, P x) :
  Q ∨ ∃ x : Int, P x := by
  skolemizeAll -- **TODO** Or support
  sorry
