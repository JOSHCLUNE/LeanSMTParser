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
set_option auto.getHints.failOnParseError true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors true
set_option querySMT.filterOpt 3

set_option trace.skolemizeAll.debug true

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

example (x : Int) (h : ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  skolemizeAll
  querySMT

example (x : Int) (h : True ∧ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  rcases h with ⟨h1, ⟨h2, h3⟩⟩
  querySMT
  -- This is causing a parse error because of a rewrite involving smtd_0
  -- (original command has smtd_0 in a quanitifer, but the rewrite just refers to smtd_0)

example (h : ∀ x : Int, ∃ y : Int, y < x) : ∃ z : Int, z < 0 := by
  -- Can't call `cases` or `rcases` on `h` but I still need to skolemize it
  querySMT

example (x : Int) (h : False ∨ ∃ y : Int, 2 * y = x) : x ≠ 1 := by
  querySMT
