import QuerySMT
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

-- set_option trace.auto.inspectMVarAssignments true in
-- set_option trace.auto.printLemmas true in
-- set_option trace.auto.runAuto.printLemmas true in
-- set_option trace.auto.lamReif.printProofs true in
-- set_option trace.auto.lamReif.prep.printResult true in
-- set_option trace.duper.printProof true in
-- set_option trace.duper.proofReconstruction true in
set_option querySMT.includeSMTHintsInSetOfSupport true in -- This bug only arises on this problem when this is set to `true`
set_option trace.duper.setOfSupport.debug true in
example (Even Odd : Int → Prop)
  (h1 : ∀ x : Int, ∀ y : Int, Odd (x) → Odd (y) → Even (x + y))
  (h2 : ∀ x : Int, ∀ y : Int, Odd (x) → Even (y) → Odd (x + y))
  (h3 : ∀ x : Int, Even (x) ↔ ¬ Odd (x))
  (h4 : Odd (1)) : Even (10) := by
  querySMT
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

set_option querySMT.includeSMTHintsInSetOfSupport true in
example (Pos Neg Zero : Int → Prop)
  (h4 : ∀ x : Int, Pos x → Pos (x + 1))
  (h5 : Pos 1)
  (h7 : ∀ x : Int, Pos x ↔ Neg (- x)) : Pos 2 := by
  sorry -- querySMT -- `querySMT` succeeds but the tactic suggestion fails

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

-------------------------------------------------------------------------------------------
-- Duper's preprocessing doesn't preserve knowledge about Booleans, causing it to fail on the Bool equivalent
-- of a problem even though Duper can solve the Prop version

mutual
  inductive IntTree where
    | node : Int → IntTreeList → IntTree

  inductive IntTreeList where
    | nil  : IntTreeList
    | cons : IntTree → IntTreeList → IntTreeList
end

open IntTree IntTreeList

mutual
  def contains1 : IntTree → Int → Prop
  | node x l, y => x = y ∨ contains2 l y

  def contains2 : IntTreeList → Int → Prop
  | nil, _ => False
  | cons t l, y => contains1 t y ∨ contains2 l y
end

mutual
  def contains3 : IntTree → Int → Bool
  | node x l, y => x == y || contains4 l y

  def contains4 : IntTreeList → Int → Bool
  | nil, _ => false
  | cons t l, y => contains3 t y || contains4 l y
end

-- `Prop` version
example : contains1 (node a (cons (node b nil) (cons (node c nil) nil))) x ↔ (x = a ∨ x = b ∨ x = c) := by
  duper [*, contains1, contains2]

-- `Bool` version
example : contains3 (node a (cons (node b nil) (cons (node c nil) nil))) x ↔ (x = a ∨ x = b ∨ x = c) := by
  sorry -- duper [*, contains3, contains4] -- Fails

-------------------------------------------------------------------------------------------
-- `skolemizeAll` issue based on `List.forall_mem_zipIdx` (from Mathlib.Data.List.Enum.lean)

/- Work has been done to improve `skolemizeAll`'s ability to get along with `getElem`, but
   `skolemizeAll` still fails on `forall_mem_zipIdx` when `α` is not known to be Inhabited -/

set_option pp.proofs true in
open List in
theorem forall_mem_zipIdx {l : List α} {n : ℕ} {p : α × ℕ → Prop} :
    (∀ x ∈ l.zipIdx n, p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (l[i], n + i) := by
  apply Classical.byContradiction
  intro negGoal
  rw [not_iff] at negGoal
  simp at negGoal
  skolemizeAll
  sorry

/- When I minimize the above problem, I basically get this. And from this problem, it's clear that
   we shouldn't really expect it to be possible for `skolemizeAll` to succeed because we can't infer
   from `h` that `α` is inhabited unless `q` is False -/
set_option pp.proofs true in
open List in
theorem forall_mem_zipIdx2 {α : Type} {q : Prop} {l : List α} {n : ℕ} {p : α × ℕ → Prop}
  (h : (∃ x x_1, (x, x_1) ∈ l.zipIdx n ∧ ¬p (x, x_1)) ∨ q) : False := by
  skolemizeAll
  -- Unknown free variable is `e1Hyp` corresponding to `∃ x x_1, (x, x_1) ∈ l.zipIdx n ∧ ¬p (x, x_1)` from
  -- `skolemizeOne` or case. There's no real getting around this problem I think
  sorry

-- Ultimately, I think it is inevitable that this fails because we can't know from `h` that
-- `α` is inhabited unless we also know that `q` is False

-- Adding `Inhabited α` is now sufficient to make `skolemizeAll` succeed
open List in
theorem forall_mem_zipIdxWithInhabited [Inhabited α] {l : List α} {n : ℕ} {p q : α × ℕ → Prop} :
    (∀ x : α × Nat, q x → p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (l[i], n + i) := by
  apply Classical.byContradiction
  intro negGoal
  skolemizeAll
  sorry

-------------------------------------------------------------------------------------------

-- set_option duper.collectDatatypes false
-- set_option querySMT.disableExpensiveRules true
-- set_option includeDatatypeRules false

-- This example requires either `duper.collectDatatypes` to be true or `querySMT.ignoreHints` to be false
set_option querySMT.ignoreHints false in
example : ∀ l : List Nat, l = [] ∨ ∃ n : Nat, ∃ l' : List Nat, l = n :: l' := by
  intros l
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 : [] = l ∨ ∃ (arg1 : List ℕ) (arg0 : ℕ), l = arg0 :: arg1 := by sorry
  duper [negGoal] [smtLemma0]

-- This example requires `includeExpensiveRules` to be true or `includeDatatypesRules` to be true or `querySMT.ignoreHints` to be false
set_option includeDatatypeRules false in
set_option querySMT.ignoreHints false in
example : [] ≠ [1] := by
  querySMT
  duper {includeExpensiveRules := false}

-- This example requires `querySMT.ignoreHints` to be false or to enable datatype acyclicity rules
set_option includeDatatypeRules true in
set_option includeUnsafeAcyclicity true in
example : ∀ l : List Nat, ∀ n : Nat, l ≠ n :: l := by
  duper

-- This example requires `includeDatatypesRules` to be true or `querySMT.ignoreHints` to be false
set_option querySMT.ignoreHints false in
example (n m : Nat) (h : [n] = [m]) : n = m := by
  querySMT

-------------------------------------------------------------------------------------------

structure myStructure where
  field1 : Int
  field2 : Int

open myStructure

-- **NOTE** AC facts need to be disabled for this example to work
-- **NOTE** `grind` fails to prove one of the hints that cvc5 generates for this problem
-- **TODO** Make an evaluation that checks whether `grind` is successful in proving all of the hints cvc5 generates
set_option querySMT.includeACFacts false in
example (sum : myStructure → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myStructure) : ∃ y : myStructure, sum y > sum x := by
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 :
    (∀ (_i _i_0 : ℤ), sum { field1 := _i, field2 := _i_0 : myStructure } = _i + _i_0) →
      ∀ (_i _i_0 : ℤ), _i = -Int.ofNat 1 * _i_0 + sum { field1 := _i, field2 := _i_0 : myStructure } :=
    by grind
  have smtLemma1 :
    (¬∃ (_m_0 : myStructure), sum x < sum _m_0) →
      ∀ (_m_0 : myStructure), sum x + -Int.ofNat 1 * sum _m_0 ≥ Int.ofNat 0 :=
    by grind
  have smtLemma2 :
    have _let_1 := x.field2;
    have _let_2 := x.field1;
    have _let_3 := { field1 := _let_2, field2 := _let_1 : myStructure };
    have _let_4 := sum _let_3;
    have _let_5 := sum { field1 := _let_2, field2 := _let_4 : myStructure };
    have _let_6 := sum x;
    have _let_7 := sum { field1 := _let_1, field2 := Int.ofNat 2 : myStructure };
    ((((¬x = _let_3 ∨ ¬_let_2 = -Int.ofNat 1 * _let_1 + _let_4) ∨ ¬_let_1 = -Int.ofNat 2 + _let_7) ∨
          ¬_let_6 + -Int.ofNat 1 * _let_7 ≥ Int.ofNat 0) ∨
        ¬_let_2 = -Int.ofNat 1 * _let_4 + _let_5) ∨
      ¬_let_6 + -Int.ofNat 1 * _let_5 ≥ Int.ofNat 0 := by
    -- `grind` alone fails to solve this
    clear negGoal smtLemma0 smtLemma1
    aesop
    grind
  have smtLemma3 : -Int.ofNat 1 * Int.ofNat 2 = -Int.ofNat 2 := by grind
  duper [hSum, negGoal] [smtLemma0, smtLemma1, smtLemma2, smtLemma3]

-------------------------------------------------------------------------------------------

--`querySMT` succeeds but proof reconstruction fails

set_option querySMT.includeSMTHintsInSetOfSupport true in -- Needs to be set to true for this example to succeed
example (x : Nat) (h : ∃ y : Nat, 2 * y = x) : x ≠ 1 := by
  querySMT


-------------------------------------------------------------------------------------------

-- This example generates a selector that contains `sorry` when `t` is not known to be inhabited
-- **TODO** Look into `Auto.buildSelector`

inductive myType2 (t : Type)
| const3 : t → myType2 t
| const4 : t → myType2 t

open myType2

set_option duper.collectDatatypes true in
example (t : Type) (x : myType2 t) : ∃ y : t, x = const3 y ∨ x = const4 y := by
  apply @Classical.byContradiction
  intro negGoal
  obtain ⟨_const3__sel0, _const3__sel0Fact⟩ :
    ∃ (_const3__sel0 : myType2 t → t), ∀ (arg0 : t), _const3__sel0 (const3 arg0) = arg0 :=
    by
    apply
      Exists.intro (myType2.rec (motive := fun (_ : myType2 t) => t) (fun (arg0 : t) => arg0) fun (arg0 : t) => sorry)
    intros
    rfl
  have smtLemma0 :
    (¬∃ (_t_0 : t), x = const3 _t_0 ∨ x = const4 _t_0) →
      ∀ (BOUND_VARIABLE_4948 : t), ¬x = const4 BOUND_VARIABLE_4948 :=
    by grind
  have smtLemma1 :
    (¬∃ (_t_0 : t), x = const3 _t_0 ∨ x = const4 _t_0) →
      ∀ (BOUND_VARIABLE_4941 : t), ¬x = const3 BOUND_VARIABLE_4941 :=
    by grind
  duper [negGoal, _const3__sel0Fact] [smtLemma0, smtLemma1]

-- Trying to construct a better looking example where the `sorry` is more appropriate

inductive mixedList (α β : Type _)
| hd1 : α → mixedList α β → mixedList α β
| hd2 : β → mixedList α β → mixedList α β
| nil : mixedList α β
deriving Inhabited

-- `querySMT` can only prove this when `α` and `β` are known to be inhabited
-- (because `duper` can only prove it when `α` and `β` are known to be inhabited)
set_option trace.duper.timeout.debug true in
set_option duper.collectDatatypes true in
example (α β : Type _) [Inhabited α] [Inhabited β] (l : mixedList α β) (hl : l ≠ .nil) :
  (∃ x : α, ∃ tl : mixedList α β, l = .hd1 x tl) ∨
  (∃ x : β, ∃ tl : mixedList α β, l = .hd2 x tl) := by
  have ⟨«_mixedList.hd1__sel0», «_mixedList.hd1__sel0Fact»⟩ :
    ∃ («_mixedList.hd1__sel0» : mixedList α β → α),
      ∀ (arg0 : α) (arg1 : mixedList α β), «_mixedList.hd1__sel0» (mixedList.hd1 arg0 arg1) = arg0 :=
    by
    apply
      Exists.intro
        (mixedList.rec (motive := fun (_ : mixedList α β) => α)
          (fun (arg0 : α) (arg1 : mixedList α β) (_ : α) => arg0)
          (fun (arg0 : β) (arg1 : mixedList α β) (_ : α) => default) default)
    intros
    rfl
  have ⟨«_mixedList.hd1__sel1», «_mixedList.hd1__sel1Fact»⟩ :
    ∃ («_mixedList.hd1__sel1» : mixedList α β → mixedList α β),
      ∀ (arg0 : α) (arg1 : mixedList α β), «_mixedList.hd1__sel1» (mixedList.hd1 arg0 arg1) = arg1 :=
    by
    apply
      Exists.intro
        (mixedList.rec (motive := fun (_ : mixedList α β) => mixedList α β)
          (fun (arg0 : α) (arg1 _ : mixedList α β) => arg1) (fun (arg0 : β) (arg1 _ : mixedList α β) => default)
          default)
    intros
    rfl
  have ⟨«_mixedList.hd2__sel0», «_mixedList.hd2__sel0Fact»⟩ :
    ∃ («_mixedList.hd2__sel0» : mixedList α β → β),
      ∀ (arg0 : β) (arg1 : mixedList α β), «_mixedList.hd2__sel0» (mixedList.hd2 arg0 arg1) = arg0 :=
    by
    apply
      Exists.intro
        (mixedList.rec (motive := fun (_ : mixedList α β) => β)
          (fun (arg0 : α) (arg1 : mixedList α β) (_ : β) => default)
          (fun (arg0 : β) (arg1 : mixedList α β) (_ : β) => arg0) default)
    intros
    rfl
  have ⟨«_mixedList.hd2__sel1», «_mixedList.hd2__sel1Fact»⟩ :
    ∃ («_mixedList.hd2__sel1» : mixedList α β → mixedList α β),
      ∀ (arg0 : β) (arg1 : mixedList α β), «_mixedList.hd2__sel1» (mixedList.hd2 arg0 arg1) = arg1 :=
    by
    apply
      Exists.intro
        (mixedList.rec (motive := fun (_ : mixedList α β) => mixedList α β)
          (fun (arg0 : α) (arg1 _ : mixedList α β) => default) (fun (arg0 : β) (arg1 _ : mixedList α β) => arg1)
          default)
    intros
    rfl
  have :
    ¬((∃ (_α_0 : α) (_m_0 : mixedList α β), l = mixedList.hd1 _α_0 _m_0) ∨
          ∃ (_β_0 : β) (_m_1 : mixedList α β), l = mixedList.hd2 _β_0 _m_1) →
      ∀ (_β_0 : β) (_m_1 : mixedList α β), ¬l = mixedList.hd2 _β_0 _m_1 :=
    sorry
  have :
    ¬((∃ (_α_0 : α) (_m_0 : mixedList α β), l = mixedList.hd1 _α_0 _m_0) ∨
          ∃ (_β_0 : β) (_m_1 : mixedList α β), l = mixedList.hd2 _β_0 _m_1) →
      ∀ (_α_0 : α) (_m_0 : mixedList α β), ¬l = mixedList.hd1 _α_0 _m_0 :=
    sorry
  have : ¬l = mixedList.nil → ¬mixedList.nil = l := sorry
  have :
    (∃ (arg1 : mixedList α β) (arg0 : β), l = mixedList.hd2 arg0 arg1) →
      l = mixedList.hd2 («_mixedList.hd2__sel0» l) («_mixedList.hd2__sel1» l) :=
    sorry
  have :
    (mixedList.nil = l ∨ ∃ (arg1 : mixedList α β) (arg0 : α), l = mixedList.hd1 arg0 arg1) ∨
      ∃ (arg1 : mixedList α β) (arg0 : β), l = mixedList.hd2 arg0 arg1 :=
    sorry
  have :
    (∃ (arg1 : mixedList α β) (arg0 : α), l = mixedList.hd1 arg0 arg1) →
      l = mixedList.hd1 («_mixedList.hd1__sel0» l) («_mixedList.hd1__sel1» l) :=
    sorry
  have :
    (∀ (_α_0 : α) (_m_0 : mixedList α β), ¬l = mixedList.hd1 _α_0 _m_0) →
      ¬l = mixedList.hd1 («_mixedList.hd1__sel0» l) («_mixedList.hd1__sel1» l) :=
    sorry
  have :
    (∀ (_β_0 : β) (_m_1 : mixedList α β), ¬l = mixedList.hd2 _β_0 _m_1) →
      ¬l = mixedList.hd2 («_mixedList.hd2__sel0» l) («_mixedList.hd2__sel1» l) :=
    sorry
  sorry
  -- querySMT -- Unfortunately, `querySMT` doesn't need the selectors output

-------------------------------------------------------------------------------------------
-- cvc5 can solve this if we don't skolemize but fails to solve this after calling `skolemizeAll`

set_option auto.smt.dumpHints false in
set_option auto.smt.trust true in
example (Even Odd : Int → Prop) (z1 z2 : Int)
  (h1 : ∀ x : Int, Even (x) ↔ ∃ y : Int, x = 2 * y)
  (h2 : ∀ x : Int, Odd (x) ↔ ∃ y : Int, x = 2 * y + 1)
  (h3 : Odd z1) (h4 : Odd z2) : Even (z1 + z2) := by
  auto [*]

example (Even Odd : Int → Prop) (z1 z2 : Int)
  (h1 : ∀ x : Int, Even (x) ↔ ∃ y : Int, x = 2 * y)
  (h2 : ∀ x : Int, Odd (x) ↔ ∃ y : Int, x = 2 * y + 1)
  (h3 : Odd z1) (h4 : Odd z2) : Even (z1 + z2) := by
  apply Classical.byContradiction
  intro negGoal
  skolemizeAll
  sorry -- autoGetHints fails

-------------------------------------------------------------------------------------------
-- Duper bug (produces a wrong proof)

#print Tree

example {α : Type} (x y : α) : Tree.node x Tree.nil Tree.nil = Tree.node y Tree.nil Tree.nil ↔ x = y := by
  duper
