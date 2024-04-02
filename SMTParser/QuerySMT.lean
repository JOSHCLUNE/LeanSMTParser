import Auto
import Duper
import Mathlib.Tactic

open Lean Auto Elab Tactic

syntax (name := querySMT) "querySMT" autoinstr hints (uord)* : tactic

@[tactic querySMT]
def evalQuerySMT : Tactic
| `(querySMT | querySMT%$stxRef $instr $hints $[$uords]*) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let instr ← parseInstr instr
    match instr with
    | .none =>
      let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
      let lemmas ← runAutoGetHints lemmas inhFacts
      IO.println s!"Auto found hints. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      let lemmasStx ← lemmas.mapM (fun lemExp => PrettyPrinter.delab lemExp)
      if lemmasStx.length = 0 then
        IO.println "SMT solver did not generate any theory lemmas"
      else
        let mut tacticsArr : Array Syntax.Tactic := #[]
        for lemmaStx in lemmasStx do
          tacticsArr := tacticsArr.push $ ← `(tactic| have : $lemmaStx := by simp; omega)
        tacticsArr := tacticsArr.push $ ← `(tactic| duper [*])
        let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $tacticsArr*)
        withOptions (fun o => (o.set `pp.analyze true).set `pp.funBinderTypes true) $
          addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax
