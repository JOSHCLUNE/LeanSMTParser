import Mathlib.Tactic
import Auto

open Lean Meta Elab Tactic Parser Tactic Auto

namespace ProveSMTLemma

syntax (name := proveSMTLemma) "proveSMTLemma" : tactic

@[tactic proveSMTLemma]
def evalProveSMTLemma : Tactic
| `(proveSMTLemma | proveSMTLemma%$stxRef) => withMainContext do
  let tacList := [
    ← `(tactic| simp),
    ← `(tactic| rfl),
    ← `(tactic| tauto),
    ← `(tactic| linarith only),
    ← `(tactic| omega),
    ← `(tactic| aesop),
  ]
  -- `loop` iterates through `allTacs`, collecting the tactics that made any progress in `usedTacs`, then
  -- returns the sublist of tactics that can be used to close the goal (if there exists one)
  let rec loop (allTacs : List Syntax.Tactic) (usedTacs : Array Syntax.Tactic)
    : TacticM (Option (Array Syntax.Tactic)) := do
    match allTacs with
    | [tac] =>
      let tacSucceeded ←
        tryCatch
          (do let _ ← evalTactic tac; pure true)
          (fun _ => pure false)
      if tacSucceeded then return some (usedTacs.push tac)
      else return none
    | tac :: tacs =>
      let tacSucceeded ←
        tryCatch
          (do let _ ← evalTactic tac; pure true)
          (fun _ => pure false)
      if tacSucceeded then
        if (← getGoals).isEmpty then return usedTacs.push tac
        else loop tacs (usedTacs.push tac)
      else loop tacs usedTacs
    | [] => throwError "loop error in proveSMTLemma" -- Should never occur because [tac] is base case
  match ← loop tacList #[] with
  | some tacsUsed =>
    let tacticSeq ← `(tacticSeq| $tacsUsed*)
    addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
  | none => throwError "proveSMTLemma was unable to prove this goal"
| _ => throwUnsupportedSyntax

end ProveSMTLemma
