import SMTParser.SMTParser
import Mathlib.Tactic

open Lean Elab Tactic Auto Parser Lexer Meta SMTTerm Tactic

syntax (name := parseSMTLemma) "parseSMTLemma" str : tactic
syntax (name := parseSMTLemmasFromFile) "parseSMTLemmasFromFile" str : tactic

-- Note: This code is adapted from Aesop's Util/Basic.lean file
def addTryThisTacticSeqSuggestion (ref : Syntax) (suggestion : TSyntax ``Lean.Parser.Tactic.tacticSeq)
  (origSpan? : Option Syntax := none) : MetaM Unit := do
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq suggestion
  let msgText := fmt.pretty (indent := 0) (column := 0)
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn map range
    dbg_trace s!"indent: {indent}, column: {column}"
    let text := fmt.pretty (width := Std.Format.defWidth) indent column
    let suggestion := {
      -- HACK: The `tacticSeq` syntax category is pretty-printed with each line
      -- indented by two spaces (for some reason), so we remove this
      -- indentation.
      suggestion := .string $ dedent text
      toCodeActionTitle? := some λ _ => "Create lemmas"
      messageData? := some msgText
      preInfo? := "  "
    }
    Lean.Meta.Tactic.TryThis.addSuggestion ref suggestion (origSpan? := origSpan?)
      (header := "Try this:\n")
where
  dedent (s : String) : String :=
    s.splitOn "\n"
    |>.map (λ line => line.dropPrefix? "  " |>.map (·.toString) |>.getD line)
    |> String.intercalate "\n"

@[tactic parseSMTLemma]
def evalParseSMTLemma : Tactic
| `(tactic| parseSMTLemma%$parseSMTLemmaStxRef $s) => withMainContext do
  let lctx ← getLCtx
  let mut symbolMap : HashMap String Expr := HashMap.empty
  for decl in lctx.decls do
    let some decl := decl
      | continue
    symbolMap := symbolMap.insert decl.userName.toString (mkFVar decl.fvarId)
  match ← lexTerm s.getString 0 {} with
  | .complete e _ =>
    let exp ← parseTerm e symbolMap
    let expStx ← PrettyPrinter.delab exp
    let suggestion ← `(tactic| have : $expStx := sorry)
    withOptions (fun o => (o.set `pp.analyze true).set `pp.funBinderTypes true) $
      Tactic.TryThis.addSuggestion parseSMTLemmaStxRef suggestion (← getRef)
  | .malformed .. => throwError "malformed"
  | .incomplete .. => throwError "incomplete"
| _ => throwUnsupportedSyntax

@[tactic parseSMTLemmasFromFile]
def evalParseSMTLemmasFromFile : Tactic
| `(tactic| parseSMTLemmasFromFile%$parseSMTLemmasFromFileStxRef $file) => withMainContext do
  let lctx ← getLCtx
  let mut symbolMap : HashMap String Expr := HashMap.empty
  for decl in lctx.decls do
    let some decl := decl
      | continue
    symbolMap := symbolMap.insert decl.userName.toString (mkFVar decl.fvarId)
  let fileReader ← IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped, cmd := "cat", args := #[file.getString]}
  let fileFirstLine ← fileReader.stdout.getLine
  if !(String.isPrefixOf "unsat" fileFirstLine) then throwError "SMT output is not unsat (fileFirstLine: {fileFirstLine})"
  let fileOutput ← fileReader.stdout.readToEnd
  let [_, fileOutput] := fileOutput.splitOn "Theory lemmas:"
    | throwError "Error parsing theory lemmas output"
  let [fileOutput, _] := fileOutput.splitOn "Instantiations:"
    | throwError "Error parsing theory lemmas output"
  let lemmaTerms ← lexAllTerms fileOutput 0 []
  let lemmaExps ← lemmaTerms.mapM (fun lemTerm => parseTerm lemTerm symbolMap)
  let lemmasStx ← lemmaExps.mapM (fun lemExp => PrettyPrinter.delab lemExp)
  if lemmasStx.length = 0 then
    IO.println "SMT solver did not generate any theory lemmas"
  else
    let mut tacticsArr : Array Syntax.Tactic := #[]
    for lemmaStx in lemmasStx do
      tacticsArr := tacticsArr.push $ ← `(tactic| have : $lemmaStx := sorry)
    let tacticSeq ← `(tacticSeq| $tacticsArr*)
    withOptions (fun o => (o.set `pp.analyze true).set `pp.funBinderTypes true) $
      addTryThisTacticSeqSuggestion parseSMTLemmasFromFileStxRef tacticSeq (← getRef)
| _ => throwUnsupportedSyntax

set_option pp.funBinderTypes true in
theorem testParseSMTLemma (x y : Int) ( P : Int → Prop) : True := by
  have : ¬x ≥ Int.ofNat 0 ∧ ¬y ≥ Int.ofNat 0 → x + y ≥ Int.ofNat 0 := by sorry

  -- parseSMTLemma "(= 0.0 0.0)"
  have : (¬x ≥ Int.ofNat 0 ∨ ¬y ≥ Int.ofNat 0) ∨ x + y ≥ Int.ofNat 0 := sorry

  -- parseSMTLemma "(or (not (exists ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= (+ x y) 0)) (P (+ x y))))"
  have : (¬∃ z, ¬z ≥ Int.ofNat 0 ∨ P z) ∨ ¬x + y ≥ Int.ofNat 0 ∨ P (x + y) := sorry

  -- This doesn't work unless the user uses `set_option pp.funBinderTypes true`. As far as I can tell, setting this option
  -- in `parseSMTLemma` isn't sufficient. I think the answer is to just have a tooltip advising users to enable pp.funBinderTypes
  -- if the produced suggestion gives the error "failed to infer binder type"
  have : ¬∃ (z : ℤ), z = z := sorry
  have : ¬∃ (z : ℤ), z = z := sorry
  -- have : ¬∃ z, ¬z = z := sorry -- TODO: This example fails because Lean can't synthesize z's type

  -- parseSMTLemma "(or (not (forall ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= (+ x y) 0)) (P (+ x y))))"
  have : (¬∀ (z : Int), ¬z ≥ Int.ofNat 0 ∨ P z) ∨ ¬x + y ≥ Int.ofNat 0 ∨ P (x + y) := sorry
  exact trivial

theorem testParseSMTLemmasFromFile (a b x y : Int) ( P : Int → Prop) : True := by
  -- parseSMTLemmasFromFile "/Users/joshClune/Desktop/CVC5 Test Files/simple-example-output.txt"
  -- have : (¬x ≥ Int.ofNat 0 ∨ ¬y ≥ Int.ofNat 0) ∨ x + y ≥ Int.ofNat 0 := sorry

  -- parseSMTLemmasFromFile "/Users/joshClune/Desktop/CVC5 Test Files/new-simple-example-output.txt"
  have : x ≥ Int.ofNat 0 ∧ y ≥ Int.ofNat 0 → x + y ≥ Int.ofNat 0 := by
    simp
    omega

  exact trivial

example (x y : Int) : x ≥ 0 → y ≥ 0 → x + y ≥ 0 := by omega
example (x y : Int) : x ≥ 0 ∧ y ≥ 0 → x + y ≥ 0 := by omega

example (x y : Int) : (¬x ≥ Int.ofNat 0 ∨ ¬y ≥ Int.ofNat 0) ∨ x + y ≥ Int.ofNat 0 := by
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero, ge_iff_le, not_le] -- This simp call is necessary
  omega

example (x y : Int) : x ≥ Int.ofNat 0 ∧ y ≥ Int.ofNat 0 → x + y ≥ Int.ofNat 0 := by
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero, ge_iff_le, and_imp] -- This simp call is necessary
  omega
