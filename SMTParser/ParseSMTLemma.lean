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
    Tactic.TryThis.addSuggestion parseSMTLemmaStxRef suggestion (← getRef)
    /-
    -- let test ← `(Parser.Term.haveDecl| test : Nat := 0)
    -- let suggestion ← `(Parser.Tactic.tacticSeq| have $test:haveDecl; case _ test => exact trivial)
    let suggestion ←`(Lean.Parser.Tactic.tacticSeq| have : exp := sorry; have : Nat := sorry)
    addTryThisTacticSeqSuggestion makeHavesStxRef suggestion (← getRef)
    -/
  | .malformed .. => throwError "malformed"
  | .incomplete .. => throwError "incomplete"
| _ => throwUnsupportedSyntax

theorem testParseSMTLemma (x y : Int) ( P : Int → Prop) : True := by
  -- parseSMTLemma "(or (not (>= x 0)) (not (>= y 0)) (>= (+ x y) 0))"
  have : (¬x ≥ Int.ofNat 0 ∨ ¬y ≥ Int.ofNat 0) ∨ x + y ≥ Int.ofNat 0 := sorry

  -- parseSMTLemma "(or (not (exists ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= (+ x y) 0)) (P (+ x y))))"
  have : (¬∃ z, ¬z ≥ Int.ofNat 0 ∨ P z) ∨ ¬x + y ≥ Int.ofNat 0 ∨ P (x + y) := sorry

  -- parseSMTLemma "(not (exists ((z Int)) (not (= z z))))"
  -- have : ¬∃ z, ¬z = z := sorry -- TODO: This example fails because Lean can't synthesize z's type

  -- parseSMTLemma "(or (not (forall ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= (+ x y) 0)) (P (+ x y))))"
  have : (¬∀ (z : Int), ¬z ≥ Int.ofNat 0 ∨ P z) ∨ ¬x + y ≥ Int.ofNat 0 ∨ P (x + y) := sorry
  exact trivial

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
    addTryThisTacticSeqSuggestion parseSMTLemmasFromFileStxRef tacticSeq (← getRef)
| _ => throwUnsupportedSyntax

theorem testParseSMTLemmasFromFile (a b x y : Int) ( P : Int → Prop) : True := by
  -- parseSMTLemmasFromFile "/Users/joshClune/Desktop/CVC5 Test Files/simple-example-output.txt"
  have : (¬x ≥ Int.ofNat 0 ∨ ¬y ≥ Int.ofNat 0) ∨ x + y ≥ Int.ofNat 0 := sorry

  -- parseSMTLemmasFromFile "/Users/joshClune/Desktop/CVC5 Test Files/simple-example2-output.txt"
  have : (¬a ≥ Int.ofNat 0 ∨ ¬b ≥ Int.ofNat 0) ∨ a + b ≥ Int.ofNat 0 := sorry
  have : (¬x ≥ Int.ofNat 0 ∨ ¬y ≥ Int.ofNat 0) ∨ x + y ≥ Int.ofNat 0 := sorry
  exact trivial
