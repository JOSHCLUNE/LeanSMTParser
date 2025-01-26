import Lean

namespace PremiseSelection

open Lean Meta

register_option hammer.premiseSelection.printTimeInformation : Bool := {
  defValue := false
  descr := "Whether to print the total time taken by premise retrieval"
}

def getPrintTimeInformation (opts : Options) : Bool :=
  hammer.premiseSelection.printTimeInformation.get opts

def getPrintTimeInformationM : CoreM Bool := do
  let opts ← getOptions
  return getPrintTimeInformation opts

register_option hammer.premiseSelection.apiUrl : String := {
  defValue := "http://52.206.70.13/retrieve"
  descr := "The URL of the premise retrieval API"
}

def getPremiseSelectionApiUrl (opts : Options) : String :=
  hammer.premiseSelection.apiUrl.get opts

def getPremiseSelectionApiUrlM : CoreM String := do
  let opts ← getOptions
  return getPremiseSelectionApiUrl opts

/-- From tactic_benchmark.lean -/
def withSeconds [Monad m] [MonadLiftT BaseIO m] (act : m α) : m (α × Float) := do
  let start ← IO.monoNanosNow
  let a ← act
  let stop ← IO.monoNanosNow
  return (a, (stop - start).toFloat / 1000000000)

structure PremiseSuggestion where
  name : Name
  score : Float
deriving Repr, FromJson

instance : ToString PremiseSuggestion where
  toString p := s!"{p.name} ({p.score})"

instance : ToMessageData PremiseSuggestion where
  toMessageData p := s!"{p.name} ({p.score})"

def retrievePremisesCore (apiUrl : String) (state : String) (importedModules localPremises : Option (Array Name))
  (k : Nat) : IO (Array PremiseSuggestion) := do
  let data := Json.mkObj [
    ("state", .str state),
    ("imported_modules", toJson importedModules),
    ("local_premises", toJson localPremises),
    ("k", .num (.fromNat k)),
  ]
  let curlArgs := #[
    "-X", "POST",
    "--header", "Content-Type: application/json",
    "--user-agent", "LeanProver (https://leanprover-community.github.io/)",
    "--data-raw", data.compress,
    apiUrl
  ]
  let out ← IO.Process.output { cmd := "curl", args := curlArgs }

  if out.exitCode != 0 then
    IO.throwServerError <|
      "Could not send API request to retrieve premises. " ++
      s!"curl exited with code {out.exitCode}:\n{out.stderr}"

  match Json.parse out.stdout >>= fromJson? with
  | .ok result => return result
  | .error e => IO.throwServerError <|
      s!"Could not parse premise retrieval output (error: {e})\nRaw output:\n{out.stdout}"

def retrievePremises (goal : MVarId) (k : Nat := 16) : MetaM (Array PremiseSuggestion) := do
  let env ← getEnv
  let state := (← ppGoal goal).pretty
  let importedModules := env.allImportedModuleNames
  let localPremises := env.constants.map₂.foldl (fun arr name _ => arr.push name) #[]
  let apiUrl ← getPremiseSelectionApiUrlM
  -- above preparation is ~1ms?

  let (s, t) ← withSeconds do
    retrievePremisesCore apiUrl state importedModules localPremises k
  if ← getPrintTimeInformationM then logInfo s!"Time: {t}"

  return s

elab "retrieve_premises" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  logInfo <| repr (← retrievePremises goal)

/-
#time
#eval retrievePremisesCore "
K : Type u
inst✝ : Field K
f g : K[X]
hfm : f.Monic
hgm : g.Monic
hf : Irreducible f
hg : ∀ (E : Type u) [inst : Field E] [inst_1 : Algebra K E] (x : E),
  minpoly K x = f → Irreducible (Polynomial.map (algebraMap K ↥K⟮x⟯) g - C (AdjoinSimple.gen K x))
hf' : f.natDegree ≠ 0
hg' : g.natDegree ≠ 0
H₁ : f.comp g ≠ 0
H₂ : ¬IsUnit (f.comp g)
p : K[X]
hp₁ : Irreducible p
hp₂ : p ∣ f.comp g
this✝ : Fact (Irreducible p)
Kx : Type u := AdjoinRoot p
this : Module.Finite K (AdjoinRoot p) := PowerBasis.finite (powerBasis (Irreducible.ne_zero hp₁))
⊢ (aeval ((aeval (root p)) g)) f = 0
" none none 8

/--
info: #[{ name := `Nat.add_comm, score := 0.619485 }, { name := `Nat.add_assoc, score := 0.617578 },
  { name := `Nat.zero_add, score := 0.550185 }, { name := `Nat.add_zero, score := 0.531990 },
  { name := `Nat.one_mul, score := 0.440850 }, { name := `Nat.le_add_left, score := 0.438798 },
  { name := `Nat.succ_add, score := 0.423647 }, { name := `Nat.add_succ, score := 0.416499 }]
-/
example (a b : Nat) : a + b = b + a := by
  retrieve_premises
  apply Nat.add_comm
-/

end PremiseSelection
