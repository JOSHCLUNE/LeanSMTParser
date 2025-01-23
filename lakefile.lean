import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "4dc52f7c6c53625fda3219b1755fa8579ae04b5f"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
