import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "dev"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
