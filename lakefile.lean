import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "2f5a1f6ed919a62c183bf07ff13f838baf7cc41d"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
