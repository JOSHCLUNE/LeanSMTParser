import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "707dc8fa41f68062efd90fd6aae24a93681bf8f6"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
