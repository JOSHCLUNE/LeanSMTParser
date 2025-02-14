import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "3303ab6fd8e454ca5ffa92cae2d7001d54bd86cd"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
