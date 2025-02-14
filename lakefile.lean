import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0-patch1"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "fde2ebf85f572a6b4e151ef9b3b35dbebafc7621"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
