import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "aab52219c72cb52951832c8e985e1dc3e9497af9"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
