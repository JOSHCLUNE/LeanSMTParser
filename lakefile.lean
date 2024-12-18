import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "dd5c32ec8bd822bc4b80425325a60bbb8a4e8626"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
