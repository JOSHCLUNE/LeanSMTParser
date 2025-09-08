import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "43be1bece7ff58a0168022c39aa223b8e730eca5"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.18.0"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
