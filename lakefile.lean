import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "4f71a99b24c1b6dc946f258ff94afec41f24ee2d"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.16.0"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
