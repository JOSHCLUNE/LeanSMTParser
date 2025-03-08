import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "f9895f953953ff3553ebf2425fefec7c4de539ea"

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
