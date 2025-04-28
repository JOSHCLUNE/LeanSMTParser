import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "8c3185d2ff48d45ef127b3137e8a6f3f31f8b1a8"

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
