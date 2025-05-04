import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.18.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "8c6873cadf17101b26061f2a409fc10474c93f5c"

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
