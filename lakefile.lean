import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0-patch1"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "efd479f7da1a29aa7a77aaead0198e7947830a7a"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.15.0"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
