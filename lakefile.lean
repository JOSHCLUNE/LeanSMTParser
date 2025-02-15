import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0-patch1"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "d5dda92539a466c73073ee3eca4ace2aa23215b8"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
