import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "a500ea7a5b9eca0ecaa7b4a229786a61b2707d30"

package QuerySMT {
  precompileModules := true
}

lean_lib QuerySMT

lean_lib Hammer

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
