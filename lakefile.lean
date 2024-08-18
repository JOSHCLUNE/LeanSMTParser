import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.9.1"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "dev"

package QuerySMT {
  -- add package configuration options here
}

lean_lib QuerySMT {
  -- add library configuration options here
}

@[default_target]
lean_exe «querysmt» {
  root := `Main
}
