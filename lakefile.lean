import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.7.0-rc2"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "dev"

package SMTParser {
  -- add package configuration options here
}

lean_lib SMTParser {
  -- add library configuration options here
}

@[default_target]
lean_exe «smtparser» {
  root := `Main
}
