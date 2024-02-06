import Lake
open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"93105204453ca14cea9ae0c58bddb6809676db50"

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
