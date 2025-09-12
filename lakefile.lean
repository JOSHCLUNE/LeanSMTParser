import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "18d7f15b17d9b3071d74ec8d5e56f2f954ceec0a"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.22.0"

package QuerySMT {
  precompileModules := false
  preferReleaseBuild := false
}

@[default_target]
lean_lib QuerySMT

lean_lib Hammer
