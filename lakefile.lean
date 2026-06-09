import Lake
open Lake DSL

package trzk

require optisat from git "https://github.com/lambdaclass/truth_research.git" @ "0439a647fa08fffe7ac445aa92f25ae47dc10d7b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

@[default_target]
lean_lib TRZK

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe trzk where
  root := `Compile
