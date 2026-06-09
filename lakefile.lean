import Lake
open Lake DSL

package trzk

require optisat from git "https://github.com/lambdaclass/truth_research.git" @ "0439a647fa08fffe7ac445aa92f25ae47dc10d7b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"
require leanExtensions from git "https://github.com/lambdaclass/lean_extensions.git" @ "a78bc66074108f7f859bf99251c791e8b2cc2e36"

/-- Builds the axiom-guard plugin's shared library so it can be loaded via `plugins`. -/
target axiomGuardPlugin : Dynlib := do
  let some lib ← findLeanLib? `LeanExtensions | error "could not find the `LeanExtensions` lean_lib"
  lib.shared.fetch

@[default_target]
lean_lib TRZK where
  plugins := #[axiomGuardPlugin]

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]
  plugins := #[axiomGuardPlugin]

@[default_target]
lean_exe trzk where
  root := `Compile
  plugins := #[axiomGuardPlugin]
