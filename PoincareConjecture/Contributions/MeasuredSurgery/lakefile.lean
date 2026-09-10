import Lake
open Lake DSL

package ComparisonGeometrySubmission where
  packagesDir := "../../../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Definitions where
  globs := #[.submodules `Definitions]

@[default_target]
lean_lib Theorems where
  globs := #[.submodules `Theorems]

@[default_target]
lean_lib Solutions where
  globs := #[.submodules `Solutions]
