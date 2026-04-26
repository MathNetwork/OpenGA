import Lake
open Lake DSL

package «altregularity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib AltRegularity where
  globs := #[.submodules `AltRegularity]
