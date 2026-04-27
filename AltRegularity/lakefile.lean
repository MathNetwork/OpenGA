import Lake
open Lake DSL

package AltRegularity where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require OpenGALib from ".."

@[default_target]
lean_lib AltRegularity where
  globs := #[.andSubmodules `AltRegularity]
