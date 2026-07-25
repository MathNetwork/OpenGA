import Lake
open Lake DSL

package OpenGALib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "v4.32.1"

@[default_target]
lean_lib OpenGALib where
  roots := #[`OpenGALib]
  globs := #[.andSubmodules `OpenGALib]
