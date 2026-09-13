import Lake
open Lake DSL

package OpenGALib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    -- Match Prove2Me's Lean v4.33.1 verification environment exactly.
    @ "0df444a360eaa60ab8c11dca51a86af692955474"

require DifferentialGeometry from git
  "https://github.com/qinz1yang/differential-geometry.git"
    -- v0.1.2, pinned to preserve reproducible upstream interfaces.
    @ "1b535dd102b94cc42b107cca27059687888f08b3"

@[default_target]
lean_lib OpenGALib where
  roots := #[`OpenGALib]
  globs := #[.andSubmodules `OpenGALib]
