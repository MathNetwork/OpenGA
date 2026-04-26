import Lake
open Lake DSL

package «altregularity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5fc0241932dd6d465bc5549308cc39011772293a"

require GeometricMeasureTheory from "GeometricMeasureTheory"
require MinMax from "MinMax"
require Regularity from "Regularity"

@[default_target]
lean_lib AltRegularity where
  globs := #[.andSubmodules `AltRegularity]
