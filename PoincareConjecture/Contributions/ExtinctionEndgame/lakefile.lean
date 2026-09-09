import Lake
open Lake DSL

package ExtinctionEndgame where
  packagesDir := "../../../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]

require OpenGALib from "../../.."

@[default_target]
lean_lib Endgame where
  roots := #[`OpenProblems, `Reduction]
