import Lake
open Lake DSL

package ColdingMinicozziReview where
  packagesDir := "../../../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]

require OpenGALib from "../../.."

@[default_target]
lean_lib Review where
  roots := #[`ReuseAudit, `ScalarAndAreaAudit, `ClosedSurfaceAreaAudit]
