import Lake
open Lake DSL

package OpenGADrafts where
  packagesDir := "../../../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]

require OpenGALib from "../../.."

@[default_target]
lean_lib LocalHomeomorph
