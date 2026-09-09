import Lean
import Theorems.Thm_DifferentialGeometry_Geometry_Riemannian_VolumeComparison_lintegral_cross_le
import Solutions.Sol_DifferentialGeometry_Geometry_Riemannian_VolumeComparison_lintegral_cross_le
open Lean in
run_meta do
  let target ← Lean.getConstInfo `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_cross_le
  let solved ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq target.type solved.type do
    throwError "The solution type does not match its target"
  let axioms ← Lean.collectAxioms `solution
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in axioms do
    unless allowed.contains name do
      throwError "Unexpected proof axiom: {name}"
  Lean.logInfo m!"Exact target type matched; proof axioms: {axioms}"
