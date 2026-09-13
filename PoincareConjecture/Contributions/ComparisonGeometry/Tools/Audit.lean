import Solutions.Sol_Riemannian_RiemannianMetric_isOpen_geodesicBall
import Theorems.Thm_Riemannian_RiemannianMetric_isOpen_geodesicBall

open Lean in
run_meta do
  let target ← getConstInfo `Riemannian.RiemannianMetric.isOpen_geodesicBall
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "The solution does not have the target's exact type"
  for name in [`DifferentialGeometry.SmoothRiemannianMetric, `Riemannian.RiemannianMetric,
    `DifferentialGeometry.riemannianEDistOf, `DifferentialGeometry.riemannianEDistOf_self,
    `Riemannian.RiemannianMetric.geodesicBall, `Riemannian.RiemannianMetric.mem_geodesicBall,
    `Riemannian.RiemannianMetric.geodesicBall_eq_empty, `Riemannian.RiemannianMetric.geodesicBall_mono,
    `Riemannian.RiemannianMetric.self_mem_geodesicBall,
    `Riemannian.RiemannianMetric.geodesicBall_nonempty, `solution] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
  logInfo "Exact target type and all 11 definition/proof axiom dependencies passed."
