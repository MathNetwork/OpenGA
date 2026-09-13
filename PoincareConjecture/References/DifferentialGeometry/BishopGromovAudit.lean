import OpenGALib.Interoperability.BishopGromov

/-!
# Bishop-Gromov axiom audit

Run from the OpenGALib root:
`lake env lean PoincareConjecture/References/DifferentialGeometry/BishopGromovAudit.lean`.

This checks transitive axiom dependencies of the reused upstream results and
the complete public OpenGA interface. Any axiom outside the standard classical
Lean foundations makes the command fail. It does not replace mathematical
review of definitions and hypotheses; see `bishop_gromov_review.json`.
-/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Name := [
    ``DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segBall_vol_rel,
    ``DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segBall_vol_pow,
    ``DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segBall_vol_fin,
    ``DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segBall_area_eq,
    ``DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_Iic_cross,
    ``Riemannian.RiemannianMetric.geodesicBall,
    ``Riemannian.RiemannianMetric.ballVolume,
    ``Riemannian.RiemannianMetric.ballVolume_pos,
    ``Riemannian.RiemannianMetric.ballVolume_lt_top,
    ``Riemannian.RiemannianMetric.ballVolume_mul_modelVolume_le,
    ``Riemannian.RiemannianMetric.antitoneOn_ballVolume_div_modelVolume,
    ``Riemannian.RiemannianMetric.ballVolume_ratio_le,
    ``Riemannian.RiemannianMetric.ballVolume_mul_pow_le,
    ``Riemannian.RiemannianMetric.antitoneOn_ballVolume_div_pow,
    ``Riemannian.RiemannianMetric.ballVolume_mul_radius_le,
    ``Riemannian.RiemannianMetric.ballVolume_two_mul_le]
  for name in declarations do
    unless (← getEnv).contains name do
      throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"Passed axiom audit for {declarations.length} declarations."
