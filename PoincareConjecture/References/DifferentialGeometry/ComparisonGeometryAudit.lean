import OpenGALib.ComparisonGeometry.CurvatureBounds
import OpenGALib.ComparisonGeometry.Volume

/-!
# Comparison geometry foundations audit

Run from the OpenGALib root:
`lake env lean PoincareConjecture/References/DifferentialGeometry/ComparisonGeometryAudit.lean`.

All public definitions and theorems of the four foundation modules are checked
transitively. In particular, a proposition that only compiles using `sorryAx`
or an added geometric axiom fails this audit.
-/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Name := [
    ``Riemannian.RiemannianMetric.geodesicBall,
    ``Riemannian.RiemannianMetric.mem_geodesicBall,
    ``Riemannian.RiemannianMetric.geodesicBall_eq_empty,
    ``Riemannian.RiemannianMetric.geodesicBall_mono,
    ``Riemannian.RiemannianMetric.self_mem_geodesicBall,
    ``Riemannian.RiemannianMetric.geodesicBall_nonempty,
    ``Riemannian.RiemannianMetric.isOpen_geodesicBall,
    ``Riemannian.RiemannianMetric.geodesicBall_subset_of_metric_le,
    ``Riemannian.RiemannianMetric.volumeMeasure,
    ``Riemannian.RiemannianMetric.volumeMeasure_isFiniteMeasure,
    ``Riemannian.RiemannianMetric.volumeMeasure_isOpenPosMeasure,
    ``Riemannian.RiemannianMetric.volumeMeasure_isFiniteMeasureOnCompacts,
    ``Riemannian.RiemannianMetric.volumeMeasure_isLocallyFiniteMeasure,
    ``Riemannian.RiemannianMetric.ballVolume,
    ``Riemannian.RiemannianMetric.ballVolume_mono,
    ``Riemannian.RiemannianMetric.ballVolume_eq_zero,
    ``Riemannian.RiemannianMetric.ballVolume_pos,
    ``Riemannian.RiemannianMetric.ballVolume_pos_iff,
    ``Riemannian.RiemannianMetric.ballVolume_lt_top_of_isCompact_closure,
    ``Riemannian.RiemannianMetric.ballVolume_lt_top_of_le_of_isCompact_closure,
    ``Riemannian.RiemannianMetric.RicciBoundedBelowOn,
    ``Riemannian.RiemannianMetric.RicciBoundedBelowOn.mono,
    ``Riemannian.RiemannianMetric.RicciBoundedBelowOn.of_le,
    ``Riemannian.RiemannianMetric.ricciBoundedBelowOn_union,
    ``Riemannian.RiemannianMetric.ricciBoundedBelowOn_univ,
    ``Riemannian.RiemannianMetric.RicciBoundedBelowOn.geodesicBall_mono]
  for name in declarations do
    unless (← getEnv).contains name do
      throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"Passed axiom audit for {declarations.length} declarations."
