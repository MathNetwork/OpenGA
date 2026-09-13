import OpenGALib.Riemannian.Surface
import OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea

/-!
Transitive axiom audit for global immersed-surface area and its Ricci-flow
variation. Run from the OpenGALib root with `lake env lean` on this file.
This is a local review entry point, not a Prove2Me publication record.
-/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Name := [
    ``DifferentialGeometry.Geometry.posDef_isVonNBounded,
    ``DifferentialGeometry.cotangentCov_clmSection_smooth_aux,
    ``DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricCLMSmoothAt,
    ``DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace,
    ``DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure,
    ``DifferentialGeometry.Integral.Measure.volume_variation_formula,
    ``OpenGA.Surface.inducedInner,
    ``OpenGA.Surface.inducedInner_apply,
    ``OpenGA.Surface.inducedInner_pos,
    ``OpenGA.Surface.inducedInner_contMDiff,
    ``OpenGA.Surface.inducedMetric,
    ``OpenGA.Surface.inducedMetric_inner,
    ``OpenGA.MetricFamilyRegularOn,
    ``OpenGA.MetricFamilyRegularOn.of_contMDiffAt,
    ``OpenGA.MetricFamilyRegularOn.comp,
    ``OpenGA.totalRiemannianVolume,
    ``OpenGA.hasDerivAt_totalRiemannianVolume_of_regular,
    ``OpenGA.hasDerivAt_totalRiemannianVolume,
    ``OpenGA.Surface.Model,
    ``OpenGA.Surface.areaMeasure,
    ``OpenGA.Surface.area,
    ``OpenGA.Surface.areaMeasure_finite,
    ``OpenGA.Surface.area_eq_measure_univ,
    ``OpenGA.Surface.area_nonneg,
    ``OpenGA.Surface.area_pos,
    ``OpenGA.Surface.surfaceMetricMatrix_inducedMetric,
    ``OpenGA.Surface.surfaceDensity_inducedMetric,
    ``OpenGA.Surface.patchArea_inducedMetric,
    ``OpenGA.RicciFlow.inducedMetric_regularOn,
    ``OpenGA.RicciFlow.inducedRicciMatrix,
    ``OpenGA.RicciFlow.inducedRicciTrace,
    ``OpenGA.RicciFlow.traceTimeDeriv_inducedMetric,
    ``OpenGA.RicciFlow.hasDerivAt_area]
  for name in declarations do
    unless (← getEnv).contains name do
      throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"Passed axiom audit for {declarations.length} declarations."
