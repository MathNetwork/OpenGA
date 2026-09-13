import Verified.patchArea_inducedMetric
open Lean in
run_meta do
  for name in [`DifferentialGeometry.Geometry.posDef_isVonNBounded,
    `DifferentialGeometry.cotangentCov_clmSection_smooth_aux,
    `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd,
    `OpenGA.Surface.inducedInner,
    `OpenGA.Surface.inducedInner_apply,
    `OpenGA.Surface.inducedInner_contMDiff,
    `OpenGA.Surface.inducedInner_pos,
    `OpenGA.Surface.inducedMetric,
    `OpenGA.Surface.inducedMetric_inner,
    `OpenGA.Surface.patchArea_inducedMetric,
    `OpenGA.Surface.surfaceDensity_inducedMetric,
    `OpenGA.Surface.surfaceMetricMatrix_inducedMetric,
    `contMDiffAt_clm_of_pointwise] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
  logInfo "All 13 declarations passed the axiom audit."
