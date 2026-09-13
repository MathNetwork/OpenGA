import OpenGALib.Interoperability.RicciFlow.ScalarLowerBound
import OpenGALib.Interoperability.RicciFlow.SurfaceAreaVariation
import OpenGALib.Interoperability.RicciFlow.SurfaceAreaCoordinates
import OpenGALib.Interoperability.RicciFlow.WidthComparison

/-!
Transitive axiom audit of the geometric scalar bound and local area variation.
The upstream PDE inputs are audited alongside every new public declaration.
Run from the OpenGALib root with `lake env lean` on this file.
-/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Name := [
    ``DifferentialGeometry.PDE.RicciFlow.scalar_curvature_evolution,
    ``DifferentialGeometry.PDE.RicciFlow.scalarRegOfSmooth,
    ``DifferentialGeometry.PDE.RicciFlow.scalar_curvature_lower_bound_of_scalarEvolution_of_regularity,
    ``DifferentialGeometry.PDE.RicciFlow.metricDerivAt,
    ``DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul,
    ``OpenGA.RicciFlow.scalar_sq_div_three_le_ricciNorm,
    ``OpenGA.RicciFlow.scalar_lower_barrier,
    ``OpenGA.RicciFlow.scalar_lower_bound,
    ``OpenGA.RicciFlow.scalar_lower_bound_normalized,
    ``OpenGA.RicciFlow.scalarMinimum,
    ``OpenGA.RicciFlow.exists_scalar_eq_minimum,
    ``OpenGA.RicciFlow.scalarMinimum_lower_bound,
    ``OpenGA.RicciFlow.SurfaceParameter,
    ``OpenGA.RicciFlow.surfaceTangent,
    ``OpenGA.RicciFlow.surfaceMetricMatrix,
    ``OpenGA.RicciFlow.surfaceDensity,
    ``OpenGA.RicciFlow.surfaceMetricMatrix_comp,
    ``OpenGA.RicciFlow.surfaceDensity_comp,
    ``OpenGA.RicciFlow.patchArea_comp,
    ``OpenGA.RicciFlow.surfaceRicciMatrix,
    ``OpenGA.RicciFlow.surfaceRicciTrace,
    ``OpenGA.RicciFlow.hasDerivAt_surfaceDensity,
    ``OpenGA.RicciFlow.patchArea,
    ``OpenGA.RicciFlow.hasDerivAt_patchArea,
    ``OpenGA.RicciFlow.eventually_width_slope_lt,
    ``OpenGA.RicciFlow.lifetime_le_of_width_comparison]
  for name in declarations do
    unless (← getEnv).contains name do
      throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"Passed axiom audit for {declarations.length} declarations."
