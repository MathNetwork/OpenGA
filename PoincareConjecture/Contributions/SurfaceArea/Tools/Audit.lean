import Verified.patchArea_comp

open Lean in
run_meta do
  for name in [`OpenGA.RicciFlow.SurfaceParameter,
    `OpenGA.RicciFlow.surfaceTangent,
    `OpenGA.RicciFlow.surfaceMetricMatrix,
    `OpenGA.RicciFlow.surfaceDensity,
    `OpenGA.RicciFlow.patchArea,
    `OpenGA.RicciFlow.surfaceMetricMatrix_comp,
    `OpenGA.RicciFlow.surfaceDensity_comp,
    `OpenGA.RicciFlow.patchArea_comp] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
  logInfo "All 8 definitions and proofs passed the axiom audit."
