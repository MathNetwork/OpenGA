import OpenGALib.Interoperability.RicciFlow.SurfaceAreaComparison
open Lean in
run_meta do
  let axioms ← collectAxioms `OpenGA.RicciFlow.area_sub_le_of_integral_inducedRicciTrace_lower
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "Unexpected axiom: {axioms}"
  logInfo m!"Surface area comparison: {axioms}"
