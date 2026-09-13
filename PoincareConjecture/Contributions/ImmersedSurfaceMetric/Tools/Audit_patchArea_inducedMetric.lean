import Solutions.Sol_OpenGA_Surface_patchArea_inducedMetric
import Theorems.Thm_OpenGA_Surface_patchArea_inducedMetric

open Lean in
run_meta do
  let target ← getConstInfo `OpenGA.Surface.patchArea_inducedMetric
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "The solution does not match the exact target type"
  logInfo "Exact solution type passed."
