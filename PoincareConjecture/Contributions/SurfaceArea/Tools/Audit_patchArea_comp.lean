import Solutions.Sol_OpenGA_RicciFlow_patchArea_comp
import Theorems.Thm_OpenGA_RicciFlow_patchArea_comp

open Lean in
run_meta do
  let target ← getConstInfo `OpenGA.RicciFlow.patchArea_comp
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "The solution does not match the exact target type"
  logInfo "Exact solution type passed."
