import Theorems.Thm_OpenGA_nonempty_widthComparisonData_of_areaEvolution
import Solutions.Sol_OpenGA_nonempty_widthComparisonData_of_areaEvolution
open Lean in
run_meta do
  let target ← getConstInfo `OpenGA.nonempty_widthComparisonData_of_areaEvolution
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "Target mismatch"
  logInfo "Exact target type matched"
