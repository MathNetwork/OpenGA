import Theorems.Thm_OpenGA_nonempty_surgeryComparisonProcess_of_measuredData
import Solutions.Sol_OpenGA_nonempty_surgeryComparisonProcess_of_measuredData

open Lean in
run_meta do
  let target ← getConstInfo `OpenGA.nonempty_surgeryComparisonProcess_of_measuredData
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "Target mismatch"
  logInfo "Exact target type matched"
