import Theorems.Thm_PoincareFormalization_surgery_comparison_process_of_not_homeomorph_sphere
import Solutions.Sol_PoincareFormalization_surgery_comparison_process_of_not_homeomorph_sphere

open Lean in
run_meta do
  let target ← getConstInfo `PoincareFormalization.surgery_comparison_process_of_not_homeomorph_sphere
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "Target mismatch"
  logInfo "Exact target type matched"
