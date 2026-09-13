import Lean
import Theorems.Thm_PoincareFormalization_persistent_comparison_data_of_not_homeomorph_sphere
import Solutions.Sol_PoincareFormalization_persistent_comparison_data_of_not_homeomorph_sphere_surgery_bridge
open Lean in
run_meta do
  let a ← Lean.getConstInfo `PoincareFormalization.persistent_comparison_data_of_not_homeomorph_sphere
  let b ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type b.type do
    throwError "Solution type mismatch"
  Lean.logInfo "Exact target type checked"
