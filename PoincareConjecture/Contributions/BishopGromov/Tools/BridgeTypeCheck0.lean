import Lean
import Theorems.Thm_OpenGA_RadialSurgeryVolumeBudget_removedVolume_lower
import Solutions.Sol_OpenGA_RadialSurgeryVolumeBudget_removedVolume_lower
open Lean in
run_meta do
  let a ← Lean.getConstInfo `OpenGA.RadialSurgeryVolumeBudget.removedVolume_lower
  let b ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type b.type do
    throwError "Solution type mismatch"
  Lean.logInfo "Exact target type checked"
