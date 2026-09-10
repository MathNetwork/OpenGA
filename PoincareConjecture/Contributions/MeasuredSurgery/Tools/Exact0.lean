import Theorems.Thm_OpenGA_MeasuredReferenceBall_anchor_pos
import Solutions.Sol_OpenGA_MeasuredReferenceBall_anchor_pos

open Lean in
run_meta do
  let target ← getConstInfo `OpenGA.MeasuredReferenceBall.anchor_pos
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "Target mismatch"
  logInfo "Exact target type matched"
