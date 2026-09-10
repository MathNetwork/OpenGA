import Theorems.Thm_PoincareFormalization_ExtinctionEndgame_exists_width_controlled_surgery_topology
import Solutions.Sol_PoincareFormalization_ExtinctionEndgame_exists_width_controlled_surgery_topology
open Lean in
run_meta do
  let target ← getConstInfo `PoincareFormalization.ExtinctionEndgame.exists_width_controlled_surgery_topology
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq target.type proof.type do
    throwError "Target mismatch"
  logInfo "Active endgame target matched exactly"
