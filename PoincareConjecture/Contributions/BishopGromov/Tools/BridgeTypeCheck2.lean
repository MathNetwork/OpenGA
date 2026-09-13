import Lean
import Theorems.Thm_OpenGA_exists_event_free_partition
import Solutions.Sol_OpenGA_exists_event_free_partition
open Lean in
run_meta do
  let a ← Lean.getConstInfo `OpenGA.exists_event_free_partition
  let b ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type b.type do
    throwError "Solution type mismatch"
  Lean.logInfo "Exact target type checked"
