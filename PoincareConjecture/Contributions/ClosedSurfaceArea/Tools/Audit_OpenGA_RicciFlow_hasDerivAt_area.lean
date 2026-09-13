import Theorems.Thm_OpenGA_RicciFlow_hasDerivAt_area
import Solutions.Sol_OpenGA_RicciFlow_hasDerivAt_area
import Lean
open Lean in
run_meta do
  let env ← getEnv
  let some target := env.find? `OpenGA.RicciFlow.hasDerivAt_area | throwError "Missing target"
  let some proof := env.find? `solution | throwError "Missing solution"
  let levels := target.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"universe_{i}")
  unless target.levelParams.length == proof.levelParams.length do
    throwError "Universe arity differs"
  unless ← Meta.isDefEq (target.type.instantiateLevelParams target.levelParams levels)
      (proof.type.instantiateLevelParams proof.levelParams levels) do
    throwError "Solution does not match the exact target type"
  logInfo "Exact solution type passed."
