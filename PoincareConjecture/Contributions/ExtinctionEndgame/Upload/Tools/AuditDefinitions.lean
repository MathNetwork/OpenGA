import Definitions.Def_OpenGA_CoordinateBallConnectedSum
import Definitions.Def_OpenGA_SurgeryTopologyEvolution
import Definitions.Def_OpenGA_ExtinctionWidthControl
import Definitions.Def_OpenGA_WidthExtinctionTime

import Lean.Util.CollectAxioms
open Lean in
run_meta do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless (`Definitions).isPrefixOf moduleName do continue
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do throwError "Unexpected axiom {axiomName} in {name}"
    count := count + 1
  logInfo m!"Audited {count} definition-module declarations: only standard logical axioms."
