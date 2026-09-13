import Solutions.Sol_OpenGA_Varifold_mass_ofParametrization_le_energy
import Theorems.Thm_OpenGA_Varifold_mass_ofParametrization_le_energy

import Lean.Util.CollectAxioms
open Lean in
run_meta do
  let target ← getConstInfo `OpenGA.Varifold.mass_ofParametrization_le_energy
  let proof ← getConstInfo `solution
  let levels := target.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"u{i}")
  unless ← Meta.isDefEq (target.type.instantiateLevelParams target.levelParams levels)
      (proof.type.instantiateLevelParams proof.levelParams levels) do
    throwError "Solution type differs from target"
  -- Imported theorem nodes are checked leaves, verified in publication order.
  -- Traverse every other proof and definition, rejecting any fresh sorry/axiom.
  let accepted : Array Name := #[`OpenGA.Varifold.tendsto_weightMeasure_integral,`OpenGA.Varifold.testIntegral_ofWeightedMap,`OpenGA.Varifold.ofWeightedMap_eq_of_plane_eq,`OpenGA.Varifold.testIntegral_ofParametrization,`OpenGA.Varifold.ofParametrization_independent_of_lift,`OpenGA.areaDensity_eq_normDet,`OpenGA.integral_areaDensity_le_energyDensity]
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut pending := [`solution]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if accepted.contains name then continue
    let some ci := env.find? name | throwError "Missing constant {name}"
    if let .axiomInfo _ := ci then
      unless standard.contains name do throwError "Unexpected axiom {name}"
    let value := match ci with
      | .thmInfo t => t.value.getUsedConstants
      | .defnInfo d => d.value.getUsedConstants
      | .opaqueInfo o => o.value.getUsedConstants
      | _ => #[]
    pending := (ci.type.getUsedConstants ++ value).toList ++ pending
  logInfo "Exact target type; no additional axioms beyond the declared theorem dependencies."
