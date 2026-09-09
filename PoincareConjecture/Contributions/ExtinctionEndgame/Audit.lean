import Reduction
import Lean.Util.CollectAxioms

/-! Verify the exact goal type and the explicit boundary of open dependencies. -/

open Lean
open PoincareFormalization.ExtinctionEndgame

-- This is the literal platform goal type, with no geometric assumptions added.
example (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) :=
  nonempty_homeomorph_sphere_three M

run_cmd do
  let env ← getEnv
  let openNodes := #[``exists_width_controlled_surgery_topology,
    ``simply_connected_factors_of_connected_sum,
    ``not_simply_connected_sphere_handle,
    ``nonempty_homeomorph_sphere_of_connected_sum_spheres]
  let cases := #[
    (``exists_finitely_extinct_surgery_topology, #[openNodes[0]!]),
    (``nonempty_homeomorph_sphere_of_finite_extinction,
      #[openNodes[1]!, openNodes[2]!, openNodes[3]!]),
    (``nonempty_homeomorph_sphere_three, openNodes)]
  for (target, expected) in cases do
    let mut pending := [target]
    let mut seen : Std.HashSet Name := {}
    let mut found : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if seen.contains name then continue
      seen := seen.insert name
      if openNodes.contains name then
        found := found.insert name
        continue
      let some ci := env.find? name | throwError "Missing declaration {name}"
      if let .axiomInfo _ := ci then
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
          throwError "Undeclared proof hole or axiom {name} reachable from {target}"
      let value := match ci with
        | .thmInfo t => t.value.getUsedConstants
        | .defnInfo d => d.value.getUsedConstants
        | .opaqueInfo o => o.value.getUsedConstants
        | _ => #[]
      pending := (ci.type.getUsedConstants ++ value).toList ++ pending
    unless found.size == expected.size && expected.all found.contains do
      throwError "Unexpected open dependencies for {target}: {found.toList}"
    logInfo m!"{target}: exactly {found.size} declared open inputs; no other proof holes."

  -- Assert the current status as well: the root remains conditional.
  let rootAxioms ← collectAxioms ``nonempty_homeomorph_sphere_three
  unless rootAxioms.contains ``sorryAx do
    throwError "Expected an open reduction; update this audit if the open nodes are proved"
  logInfo "Exact platform goal type checked. Root status: conditional reduction, not a proof."
