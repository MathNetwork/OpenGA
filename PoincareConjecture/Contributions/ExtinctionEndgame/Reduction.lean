import OpenProblems

/-!
# The formal finite-extinction reduction of the Poincare goal

The proofs in this file have no holes of their own, but depend on the four
explicit open theorems in `OpenProblems.lean`. They are conditional proof
sketches, not proofs of the Poincare conjecture or of geometric extinction.

Dependency chain:
  geometric construction (open) -> width-controlled component evolution
  -> finite extinction -> connected-sum reconstruction
  -> simply connected endgame (three open topology lemmas) -> mission goal.

The auxiliary definitions and analytic/topological iteration theorems in
OpenGALib have no project axioms or proof holes. The distinction is checked
by `Audit.lean` and the reusable-library regression check.
-/

namespace PoincareFormalization.ExtinctionEndgame

open OpenGA

universe u

/-- **Conditional reduction.** The constructed evolution becomes extinct.
The only open input here is its geometric construction. -/
theorem exists_finitely_extinct_surgery_topology (M : ClosedThreeManifold.{u})
    [SimplyConnectedSpace M] :
    ∃ E : SurgeryTopologyEvolution M, E.FiniteExtinction := by
  obtain ⟨E, W, _, hcontrol⟩ := exists_width_controlled_surgery_topology M
  exact ⟨E, E.finiteExtinction_of_width_control hcontrol⟩

/-- **Conditional reduction.** Combine the covering-space base case with
the three open connected-sum topology lemmas. -/
theorem nonempty_homeomorph_sphere_of_standard_decomposition
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M]
    (h : ConnectedSumClosure ClosedThreeManifold.IsStandardFactor M) :
    Nonempty (M ≃ₜ SphereThree) := by
  exact nonempty_homeomorph_sphere_of_standard_connectedSum
    simply_connected_factors_of_connected_sum not_simply_connected_sphere_handle
    nonempty_homeomorph_sphere_of_connected_sum_spheres h inferInstance

/-- **Conditional reduction.** This is the explicit link from finite
extinction to a sphere. The evolution's reconstruction records are used;
mere disappearance of an arbitrary family of spaces is insufficient. -/
theorem nonempty_homeomorph_sphere_of_finite_extinction
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M]
    (E : SurgeryTopologyEvolution M) (hextinct : E.FiniteExtinction) :
    Nonempty (M ≃ₜ SphereThree) :=
  nonempty_homeomorph_sphere_of_standard_decomposition M
    (E.topology_from_extinction hextinct)

/-- **Conditional reduction.** The exact hypotheses and conclusion of the
platform's topological Poincare goal. There is no added smoothness,
second-countability, positive-curvature, or geometric-existence hypothesis:
constructing the necessary geometric data is the first explicit open node.
This theorem still depends on all four open inputs. -/
theorem nonempty_homeomorph_sphere_three (M : Type u) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  let N : ClosedThreeManifold := {
    Carrier := M
    topology := inferInstance
    hausdorff := inferInstance
    charts := inferInstance
    compact := inferInstance
    connected := inferInstance
  }
  have : SimplyConnectedSpace N := inferInstanceAs (SimplyConnectedSpace M)
  obtain ⟨E, hextinct⟩ := exists_finitely_extinct_surgery_topology N
  exact nonempty_homeomorph_sphere_of_finite_extinction N E hextinct

end PoincareFormalization.ExtinctionEndgame
