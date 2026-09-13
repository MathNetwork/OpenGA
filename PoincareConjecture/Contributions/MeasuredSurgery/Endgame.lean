import OpenGALib.ComparisonGeometry.MeasuredSurgery
import OpenGALib.Topology.ExtinctionEndgame

set_option autoImplicit false
open OpenGA
universe u

namespace PoincareFormalization.ExtinctionEndgame

/-- **Math.** Open geometric construction: one topological surgery evolution
and one initial width bound, together with measured comparison data at every
positive horizon whose final slice is nonempty. This does not assume the
finiteness of the set of events. Uniform radial lower bounds and the actual
relation of the reference measure to the flow remain geometric obligations. -/
theorem exists_measured_surgery_topology (M : ClosedThreeManifold.{u})
    [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧
      ∀ T : ℝ, 0 < T → E.components T ≠ [] →
        Nonempty (MeasuredSurgeryComparisonData W T) := by
  sorry

/-- **Math.** Reduction of the unchanged active endgame input to measured
comparison data. The proved constructors supply the finite width trace. -/
theorem exists_width_controlled_surgery_topology (M : ClosedThreeManifold.{u})
    [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧ E.HasWidthControl W := by
  obtain ⟨E, W, hW, hdata⟩ := exists_measured_surgery_topology M
  refine ⟨E, W, hW, ?_⟩
  intro T hT hnonempty
  obtain ⟨D⟩ := hdata T hT hnonempty
  obtain ⟨P⟩ := nonempty_surgeryComparisonProcess_of_measuredData D
  exact nonempty_widthComparisonTrace_of_surgeryComparisonProcess P

end PoincareFormalization.ExtinctionEndgame
