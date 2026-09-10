import Theorems.Thm_PoincareFormalization_ExtinctionEndgame_exists_area_evolution_surgery_topology
import Theorems.Thm_OpenGA_nonempty_measuredSurgeryComparisonData_of_areaEvolution
import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData
import Definitions.Def_OpenGA_ExtinctionWidthControl

set_option autoImplicit false
open OpenGA
universe u

theorem solution
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧
      ∀ T : ℝ, 0 < T → E.components T ≠ [] →
        Nonempty (MeasuredSurgeryComparisonData W T) := by
  obtain ⟨E, W, hW, hdata⟩ := PoincareFormalization.ExtinctionEndgame.exists_area_evolution_surgery_topology M
  refine ⟨E, W, hW, ?_⟩
  intro T hT hnonempty
  obtain ⟨D⟩ := hdata T hT hnonempty
  exact OpenGA.nonempty_measuredSurgeryComparisonData_of_areaEvolution D
