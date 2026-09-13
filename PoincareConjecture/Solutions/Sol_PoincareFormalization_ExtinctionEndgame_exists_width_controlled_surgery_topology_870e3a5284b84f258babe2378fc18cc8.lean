import Theorems.Thm_PoincareFormalization_ExtinctionEndgame_exists_measured_surgery_topology
import Theorems.Thm_OpenGA_nonempty_surgeryComparisonProcess_of_measuredData
import Theorems.Thm_OpenGA_nonempty_widthComparisonTrace_of_surgeryComparisonProcess
import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData
import Definitions.Def_OpenGA_ExtinctionWidthControl

set_option autoImplicit false
open OpenGA
universe u

theorem solution (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧ E.HasWidthControl W := by
  obtain ⟨E, W, hW, hdata⟩ := PoincareFormalization.ExtinctionEndgame.exists_measured_surgery_topology M
  refine ⟨E, W, hW, ?_⟩
  intro T hT hnonempty
  obtain ⟨D⟩ := hdata T hT hnonempty
  obtain ⟨P⟩ := nonempty_surgeryComparisonProcess_of_measuredData D
  exact nonempty_widthComparisonTrace_of_surgeryComparisonProcess P
