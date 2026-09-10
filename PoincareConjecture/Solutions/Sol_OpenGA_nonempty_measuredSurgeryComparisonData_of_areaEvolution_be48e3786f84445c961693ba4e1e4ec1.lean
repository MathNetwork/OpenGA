import Theorems.Thm_OpenGA_nonempty_widthComparisonData_of_areaEvolution
import Definitions.Def_OpenGA_SurgeryAreaEvolutionData
set_option autoImplicit false
open Set Filter
open scoped Topology
open OpenGA

namespace OpenGA
noncomputable def SurgeryAreaEvolutionData.toMeasured {W T : ℝ}
    (D : SurgeryAreaEvolutionData W T) : MeasuredSurgeryComparisonData W T where
  volumeControl := D.volumeControl
  events_inside := D.events_inside
  finalTime_pos := D.finalTime_pos
  scalar := D.scalar
  width := D.width
  scalar_cont := D.scalar_cont
  width_cont := D.width_cont
  scalar_initial := D.scalar_initial
  width_initial := D.width_initial
  width_nonneg := D.width_nonneg
  scalar_slope := D.scalar_slope
  scalar_jump := D.scalar_jump
  width_jump := D.width_jump
  comparison := by
    intro a b hab t ht
    obtain ⟨A⟩ := D.area_evolution a b hab t ht
    exact nonempty_widthComparisonData_of_areaEvolution A


end OpenGA
theorem solution {W T : ℝ}
    (D : SurgeryAreaEvolutionData W T) : Nonempty (MeasuredSurgeryComparisonData W T) := ⟨D.toMeasured⟩
