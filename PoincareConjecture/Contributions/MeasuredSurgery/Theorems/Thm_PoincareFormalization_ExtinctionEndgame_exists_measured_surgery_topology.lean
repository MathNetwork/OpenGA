import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData
import Definitions.Def_OpenGA_ExtinctionWidthControl

set_option autoImplicit false
open OpenGA
universe u


theorem PoincareFormalization.ExtinctionEndgame.exists_measured_surgery_topology
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧
      ∀ T : ℝ, 0 < T → E.components T ≠ [] →
        Nonempty (MeasuredSurgeryComparisonData W T) := by sorry
