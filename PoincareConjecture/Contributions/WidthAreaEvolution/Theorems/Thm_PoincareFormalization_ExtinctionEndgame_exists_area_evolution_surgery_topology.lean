import Definitions.Def_OpenGA_SurgeryAreaEvolutionData
import Definitions.Def_OpenGA_ExtinctionWidthControl
set_option autoImplicit false
open Set Filter
open scoped Topology
open OpenGA
universe u


theorem PoincareFormalization.ExtinctionEndgame.exists_area_evolution_surgery_topology
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧
      ∀ T : ℝ, 0 < T → E.components T ≠ [] →
        Nonempty (SurgeryAreaEvolutionData W T) := by sorry
