import Theorems.Thm_PoincareFormalization_homotopyEquiv_sphere_three
import Theorems.Thm_PoincareFormalization_homotopy_three_sphere_nonempty_homeomorph

open scoped ContinuousMap

theorem solution (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  obtain ⟨e⟩ := PoincareFormalization.homotopyEquiv_sphere_three M
  exact PoincareFormalization.homotopy_three_sphere_nonempty_homeomorph M e
