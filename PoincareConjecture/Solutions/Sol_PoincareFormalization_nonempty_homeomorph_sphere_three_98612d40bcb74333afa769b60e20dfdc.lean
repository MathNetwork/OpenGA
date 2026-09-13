import Theorems.Thm_PoincareFormalization_covering_is_homeomorph
import Theorems.Thm_PoincareFormalization_spherical_cover_of_finite_fundamental_group
import Mathlib.Analysis.Normed.Module.Connected

namespace PoincareFormalization

/-- The last covering-space step in the spherical-space-form route to Poincaré.
The existence of the covering map is an explicit hypothesis, not proved here. -/
theorem homeomorph_sphere_three_of_cover
    (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M]
    (p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) → M)
    (hp : IsCoveringMap p) :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  have : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hconn := isConnected_sphere
    (E := EuclideanSpace ℝ (Fin (3 + 1))) (by rw [← Module.finrank_eq_rank]; norm_num) 0 (show (0 : ℝ) ≤ 1 by norm_num)
  have : ConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) :=
    isConnected_iff_connectedSpace.mp hconn
  obtain ⟨e, _⟩ := covering_is_homeomorph p hp
  exact ⟨e.symm⟩

end PoincareFormalization

theorem solution (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  classical
  let x : M := Classical.choice inferInstance
  obtain ⟨p, hp⟩ := PoincareFormalization.spherical_cover_of_finite_fundamental_group M x
  exact PoincareFormalization.homeomorph_sphere_three_of_cover M p hp
