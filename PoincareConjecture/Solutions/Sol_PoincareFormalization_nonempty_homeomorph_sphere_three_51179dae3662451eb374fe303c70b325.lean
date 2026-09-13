import Theorems.Thm_PoincareFormalization_exists_smooth_structure_three
import Theorems.Thm_PoincareFormalization_nonempty_sdiffeomorph_sphere_three
import Mathlib.Geometry.Manifold.ChartedSpace

open scoped Manifold ContDiff

theorem solution (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  -- A compact charted space over a second-countable model is second countable.
  haveI : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) M
  -- Moise: the topological 3-manifold `M` carries a smooth structure.
  obtain ⟨cs, hcs⟩ := PoincareFormalization.exists_smooth_structure_three M
  -- Perelman: a closed simply connected smooth 3-manifold is diffeomorphic to the 3-sphere.
  exact ⟨(@PoincareFormalization.nonempty_sdiffeomorph_sphere_three M _ _ cs hcs _ _).some.toHomeomorph⟩
