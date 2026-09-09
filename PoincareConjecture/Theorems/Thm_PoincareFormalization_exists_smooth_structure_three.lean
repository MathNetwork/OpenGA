import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareFormalization

theorem exists_smooth_structure_three (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      @IsManifold ℝ _ _ _ _ _ _ (𝓡 3) ∞ M _ cs := by
  sorry

end PoincareFormalization

