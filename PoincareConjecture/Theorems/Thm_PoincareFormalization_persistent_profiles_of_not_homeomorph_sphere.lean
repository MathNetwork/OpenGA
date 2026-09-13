import Definitions.Def_OpenGA_ScalarWidthTrace
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

theorem PoincareFormalization.persistent_profiles_of_not_homeomorph_sphere
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (hnot : ¬ Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))) :
    ∃ W₀ : ℝ, 0 ≤ W₀ ∧ ∀ T : ℝ, 0 < T → Nonempty (OpenGA.ScalarWidthTrace W₀ T) := by sorry
