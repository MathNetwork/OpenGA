import Definitions.Def_OpenGA_WidthComparisonTrace
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

theorem PoincareFormalization.persistent_comparison_data_of_not_homeomorph_sphere
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (hnot : ¬ Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))) :
    ∃ initialWidth : ℝ, 0 ≤ initialWidth ∧ ∀ finalTime : ℝ, 0 < finalTime →
      Nonempty (OpenGA.WidthComparisonTrace initialWidth finalTime) := by sorry
