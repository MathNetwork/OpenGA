import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic

theorem PoincareFormalization.spherical_cover_of_finite_fundamental_group
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [CompactSpace M] [ConnectedSpace M]
    (x : M) [Finite (FundamentalGroup M x)] :
    ∃ p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1) → M,
      IsCoveringMap p := by sorry
