import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Equiv
open scoped ContinuousMap

namespace PoincareFormalization

theorem homotopy_three_sphere_nonempty_homeomorph (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    (M ≃ₕ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) →
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  sorry

end PoincareFormalization
