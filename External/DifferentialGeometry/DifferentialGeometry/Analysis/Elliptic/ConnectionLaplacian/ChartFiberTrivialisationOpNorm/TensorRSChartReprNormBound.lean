import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberForwardOpNorm

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

end DifferentialGeometry.Integral.Connection

end
