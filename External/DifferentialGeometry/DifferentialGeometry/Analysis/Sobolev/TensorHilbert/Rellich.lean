import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Inclusion
import Mathlib.Analysis.Normed.Operator.Compact








noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]




















theorem tensorPouSobolevHilbert_inclusion_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    IsCompactOperator (inclusionHk_succ (I := I) (M := M) g r s k) := by
  sorry





theorem TensorPouSobolevHilbert_inclusion_H2_L2_isCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (inclusionHk_succ (I := I) (M := M) g r s 0) :=
  tensorPouSobolevHilbert_inclusion_isCompactOperator
    (I := I) (M := M) g r s 0

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
