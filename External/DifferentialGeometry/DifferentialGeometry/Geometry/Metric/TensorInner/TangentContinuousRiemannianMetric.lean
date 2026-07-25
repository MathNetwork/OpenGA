import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Tensor
namespace RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def tangentContinuousRiemannianMetric
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) :
    Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
  g.toContinuousRiemannianMetric

omit [FiniteDimensional ℝ E] in
@[simp] theorem tangentContinuousRiemannianMetric_inner
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (b : M) :
    (tangentContinuousRiemannianMetric (I := I) (M := M) g).inner b = g.inner b :=
  rfl

end RSTensor
end Tensor
end DifferentialGeometry

end
