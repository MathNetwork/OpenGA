import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradMetricBridge


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]   [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T).toFun
        (covGrad (I := I) (M := M) g r s v).toFun =
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  change tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s T).toSection x))
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s v).toSection x)) =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
  exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s T v x).symm

end Connection
end Integral
end DifferentialGeometry

end
