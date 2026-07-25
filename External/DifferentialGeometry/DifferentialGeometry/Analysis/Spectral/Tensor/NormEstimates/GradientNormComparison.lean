import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section HeadlineGradientNormComparison

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem
    chartTrivializationNorm_grad_le_const_mul_chartTensorInnerPointwise_rs_succ_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r (s + 1) α b T T :=
  chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (I := I) (M := M) g r (s + 1) α

omit [InnerProductSpace ℝ E] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem
    chartTrivializationNorm_grad_le_const_mul_tensorInnerPointwise_chartRSTwist_succ_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T)
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T) :=
  chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport
    (I := I) (M := M) g r (s + 1) α

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] in
lemma tensorInnerPointwise_chartRSTwist_succ_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSModel r (s + 1) ℝ E) :
    0 ≤ tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
      (chartRSTwist (I := I) (M := M) α b r (s + 1) T)
      (chartRSTwist (I := I) (M := M) α b r (s + 1) T) := by
  have hbridge :=
    chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r (s + 1) α hb T T
  rw [← hbridge]
  exact chartTensorInnerPointwise_rs_model_nonneg
    (I := I) (M := M) g r (s + 1) α hb T

end HeadlineGradientNormComparison

section CombinedGradient

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem
    chartTrivializationNorm_section_and_grad_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T) ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r (s + 1) α b T T) := by
  classical
  obtain ⟨K₀, hK₀_nn, h₀⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) g r s α
  obtain ⟨K₁, hK₁_nn, h₁⟩ :=
    chartTrivializationNorm_grad_le_const_mul_chartTensorInnerPointwise_rs_succ_model_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K₀ + K₁, add_nonneg hK₀_nn hK₁_nn, ?_, ?_⟩
  · intro b hb T
    have h := h₀ b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hQ_nn : 0 ≤ chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T T :=
      chartTensorInnerPointwise_rs_model_nonneg
        (I := I) (M := M) g r s α hb_base T
    have hineq : K₀ * chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T T ≤
        (K₀ + K₁) * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T :=
      mul_le_mul_of_nonneg_right
        (by linarith : K₀ ≤ K₀ + K₁) hQ_nn
    linarith
  · intro b hb T
    have h := h₁ b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hQ_nn : 0 ≤ chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r (s + 1) α b T T :=
      chartTensorInnerPointwise_rs_model_nonneg
        (I := I) (M := M) g r (s + 1) α hb_base T
    have hineq : K₁ * chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r (s + 1) α b T T ≤
        (K₀ + K₁) * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r (s + 1) α b T T :=
      mul_le_mul_of_nonneg_right
        (by linarith : K₁ ≤ K₀ + K₁) hQ_nn
    linarith

omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem
    chartTrivializationNorm_section_and_grad_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r s b
            (chartRSTwist (I := I) (M := M) α b r s T)
            (chartRSTwist (I := I) (M := M) α b r s T)) ∧
      (∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r (s + 1) ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T)
            (chartRSTwist (I := I) (M := M) α b r (s + 1) T)) := by
  classical
  obtain ⟨K, hK_nn, h_sec, h_grad⟩ :=
    chartTrivializationNorm_section_and_grad_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K, hK_nn, ?_, ?_⟩
  · intro b hb T
    have h := h_sec b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
        (I := I) (M := M) g r s α hb_base T T] at h
    exact h
  · intro b hb T
    have h := h_grad b hb T
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
        (I := I) (M := M) g r (s + 1) α hb_base T T] at h
    exact h

end CombinedGradient

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
