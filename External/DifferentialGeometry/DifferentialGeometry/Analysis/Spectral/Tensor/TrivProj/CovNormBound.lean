import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerCovDiagonalBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerPointwiseUpperBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ K_M →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X := by
  classical
  obtain ⟨K, hK_nn, h_chart⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
      (I := I) (M := M) (E := E) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K, hK_nn, ?_⟩
  intro b hb X
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub_baseSet hb
  set T : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s X with hT_def
  have h_T : ‖T‖ ^ 2 ≤ K *
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T :=
    h_chart b hb T
  have h_bridge :
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T =
        tensorInnerPointwise (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T)
          (chartRSTwist (I := I) (M := M) α b r s T) :=
    chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T
  have h_round : chartRSTwist (I := I) (M := M) α b r s T = X := by
    rw [hT_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s X
  rw [h_bridge, h_round] at h_T
  exact h_T

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ K_M →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  obtain ⟨K, hK_nn, h_per⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  obtain ⟨C', hC'_nn, h_diag⟩ :=
    exists_sum_tensorInnerPointwise_cov_chartBasis_diagonal_le_const_mul_tensorCovDerivPointwiseInner_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K * C', mul_nonneg hK_nn hC'_nn, ?_⟩
  intro S b hb
  set cov : Fin (Module.finrank ℝ E) → TensorRSModel r s ℝ E := fun i =>
    TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) with hcov_def
  set D : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b (cov i) (cov i) with hD_def
  have h_D_le : D ≤ C' * tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s S S b := by
    rw [hD_def]
    exact h_diag S hb
  have h_sum_le_KD :
      ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2 ≤
        K * D := by
    rw [hD_def, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    exact h_per hb (cov i)
  have h_KD_le : K * D ≤
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) :=
    mul_le_mul_of_nonneg_left h_D_le hK_nn
  have h_assoc :
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) =
        (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
    ring
  calc ∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2
      ≤ K * D := h_sum_le_KD
    _ ≤ K * (C' * tensorCovDerivPointwiseInner
              (I := I) (M := M) g r s S S b) := h_KD_le
    _ = (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := h_assoc

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X :=
  chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b :=
  exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
