import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerJointCont
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Metric
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section UpperBoundUnitSphere

variable [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_chartTensorInnerPointwise_rs_model_unit_sphere_upper_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ M_ub : ℝ, 0 ≤ M_ub ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T ≤ M_ub := by
  classical
  haveI : ProperSpace (TensorRSModel r s ℝ E) :=
    FiniteDimensional.proper_real (TensorRSModel r s ℝ E)
  set K_M : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_M_def
  have hK_M_compact : IsCompact K_M :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  set S_T : Set (TensorRSModel r s ℝ E) := Metric.sphere (0 : TensorRSModel r s ℝ E) 1
    with hS_T_def
  have hS_T_compact : IsCompact S_T :=
    isCompact_sphere (0 : TensorRSModel r s ℝ E) 1
  set K : Set (M × TensorRSModel r s ℝ E) := K_M ×ˢ S_T with hK_def
  have hK_compact : IsCompact K := hK_M_compact.prod hS_T_compact
  set Q : M × TensorRSModel r s ℝ E → ℝ := fun bT =>
    chartTensorInnerPointwise_rs_model (I := I) (M := M)
      g r s α bT.1 bT.2 bT.2 with hQ_def
  have hQ_contOn_full :
      ContinuousOn Q
        ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) :=
    chartTensorInnerPointwise_rs_model_quadratic_continuousOn
      (I := I) (M := M) g r s α
  have hK_sub_full :
      K ⊆ ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) := by
    intro p hp
    refine ⟨hK_M_sub_baseSet hp.1, ?_⟩
    exact Set.mem_univ _
  have hQ_contOn : ContinuousOn Q K :=
    hQ_contOn_full.mono hK_sub_full
  by_cases hK_ne : K.Nonempty
  · obtain ⟨p₀, hp₀_mem, hp₀_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne hQ_contOn
    have hp₀_M : p₀.1 ∈ K_M := hp₀_mem.1
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hK_M_sub_baseSet hp₀_M
    have hp₀_nn : 0 ≤ Q p₀ :=
      chartTensorInnerPointwise_rs_model_nonneg
        (I := I) (M := M) g r s α hp₀_base p₀.2
    refine ⟨Q p₀, hp₀_nn, ?_⟩
    intro b hb T hT_norm
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    have := hp₀_max hp_mem
    exact this
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb T hT_norm
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    exact absurd ⟨(b, T), hp_mem⟩ hK_ne

end UpperBoundUnitSphere

section UpperBound

variable [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartTensorInnerPointwise_rs_model_le_mul_sq_norm_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {M_ub : ℝ}
    (h_ub : ∀ b : M, b ∈ tsupport (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
        chartTensorInnerPointwise_rs_model (I := I) (M := M)
          g r s α b T T ≤ M_ub) :
    ∀ b : M, b ∈ tsupport (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ∀ T : TensorRSModel r s ℝ E,
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T ≤
          M_ub * ‖T‖ ^ 2 := by
  classical
  intro b hb T
  by_cases hT0 : T = 0
  · subst hT0
    have h_left : chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E) = 0 := by
      have h_zero_smul :
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b
              ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
              (0 : TensorRSModel r s ℝ E) =
          (0 : ℝ) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
        chartTensorInnerPointwise_rs_model_smul_left
          (I := I) (M := M) g r s α b 0 (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E)
      have h_eq : (0 : TensorRSModel r s ℝ E) =
          ((0 : ℝ) • (0 : TensorRSModel r s ℝ E)) := by rw [zero_smul]
      calc chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b
              (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E)
          = chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
                (0 : TensorRSModel r s ℝ E) := by rw [← h_eq]
        _ = (0 : ℝ) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
              h_zero_smul
        _ = 0 := by ring
    have h_right : M_ub * ‖(0 : TensorRSModel r s ℝ E)‖ ^ 2 = 0 := by simp
    rw [h_left, h_right]
  · have hT_ne : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT0
    have hT_pos : 0 < ‖T‖ := (norm_pos_iff).mpr hT0
    letI : NormSMulClass ℝ (TensorRSModel r s ℝ E) :=
      NormedSpace.toNormSMulClass
    set T' : TensorRSModel r s ℝ E := ‖T‖⁻¹ • T with hT'_def
    have hT'_norm : ‖T'‖ = 1 := by
      rw [hT'_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hT_pos]
      field_simp
    have h_T' : chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T' T' ≤ M_ub :=
      h_ub b hb T' hT'_norm
    have h_bilin :
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T' T' =
          (‖T‖⁻¹ * ‖T‖⁻¹) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b T T := by
      rw [hT'_def]
      rw [chartTensorInnerPointwise_rs_model_smul_left
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T (‖T‖⁻¹ • T)]
      rw [chartTensorInnerPointwise_rs_model_smul_right
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T T]
      ring
    rw [h_bilin] at h_T'
    have h_sq_nn : 0 ≤ ‖T‖ ^ 2 := by positivity
    have h_mul : ((‖T‖⁻¹ * ‖T‖⁻¹) *
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 ≤
        M_ub * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_T' h_sq_nn
    have h_lhs :
        ((‖T‖⁻¹ * ‖T‖⁻¹) *
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 =
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T := by
      have h_sq_eq : ‖T‖ ^ 2 = ‖T‖ * ‖T‖ := by ring
      rw [h_sq_eq]
      field_simp
    rw [h_lhs] at h_mul
    exact h_mul

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartTensorInnerPointwise_rs_model_upper_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T ≤ C * ‖T‖ ^ 2 := by
  classical
  obtain ⟨M_ub, hM_ub_nn, h_ub⟩ :=
    exists_chartTensorInnerPointwise_rs_model_unit_sphere_upper_bound
      (I := I) (M := M) g r s α
  refine ⟨M_ub, hM_ub_nn, ?_⟩
  exact chartTensorInnerPointwise_rs_model_le_mul_sq_norm_on_pouTsupport
    (I := I) (M := M) g r s α h_ub

end UpperBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
