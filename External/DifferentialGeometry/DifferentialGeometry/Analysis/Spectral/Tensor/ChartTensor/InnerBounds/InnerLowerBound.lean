import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerJointCont
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
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

section TwistInvertible

noncomputable def chartRSTwistInv
    (α : M) (b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).comp <|
    T.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))

@[simp]
lemma chartRSTwistInv_apply
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E)
    (α' : Tensor0SModel r ℝ E) :
    chartRSTwistInv (I := I) (M := M) α b r s T α' =
      (T (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
  rfl

lemma chartRSTwistInv_chartRSTwist
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    chartRSTwistInv (I := I) (M := M) α b r s
        (chartRSTwist (I := I) (M := M) α b r s T) = T := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwistInv_apply, chartRSTwist_apply]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hα' :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (v k)
  rw [hα']
  congr 1
  funext k
  exact chartJ_chartJinv (I := I) (M := M) α hb (w k)

lemma chartRSTwist_chartRSTwistInv
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    chartRSTwist (I := I) (M := M) α b r s
        (chartRSTwistInv (I := I) (M := M) α b r s T) = T := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwist_apply, chartRSTwistInv_apply]
  have hinner :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJinv_chartJ_self (I := I) (M := M) α hb (v k)
  rw [hinner]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  exact chartJinv_chartJ_self (I := I) (M := M) α hb (w k)

lemma chartRSTwist_injective
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) :
    Function.Injective
      (chartRSTwist (I := I) (M := M) α b r s) := by
  intro T₀ T₁ h
  have h0 := chartRSTwistInv_chartRSTwist (I := I) (M := M) α hb r s T₀
  have h1 := chartRSTwistInv_chartRSTwist (I := I) (M := M) α hb r s T₁
  rw [← h0, ← h1, h]

lemma chartRSTwist_ne_zero
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) {T : TensorRSModel r s ℝ E} (hT : T ≠ 0) :
    chartRSTwist (I := I) (M := M) α b r s T ≠ 0 := by
  intro hzero
  have hround : chartRSTwistInv (I := I) (M := M) α b r s
      (chartRSTwist (I := I) (M := M) α b r s T) = T :=
    chartRSTwistInv_chartRSTwist (I := I) (M := M) α hb r s T
  have hzero_inv :
      chartRSTwistInv (I := I) (M := M) α b r s
        (0 : TensorRSModel r s ℝ E) = 0 := by
    classical
    refine ContinuousLinearMap.ext ?_
    intro α'
    rw [chartRSTwistInv_apply]
    change ((0 : TensorRSModel r s ℝ E)
        (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) = 0
    rw [show ((0 : TensorRSModel r s ℝ E)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))) =
            (0 : Tensor0SModel s ℝ E) from rfl]
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl
  rw [hzero, hzero_inv] at hround
  exact hT hround.symm

end TwistInvertible

section Positivity

lemma chartTensorInnerPointwise_rs_model_pos_of_ne_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {T : TensorRSModel r s ℝ E} (hT : T ≠ 0) :
    0 < chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T := by
  classical
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb T T]
  have hTwist_ne : chartRSTwist (I := I) (M := M) α b r s T ≠ 0 :=
    chartRSTwist_ne_zero (I := I) (M := M) α hb r s hT
  set Q : ℝ :=
    tensorInnerPointwise (I := I) (M := M) g r s b
      (chartRSTwist (I := I) (M := M) α b r s T)
      (chartRSTwist (I := I) (M := M) α b r s T)
  have hQ_nn : 0 ≤ Q :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have := (tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g r s b
      (chartRSTwist (I := I) (M := M) α b r s T)).mp hQ0
    exact hTwist_ne this
  exact lt_of_le_of_ne hQ_nn (Ne.symm hQ_ne)

end Positivity

section Compactness

variable [CompactSpace M]

lemma pouTsupport_isCompact
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

omit [CompactSpace M] in
lemma pouTsupport_subset_baseSet
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α hx

end Compactness

section LowerBound

variable [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartTensorInnerPointwise_rs_model_lower_bound_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ b : M, b ∈ K_M →
        ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          ε ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T := by
  classical
  haveI : ProperSpace (TensorRSModel r s ℝ E) :=
    FiniteDimensional.proper_real (TensorRSModel r s ℝ E)
  set S_T : Set (TensorRSModel r s ℝ E) := Metric.sphere (0 : TensorRSModel r s ℝ E) 1
    with hS_T_def
  have hS_T_compact : IsCompact S_T :=
    isCompact_sphere (0 : TensorRSModel r s ℝ E) 1
  have hS_T_norm : ∀ T : TensorRSModel r s ℝ E, T ∈ S_T → ‖T‖ = 1 := by
    intro T hT
    rw [hS_T_def, Metric.mem_sphere, dist_zero_right] at hT
    exact hT
  have hS_T_ne_zero : ∀ T : TensorRSModel r s ℝ E, T ∈ S_T → T ≠ 0 := by
    intro T hT hT0
    have : ‖T‖ = 1 := hS_T_norm T hT
    rw [hT0, norm_zero] at this
    exact one_ne_zero this.symm
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
  · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
      hK_compact.exists_isMinOn hK_ne hQ_contOn
    have hp₀_M : p₀.1 ∈ K_M := hp₀_mem.1
    have hp₀_S : p₀.2 ∈ S_T := hp₀_mem.2
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hK_M_sub_baseSet hp₀_M
    have hp₀_ne : p₀.2 ≠ 0 := hS_T_ne_zero p₀.2 hp₀_S
    have hp₀_pos : 0 < Q p₀ :=
      chartTensorInnerPointwise_rs_model_pos_of_ne_zero
        (I := I) (M := M) g r s α hp₀_base hp₀_ne
    refine ⟨Q p₀, hp₀_pos, ?_⟩
    intro b hb T hT_norm
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    have := hp₀_min hp_mem
    exact this
  · refine ⟨1, one_pos, ?_⟩
    intro b hb T hT_norm
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    exact absurd ⟨(b, T), hp_mem⟩ hK_ne

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartTensorInnerPointwise_rs_model_lower_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          ε ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T :=
  exists_chartTensorInnerPointwise_rs_model_lower_bound_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end LowerBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
