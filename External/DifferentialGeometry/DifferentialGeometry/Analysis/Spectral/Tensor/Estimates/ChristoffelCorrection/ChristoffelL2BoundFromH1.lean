import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelCorrectionL2Bound
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPou_mul_chart_christoffel_correction_sum_sq_le_const_mul_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b')
    {M_F : ℝ} (hM_F_nn : 0 ≤ M_F)
    (hM_F_input : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b k‖ ≤
            M_F * ‖S.toSection b‖)
    (hM_F_output : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b l‖ ≤
            M_F * ‖S.toSection b‖)
    {K_S : ℝ} (hK_S_nn : 0 ≤ K_S)
    (hK_S_bound : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b ^ 2 *
            ((∑ k : Fin r,
                ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b') X b k‖ ^ 2) +
              (∑ l : Fin s,
                ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b') X b l‖ ^ 2)) ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨C, hC_nn, h_sum⟩ :=
    exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) g r s α X M_F hM_F_nn hM_F_input hM_F_output K_S hK_S_nn
      hK_S_bound
  refine ⟨C, hC_nn, ?_⟩
  intro S b
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set SumSq : ℝ :=
    (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b k‖ ^ 2) +
      (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b l‖ ^ 2) with hSumSq_def
  set Q : ℝ := tensorInnerPointwise (I := I) (M := M) g r s b
    (S.toFun b) (S.toFun b) with hQ_def
  have hSumSq_nn : 0 ≤ SumSq := by
    rw [hSumSq_def]
    refine add_nonneg ?_ ?_
    · refine Finset.sum_nonneg ?_
      intro k _
      exact sq_nonneg _
    · refine Finset.sum_nonneg ?_
      intro l _
      exact sq_nonneg _
  have hQ_nn : 0 ≤ Q := by
    rw [hQ_def]
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  by_cases hb : b ∈ tsupport ρ
  · have hρ_nn : 0 ≤ ρ b := (chartAtlasPOU I M).nonneg α b
    have hρ_le_one : ρ b ≤ 1 := (chartAtlasPOU I M).le_one α b
    have hρ_sq_le_one : ρ b ^ 2 ≤ 1 := by
      have hsq : ρ b * ρ b ≤ 1 * 1 :=
        mul_le_mul hρ_le_one hρ_le_one hρ_nn (by linarith)
      have hsq' : ρ b * ρ b ≤ 1 := by linarith
      rw [sq]; exact hsq'
    have hSumSq_le : SumSq ≤ C * Q := by
      rw [hSumSq_def, hQ_def]
      exact h_sum S hb
    have hCQ_nn : 0 ≤ C * Q := mul_nonneg hC_nn hQ_nn
    calc ρ b ^ 2 * SumSq
        ≤ 1 * (C * Q) :=
          mul_le_mul hρ_sq_le_one hSumSq_le hSumSq_nn (by linarith)
      _ = C * Q := one_mul _
  · have hρ_zero : ρ b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    have hLHS_zero : ρ b ^ 2 * SumSq = 0 := by
      rw [hρ_zero]; ring
    rw [hLHS_zero]
    exact mul_nonneg hC_nn hQ_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma integral_tensorInnerPointwise_diagonal_le_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ∫ b, tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ‖S‖ ^ 2 := by
  classical
  have h_l2_eq :
      ∫ b, tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun := rfl
  rw [h_l2_eq]
  have h_l2_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun =
        ‖S.toCcTensor‖ ^ 2 :=
    (SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) S.toCcTensor).symm
  rw [h_l2_norm_sq]
  exact SmoothCcTensorH1.l2NormSq_le_h1NormSq (I := I) (M := M) S

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_eLpNorm_chartPou_mul_sqrt_chart_christoffel_correction_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b')
    {M_F : ℝ} (hM_F_nn : 0 ≤ M_F)
    (hM_F_input : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b k‖ ≤
            M_F * ‖S.toSection b‖)
    (hM_F_output : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b l‖ ≤
            M_F * ‖S.toSection b‖)
    {K_S : ℝ} (hK_S_nn : 0 ≤ K_S)
    (hK_S_bound : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b') X b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b') X b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    chartPou_mul_chart_christoffel_correction_sum_sq_le_const_mul_tensorInnerPointwise
      (I := I) (M := M) g r s α X hM_F_nn hM_F_input hM_F_output hK_S_nn hK_S_bound
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set SumSq : M → ℝ := fun b : M =>
    (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b') X b k‖ ^ 2) +
      (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b') X b l‖ ^ 2) with hSumSq_def
  set f : M → ℝ := fun b : M => ρ b * Real.sqrt (SumSq b) with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have hSumSq_nn : ∀ b : M, 0 ≤ SumSq b := by
    intro b
    rw [hSumSq_def]
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h_pt_sq : ∀ b : M, (f b) ^ 2 ≤
      C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := by
    intro b
    have h_eq : (f b) ^ 2 = ρ b ^ 2 * SumSq b := by
      rw [hf_def, mul_pow,
        show Real.sqrt (SumSq b) ^ 2 = SumSq b from Real.sq_sqrt (hSumSq_nn b)]
    rw [h_eq]
    exact h_pt S.toCcTensor b
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b
            (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt_sq b)
  have h_inner_int :
      Integrable (fun b : M => tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) μ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      S.toCcTensor S.toCcTensor
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) :=
    Filter.Eventually.of_forall fun b => mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_int_le :
      ∫ b, tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ ≤
      ‖S‖ ^ 2 :=
    integral_tensorInnerPointwise_diagonal_le_h1NormSq
      (I := I) (M := M) g r s S
  have h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal (C * ‖S‖ ^ 2) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
    calc ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ
        ≤ ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
            (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards with b using h_pt_enn b
      _ = ENNReal.ofReal (∫ b, C * tensorInnerPointwise
            (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_C_smul_int h_C_smul_nn).symm
      _ = ENNReal.ofReal (C *
            ∫ b, tensorInnerPointwise
              (I := I) (M := M) g r s b
                (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ) := by
          rw [integral_const_mul]
      _ ≤ ENNReal.ofReal (C * ‖S‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h_int_le hC_nn)
  set T : ℝ := C * ‖S‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ T := mul_nonneg hC_nn (sq_nonneg _)
  have h_eLpNorm_le := eLpNorm_two_le_ofReal_sqrt hT_nn h_sq
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_factor :
      Real.sqrt T = Real.sqrt C * ‖S‖ := by
    rw [hT_def, Real.sqrt_mul hC_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring,
      Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  rw [show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
    (coe_nnnorm_eq_ofReal_norm S).symm] at h_eLpNorm_le
  exact h_eLpNorm_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
