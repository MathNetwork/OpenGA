import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckPrincipalCometricCoeff
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldCompose_l2_le_of_pointwise_fiberNormSq_bound_left
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (B : ℝ) (hB : 0 ≤ B)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) ≤ B ^ 2) :
    ‖ccOperatorFieldComp (I := I) (M := M) g a b c Φ W‖ ≤ B * ‖W‖ := by
  classical
  set F : M → ℝ := fun x => B ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g a b W).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a c x
          ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) ≤ F x := by
    intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g a b c x
      (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    exact mul_le_mul_of_nonneg_right (hΦ x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g a b x _)
  have hsq : ‖ccOperatorFieldComp (I := I) (M := M) g a b c Φ W‖ ^ 2 ≤ B ^ 2 * ‖W‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g a c
      (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) F hF_int hpt
    rw [hF_def, MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g a b W
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ B * ‖W‖ := mul_nonneg hB (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  rw [mul_pow]
  exact hsq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldCompose_l2_le_of_pointwise_fiberNormSq_bound_right
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x) ≤ B ^ 2) :
    ‖ccOperatorFieldComp (I := I) (M := M) g a b c Φ W‖ ≤ ‖Φ‖ * B := by
  classical
  set F : M → ℝ := fun x => B ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g b c Φ).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a c x
          ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) ≤ F x := by
    intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g a b c x
      (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    calc riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x)
        ≤ riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) * B ^ 2 :=
          mul_le_mul_of_nonneg_left (hW x)
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g b c x _)
      _ = B ^ 2 * riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) := by ring
  have hsq : ‖ccOperatorFieldComp (I := I) (M := M) g a b c Φ W‖ ^ 2 ≤ ‖Φ‖ ^ 2 * B ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g a c
      (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) F hF_int hpt
    rw [hF_def, MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g b c Φ
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    nlinarith [h1]
  have hrhs_nn : 0 ≤ ‖Φ‖ * B := mul_nonneg (norm_nonneg _) hB
  refine le_of_sq_le_sq ?_ hrhs_nn
  rw [mul_pow]
  exact hsq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (B : ℝ) (hB : 0 ≤ B)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) ≤ B ^ 2) :
    ‖operatorFieldApply (I := I) (M := M) g r s Φ W‖ ≤ B * ‖W‖ := by
  rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g r s Φ W]
  exact operatorFieldCompose_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g 0 r s Φ W B hB hΦ

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) ≤ B ^ 2) :
    ‖operatorFieldApply (I := I) (M := M) g r s Φ W‖ ≤ ‖Φ‖ * B := by
  rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g r s Φ W]
  exact operatorFieldCompose_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g 0 r s Φ W B hB hW

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_iteratedCovGrad_fiberNormSq_le_smoothCcToTensorHs_sq
    (g₀ : SmoothRiemannianMetric I M) (q m : ℕ)
    (h_super : 2 * (2 * (Module.finrank ℝ E / 2 + 1) + q) ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T₀ : SmoothCcTensor g₀ 0 2) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x) ≤
        C ^ 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T₀‖ ^ 2 := by
  classical
  set K : ℕ := Module.finrank ℝ E / 2 + 1 with hK_def
  have hK_super : 2 * K > Module.finrank ℝ E + 2 * 0 := by rw [hK_def]; omega
  set N : ℕ := 2 * (2 * K + q) with hN_def
  have hNm : N ≤ m := by rw [hN_def, hK_def]; omega
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g₀ 0 (2 + q) K 0 hK_super
  obtain ⟨Cit, hCit_nn, hCit⟩ :=
    iteratedCovGrad_toHs_norm_le (I := I) (M := M) g₀ 0 2 q (2 * K)
  obtain ⟨Crev, hCrev_nn, hCrev⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * K + q)
  obtain ⟨Cspec, hCspec_nn, hCspec⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ N
  refine ⟨Cemb * Cit * Crev * Cspec, by positivity, fun T₀ x => ?_⟩
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
  set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T₀‖ with hNm_def
  have hNm_nn : 0 ≤ Nm := norm_nonneg _
  have hbridge : ∀ σ : ℝ, smoothCcToTensorHs (I := I) (M := M) g₀ σ T₀ =
      ccSpectralEmbed (I := I) (M := M) g₀ σ T₀ :=
    fun σ => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
      (funext (fun i => rfl))
  have hspecmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (N : ℝ) T₀‖ ≤ Nm := by
    rw [hNm_def, hbridge (N : ℝ), hbridge (m : ℝ)]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T₀
    exact_mod_cast hNm
  have hsumcongr : (∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
        tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
          (iteratedCovGrad (I := I) g₀ 0 2 j T₀).toFun) =
      ∑ j ∈ Finset.range (N + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ := by
    rw [hN_def]
    exact Finset.sum_congr rfl
      (fun j _ => (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j T₀)).symm)
  have hrev : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) T₀‖ ≤
      Crev * (Cspec * Nm) := by
    refine le_trans (hCrev T₀) ?_
    rw [hsumcongr]
    refine mul_le_mul_of_nonneg_left
      (le_trans (hCspec T₀) (mul_le_mul_of_nonneg_left hspecmono hCspec_nn)) hCrev_nn
  have hit : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
        (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q T₀)‖ ≤
      Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) T₀‖ := hCit T₀
  have hemb := hCemb (iteratedCovGrad (I := I) g₀ 0 2 q T₀) x
  have hnorm : ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖ ≤
      (Cemb * Cit * Crev * Cspec) * Nm := by
    calc ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖
        ≤ Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
            (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q T₀)‖ := hemb
      _ ≤ Cemb * (Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            (2 * K + q) T₀‖) := mul_le_mul_of_nonneg_left hit hCemb_pos.le
      _ ≤ Cemb * (Cit * (Crev * (Cspec * Nm))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrev hCit_nn) hCemb_pos.le
      _ = (Cemb * Cit * Crev * Cspec) * Nm := by ring
  have hns : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x) =
      ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖ ^ 2 := by
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        (iteratedCovGrad (I := I) g₀ 0 2 q T₀),
      Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)]
  rw [hns]
  have hsq_le : ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖ ^ 2 ≤
      ((Cemb * Cit * Crev * Cspec) * Nm) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  refine le_trans hsq_le ?_
  rw [hNm_def, mul_pow]

theorem deTurckPrincipalCometricCoeff_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨Kslot, hKslot_nn, hKslot⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), Kslot j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hKslot_nn j), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hC g₁ i x)
  have hjetL2 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      C i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
    refine le_trans key (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
    exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm
  refine le_trans hjetL2 ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
  intro j hj
  have hj_le : j ≤ a :=
    le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
  exact hKslot g₁ P hδ_le hδ htie hPball j hj_le

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem productGridTerm_integral_le_topOrderJetSq
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (max Λ (max C 1)) ^ (7 * i) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set Rtop : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ with hRtop_def
  have hRtop_nn : 0 ≤ Rtop := norm_nonneg _
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
  have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
  have hΛZle : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
    le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) = Rtop ^ 2 := by
      rw [hRtop_def, SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
      exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ = Λ ^ (2 * Zset.card) * Rtop ^ 2 := by rw [hintFi]
      _ ≤ Mbar ^ (7 * i) * Rtop ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg Rtop)
          exact le_trans hΛZle (pow_le_pow_right₀ hMbar1 (by omega))
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (3 * i) * Rtop ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hD_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hD_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
              mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
          _ = Mbar ^ (3 : ℕ) := by ring
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hidiv_nn : 0 ≤ (i : ℝ) / (e m : ℝ) := by positivity
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hRtoppow : (Rtop ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = Rtop ^ 2 := by
        rw [← Real.rpow_mul hRtop_nn]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hDpow_le : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (3 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hD_nn hD_le hidiv_nn
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) *
              Rtop ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn hidiv_nn
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (Rtop ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
            rw [Real.mul_rpow hD_nn (Real.rpow_nonneg hRtop_nn _)]
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * Rtop ^ 2 := by
            rw [hRtoppow]
        _ ≤ Mbar ^ (3 * i) * Rtop ^ 2 :=
            mul_le_mul_of_nonneg_right hDpow_le (sq_nonneg Rtop)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (3 * i) * Rtop ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (3 * i) * Rtop ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (3 * i) * Rtop ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (3 * i) * Rtop ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (3 * i) * Rtop ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ Mbar ^ (7 * i) * Rtop ^ 2 := by
          have e3 : Mbar ^ (2 * i) * Mbar ^ (3 * i) = Mbar ^ (5 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (3 * i) * Rtop ^ 2) ≤
              Mbar ^ (5 * i) * Rtop ^ 2 := by
            have h1 : Λ ^ (2 * Zset.card) * Mbar ^ (3 * i) ≤ Mbar ^ (5 * i) := by
              calc Λ ^ (2 * Zset.card) * Mbar ^ (3 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (3 * i) :=
                    mul_le_mul_of_nonneg_right hΛZle (by positivity)
                _ = Mbar ^ (5 * i) := e3
            nlinarith [sq_nonneg Rtop, pow_nonneg hMbar_nn (3 * i), hΛZ_nn, h1]
          have e5 : Mbar ^ (5 * i) * Rtop ^ 2 ≤ Mbar ^ (7 * i) * Rtop ^ 2 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hMbar1 (by omega)) (sq_nonneg Rtop)
          exact le_trans e4 e5

private theorem gInvDiffSlotCoeff_perOrder_l2_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R₀) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cgrid, hCgrid_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R₀ with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  set tupCard : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.range (k + 1), ((Finset.Nat.antidiagonalTuple n k).card : ℝ) with htup
  have htup_nn : ∀ k, 0 ≤ tupCard k :=
    fun k => Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  have hMbar_nn : ∀ k, 0 ≤ max Lam (max (Cgn k) 1) :=
    fun k => le_trans zero_le_one (le_trans (le_max_right (Cgn k) 1) (le_max_right Lam _))
  refine ⟨fun k => Cgrid k * (tupCard k * (max Lam (max (Cgn k) 1)) ^ (7 * k) + vol), ?_, ?_⟩
  · intro k
    dsimp only
    refine mul_nonneg (hCgrid_nn k) ?_
    exact add_nonneg (mul_nonneg (htup_nn k) (pow_nonneg (hMbar_nn k) _)) hvol_nn
  · intro g₁ P δ hδ_le hδ htie hPball i
    dsimp only
    set Rtop : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ with hRtop_def
    have hRtop_nn : 0 ≤ Rtop := norm_nonneg _
    set Kival : ℝ := Cgrid i * (tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) + vol) with hKival
    have hKterm_nn : 0 ≤ tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) + vol :=
      add_nonneg (mul_nonneg (htup_nn i) (pow_nonneg (hMbar_nn i) _)) hvol_nn
    have hKival_nn : 0 ≤ Kival := mul_nonneg (hCgrid_nn i) hKterm_nn
    by_cases hM : Nonempty M
    · obtain ⟨x₀⟩ := hM
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      have hδ0 : 0 ≤ δ := by
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
            mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      have hgridpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
            Cgrid i * ∑ n ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x
      by_cases hi0 : i = 0
      · subst hi0
        have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
          funext x
          simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
            Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
        have hSig_int : MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (0 + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          rw [hgrid0]
          exact MeasureTheory.integrable_const 1
        have hF_int0 : MeasureTheory.Integrable
            (fun x => Cgrid 0 * ∑ n ∈ Finset.range (0 + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          hSig_int.const_mul (Cgrid 0)
        have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + 0)
          (iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁))
          (fun x => Cgrid 0 * ∑ n ∈ Finset.range (0 + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          hF_int0 hgridpt
        rw [MeasureTheory.integral_const_mul] at key
        have hSig_intval : (∫ x, ∑ n ∈ Finset.range (0 + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) = vol := by
          rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
            MeasureTheory.measureReal_def, ← hvol]
        rw [hSig_intval] at key
        refine le_trans key ?_
        have hb1 : Cgrid 0 * vol ≤ Kival := by
          rw [hKival]
          refine mul_le_mul_of_nonneg_left ?_ (hCgrid_nn 0)
          exact le_add_of_nonneg_left (mul_nonneg (htup_nn 0) (pow_nonneg (hMbar_nn 0) _))
        refine le_trans hb1 ?_
        nlinarith [hKival_nn, sq_nonneg Rtop]
      · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            Lam ^ 2 := by
          intro x
          have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R₀ ^ 2 := by
            calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
                ≤ ∑ j ∈ Finset.range (a + 1 + 1), R₀ ^ 2 := by
                  apply Finset.sum_le_sum
                  intro j hj
                  have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                  nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR₀]
              _ = ((a + 1 + 1 : ℕ) : ℝ) * R₀ ^ 2 := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
              ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
            have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
            have hsl := Finset.single_le_sum
              (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
              (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
            simpa using hsl
          have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R₀ ^ 2 := by
            rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
            refine le_trans (hCemb P x) ?_
            rw [hLam2]
            calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
                ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R₀ ^ 2) :=
                  mul_le_mul_of_nonneg_left hsum_le (by positivity)
              _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R₀ ^ 2 := by ring
          exact le_trans hsingle hchain
        have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
        have hGNP : ∀ j : ℕ, 0 < j → j < i →
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
              Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ (2 * (j : ℝ) / (i : ℝ)) := by
          intro j hj0 hji
          have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
          have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
              (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
            rw [hCgn]; simp only [dif_pos hi1]
          rw [hchoose] at hb
          have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
              (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
            (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
          rw [hnorm] at hb
          exact hb
        have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
            MeasureTheory.Integrable (fun x => ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              (max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2 := by
          intro n hn e he
          have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
          have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
          exact productGridTerm_integral_le_topOrderJetSq (I := I) (M := M) g₀ P i hi1 hLam_nn
            hΛsup (hCgn_nn i) hGNP n hn_le e hsum_e
        have hGi_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          apply MeasureTheory.integrable_finset_sum
          intro n hn
          apply MeasureTheory.integrable_finset_sum
          intro e he
          exact (hPT n hn e he).1
        have hF_int : MeasureTheory.Integrable
            (fun x => Cgrid i * ∑ n ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          hGi_int.const_mul (Cgrid i)
        have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁))
          (fun x => Cgrid i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          hF_int hgridpt
        have hGi_bound : (∫ x, ∑ n ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2 := by
          rw [MeasureTheory.integral_finset_sum _
            (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
          have hinner : ∀ n ∈ Finset.range (i + 1),
              (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
              ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
            fun n hn => MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
          rw [Finset.sum_congr rfl hinner]
          have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                (max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2 := by
            apply Finset.sum_le_sum; intro n hn
            apply Finset.sum_le_sum; intro e he
            exact (hPT n hn e he).2
          refine le_trans hle1 ?_
          have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                (max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2 =
              tupCard i * ((max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2) := by
            rw [htup, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro n _
            rw [Finset.sum_const, nsmul_eq_mul]
          rw [heq2, ← mul_assoc]
        have hInt_bound : (∫ x, Cgrid i * ∑ n ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            Cgrid i * (tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
          exact mul_le_mul_of_nonneg_left hGi_bound (hCgrid_nn i)
        refine le_trans key (le_trans hInt_bound ?_)
        have hMpow_nn : 0 ≤ tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) :=
          mul_nonneg (htup_nn i) (pow_nonneg (hMbar_nn i) _)
        have hstep : tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) * Rtop ^ 2 ≤
            (tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) + vol) * (1 + Rtop ^ 2) := by
          nlinarith [hMpow_nn, hvol_nn, sq_nonneg Rtop]
        rw [hKival,
          mul_assoc (Cgrid i) (tupCard i * (max Lam (max (Cgn i) 1)) ^ (7 * i) + vol) (1 + Rtop ^ 2)]
        exact mul_le_mul_of_nonneg_left hstep (hCgrid_nn i)
    · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have : (0 : ℝ) ≤ Kival * (1 + Rtop ^ 2) :=
        mul_nonneg hKival_nn (by positivity)
      simpa using this

theorem deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R₀) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ≤
            K i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ (i : ℝ) P‖) := by
  classical
  obtain ⟨Cpo, hCpo_nn, hCpo⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨Kslot, hKslot_nn, hKslot⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_tame (I := I) (M := M) g₀ a ha_super hR₀ hδ₀
  set Cbr : ℕ → ℝ := fun j =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ j).choose with hCbr
  have hCbr_nn : ∀ j, 0 ≤ Cbr j :=
    fun j => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ j).choose_spec.1
  have hCbr_bound : ∀ (j : ℕ) (S : SmoothCcTensor g₀ 0 2),
      ∑ k ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖ ≤
        Cbr j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) S‖ :=
    fun j S => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ j).choose_spec.2 S
  refine ⟨fun i => Real.sqrt (Cpo i * ∑ j ∈ Finset.range (i + 1), Kslot j * (1 + Cbr j ^ 2)),
    fun i => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  dsimp only
  set H : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (i : ℝ) P‖ with hH_def
  have hH_nn : 0 ≤ H := norm_nonneg _
  set Ktot : ℝ := Cpo i * ∑ j ∈ Finset.range (i + 1), Kslot j * (1 + Cbr j ^ 2) with hKtot
  have hKtot_nn : 0 ≤ Ktot :=
    mul_nonneg (hCpo_nn i)
      (Finset.sum_nonneg (fun j _ => mul_nonneg (hKslot_nn j) (by positivity)))
  have hbridge : ∀ σ : ℝ, smoothCcToTensorHs (I := I) (M := M) g₀ σ P =
      ccSpectralEmbed (I := I) (M := M) g₀ σ P :=
    fun σ => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
      (funext (fun i => rfl))
  have hHmono : ∀ j : ℕ, j ≤ i →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) P‖ ≤ H := by
    intro j hj
    rw [hH_def, hbridge (j : ℝ), hbridge (i : ℝ)]
    exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ (by exact_mod_cast hj) P
  have hF_int : MeasureTheory.Integrable
      (fun x => Cpo i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (Cpo i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
    (fun x => Cpo i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hCpo g₁ i x)
  have hjetL2 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      Cpo i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
    refine le_trans key (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
    exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm
  have hslotBound : ∀ j : ℕ, j ≤ i →
      ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
        Kslot j * (1 + Cbr j ^ 2) * (1 + H ^ 2) := by
    intro j hj_le
    have hks := hKslot g₁ P hδ_le hδ htie hPball j
    have hjetH : ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ Cbr j * H := by
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤
          ∑ k ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ := by
        have hjmem : j ∈ Finset.range (j + 1) := Finset.self_mem_range_succ j
        exact Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖)
          (fun k _ => norm_nonneg _) hjmem
      have hHj : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) P‖ ≤ H := hHmono j hj_le
      calc ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖
          ≤ ∑ k ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ := hsingle
        _ ≤ Cbr j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) P‖ := hCbr_bound j P
        _ ≤ Cbr j * H := mul_le_mul_of_nonneg_left hHj (hCbr_nn j)
    have hjet_sq : ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ Cbr j ^ 2 * H ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hjetH 2
      calc ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ (Cbr j * H) ^ 2 := h1
        _ = Cbr j ^ 2 * H ^ 2 := by ring
    have hbound1 : 1 + ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        (1 + Cbr j ^ 2) * (1 + H ^ 2) := by
      nlinarith [hjet_sq, sq_nonneg (Cbr j), sq_nonneg H,
        mul_nonneg (sq_nonneg (Cbr j)) (sq_nonneg H)]
    calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
        ≤ Kslot j * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := hks
      _ ≤ Kslot j * ((1 + Cbr j ^ 2) * (1 + H ^ 2)) :=
          mul_le_mul_of_nonneg_left hbound1 (hKslot_nn j)
      _ = Kslot j * (1 + Cbr j ^ 2) * (1 + H ^ 2) := by ring
  have hsumBound : ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ j ∈ Finset.range (i + 1), Kslot j * (1 + Cbr j ^ 2)) * (1 + H ^ 2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hj_le : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact hslotBound j hj_le
  have hnorm_sq : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Ktot * (1 + H ^ 2) := by
    refine le_trans hjetL2 ?_
    rw [hKtot, mul_assoc]
    exact mul_le_mul_of_nonneg_left hsumBound (hCpo_nn i)
  have hsqrt_le : Real.sqrt (1 + H ^ 2) ≤ 1 + H := by
    have h1 : (1 : ℝ) + H ^ 2 ≤ (1 + H) ^ 2 := by nlinarith [hH_nn]
    have h2 : Real.sqrt (1 + H ^ 2) ≤ Real.sqrt ((1 + H) ^ 2) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by linarith [hH_nn])] at h2
  calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖
      = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Ktot * (1 + H ^ 2)) := Real.sqrt_le_sqrt hnorm_sq
    _ = Real.sqrt Ktot * Real.sqrt (1 + H ^ 2) := Real.sqrt_mul hKtot_nn _
    _ ≤ Real.sqrt Ktot * (1 + H) := mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)


theorem appCc_jet_l2Sq_le
    (g : SmoothRiemannianMetric I M) (b c j : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b) (K : ℕ → ℝ)
    (hK : ∀ i, i ≤ j → 0 ≤ K i)
    (hΦ : ∀ i, i ≤ j → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ K i) :
    ‖iteratedCovGrad (I := I) g 0 c j
        (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
      diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1), K i *
          ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  set F : M → ℝ := fun x => diagonalGridGrowthFactor (E := E) j *
    ∑ i ∈ Finset.range (j + 1), K i *
      ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
          ((iteratedCovGrad (I := I) g 0 b l W).toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F μ := by
    rw [hF_def]
    exact (MeasureTheory.integrable_finset_sum (Finset.range (j + 1)) (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
          (iteratedCovGrad (I := I) g 0 b l W))).const_mul (K i))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (c + j) x
          ((iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c Φ W)).toSection x) ≤ F x := by
    intro x
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le
        (I := I) (M := M) g b c Φ W j x) ?_
    rw [hF_def]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact mul_le_mul (hΦ i hij x) le_rfl
      (Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (b + l) x _)) (hK i hij)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 0 (c + j)
    (iteratedCovGrad (I := I) g 0 c j
      (operatorFieldApply (I := I) (M := M) g b c Φ W)) F hF_int hpt
  refine le_trans hnorm (le_of_eq ?_)
  rw [hF_def, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (j + 1)) (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
          (iteratedCovGrad (I := I) g 0 b l W))).const_mul (K i))]
  apply congrArg (fun z : ℝ => diagonalGridGrowthFactor (E := E) j * z)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
        (iteratedCovGrad (I := I) g 0 b l W))]
  apply congrArg (fun z : ℝ => K i * z)
  exact Finset.sum_congr rfl (fun l _ => by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (b + l)])


end DifferentialGeometry.Integral.Connection

end
