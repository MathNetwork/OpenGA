import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]


theorem ccTensorContract_l2_twoArm_mixed_orderUniform_le
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ), q ≤ a →
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  set Kf : ℕ → ℝ := fun k => (ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose
    with hKf_def
  have hKf_nn : ∀ k, 0 ≤ Kf k := fun k =>
    (ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.1
  have hKf_spec : ∀ k, ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          Kf k * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := fun k =>
    (ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.2
  refine ⟨(Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf,
    le_trans (hKf_nn 0) (Finset.le_sup' Kf (Finset.mem_range.mpr (Nat.succ_pos a))), ?_⟩
  intro q hq Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  have hqmem : q ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
  have hKq_le : Kf q ≤
      (Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf :=
    Finset.le_sup' Kf hqmem
  refine le_trans (hKf_spec q Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup) ?_
  refine mul_le_mul_of_nonneg_right hKq_le ?_
  have h1 : 0 ≤ ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by positivity
  have h2 : 0 ≤ ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by positivity
  linarith

set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem ccTensorBilinSymm_metricCauchySchwarzBound_le_sobolevHsNorm_lossy_order
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ)
    (h_lossy : 2 * Module.finrank ℝ E + 4 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : SmoothCcTensor g₀ 0 2),
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) := by
  classical
  set kE : ℕ := Module.finrank ℝ E / 2 + 1 with hkE_def
  have hkE_super : 2 * kE > Module.finrank ℝ E + 2 * 0 := by
    rw [hkE_def]; omega
  have h4kEm : (4 * kE : ℕ) ≤ m := by
    rw [hkE_def]; omega

  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck_gNorm
      (I := I) (M := M) g₀ 0 2 kE 0 hkE_super

  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g₀ (2 * kE)
  refine ⟨C₁ * (C₂ + 1), by positivity, fun T => ?_⟩
  letI : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2

  have hupper : C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ ≤
      (C₁ * (C₂ + 1)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ := by
    have hstep2 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ =
        (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq
        (I := I) (M := M) g₀ (2 * kE) T
    have hstep3 : (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal ≤
        C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ := hC₂ T
    have hstep4 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T‖ := by
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
      have : (2 * (2 * kE) : ℕ) ≤ m := by omega
      exact_mod_cast this
    have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T =
        smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ with hNm_def
    have hNm_nn : 0 ≤ Nm := norm_nonneg _
    have hspec_le : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤ Nm := by
      rw [hNm_def, ← hembed_eq]; exact hstep4
    calc C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (2 * kE) T‖
        = C₁ * (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal := by rw [hstep2]
      _ ≤ C₁ * (C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖) :=
          mul_le_mul_of_nonneg_left hstep3 hC₁_pos.le
      _ ≤ C₁ * (C₂ * Nm) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hspec_le hC₂_nn) hC₁_pos.le
      _ ≤ (C₁ * (C₂ + 1)) * Nm := by nlinarith [hNm_nn, hC₁_pos.le, hC₂_nn]

  have hfibre := fun x : M => le_trans (hC₁ T x) hupper

  intro x v w
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ T x
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn

  have hvw := hcs v w
  have hwv := hcs w v
  have hfx := hfibre x

  rw [ccTensorBilinSymm_apply]
  have habs : |(1 / 2 : ℝ) *
      (smoothCcTensorBilinForm (I := I) g₀ T x v w + smoothCcTensorBilinForm (I := I) g₀ T x w v)| ≤
      (1 / 2 : ℝ) * (|smoothCcTensorBilinForm (I := I) g₀ T x v w| +
        |smoothCcTensorBilinForm (I := I) g₀ T x w v|) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  refine habs.trans ?_

  nlinarith [hvw, hwv, hfx, hsv_nn, hsw_nn, hmul_nn, mul_nonneg hsw_nn hsv_nn,
    mul_le_mul_of_nonneg_right hfx hmul_nn,
    mul_le_mul_of_nonneg_right hfx (mul_nonneg hsw_nn hsv_nn)]

theorem deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_dataWeighted_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤
            (ΛC * max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                 ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖) ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨Ksob, hKsob_pos, hKsob⟩ :=
    ccTensorBilinSymm_metricCauchySchwarzBound_le_sobolevHsNorm_lossy_order (I := I) (M := M) g₀ (a + 1)
      (by omega)
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hfib⟩ :=
    deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm
      (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
  refine ⟨ΛC * (Ksob + 1), Γ, by positivity, hΓ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  set βT : ℝ := Ksob * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 1 : ℕ) : ℝ) T‖ with hβT_def
  set βT' : ℝ := Ksob * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 1 : ℕ) : ℝ) T'‖ with hβT'_def
  have hβT_nn : 0 ≤ βT := by rw [hβT_def]; positivity
  have hβT'_nn : 0 ≤ βT' := by rw [hβT'_def]; positivity
  have hcastord : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hβTfib : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) βT := by
    rw [hβT_def]; exact hKsob T
  have hβT'fib : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') βT' := by
    rw [hβT'_def]; exact hKsob T'
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hfib T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hβT_nn hβT'_nn hβTfib hβT'fib hTball hT'ball
  set Dm : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ with hDm_def
  have hDm_nn : 0 ≤ Dm := le_trans (norm_nonneg _) (le_max_left _ _)
  have hΛle : ΛC ^ 2 ≤ (ΛC * (Ksob + 1)) ^ 2 := by
    refine pow_le_pow_left₀ hΛC_nn ?_ 2
    nlinarith [hΛC_nn, hKsob_pos.le]
  have hβmax_eq : max βT βT' = Ksob * Dm := by
    rw [hβT_def, hβT'_def, hDm_def, hcastord, mul_max_of_nonneg _ _ hKsob_pos.le]
  refine ⟨C₀, C₁, C₂, hid, fun x => le_trans (hC₀sup x) hΛle,
    fun x => le_trans (hC₁sup x) hΛle, ?_, hC₀jet, hC₁jet, hC₂jet⟩
  intro x
  refine le_trans (hC₂sup x) ?_
  rw [hβmax_eq]
  refine pow_le_pow_left₀ (mul_nonneg hΛC_nn (mul_nonneg hKsob_pos.le hDm_nn)) ?_ 2
  nlinarith [hΛC_nn, hKsob_pos.le, hDm_nn, mul_nonneg hKsob_pos.le hDm_nn]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_dataWeighted_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * (max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                     ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
                   * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
                       ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
              Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)) := by
  classical
  by_cases hδ₀_nn : 0 ≤ δ₀
  · obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
      deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_dataWeighted_ballUniform_of_symm
        (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
    obtain ⟨K₀, hK₀_nn, hK₀⟩ := ccTensorContract_l2_twoArm_mixed_orderUniform_le (I := I) g₀ 2 2 a
    obtain ⟨K₁, hK₁_nn, hK₁⟩ := ccTensorContract_l2_twoArm_mixed_orderUniform_le (I := I) g₀ 3 2 a
    obtain ⟨K₂, hK₂_nn, hK₂⟩ := ccTensorContract_l2_twoArm_mixed_orderUniform_le (I := I) g₀ 4 2 a
    obtain ⟨Cemb1, hCemb1_nn, hemb1⟩ :=
      deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow (I := I) g₀ a ha_super
    set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
    have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
    have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
    have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
    set base : ℝ := Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1)) with hbase_def
    have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity
    refine ⟨3 * Real.sqrt base, by positivity, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
    set Dm : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ with hDm_def
    have hDm_nn : 0 ≤ Dm := le_trans (norm_nonneg _) (le_max_left _ _)
    set S₂ : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₂_def
    set S₁ : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₁_def
    have hS₂_nn : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun i _ => sq_nonneg _
    obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
      hcoeff T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
    set A₀ := operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
    set A₁ := operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
    set A₂ := operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
    have hN_split : deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
          A₀ + A₁ + A₂ := by
      rw [hA₀, hA₁, hA₂]; exact hid
    have hWsup1 : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
          (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 := by
      intro m hm x
      rw [Real.sq_sqrt (by positivity)]
      have hembx := hemb1 (T - T') x
      rw [hS₁_def]
      have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
      refine le_trans (Finset.single_le_sum
        (f := fun qq => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + qq) x
          ((iteratedCovGrad (I := I) g₀ 0 2 qq (T - T')).toSection x))
        (fun qq _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + qq) x _) hmem) ?_
      exact hembx
    have hWjet : ∀ (m : ℕ), m ≤ 2 →
        (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
      intro m hm
      have hcomp : ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
            ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
        intro l
        have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          rw [SmoothCcTensor.norm_def]
          exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
            (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
        have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          rw [SmoothCcTensor.norm_def]
          exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
        rw [hbridgeL, hbridgeR]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x
        simpa only [Nat.add_assoc] using hrw
      rw [show (∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
          ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
        Finset.sum_congr rfl (fun l _ => hcomp l)]
      set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
      have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
      have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆ Finset.range (a + m + 1) := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨l, hl, rfl⟩ := hi
        rw [Finset.mem_range] at hl ⊢
        omega
      have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
          m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
      calc (∑ l ∈ Finset.range (q + 1), f (m + l))
          = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), f i :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ i ∈ Finset.range (a + m + 1), f i :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)
    have hcoeffjet_le : ∀ (m : ℕ) (Cm : SmoothCcTensor g₀ (2 + m) 2) (bnd : ℝ),
        0 ≤ bnd →
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd →
        (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd := by
      intro m Cm bnd hbnd_nn hjet
      refine le_trans ?_ hjet
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => sq_nonneg _)
      exact Finset.range_mono (by omega)
    have harmTop : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
        Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
      have htame := hK₂ q hq C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
        (ΛC * Dm) (Real.sqrt (Cemb1 ^ 2 * S₁)) (mul_nonneg hΛC_nn hDm_nn) (Real.sqrt_nonneg _)
        hC₂sup (hWsup1 2 (by norm_num))
      have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 = Cemb1 ^ 2 * S₁ := Real.sq_sqrt (by positivity)
      have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤
          Γ ^ 2 :=
        hcoeffjet_le 2 C₂ (Γ ^ 2) (sq_nonneg _) hC₂jet
      have hwjet : (∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 4 l (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2) ≤
          S₂ := by
        have h := hWjet 2 (by norm_num)
        rw [hS₂_def]
        exact h
      have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2 ≤ base * (S₁ + Dm ^ 2 * S₂) := by
        rw [hA₂]
        refine le_trans htame ?_
        rw [hΛWsq]
        have ha1 : (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2 ≤ (Cemb1 ^ 2 * S₁) * Γ ^ 2 :=
          mul_le_mul_of_nonneg_left hcjet (by positivity)
        have ha2 : (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 4 l
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 ≤ (ΛC * Dm) ^ 2 * S₂ :=
          mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
        have hinner :
            (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
              + (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 4 l
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2
            ≤ (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + Dm ^ 2 * S₂) := by
          set B : ℝ := (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) with hB_def
          have hB_nn : 0 ≤ B := by rw [hB_def]; positivity
          have hcoeff_le : Cemb1 ^ 2 * Γ ^ 2 ≤ B := by
            rw [hB_def]
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          have hΛC_le : ΛC ^ 2 ≤ B := by
            rw [hB_def]
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg Γ),
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          have hterm1 : (Cemb1 ^ 2 * S₁) * Γ ^ 2 ≤ B * S₁ := by
            rw [show (Cemb1 ^ 2 * S₁) * Γ ^ 2 = (Cemb1 ^ 2 * Γ ^ 2) * S₁ by ring]
            exact mul_le_mul_of_nonneg_right hcoeff_le hS₁_nn
          have hterm2 : (ΛC * Dm) ^ 2 * S₂ ≤ B * (Dm ^ 2 * S₂) := by
            rw [show (ΛC * Dm) ^ 2 * S₂ = ΛC ^ 2 * (Dm ^ 2 * S₂) by ring]
            exact mul_le_mul_of_nonneg_right hΛC_le (by positivity)
          have hsum_le : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + (ΛC * Dm) ^ 2 * S₂ ≤
              B * (S₁ + Dm ^ 2 * S₂) := by
            calc (Cemb1 ^ 2 * S₁) * Γ ^ 2 + (ΛC * Dm) ^ 2 * S₂
                ≤ B * S₁ + B * (Dm ^ 2 * S₂) := add_le_add hterm1 hterm2
              _ = B * (S₁ + Dm ^ 2 * S₂) := by ring
          linarith [ha1, ha2, hsum_le]
        have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
              + (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 4 l
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 := by positivity
        calc K₂ * ((Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
                + (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 4 l
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2)
            ≤ Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + Dm ^ 2 * S₂)) :=
              mul_le_mul hK₂_le hinner hinner_nn hKmax_nn
          _ = base * (S₁ + Dm ^ 2 * S₂) := by rw [hbase_def]; ring
      have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
          Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
        have hsqrt_le : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
            Real.sqrt (base * (S₁ + Dm ^ 2 * S₂)) := by
          rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ =
              Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2) from
            (Real.sqrt_sq (norm_nonneg _)).symm]
          exact Real.sqrt_le_sqrt hsq
        refine hsqrt_le.trans ?_
        have hrhs_nn : 0 ≤ Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
          have : 0 ≤ Real.sqrt S₁ + Dm * Real.sqrt S₂ := by
            have := mul_nonneg hDm_nn (Real.sqrt_nonneg S₂)
            have := Real.sqrt_nonneg S₁
            linarith
          exact mul_nonneg (Real.sqrt_nonneg _) this
        have hsq_rhs : (Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂)) ^ 2 =
            base * (S₁ + Dm ^ 2 * S₂ + 2 * Dm * (Real.sqrt S₁ * Real.sqrt S₂)) := by
          rw [mul_pow, Real.sq_sqrt hbase_nn, add_sq, mul_pow,
            Real.sq_sqrt hS₁_nn, Real.sq_sqrt hS₂_nn]
          ring
        have hle_sq : base * (S₁ + Dm ^ 2 * S₂) ≤
            (Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂)) ^ 2 := by
          rw [hsq_rhs]
          have hcross_nn : 0 ≤ 2 * Dm * (Real.sqrt S₁ * Real.sqrt S₂) := by
            have := mul_nonneg (Real.sqrt_nonneg S₁) (Real.sqrt_nonneg S₂)
            linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hDm_nn)
              (mul_nonneg (Real.sqrt_nonneg S₁) (Real.sqrt_nonneg S₂))]
          nlinarith [hbase_nn, hcross_nn, mul_nonneg hbase_nn hcross_nn]
        calc Real.sqrt (base * (S₁ + Dm ^ 2 * S₂))
            ≤ Real.sqrt ((Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂)) ^ 2) :=
              Real.sqrt_le_sqrt hle_sq
          _ = Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := Real.sqrt_sq hrhs_nn
      exact hfinal
    have harmLow : ∀ (m : ℕ) (hm : m ≤ 1) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
        (hKm_le : Km ≤ Kmax)
        (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
          0 ≤ ΛΦ → 0 ≤ ΛW →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
            Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
                + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
        (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
        (hCmjet : (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤ Real.sqrt (base * S₁) := by
      intro m hm Cm Km hKm_le hKm hCmsup hCmjet
      have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
        ΛC (Real.sqrt (Cemb1 ^ 2 * S₁)) hΛC_nn (Real.sqrt_nonneg _) hCmsup
        (hWsup1 m (by omega))
      have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 = Cemb1 ^ 2 * S₁ := Real.sq_sqrt (by positivity)
      have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤
          Γ ^ 2 := hcoeffjet_le m Cm (Γ ^ 2) (sq_nonneg _) hCmjet
      have hwjet : (∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S₁ := by
        have h := hWjet m (by omega)
        refine le_trans h ?_
        rw [hS₁_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun i _ _ => sq_nonneg _)
      have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤ base * S₁ := by
        refine le_trans htame ?_
        rw [hΛWsq]
        have ha1 : (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb1 ^ 2 * S₁) * Γ ^ 2 :=
          mul_le_mul_of_nonneg_left hcjet (by positivity)
        have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S₁ :=
          mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
        have hinner :
            (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
            ≤ (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁ := by
          have hsum_le : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + ΛC ^ 2 * S₁ ≤
              (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁ := by
            have hfactor : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + ΛC ^ 2 * S₁ =
                (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₁ := by ring
            rw [hfactor]
            refine mul_le_mul_of_nonneg_right ?_ hS₁_nn
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg Γ),
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          linarith [ha1, ha2, hsum_le]
        have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by positivity
        calc Km * ((Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
                + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                    (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
            ≤ Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁) :=
              mul_le_mul hKm_le hinner hinner_nn hKmax_nn
          _ = base * S₁ := by rw [hbase_def]; ring
      rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ =
          Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq
    have ha0 := harmLow 0 (by norm_num) C₀ K₀ hK₀_le (hK₀ q hq) hC₀sup hC₀jet
    have ha1 := harmLow 1 (by norm_num) C₁ K₁ hK₁_le (hK₁ q hq) hC₁sup hC₁jet
    have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀‖ ≤ Real.sqrt (base * S₁) := by
      rw [hA₀]; exact ha0
    have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₁‖ ≤ Real.sqrt (base * S₁) := by
      rw [hA₁]; exact ha1
    have hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        3 * Real.sqrt base * (Dm * Real.sqrt S₂ + Real.sqrt S₁) := by
      rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 q (A₀ + A₁) A₂,
        iteratedCovGrad_add (I := I) g₀ 0 2 q A₀ A₁]
      have hsqrt_lowfac : Real.sqrt (base * S₁) = Real.sqrt base * Real.sqrt S₁ :=
        Real.sqrt_mul hbase_nn S₁
      have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀ +
            iteratedCovGrad (I := I) g₀ 0 2 q A₁ +
            iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
          Real.sqrt (base * S₁) + Real.sqrt (base * S₁) +
            Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
        refine le_trans (norm_add_le _ _) ?_
        refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) harmTop
      refine htri.trans ?_
      rw [hsqrt_lowfac]
      have hsb_nn : 0 ≤ Real.sqrt base := Real.sqrt_nonneg _
      have hs1_nn : 0 ≤ Real.sqrt S₁ := Real.sqrt_nonneg _
      have hs2_nn : 0 ≤ Real.sqrt S₂ := Real.sqrt_nonneg _
      nlinarith [hsb_nn, hs1_nn, hs2_nn, hDm_nn,
        mul_nonneg hsb_nn hs1_nn, mul_nonneg hsb_nn hs2_nn,
        mul_nonneg (mul_nonneg hDm_nn hsb_nn) hs2_nn]
    refine hgoal.trans (le_of_eq ?_)
    rw [hS₂_def, hS₁_def]
  · refine ⟨0, le_refl 0, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
    have hδ₀_neg : δ₀ < 0 := lt_of_not_ge hδ₀_nn
    have hδ_neg : δ < 0 := lt_of_le_of_lt hδ_le hδ₀_neg
    by_cases hM : Nonempty M
    · obtain ⟨x₀⟩ := hM
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [this]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T x₀ v v| := abs_nonneg _
      have hδ_nonneg : 0 ≤ δ := by
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
            mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      linarith
    · rw [not_nonempty_iff] at hM
      have hzero : ∀ (r s : ℕ) (P : SmoothCcTensor g₀ r s), ‖P‖ = 0 := by
        intro r s P
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [zero_mul]
      exact le_of_eq (hzero _ _ _)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
