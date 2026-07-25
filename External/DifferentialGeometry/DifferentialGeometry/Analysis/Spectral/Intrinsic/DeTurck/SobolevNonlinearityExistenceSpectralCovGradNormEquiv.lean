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

omit [CompactSpace M] [I.Boundaryless] in
private theorem oneMinusConnLapSmoothIter_succ'
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (k + 1) S =
      oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ, ih, ← oneMinusConnLapSmoothIter_succ]

private theorem exists_oneMinusConnLapSmooth_toHs_le_toHs_succ
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (oneMinusConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ m
  refine ⟨1 + C₁, by positivity, fun U => ?_⟩
  have hsub : oneMinusConnLapSmooth (I := I) g₀ 0 2 U =
      U - rawTensorConnLapSmooth (I := I) g₀ 0 2 U := rfl
  rw [hsub, SmoothCcTensor.toHs_sub]
  have hmono : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) m U‖ ≤
      ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (m + 1) U‖ :=
    toHs_norm_mono (I := I) g₀ (Nat.le_succ m) U
  have hlap := hC₁ U
  calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) m U -
          DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖
      ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m U‖ +
          ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ :=
        norm_sub_le _ _
    _ ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ +
          C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := add_le_add hmono hlap
    _ = (1 + C₁) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by ring

private theorem exists_oneMinusConnLapSmoothIter_toHs_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) k S‖ := by
  induction k with
  | zero =>
      refine ⟨1, zero_le_one, fun S => ?_⟩
      simp only [oneMinusConnLapSmoothIter_zero, one_mul, le_refl]
  | succ k ih =>
      obtain ⟨Ck, hCk_nn, hCk⟩ := ih
      obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
        exists_oneMinusConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ k
      refine ⟨Ck * Cstep, mul_nonneg hCk_nn hCstep_nn, fun S => ?_⟩
      rw [oneMinusConnLapSmoothIter_succ']
      calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) 0
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖
          ≤ Ck * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ :=
            hCk (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
        _ ≤ Ck * (Cstep * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖) :=
            mul_le_mul_of_nonneg_left (hCstep S) hCk_nn
        _ = (Ck * Cstep) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖ := by ring

theorem exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
  classical
  obtain ⟨Cl2, hCl2_nn, hCl2⟩ := exists_l2Norm_le_toHs_zero (I := I) g₀
  obtain ⟨Cdrop, hCdrop_nn, hCdrop⟩ := exists_oneMinusConnLapSmoothIter_toHs_le_toHs (I := I) g₀ k
  obtain ⟨Chebey, hChebey_nn, hChebey⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 k
  refine ⟨Cl2 * Cdrop * Chebey, by positivity, fun S => ?_⟩

  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hsq := ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2 (I := I) (M := M) g₀ k S
  have hnorm_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
    have h1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by rw [hembed_eq]
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
      have hnn1 : (0 : ℝ) ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      have hnn2 : (0 : ℝ) ≤
          ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := norm_nonneg _
      nlinarith [hsq, hnn1, hnn2]
    rw [h1, h2]
  rw [hnorm_eq]

  have hjet_eq : ∀ j : ℕ,
      tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j) (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := fun j =>
    (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
  have hl2 := hCl2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)
  have hdrop := hCdrop S
  have hhebey := hChebey S
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have htoHsk_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) k S‖ := norm_nonneg _
  have htoHs0_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ :=
    norm_nonneg _
  have hhebey' : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) k S‖ ≤
      Chebey * ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
    refine le_trans hhebey ?_
    refine mul_le_mul_of_nonneg_left ?_ hChebey_nn
    exact le_of_eq (Finset.sum_congr rfl (fun j _ => hjet_eq j))
  calc ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖
      ≤ Cl2 * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := hl2
    _ ≤ Cl2 * (Cdrop * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) k S‖) := mul_le_mul_of_nonneg_left hdrop hCl2_nn
    _ ≤ Cl2 * (Cdrop * (Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCl2_nn
        exact mul_le_mul_of_nonneg_left hhebey' hCdrop_nn
    _ = Cl2 * Cdrop * Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by ring

omit [BoundarylessManifold I M] in
private theorem tensorL2Inner_eq_tsum_tensorL2Coeff_cross
    (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner_eq]
  have h_par := b.tsum_inner_mul_inner (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← h_par]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 A) i,
    tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 B) i]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) = ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from
    real_inner_comm _ _]

private theorem covGrad_rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set U : SmoothCcTensor g₀ 0 2 := rawTensorConnLapIter (I := I) g₀ 0 2 i S with hU_def
  have hnorm_sq : ‖covGrad (I := I) (M := M) g₀ 0 2 U‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun := by
    rw [SmoothCcTensor.norm_def (covGrad (I := I) (M := M) g₀ 0 2 U)]
    exact tensorL2Norm_sq_toFun (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 U)
  rw [hnorm_sq,
    tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g₀ 2 U]
  have hraw_eq : rawTensorConnLapSmooth (I := I) g₀ 0 2 U =
      rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S := by
    rw [hU_def, rawTensorConnLapIter_succ]
  rw [hraw_eq, tensorL2Inner_eq_tsum_tensorL2Coeff_cross (I := I) (M := M) g₀
    (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S) U, hU_def]
  rw [← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m (i + 1),
    tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  have hpow : ((-L) ^ (i + 1) * c) * ((-L) ^ i * c) = (-L) ^ (2 * i + 1) * c ^ 2 := by
    rw [show (2 * i + 1) = (i + 1) + i by ring, pow_add]
    ring
  rw [hpow]
  rw [(odd_two_mul_add_one i).neg_pow L]
  ring

private theorem covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  have hnn : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  have hsq :
      ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ ^ 2 := by
    rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ i S,
      ccSpectralEmbed_norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      have hpow_le : (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) ≤
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) :=
        pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)
      exact mul_le_mul_of_nonneg_right hpow_le (sq_nonneg c)
    · have hsummable := (ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
      refine Summable.of_nonneg_of_le ?_ ?_ hsummable
      · intro m
        have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        positivity
      · intro m
        have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
            1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
        have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
            (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast]
        rw [hweight_eq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg _)
    · exact (ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_iteratedCovGrad_comp_local
    (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i) (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
      (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_iteratedCovGrad_order_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {n n' : ℕ} (h : n = n')
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Clow, hClow_nn, hClow⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
  obtain ⟨Cgard, hCgard_nn, hCgard⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) (M := M) g₀ 3 k
  obtain ⟨Ceven, hCeven_nn, hCeven⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
  have hcommfam : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          C * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => exists_rawConnLapIter_covGrad_commutator_l2Norm_le (I := I) (M := M) g₀ 2 i
  set Ccomm : ℕ → ℝ := fun i => Classical.choose (hcommfam i) with hCcomm_def
  have hCcomm_nn : ∀ i, 0 ≤ Ccomm i := fun i => (Classical.choose_spec (hcommfam i)).1
  have hCcomm : ∀ i, ∀ S : SmoothCcTensor g₀ 0 2,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        Ccomm i * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => (Classical.choose_spec (hcommfam i)).2
  set Ccommsum : ℝ := ∑ i ∈ Finset.range (k + 1), Ccomm i with hCcommsum_def
  have hCcommsum_nn : 0 ≤ Ccommsum :=
    Finset.sum_nonneg (fun i _ => hCcomm_nn i)
  refine ⟨Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven), by positivity,
    fun S => ?_⟩
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hccmono : ∀ (σ : ℕ), σ ≤ 2 * k + 1 →
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((σ : ℕ) : ℝ) S‖ ≤ Nspec := by
    intro σ hσ
    rw [hNspec_def, ← hembed_eq]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
    have : (σ : ℕ) ≤ (2 * k + 1 : ℕ) := hσ
    exact_mod_cast this

  have hlow_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤ Nspec := by
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)

  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Clow * Nspec := by
    refine le_trans (hClow S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hClow_nn

  have heven_le : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Ceven * Nspec := by
    refine le_trans (hCeven S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hCeven_nn

  have hccoeff_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 3 i
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (1 + Ccomm i * Ceven) * Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit :
        rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S) =
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S) +
            (rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)) := by
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hmain : ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤ Nspec := by
      refine le_trans
        (covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd (I := I) (M := M) g₀ i S) ?_
      exact hccmono (2 * i + 1) (by omega)
    have hcomm := hCcomm i S
    have hsub_le : 2 * i ≤ 2 * k + 1 := by omega
    have hsubrange : ∑ a ∈ Finset.range (2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ ≤
        ∑ a ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖)
        (Finset.range_mono hsub_le) (fun a _ _ => norm_nonneg _)
    have hcommterm :
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          Ccomm i * Ceven * Nspec := by
      calc ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
          ≤ Ccomm i * ∑ a ∈ Finset.range (2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := hcomm
        _ ≤ Ccomm i * ∑ a ∈ Finset.range (2 * k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
            mul_le_mul_of_nonneg_left hsubrange (hCcomm_nn i)
        _ ≤ Ccomm i * (Ceven * Nspec) :=
            mul_le_mul_of_nonneg_left heven_le (hCcomm_nn i)
        _ = Ccomm i * Ceven * Nspec := by ring
    calc ‖covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ +
          ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
        ≤ Nspec + Ccomm i * Ceven * Nspec :=
          add_le_add hmain hcommterm
      _ = (1 + Ccomm i * Ceven) * Nspec := by ring

  have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ ≤
      Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
    have hbridge : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have h := norm_iteratedCovGrad_comp_local (I := I) (M := M) g₀ 2 1 (2 * k) S
      have hcov : covGrad (I := I) (M := M) g₀ 0 2 S =
          iteratedCovGrad (I := I) g₀ 0 2 1 S := rfl
      have horder : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 2 * k) S‖ :=
        norm_iteratedCovGrad_order_eq (I := I) (M := M) g₀ 2 (by omega) S
      rw [horder, ← h, hcov]
    rw [hbridge]
    have hgard := hCgard (2 * k) (le_refl _) (covGrad (I := I) (M := M) g₀ 0 2 S)
    have hgard' : ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        Cgard * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have heq1 : tensorL2Norm (I := I) (M := M) g₀ 0 (3 + 2 * k)
            (iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
              (covGrad (I := I) (M := M) g₀ 0 2 S)).toFun =
          ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ :=
        DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
          (iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S))
      rw [← heq1]
      refine le_trans hgard ?_
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCgard_nn
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S))
    have hsumcoeff : ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
      calc ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖
          ≤ ∑ i ∈ Finset.range (k + 1), (1 + Ccomm i * Ceven) * Nspec :=
            Finset.sum_le_sum hccoeff_le
        _ = ∑ i ∈ Finset.range (k + 1), (Nspec + (Ccomm i) * (Ceven * Nspec)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_mul]
            rw [hCcommsum_def]
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖
        ≤ Cgard * ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := hgard'
      _ ≤ Cgard * ((((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec) :=
          mul_le_mul_of_nonneg_left hsumcoeff hCgard_nn
      _ = Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by ring

  rw [Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖) (2 * k + 1)]
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖
      ≤ Clow * Nspec + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec :=
        add_le_add hlowsum htop_le
    _ = (Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven)) * Nspec := by ring

theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ := by
  classical
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact hC S
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact hC S

private theorem rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * t) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S))]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m t]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  rw [mul_pow, ← pow_mul, mul_comm t 2, (even_two_mul t).neg_pow L]

private theorem exists_spectralModeTsum_le_iteratedCovGrad_sum_sq
    (g₀ : SmoothRiemannianMetric I M) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 ≤
          C * (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by
  classical
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      exists_iteratedCovGrad_rawConnLapIter_l2Norm_le (I := I) (M := M) g₀ t 2
    refine ⟨(Cfun 0) ^ 2, by positivity, fun S => ?_⟩
    have hj2t : j = 2 * t := by omega
    have htsum : ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 := by
      rw [rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ t S, hj2t]
    rw [htsum]
    have hnorm_le : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ≤
        Cfun 0 * ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := by
      have h := hCfun 0 S
      rw [iteratedCovGrad_zero (I := I) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 t S)] at h
      rw [SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)]
      have hrange : 2 * t + 0 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hsum_nn : 0 ≤ ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    have hnn : 0 ≤ ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ :=
      norm_nonneg _
    calc ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2
        ≤ (Cfun 0 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg (hCfun_nn 0) hsum_nn]
          · exact hnorm_le
      _ = (Cfun 0) ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by ring
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      exists_iteratedCovGrad_rawConnLapIter_l2Norm_le (I := I) (M := M) g₀ t 2
    refine ⟨(Cfun 1) ^ 2, by positivity, fun S => ?_⟩
    have hj2t : j = 2 * t + 1 := by omega
    have htsum : ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
        ‖covGrad (I := I) (M := M) g₀ 0 2
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 := by
      rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ t S, hj2t]
    rw [htsum]
    have hnorm_le : ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ≤
        Cfun 1 * ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := by
      have h := hCfun 1 S
      have hcov : iteratedCovGrad (I := I) g₀ 0 2 1
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S) =
          covGrad (I := I) (M := M) g₀ 0 2
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S) := rfl
      rw [hcov] at h
      have hrange : 2 * t + 1 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hsum_nn : 0 ≤ ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    have hnn : 0 ≤ ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ := norm_nonneg _
    calc ‖covGrad (I := I) (M := M) g₀ 0 2
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2
        ≤ (Cfun 1 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg (hCfun_nn 1) hsum_nn]
          · exact hnorm_le
      _ = (Cfun 1) ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by ring

theorem exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set Cmode : ℕ → ℝ := fun j =>
    (exists_spectralModeTsum_le_iteratedCovGrad_sum_sq (I := I) (M := M) g₀ j).choose
    with hCmode_def
  have hCmode_nn : ∀ j, 0 ≤ Cmode j := fun j =>
    (exists_spectralModeTsum_le_iteratedCovGrad_sum_sq (I := I) (M := M) g₀ j).choose_spec.1
  have hCmode : ∀ j, ∀ S : SmoothCcTensor g₀ 0 2,
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 ≤
        Cmode j * (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 :=
    fun j => (exists_spectralModeTsum_le_iteratedCovGrad_sum_sq (I := I) (M := M) g₀ j).choose_spec.2
  set Csum : ℝ := ∑ j ∈ Finset.range (n + 1), Cmode j with hCsum_def
  have hCsum_nn : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hCmode_nn j)
  refine ⟨Real.sqrt ((2 : ℝ) ^ n * Csum), Real.sqrt_nonneg _, fun S => ?_⟩
  set Sall : ℝ := ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
    with hSall_def
  have hSall_nn : 0 ≤ Sall := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S =
      ccSpectralEmbed (I := I) (M := M) g₀ (n : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hweight_eq : ∀ m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) m (n : ℝ) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ n := by
    intro m
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  have hsq_tsum : Nspec ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ n *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 := by
    rw [hNspec_def, hembed_eq, ccSpectralEmbed_norm_sq_eq_tsum]
    exact tsum_congr (fun m => by rw [hweight_eq m])
  have hmode_summable : ∀ j : ℕ, Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
    intro j
    have hfull := (ccSpectralEmbed (I := I) (M := M) g₀ (j : ℝ) S).weighted_summable
    refine Summable.of_nonneg_of_le ?_ ?_ hfull
    · intro m
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · intro m
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      have hweightj : tensorSobolevWeight (I := I) (M := M) m (j : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ j := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweightj, ccSpectralEmbed_coeff]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le j) (sq_nonneg _)
  have hbinom_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
    apply Summable.mul_left
    exact summable_sum (fun j _ => hmode_summable j)
  have hlhs_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ n *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
    have hfull := (ccSpectralEmbed (I := I) (M := M) g₀ (n : ℝ) S).weighted_summable
    refine (summable_congr (fun m => ?_)).mp hfull
    rw [hweight_eq m, ccSpectralEmbed_coeff]
  have hsq_le : Nspec ^ 2 ≤ (2 : ℝ) ^ n * Csum * Sall ^ 2 := by
    have hstep1 : Nspec ^ 2 ≤
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 := by
      rw [hsq_tsum]
      refine Summable.tsum_le_tsum (fun m => ?_) hlhs_summable hbinom_summable
      · set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
        set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
        have hL_nn : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) m
        have hbinom : (1 + L) ^ n ≤ (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), L ^ j := by
          rw [add_comm, add_pow, Finset.mul_sum]
          refine Finset.sum_le_sum (fun p hp => ?_)
          rw [one_pow, mul_one]
          have hch : ((n.choose p : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
            have hbnd := Nat.choose_le_two_pow n p
            calc ((n.choose p : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hbnd
              _ = (2 : ℝ) ^ n := by push_cast; ring
          calc L ^ p * (n.choose p) ≤ L ^ p * (2 : ℝ) ^ n :=
                mul_le_mul_of_nonneg_left hch (pow_nonneg hL_nn p)
            _ = (2 : ℝ) ^ n * L ^ p := by ring
        have hc2_nn : 0 ≤ c ^ 2 := sq_nonneg c
        calc (1 + L) ^ n * c ^ 2
            ≤ ((2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), L ^ j) * c ^ 2 :=
              mul_le_mul_of_nonneg_right hbinom hc2_nn
          _ = (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), L ^ j * c ^ 2 := by
              rw [mul_assoc, Finset.sum_mul]
    have hstep2 : ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 =
        (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
          ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact Summable.tsum_finsetSum (fun j _ => hmode_summable j)
    rw [hstep2] at hstep1
    refine hstep1.trans ?_
    have hsum_le : ∑ j ∈ Finset.range (n + 1),
          ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 ≤
        Csum * Sall ^ 2 := by
      have hSmono : ∀ j ∈ Finset.range (n + 1),
          (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 ≤ Sall ^ 2 := by
        intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ ≤ Sall := by
          rw [hSall_def]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => norm_nonneg _)
          intro a ha; rw [Finset.mem_range] at ha ⊢; omega
        have hlow_nn : 0 ≤ ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
          Finset.sum_nonneg (fun a _ => norm_nonneg _)
        exact pow_le_pow_left₀ hlow_nn hsub 2
      calc ∑ j ∈ Finset.range (n + 1),
            ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
                (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2
          ≤ ∑ j ∈ Finset.range (n + 1),
              Cmode j * (∑ a ∈ Finset.range (j + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 :=
            Finset.sum_le_sum (fun j _ => hCmode j S)
        _ ≤ ∑ j ∈ Finset.range (n + 1), Cmode j * Sall ^ 2 :=
            Finset.sum_le_sum (fun j hj =>
              mul_le_mul_of_nonneg_left (hSmono j hj) (hCmode_nn j))
        _ = Csum * Sall ^ 2 := by rw [hCsum_def, Finset.sum_mul]
    calc (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
          ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2
        ≤ (2 : ℝ) ^ n * (Csum * Sall ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (2 : ℝ) ^ n * Csum * Sall ^ 2 := by ring
  have hrhs_nn : 0 ≤ Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall :=
    mul_nonneg (Real.sqrt_nonneg _) hSall_nn
  have hsqrt_sq : (Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall) ^ 2 =
      (2 : ℝ) ^ n * Csum * Sall ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hNspec_sq_le : Nspec ^ 2 ≤ (Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall) ^ 2 := by
    rw [hsqrt_sq]; exact hsq_le
  have := Real.sqrt_le_sqrt hNspec_sq_le
  rw [Real.sqrt_sq hNspec_nn, Real.sqrt_sq hrhs_nn] at this
  calc Nspec ≤ Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall := this
    _ = Real.sqrt ((2 : ℝ) ^ n * Csum) * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by rw [hSall_def]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
