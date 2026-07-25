import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor
open Tensor0SBundle
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
private theorem tensorL2Inner_eq_tsum_l2Coeff_cross
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) :
    tensorL2Inner (I := I) (M := M) g₀ 0 s A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 s A.toFun B.toFun =
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

private theorem cc_raw_coeff
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g₀ 0 s))
    (S : SmoothCcTensor g₀ 0 s)
    (m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 s) (i : ℕ) :
    tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)) m =
      (-TensorEigenIdx.lambda (I := I) (M := M) m) ^ i *
        tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 S) m := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [rawTensorConnLapIter_succ,
        rawLap_coeff (I := I) (M := M) g₀ s hc
          (rawTensorConnLapIter (I := I) g₀ 0 s i S) m,
        ih, pow_succ]
      ring

set_option maxHeartbeats 1600000 in
private theorem rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (s t : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s t S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * t) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
    with hcompact_def
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s t S))]
  refine tsum_congr (fun m => ?_)
  rw [cc_raw_coeff (I := I) (M := M) g₀ s h_compact S m t]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  rw [mul_pow, ← pow_mul, mul_comm t 2, (even_two_mul t).neg_pow L]

set_option maxHeartbeats 1600000 in
private theorem covGrad_rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖covGrad (I := I) (M := M) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
    with hcompact_def
  set U : SmoothCcTensor g₀ 0 s := rawTensorConnLapIter (I := I) g₀ 0 s i S with hU_def
  have hnorm_sq : ‖covGrad (I := I) (M := M) g₀ 0 s U‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 (s + 1)
        (covGrad (I := I) (M := M) g₀ 0 s U).toFun
        (covGrad (I := I) (M := M) g₀ 0 s U).toFun := by
    rw [SmoothCcTensor.norm_def (covGrad (I := I) (M := M) g₀ 0 s U)]
    exact tensorL2Norm_sq_toFun (I := I) (M := M) g₀ 0 (s + 1)
      (covGrad (I := I) (M := M) g₀ 0 s U)
  rw [hnorm_sq,
    tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g₀ s U]
  have hraw_eq : rawTensorConnLapSmooth (I := I) g₀ 0 s U =
      rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S := by
    rw [hU_def, rawTensorConnLapIter_succ]
  rw [hraw_eq, tensorL2Inner_eq_tsum_l2Coeff_cross (I := I) (M := M) g₀
    s (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S) U, hU_def]
  rw [← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [cc_raw_coeff (I := I) (M := M) g₀ s h_compact S m (i + 1),
    cc_raw_coeff (I := I) (M := M) g₀ s h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  have hpow : ((-L) ^ (i + 1) * c) * ((-L) ^ i * c) = (-L) ^ (2 * i + 1) * c ^ 2 := by
    rw [show (2 * i + 1) = (i + 1) + i by ring, pow_add]
    ring
  rw [hpow, (odd_two_mul_add_one i).neg_pow L]
  ring

private theorem smoothCcToTensorHs_rawTensorConnLapSmooth_le_self
    (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set lam : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
      (I := I) (M := M) i with hlam_def
  set c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i
    with hc_def
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := norm_nonneg _
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
      (I := I) (M := M) i
  have hLHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)) i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ h_compact T i]
    rw [show (- lam i * c i) ^ 2 = (lam i) ^ 2 * (c i) ^ 2 by ring]
    ring
  have hRHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (σ + 2) * (c i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2]
    have hw2 : tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) = (1 + lam i) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hw2]
  have hsummable_RHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2) := by
    have hw := (ccSpectralEmbed (I := I) (M := M) g₀ (σ + 2) T).weighted_summable
    refine hw.congr (fun i => ?_)
    rw [ccSpectralEmbed_coeff,
      show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
    exact hRHS_term i
  have hsummable_LHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsummable_RHS
    · have := tensorSobolevWeight_pos (I := I) (M := M) i σ
      have := hlam_nn i
      positivity
    · have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
        have := hlam_nn i; nlinarith
      have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def]
      exact hLHS_term i]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def,
        show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
      exact hRHS_term i]
    refine Summable.tsum_le_tsum (fun i => ?_) hsummable_LHS hsummable_RHS
    have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
      have := hlam_nn i; nlinarith
    have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  exact le_of_sq_le_sq hsq hnn

private theorem spectralModeMass_succ_le_smoothCcToTensorHs_succ_normSq
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 u) m) ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u‖ ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcomp
  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u =
      ccSpectralEmbed (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u :=
    tensorHs.ext (funext (fun i => rfl))
  rw [hembed_eq, ccSpectralEmbed_norm_sq_eq_tsum]
  have hweight_eq : ∀ m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) m (((n : ℕ) : ℝ) + 1) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) := by
    intro m
    unfold tensorSobolevWeight
    rw [show ((n : ℕ) : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hRHS_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) m (((n : ℕ) : ℝ) + 1) *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 u) m) ^ 2) :=
    (ccSpectralEmbed (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u).weighted_summable
  have hLHS_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 u) m) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hRHS_summable
    · intro m
      have := tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · intro m
      rw [hweight_eq m]
      have hL_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hle : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL_nn hle (n + 1)) (sq_nonneg _)
  refine Summable.tsum_le_tsum (fun m => ?_) hLHS_summable hRHS_summable
  rw [hweight_eq m]
  have hL_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
    tensor_lambda_nonneg (I := I) (M := M) m
  have hle : TensorEigenIdx.lambda (I := I) (M := M) m ≤
      1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL_nn hle (n + 1)) (sq_nonneg _)

private theorem cc_raw_hs_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g₀ s σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 s T)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s (σ + 2) T‖ := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
  have hright : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s (σ + 2) T‖ := norm_nonneg _
  apply le_of_sq_le_sq _ hright
  rw [ccToHs_norm_sq, ccToHs_norm_sq]
  have hrs := (ccTensorToHs (I := I) (M := M) g₀ s (σ + 2) T).weighted_summable
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ hrs
  · rw [rawLap_coeff (I := I) (M := M) g₀ s hc T m]
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
      tensor_lambda_nonneg (I := I) (M := M) m
    have hw : tensorSobolevWeight (I := I) (M := M) m (σ + 2) =
        tensorSobolevWeight (I := I) (M := M) m σ *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ 2 := by
      rw [tensorHs.tensorSobolevWeight_add]
      congr 1
      unfold tensorSobolevWeight
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hw, show (-TensorEigenIdx.lambda (I := I) (M := M) m *
        tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 T) m) ^ 2 =
      TensorEigenIdx.lambda (I := I) (M := M) m ^ 2 *
        tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 T) m ^ 2 by ring]
    have hle : TensorEigenIdx.lambda (I := I) (M := M) m ≤
        1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlam hle 2)
          (le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) m σ)))
        (sq_nonneg (tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 T) m)))
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hrs
    · rw [rawLap_coeff (I := I) (M := M) g₀ s hc T m]
      exact mul_nonneg
        (le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) m σ))
        (sq_nonneg _)
    · rw [rawLap_coeff (I := I) (M := M) g₀ s hc T m]
      rw [ccTensorToHs_coeff]
      have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hw : tensorSobolevWeight (I := I) (M := M) m (σ + 2) =
          tensorSobolevWeight (I := I) (M := M) m σ *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ 2 := by
        rw [tensorHs.tensorSobolevWeight_add]
        congr 1
        unfold tensorSobolevWeight
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hw, show (-TensorEigenIdx.lambda (I := I) (M := M) m *
          tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 T) m) ^ 2 =
        TensorEigenIdx.lambda (I := I) (M := M) m ^ 2 *
          tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 T) m ^ 2 by ring]
      have hle : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hlam hle 2)
            (le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) m σ)))
          (sq_nonneg (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 T) m)))

private theorem cc_mass_le
    (g₀ : SmoothRiemannianMetric I M) (s n : ℕ)
    (u : SmoothCcTensor g₀ 0 s) :
    (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s,
      TensorEigenIdx.lambda (I := I) (M := M) m ^ (n + 1) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
          (SmoothCcTensor.toL2 u) m ^ 2) ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s (((n : ℕ) : ℝ) + 1) u‖ ^ 2 := by
  classical
  rw [ccToHs_norm_sq]
  have hrs := (ccTensorToHs (I := I) (M := M) g₀ s (((n : ℕ) : ℝ) + 1) u).weighted_summable
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ hrs
  · have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
      tensor_lambda_nonneg (I := I) (M := M) m
    have hw : tensorSobolevWeight (I := I) (M := M) m (((n : ℕ) : ℝ) + 1) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) := by
      unfold tensorSobolevWeight
      rw [show ((n : ℕ) : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hw]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hlam (by linarith) (n + 1)) (sq_nonneg _)
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hrs
    · have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hw : tensorSobolevWeight (I := I) (M := M) m (((n : ℕ) : ℝ) + 1) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) := by
        unfold tensorSobolevWeight
        rw [show ((n : ℕ) : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      rw [hw]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hlam (by linarith) (n + 1)) (sq_nonneg _)

private theorem covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd_local
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
    rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ 2 i S,
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
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg c)
    · have hsummable := (ccSpectralEmbed (I := I) (M := M) g₀
        ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
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
    exact riemannianFiberNormSq_iteratedCovGrad_comp
      (I := I) (M := M) g₀ 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
      (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_iteratedCovGrad_order_eq_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {n n' : ℕ} (h : n = n')
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contract_eq_covGradBundleEquiv_symm_local
    (s : ℕ) (x : M) (v : TangentSpace I x) (A : TensorRSSpace 0 (s + 1) I x) :
    Tensor0SBundle.contract_covariant 0 s x v A =
      (Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) 0 s x).symm A v := by
  apply tensorRSSpace_ext 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [Tensor0SBundle.covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 s x A v D m]
  rfl

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_eq_sum_contract_orthoFrame_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : TensorRSSpace 0 (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1) x A =
      ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        (Tensor0SBundle.contract_covariant 0 s x (e a) A) := by
  classical
  set Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
    (Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) 0 s x).symm A with hΦ_def
  have hAeq : A = Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) 0 s x Φ := by
    rw [hΦ_def]
    exact ((Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) 0 s x).apply_symm_apply A).symm
  rw [hAeq]
  rw [riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame_rs (I := I) (M := M) g₀ 0 s x
    Φ e hn horth]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← hAeq, contract_eq_covGradBundleEquiv_symm_local (I := I) (M := M) s x (e a) A, hΦ_def]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_contract_le_succ_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : TensorRSSpace 0 (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (i : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        (Tensor0SBundle.contract_covariant 0 s x (e i) A) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1) x A := by
  classical
  rw [riemannianFiberNormSq_eq_sum_contract_orthoFrame_local (I := I) (M := M) g₀ s x A e hn horth]
  refine Finset.single_le_sum
    (f := fun a => riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
      (Tensor0SBundle.contract_covariant 0 s x (e a) A))
    (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 s x _) (Finset.mem_univ i)

omit [CompactSpace M] in
private lemma covDivergenceRaw_eq_sum_contract_covDeriv_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) (b : M) :
    covDivergenceRaw (I := I) (M := M) g₀ s V b =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.contract_covariant 0 s b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b
            (smoothOrthoFrame (I := I) g₀ b i b)) := by
  classical
  rw [covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace (I := I) (M := M) g₀ s V b
    (fun i => smoothOrthoFrame (I := I) g₀ b i b)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ b i j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g₀ b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g₀ b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g₀ s V b hSmooth_at hSmooth_at]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 (s + 1) V b
    (smoothOrthoFrame (I := I) g₀ b i b)]

private lemma riemannianFiberNormSq_covGrad_eq_sum_frame_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) (b : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1 + 1) b
        ((covGrad (I := I) (M := M) g₀ 0 (s + 1) V).toSection b) =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1) b
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b
            (smoothOrthoFrame (I := I) g₀ b i b)) := by
  classical
  rw [covGrad_toSection_apply (I := I) (M := M) g₀ 0 (s + 1) V b]
  rw [riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame_rs (I := I) (M := M) g₀ 0 (s + 1) b
    (tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g₀)
      (fun y : M => V.toSection y) b)
    (fun i => smoothOrthoFrame (I := I) g₀ b i b) rfl
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ b i j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 (s + 1) V b
    (smoothOrthoFrame (I := I) g₀ b i b)]

private lemma riemannianFiberNormSq_covDivergence_le_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) (b : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s b (covDivergenceRaw (I := I) (M := M) g₀ s V b) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1 + 1) b
          ((covGrad (I := I) (M := M) g₀ 0 (s + 1) V).toSection b) := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g₀ b i b with he_def
  have horth : ∀ a c : Fin (Module.finrank ℝ E),
      g₀.inner b (e a) (e c) = if a = c then (1 : ℝ) else 0 :=
    fun a c => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ b a c
  set F : Fin (Module.finrank ℝ E) → TensorRSSpace 0 s I b :=
    fun i => Tensor0SBundle.contract_covariant 0 s b (e i)
      (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b (e i)) with hF_def
  have hdiv_eq : covDivergenceRaw (I := I) (M := M) g₀ s V b = ∑ i, F i := by
    rw [covDivergenceRaw_eq_sum_contract_covDeriv_local (I := I) (M := M) g₀ s V b]
  rw [hdiv_eq]
  have hcard : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).card =
      Module.finrank ℝ E := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hsum_le := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 0 s b
    Finset.univ F
  rw [hcard] at hsum_le
  refine le_trans hsum_le ?_
  rw [riemannianFiberNormSq_covGrad_eq_sum_frame_local (I := I) (M := M) g₀ s V b]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ))
  rw [hF_def]
  exact riemannianFiberNormSq_contract_le_succ_local (I := I) (M := M) g₀ s b
    (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b (e i)) e rfl horth i

private lemma covDivergence_l2Norm_le_covGrad_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) :
    ‖covDivergence (I := I) (M := M) g₀ s V‖ ≤
      Real.sqrt (Module.finrank ℝ E) *
        ‖covGrad (I := I) (M := M) g₀ 0 (s + 1) V‖ := by
  classical
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (c := s) 1 (fun _ => s + 1 + 1)
    (fun _ => covGrad (I := I) (M := M) g₀ 0 (s + 1) V)
    (covDivergence (I := I) (M := M) g₀ s V)
    (Real.sqrt (Module.finrank ℝ E)) (Real.sqrt_nonneg _) (fun x => ?_)
  · simpa only [Finset.sum_const, Finset.card_range, one_smul, one_nsmul] using hbound
  · rw [Finset.sum_range_one]
    rw [Real.sq_sqrt (by positivity)]
    rw [covDivergence_toSection_apply (I := I) (M := M) g₀ s V x]
    exact riemannianFiberNormSq_covDivergence_le_local (I := I) (M := M) g₀ s V x

private theorem iteratedRoughLapGrad_commutator_l2Norm_le_local
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + m) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  classical
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S => ?_⟩
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz, norm_zero]
    exact mul_nonneg (le_refl 0) (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => K p + Cm (p + 1), fun p => add_nonneg (hK_nn p) (hCm_nn (p + 1)),
      fun p S => ?_⟩
    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
            (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      change rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S
      with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p]
    refine le_trans (norm_add_le _ _) ?_
    have harm1 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ ≤
          K p * fullSum := by
      have hKb := hK p gradm
      have hreindex : ∀ a, ‖iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := by
        intro a
        rw [hgradm, norm_iteratedCovGrad_comp_local (I := I) (M := M) g₀ s m a S]
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      have hsub : ∑ a ∈ Finset.range (p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ ≤ fullSum := by
        rw [hfullSum]
        have hIco : ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ =
            ∑ b ∈ Finset.Ico m (m + (p + 2)),
              ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr ?_ (fun a _ => rfl)
          congr 1
          omega
        rw [hIco]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
        intro b hb
        rw [Finset.mem_Ico] at hb
        rw [Finset.mem_range]
        omega
      calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖
          ≤ K p * ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := hKb
        _ ≤ K p * fullSum := mul_le_mul_of_nonneg_left hsub (hK_nn p)
    have harm2 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ ≤
          Cm (p + 1) * fullSum := by
      have hcomp :
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + m) (p + 1) comm_m‖ := by
        have h := norm_iteratedCovGrad_comp_local (I := I) (M := M) g₀ (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := hCm (p + 1) S
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    have hfinal : K p * fullSum + Cm (p + 1) * fullSum =
        (K p + Cm (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖
        ≤ K p * fullSum + Cm (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (K p + Cm (p + 1)) * fullSum := hfinal

private theorem exists_iteratedCovGrad_rawConnLap_l2Norm_le_local
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
          C * ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  intro s
  obtain ⟨K, hK_one, hK⟩ :=
    exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen (I := I) (M := M) g₀
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    iteratedRoughLapGrad_commutator_l2Norm_le_local (I := I) (M := M) g₀ a s
  have hK_nn : 0 ≤ K := le_trans (by norm_num) hK_one
  refine ⟨K + Cfun 0, add_nonneg hK_nn (hCfun_nn 0), fun S => ?_⟩
  set FULL : ℝ := ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFULL
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hlap_second :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ ≤
        K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
    have hgen := hK (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)
    rw [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)),
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)))] at hgen
    have hcomp :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S))‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
      have h := norm_iteratedCovGrad_comp_local (I := I) (M := M) g₀ s a 2 S
      have heq :
          iteratedCovGrad (I := I) g₀ 0 (s + a) 2 (iteratedCovGrad (I := I) g₀ 0 s a S) =
            covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
              (covGrad (I := I) (M := M) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)) :=
        rfl
      rw [heq] at h
      rw [h]
    rw [hcomp] at hgen
    exact hgen
  have hcomm :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
          iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
    have h := hCfun 0 S
    simpa only [iteratedCovGrad_zero, Nat.add_zero] using h
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := by
    have := norm_sub_le
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S))
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
        iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
    simpa using this
  have hsecond_le : ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.single_le_sum (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 s b S‖)
      (fun b _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  have hsub_le : ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
    intro b hb; rw [Finset.mem_range] at hb ⊢; omega
  calc ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖
      ≤ ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := htri
    _ ≤ K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ +
          Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ :=
        add_le_add hlap_second hcomm
    _ ≤ K * FULL + Cfun 0 * FULL :=
        add_le_add (mul_le_mul_of_nonneg_left hsecond_le hK_nn)
          (mul_le_mul_of_nonneg_left hsub_le (hCfun_nn 0))
    _ = (K + Cfun 0) * FULL := by ring

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 2 k
  refine ⟨((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)), by positivity, fun S => ?_⟩
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hlap_le : ∀ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have heq : tensorL2Norm (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ :=
      (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀ (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).trans
        (SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).symm
    rw [heq]
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ :=
      rawConnLapIter_l2_le_ccSpectralEmbed_even (I := I) (M := M) g₀ i S
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ ≤ Nspec := by
      rw [hNspec_def, ← hembed_eq]
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
      have : (2 * i : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  have hlapsum : ∑ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        ((k + 1 : ℕ) : ℝ) * Nspec := by
    calc ∑ i ∈ Finset.range (k + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun
        ≤ ∑ _i ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hlap_le
      _ = ((k + 1 : ℕ) : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hjet_le : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cg * (((k + 1 : ℕ) : ℝ) * Nspec) := by
    intro j hj
    have hj2k : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgj := hCg j hj2k S
    have heqj : tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
          (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
    rw [heqj] at hgj
    exact le_trans hgj (mul_le_mul_of_nonneg_left hlapsum hCg_nn)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
      ≤ ∑ _j ∈ Finset.range (2 * k + 1), Cg * (((k + 1 : ℕ) : ℝ) * Nspec) :=
        Finset.sum_le_sum hjet_le
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (((k + 1 : ℕ) : ℝ) * Nspec)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)) * Nspec := by push_cast; ring

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd_local
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Clow, hClow_nn, hClow⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local (I := I) (M := M) g₀ k
  obtain ⟨Cgard, hCgard_nn, hCgard⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 3 k
  obtain ⟨Ceven, hCeven_nn, hCeven⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local (I := I) (M := M) g₀ k
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
  have heven_le : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Ceven * Nspec := by
    refine le_trans (hCeven S) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCeven_nn
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)
  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Clow * Nspec := by
    refine le_trans (hClow S) ?_
    refine mul_le_mul_of_nonneg_left ?_ hClow_nn
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)
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
        (covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd_local (I := I) (M := M) g₀ i S) ?_
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
        norm_iteratedCovGrad_order_eq_local (I := I) (M := M) g₀ 2 (by omega) S
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

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general_local
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ := by
  classical
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact hC S
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd_local (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact hC S

set_option maxHeartbeats 1600000 in
private theorem rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 s),
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + k)
          (iteratedCovGrad (I := I) g₀ 0 s k u)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 s k
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2
        + C * (∑ a ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  classical
  rcases k with _ | j
  · refine ⟨0, le_refl _, fun u => ?_⟩
    have hD0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 u) =
          iteratedCovGrad (I := I) g₀ 0 s 0
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero]
    rw [hD0]
    simp
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      iteratedRoughLapGrad_commutator_l2Norm_le_local (I := I) (M := M) g₀ (j + 1) s
    obtain ⟨Crc, hCrc_nn, hCrc⟩ :=
      exists_iteratedCovGrad_rawConnLap_l2Norm_le_local (I := I) (M := M) g₀ j s
    set dimR : ℝ := Real.sqrt (Module.finrank ℝ E) with hdimR
    have hdimR_nn : 0 ≤ dimR := Real.sqrt_nonneg _
    refine ⟨(Cfun 0) ^ 2 + 2 * (Crc * (dimR * Cfun 1)),
      add_nonneg (sq_nonneg _)
        (by have := hCfun_nn 0; have := hCfun_nn 1
            exact mul_nonneg (by norm_num)
              (mul_nonneg hCrc_nn (mul_nonneg hdimR_nn (hCfun_nn 1)))),
      fun u => ?_⟩
    set SUM : ℝ := ∑ a ∈ Finset.range (j + 1 + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ with hSUM
    have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
    set B : SmoothCcTensor g₀ 0 (s + (j + 1)) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
        (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u) with hB_def
    set A : SmoothCcTensor g₀ 0 (s + (j + 1)) :=
      iteratedCovGrad (I := I) g₀ 0 s (j + 1)
        (rawTensorConnLapSmooth (I := I) g₀ 0 s u) with hA_def
    set D : SmoothCcTensor g₀ 0 (s + (j + 1)) := B - A with hD_def
    have hBAD : B = A + D := by rw [hD_def]; abel
    have hnorm_add :
        ‖B‖ ^ 2 = ‖A‖ ^ 2 + 2 * (⟪A, D⟫_ℝ : ℝ) + ‖D‖ ^ 2 := by
      rw [hBAD, ← SmoothCcTensor.norm_toL2 (A + D), map_add,
        @norm_add_sq_real _ _ _ (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 D),
        SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2,
        SmoothCcTensor.inner_toL2]
    have hD_eq_comm : D =
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
            (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u) -
          iteratedCovGrad (I := I) g₀ 0 s (j + 1)
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u) := by
      rw [hD_def, hB_def, hA_def]
    have hDnorm : ‖D‖ ≤ Cfun 0 * SUM := by
      have h := hCfun 0 u
      simp only [iteratedCovGrad_zero, Nat.add_zero] at h
      rw [hD_eq_comm]
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
      rw [hSUM]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
      intro b hb; rw [Finset.mem_range] at hb ⊢; omega
    have hgradDnorm :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + (j + 1)) D‖ ≤ Cfun 1 * SUM := by
      have h := hCfun 1 u
      have hcovD :
          ‖covGrad (I := I) (M := M) g₀ 0 (s + (j + 1)) D‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + (j + 1)) 1
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
                  (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u) -
                iteratedCovGrad (I := I) g₀ 0 s (j + 1)
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ := by
        rw [hD_eq_comm]
        simp only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
      rw [hcovD]
      have hrange : ∑ a ∈ Finset.range (j + 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ = SUM := by
        rw [hSUM, show j + 1 + 1 + 1 = j + 1 + 2 from by omega]
      rw [hrange] at h
      exact h
    set T : SmoothCcTensor g₀ 0 (s + j) :=
      iteratedCovGrad (I := I) g₀ 0 s j (rawTensorConnLapSmooth (I := I) g₀ 0 s u) with hT_def
    have hA_covGrad : A = covGrad (I := I) (M := M) g₀ 0 (s + j) T := by
      rw [hA_def, hT_def, iteratedCovGrad_succ]
    have hTnorm : ‖T‖ ≤ Crc * SUM := by
      have h := hCrc u
      rw [hT_def]
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_left ?_ hCrc_nn
      rw [hSUM, show j + 3 = j + 1 + 2 from by omega]
    have hcovDivD :
        ‖covDivergence (I := I) (M := M) g₀ (s + j) D‖ ≤ dimR * (Cfun 1 * SUM) := by
      have hp1 := covDivergence_l2Norm_le_covGrad_local (I := I) (M := M) g₀ (s + j) D
      refine le_trans hp1 ?_
      exact mul_le_mul_of_nonneg_left hgradDnorm hdimR_nn
    have hIBP :
        (⟪A, D⟫_ℝ : ℝ) =
          - tensorL2Inner (I := I) (M := M) g₀ 0 (s + j) T.toFun
              (covDivergence (I := I) (M := M) g₀ (s + j) D).toFun := by
      rw [SmoothCcTensor.inner_def A D, hA_covGrad]
      exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
        (I := I) (M := M) g₀ (s + j) T D
    have hcross_abs : |(⟪A, D⟫_ℝ : ℝ)| ≤ (Crc * SUM) * (dimR * (Cfun 1 * SUM)) := by
      rw [hIBP, abs_neg]
      have habs_inner :
          |tensorL2Inner (I := I) (M := M) g₀ 0 (s + j) T.toFun
              (covDivergence (I := I) (M := M) g₀ (s + j) D).toFun| ≤
            ‖T‖ * ‖covDivergence (I := I) (M := M) g₀ (s + j) D‖ := by
        rw [show tensorL2Inner (I := I) (M := M) g₀ 0 (s + j) T.toFun
              (covDivergence (I := I) (M := M) g₀ (s + j) D).toFun =
            (⟪T, covDivergence (I := I) (M := M) g₀ (s + j) D⟫_ℝ : ℝ) from
          (SmoothCcTensor.inner_def T (covDivergence (I := I) (M := M) g₀ (s + j) D)).symm]
        exact abs_real_inner_le_norm T (covDivergence (I := I) (M := M) g₀ (s + j) D)
      refine le_trans habs_inner ?_
      exact mul_le_mul hTnorm hcovDivD (norm_nonneg _)
        (mul_nonneg hCrc_nn hSUM_nn)
    have hDnorm_sq : ‖D‖ ^ 2 ≤ (Cfun 0) ^ 2 * SUM ^ 2 := by
      have h1 : ‖D‖ ^ 2 ≤ (Cfun 0 * SUM) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hDnorm 2
      calc ‖D‖ ^ 2 ≤ (Cfun 0 * SUM) ^ 2 := h1
        _ = (Cfun 0) ^ 2 * SUM ^ 2 := by ring
    rw [show ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
          (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u)‖ ^ 2 = ‖B‖ ^ 2 from rfl,
      show ‖iteratedCovGrad (I := I) g₀ 0 s (j + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2 = ‖A‖ ^ 2 from rfl,
      hnorm_add]
    have hcross_le : 2 * (⟪A, D⟫_ℝ : ℝ) ≤
        2 * ((Crc * SUM) * (dimR * (Cfun 1 * SUM))) := by
      have := (abs_le.mp hcross_abs).2
      linarith [this]
    nlinarith [hcross_le, hDnorm_sq, hSUM_nn, hCrc_nn, hdimR_nn, hCfun_nn 0, hCfun_nn 1]

set_option maxHeartbeats 1600000 in
private theorem iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 s),
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (k + 2) u)‖ ^ 2 ≤
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s k
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2
        + C * (∑ a ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  classical
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower
      (I := I) (M := M) g₀ s k
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (s + k)
  refine ⟨Cgap + K 0, add_nonneg hCgap_nn (hK_nn 0), fun u => ?_⟩
  set P : SmoothCcTensor g₀ 0 (s + k) := iteratedCovGrad (I := I) g₀ 0 s k u with hP_def
  set SUM : ℝ := ∑ a ∈ Finset.range (k + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ with hSUM
  have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hPnorm : ‖P‖ ≤ SUM := by
    rw [hP_def, hSUM]
    refine Finset.single_le_sum (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 s a u‖)
      (fun a _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  have hgradP_eq : covGrad (I := I) (M := M) g₀ 0 (s + k) P =
      iteratedCovGrad (I := I) g₀ 0 s (k + 1) u := by
    rw [hP_def, iteratedCovGrad_succ]
  have hgradPnorm : ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ ≤ SUM := by
    rw [hgradP_eq, hSUM]
    refine Finset.single_le_sum (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 s a u‖)
      (fun a _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  have hLHS_eq : iteratedCovGrad (I := I) g₀ 0 s (k + 2) u =
      covGrad (I := I) (M := M) g₀ 0 (s + k + 1)
        (covGrad (I := I) (M := M) g₀ 0 (s + k) P) := by
    rw [hP_def]
    rfl
  have hLHS_norm_sq :
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (k + 2) u)‖ ^ 2 =
        tensorL2Norm (I := I) (M := M) g₀ 0 (s + k + 1 + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + k + 1)
              (covGrad (I := I) (M := M) g₀ 0 (s + k) P)).toFun ^ 2 := by
    rw [SmoothCcTensor.norm_toL2, hLHS_eq,
      DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (covGrad (I := I) (M := M) g₀ 0 (s + k + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P))]
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g₀ (s + k) P
  have hcurv_eq :
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + k + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P) -
        covGrad (I := I) (M := M) g₀ 0 (s + k)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P) =
      pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P := rfl
  rw [hcurv_eq] at hweitz
  have hbase_eq :
      tensorL2Norm (I := I) (M := M) g₀ 0 (s + k)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P).toFun ^ 2 =
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P‖ ^ 2 := by
    rw [DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
      (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P)]
  have hpair_le :
      |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun| ≤
        ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ *
          ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := by
    have habs :
        tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
            (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun =
          (⟪pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P,
              covGrad (I := I) (M := M) g₀ 0 (s + k) P⟫_ℝ : ℝ) :=
      (SmoothCcTensor.inner_def (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P)
        (covGrad (I := I) (M := M) g₀ 0 (s + k) P)).symm
    rw [habs]
    exact abs_real_inner_le_norm
      (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P)
      (covGrad (I := I) (M := M) g₀ 0 (s + k) P)
  have hcurvnorm :
      ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ ≤ K 0 * SUM := by
    have hKb := hK 0 P
    have hsumexp :
        ∑ a ∈ Finset.range (0 + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + k) a P‖ =
          ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := by
      rw [show (0 + 2) = 2 by ring, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
    rw [iteratedCovGrad_zero] at hKb
    rw [hsumexp] at hKb
    refine le_trans hKb ?_
    have hsum_le : ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ ≤ SUM := by
      have hPexpand : ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s k u‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 s (k + 1) u‖ := by
        rw [hgradP_eq, hP_def]
      rw [hPexpand, hSUM]
      have hpair : ({k, k + 1} : Finset ℕ) ⊆ Finset.range (k + 2) := by
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_range]; omega
      have hsub :=
        Finset.sum_le_sum_of_subset_of_nonneg hpair
          (fun a _ _ => norm_nonneg (iteratedCovGrad (I := I) g₀ 0 s a u))
      have hpairsum :
          ∑ a ∈ ({k, k + 1} : Finset ℕ), ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 s k u‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 s (k + 1) u‖ := by
        rw [Finset.sum_insert (by simp), Finset.sum_singleton]
      rw [hpairsum] at hsub
      exact hsub
    nlinarith [hsum_le, hK_nn 0, hSUM_nn]
  have hpair_bound :
      |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun| ≤ K 0 * SUM ^ 2 := by
    calc |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
            (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun|
        ≤ ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ *
            ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := hpair_le
      _ ≤ (K 0 * SUM) * SUM := by
          refine mul_le_mul hcurvnorm hgradPnorm (norm_nonneg _) ?_
          exact mul_nonneg (hK_nn 0) hSUM_nn
      _ = K 0 * SUM ^ 2 := by ring
  have hbase_le := hgap u
  rw [← hP_def] at hbase_le
  have hbase_toL2 :
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s k
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s k
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_toL2]
  rw [hLHS_norm_sq, hweitz, hbase_eq, hbase_toL2]
  have hneg_le := neg_abs_le
    (tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
      (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
      (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun)
  nlinarith [hbase_le, hpair_bound, hneg_le, hSUM_nn, hCgap_nn, hK_nn 0]

private theorem spectralModeMass_base0
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (u : SmoothCcTensor g₀ 0 s) :
    ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (0 + 1) u)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (0 + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
              (SmoothCcTensor.toL2 u) m) ^ 2 := by
  have hcov : iteratedCovGrad (I := I) g₀ 0 s (0 + 1) u =
      covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s 0 u) := by
    rw [rawTensorConnLapIter_zero]
    rfl
  rw [show ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (0 + 1) u)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (0 + 1) u‖ ^ 2 by
      rw [SmoothCcTensor.norm_toL2], hcov]
  rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ s 0 u]

private theorem spectralModeMass_base1
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 s),
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (1 + 1) u)‖ ^ 2 ≤
        (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 u) m) ^ 2)
        + C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((1 : ℕ) : ℝ) u‖ ^ 2 := by
  classical
  obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
    iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower (I := I) (M := M) g₀ s 0
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    hsJet_le (I := I) (M := M) g₀ s 1
  refine ⟨Cstep * Csob ^ 2, by positivity, fun u => ?_⟩
  have hS := hCstep u
  have hbase0 :
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s 0
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2 =
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 u) m) ^ 2 := by
    rw [iteratedCovGrad_zero,
      show rawTensorConnLapSmooth (I := I) g₀ 0 s u =
        rawTensorConnLapIter (I := I) g₀ 0 s 1 u by rw [rawTensorConnLapIter_succ,
          rawTensorConnLapIter_zero],
      rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ s 1 u]
  have hSobu := hCsob u
  set SUM := ∑ a ∈ Finset.range (0 + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ with hSUM
  have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  set HN := ‖ccTensorToHs (I := I) (M := M) g₀ s ((1 : ℕ) : ℝ) u‖ with hHN
  have hHN_nn : (0 : ℝ) ≤ HN := norm_nonneg _
  have hSobidx : SUM ≤ Csob * HN := by
    have hh : ∑ a ∈ Finset.range (1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ ≤
        Csob * ‖ccTensorToHs (I := I) (M := M) g₀ s ((1 : ℕ) : ℝ) u‖ := hSobu
    rw [hSUM, hHN, show (0 + 2) = (1 + 1) by ring]
    exact hh
  have hstep_sq : Cstep * SUM ^ 2 ≤ (Cstep * Csob ^ 2) * HN ^ 2 := by
    have h1 : SUM ^ 2 ≤ (Csob * HN) ^ 2 := pow_le_pow_left₀ hSUM_nn hSobidx 2
    calc Cstep * SUM ^ 2 ≤ Cstep * (Csob * HN) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hCstep_nn
      _ = (Cstep * Csob ^ 2) * HN ^ 2 := by ring
  calc ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (1 + 1) u)‖ ^ 2
      ≤ ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s 0
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2 + Cstep * SUM ^ 2 := hS
    _ = (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 u) m) ^ 2) + Cstep * SUM ^ 2 := by rw [hbase0]
    _ ≤ (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 u) m) ^ 2) + (Cstep * Csob ^ 2) * HN ^ 2 := by
        linarith [hstep_sq]

private theorem exists_iteratedCovGrad_l2NormSq_le_spectralModeMass_succ_add_lower
    (g₀ : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : SmoothCcTensor g₀ 0 s),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (n + 1) u)‖ ^ 2 ≤
          (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 s,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                  (SmoothCcTensor.toL2 u) m) ^ 2) +
            C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((n : ℕ) : ℝ) u‖ ^ 2 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n, IH with
    | 0, _ =>
      refine ⟨0, le_refl _, fun u => ?_⟩
      rw [spectralModeMass_base0 (I := I) (M := M) g₀ s u]
      simp
    | 1, _ => exact spectralModeMass_base1 (I := I) (M := M) g₀ s
    | (Nat.succ (Nat.succ N)), IH =>
      obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
        iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower (I := I) (M := M) g₀ s (N + 1)
      obtain ⟨Cih, hCih_nn, hCih⟩ := IH N (by omega)
      obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
        hsJet_le (I := I) (M := M) g₀ s (N + 2)
      refine ⟨Cstep * Csob ^ 2 + Cih, by positivity, fun u => ?_⟩
      have hS := hCstep u
      have hIH := hCih (rawTensorConnLapSmooth (I := I) g₀ 0 s u)
      have hHsh := cc_raw_hs_le
        (I := I) (M := M) g₀ s ((N : ℕ) : ℝ) u
      have hSobu := hCsob u
      have hLHSidx : (N + 1 + 2) = (N + 2 + 1) := by ring
      rw [hLHSidx] at hS
      have hTopShift :
          (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 s,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (N + 1) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                  (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 s u)) m) ^ 2) =
            ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 s,
              (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (N + 2 + 1) *
                (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                    (SmoothCcTensor.toL2 u) m) ^ 2 := by
        refine tsum_congr (fun m => ?_)
        rw [rawLap_coeff (I := I) (M := M) g₀ s
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s) u m]
        set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL
        set c := tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
          (SmoothCcTensor.toL2 u) m with hc
        rw [show (- L * c) ^ 2 = L ^ 2 * c ^ 2 by ring,
          show N + 2 + 1 = (N + 1) + 2 by ring, pow_add]
        ring
      rw [hTopShift] at hIH
      have hHidx : ((N : ℕ) : ℝ) + 2 = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hHidx] at hHsh
      set A := ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (N + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2 with hA
      set TOPg := ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (N + 2 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 u) m) ^ 2 with hTOPg
      set SUM := (∑ a ∈ Finset.range ((N + 1) + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) with hSUM
      set HN := ‖ccTensorToHs (I := I) (M := M) g₀ s ((N : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ with hHN
      set HNu := ‖ccTensorToHs (I := I) (M := M) g₀ s ((N + 2 : ℕ) : ℝ) u‖ with hHNu
      have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
      have hHN_nn : (0 : ℝ) ≤ HN := norm_nonneg _
      have hHNu_nn : (0 : ℝ) ≤ HNu := norm_nonneg _
      have hSob_le : SUM ≤ Csob * HNu := by
        have hSobu' : ∑ a ∈ Finset.range ((N + 2) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ ≤
              Csob * ‖ccTensorToHs (I := I) (M := M) g₀ s ((N + 2 : ℕ) : ℝ) u‖ := hSobu
        rw [hSUM, hHNu, show ((N + 1) + 2) = ((N + 2) + 1) by ring]
        exact hSobu'
      have hIH_H : Cih * HN ^ 2 ≤ Cih * HNu ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hCih_nn
        exact pow_le_pow_left₀ hHN_nn hHsh 2
      have hStep_sq : Cstep * SUM ^ 2 ≤ (Cstep * Csob ^ 2) * HNu ^ 2 := by
        have h1 : SUM ^ 2 ≤ (Csob * HNu) ^ 2 := pow_le_pow_left₀ hSUM_nn hSob_le 2
        calc Cstep * SUM ^ 2 ≤ Cstep * (Csob * HNu) ^ 2 :=
              mul_le_mul_of_nonneg_left h1 hCstep_nn
          _ = (Cstep * Csob ^ 2) * HNu ^ 2 := by ring
      have hgoal : ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (N + 2 + 1) u)‖ ^ 2 ≤
          TOPg + (Cstep * Csob ^ 2 + Cih) * HNu ^ 2 := by
        calc ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (N + 2 + 1) u)‖ ^ 2
            ≤ A + Cstep * SUM ^ 2 := hS
          _ ≤ (TOPg + Cih * HN ^ 2) + Cstep * SUM ^ 2 := by linarith [hIH]
          _ ≤ TOPg + (Cstep * Csob ^ 2 + Cih) * HNu ^ 2 := by nlinarith [hIH_H, hStep_sq]
      exact hgoal


theorem cc_dirichlet_gap
    (g₀ : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ Cgap : ℝ, 0 ≤ Cgap ∧
      ∀ (u : SmoothCcTensor g₀ 0 s),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (n + 1) u)‖ ^ 2 ≤
          ‖ccTensorToHs (I := I) (M := M) g₀ s (((n : ℕ) : ℝ) + 1) u‖ ^ 2 +
            Cgap * ‖ccTensorToHs (I := I) (M := M) g₀ s ((n : ℕ) : ℝ) u‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_spectralModeMass_succ_add_lower (I := I) (M := M) g₀ s n
  refine ⟨C, hC_nn, fun u => ?_⟩
  have hmass := cc_mass_le
    (I := I) (M := M) g₀ s n u
  have hbound := hC u
  calc ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (n + 1) u)‖ ^ 2
      ≤ (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 u) m) ^ 2) +
          C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((n : ℕ) : ℝ) u‖ ^ 2 := hbound
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s (((n : ℕ) : ℝ) + 1) u‖ ^ 2 +
          C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((n : ℕ) : ℝ) u‖ ^ 2 := by
        have hMn_nn : 0 ≤ C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((n : ℕ) : ℝ) u‖ ^ 2 :=
          mul_nonneg hC_nn (sq_nonneg _)
        linarith [hmass]


theorem exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cgap : ℝ, 0 ≤ Cgap ∧
      ∀ (u : SmoothCcTensor g₀ 0 2),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u)‖ ^ 2 ≤
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u‖ ^ 2 +
            Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 := by
  obtain ⟨Cgap, hCgap, hbound⟩ := cc_dirichlet_gap (I := I) (M := M) g₀ 2 n
  refine ⟨Cgap, hCgap, fun u => ?_⟩
  have h := hbound u
  have hhigh :
      ccTensorToHs (I := I) (M := M) g₀ 2 (((n : ℕ) : ℝ) + 1) u =
        smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u :=
    tensorHs.ext (funext (fun _ => rfl))
  have hlow :
      ccTensorToHs (I := I) (M := M) g₀ 2 ((n : ℕ) : ℝ) u =
        smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u :=
    tensorHs.ext (funext (fun _ => rfl))
  rw [hhigh, hlow] at h
  exact h

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
