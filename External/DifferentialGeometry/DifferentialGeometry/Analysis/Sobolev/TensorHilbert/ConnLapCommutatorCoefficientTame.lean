import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.KoszulSectionParallelRaise
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianAppCcCommutation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma weight_natCast (g₀ : SmoothRiemannianMetric I M)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) (n : ℕ) :
    tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
  unfold tensorSobolevWeight
  rw [Real.rpow_natCast]

private lemma smoothCcToTensorHs_rawConnLap_coeff (g₀ : SmoothRiemannianMetric I M)
    (σ : ℝ) (T₀ : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T₀).coeff i := by
  classical
  have hdiag := tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) T₀ i 1
  have hiter1 : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 1 T₀ =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 T₀ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero]
  have hsub : SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 T₀) =
      SmoothCcTensor.toL2 T₀ -
        SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀) := by
    unfold oneMinusConnLapSmooth
    exact map_sub _ _ _
  rw [hiter1, hsub] at hdiag
  rw [tensorL2Coeff_eq_inner, inner_sub_right, ← tensorL2Coeff_eq_inner,
    ← tensorL2Coeff_eq_inner] at hdiag
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [pow_one] at hdiag
  linear_combination -hdiag

private lemma hs_zero_norm_eq (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ =
      ‖SmoothCcTensor.toL2 X‖ := by
  classical
  have hnn_lhs : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ := norm_nonneg _
  have hnn_rhs : 0 ≤ ‖SmoothCcTensor.toL2 X‖ := norm_nonneg _
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ ^ 2 =
      ‖SmoothCcTensor.toL2 X‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ 0 X).coeff i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 X) i) ^ 2 by
      funext i
      rw [tensorSobolevWeight_zero, one_mul, smoothCcToTensorHs_coeff]]
    exact tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 X)
  nlinarith [hsq, hnn_lhs, hnn_rhs, sq_nonneg
    (‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ - ‖SmoothCcTensor.toL2 X‖)]

private lemma hs_norm_order_congr (g₀ : SmoothRiemannianMetric I M)
    {σ σ' : ℝ} (h : σ = σ') (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' T‖ := by
  subst h; rfl

private lemma hs_norm_mono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w := tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w := tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

private lemma hs_connLap_shift_le (g₀ : SmoothRiemannianMetric I M)
    (k : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ +
        Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ := by
  classical
  have hsumA : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).weighted_summable
  have hsumB : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).weighted_summable
  have hsumC : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).weighted_summable
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ^ 2 +
        2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    have hterm : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2 +
          2 * (tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2) := by
      intro i
      have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u i,
        weight_natCast (I := I) (M := M) g₀ i (k + 2),
        weight_natCast (I := I) (M := M) g₀ i k,
        weight_natCast (I := I) (M := M) g₀ i (k + 1)]
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i with hci_def
      have hc2 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i = ci := rfl
      have hc0 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u).coeff i = ci := rfl
      rw [hc2, hc0]
      have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ k := by positivity
      have e2 : (1 + lam) ^ (k + 2) = (1 + lam) ^ k * (1 + lam) ^ 2 := by rw [pow_add]
      have e1 : (1 + lam) ^ (k + 1) = (1 + lam) ^ k * (1 + lam) := by rw [pow_succ]
      rw [e2, e1]
      nlinarith [hbase_nn, sq_nonneg ci, hlam_nn,
        mul_nonneg hbase_nn (sq_nonneg ci),
        mul_nonneg (mul_nonneg hbase_nn (sq_nonneg ci)) hlam_nn]
    calc (∑' i, tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2)
        ≤ ∑' i, (tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2 +
            2 * (tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2)) :=
          Summable.tsum_le_tsum hterm hsumA (hsumB.add (hsumC.mul_left 2))
      _ = (∑' i, tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2) +
            2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2 := by
          rw [Summable.tsum_add hsumB (hsumC.mul_left 2), tsum_mul_left]
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ := norm_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  nlinarith [hsq, hs2, mul_nonneg (mul_nonneg hsqrt2_nn hb_nn) hc_nn]

private lemma hs_rawConnLap_order_le (g₀ : SmoothRiemannianMetric I M)
    (k : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ := by
  classical
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ := norm_nonneg _
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).weighted_summable)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).weighted_summable)
    have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u i,
      weight_natCast (I := I) (M := M) g₀ i k, weight_natCast (I := I) (M := M) g₀ i (k + 2)]
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i with hci_def
    have hc : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u).coeff i = ci := rfl
    rw [hc]
    have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ k := by positivity
    have e2 : (1 + lam) ^ (k + 2) = (1 + lam) ^ k * (1 + lam) ^ 2 := by rw [pow_add]
    rw [e2]
    nlinarith [hbase_nn, sq_nonneg ci, hlam_nn, mul_nonneg hbase_nn (sq_nonneg ci)]
  exact le_of_sq_le_sq hsq hnn

private lemma iteratedCovGrad_le_connLap_add (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Cj * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower (I := I) (M := M) g₀ (k + 1)
  refine ⟨Real.sqrt 2 + Real.sqrt Cgap, by positivity, fun S => ?_⟩
  have hgapS := hgap S
  have hJeq : SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 1 + 1) S) =
      SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S) := rfl
  rw [hJeq, SmoothCcTensor.norm_toL2] at hgapS
  have hcast_succ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((k + 1 : ℕ) : ℝ) + 1) S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ :=
    hs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := norm_nonneg _
  have hjet_two : ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ +
        Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
    have hsqrt_nn : 0 ≤ Real.sqrt Cgap := Real.sqrt_nonneg _
    have hsC : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
    rw [← hcast_succ]
    refine le_of_sq_le_sq ?_ (by positivity)
    nlinarith [hgapS, hsC, mul_nonneg (mul_nonneg hsqrt_nn
      (norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ (((k + 1 : ℕ) : ℝ) + 1) S)))
      hc_nn, hcast_succ, hb_nn, hc_nn]
  have hshift := hs_connLap_shift_le (I := I) (M := M) g₀ k S
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ +
          Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ :=
        hjet_two
    _ ≤ (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖) +
          Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
        linarith [hshift]
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          (Real.sqrt 2 + Real.sqrt Cgap) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by ring

private lemma hs_norm_family_shift (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) :
    ∀ (p σ : ℕ),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ : ℕ) : ℝ)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ + 2 * p : ℕ) : ℝ) T₀‖ := by
  intro p
  induction p with
  | zero => intro σ; simp only [oneMinusConnLapSmoothIter_zero, Nat.mul_zero, Nat.add_zero]
  | succ p ih =>
    intro σ
    rw [oneMinusConnLapSmoothIter_succ,
      ← smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ σ
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀),
      ih (σ + 2)]
    exact hs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀

private lemma hs_logConvex (g₀ : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) T₀‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) T₀‖ *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ := by
  have hv := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tensorHs_incl_norm_sq_le
    (I := I) (M := M) (g := g₀) (r := 0) (s := 2) (a := (k : ℝ))
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℝ) + 2) T₀)
  rw [tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
        (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith) T₀,
      tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
        (show (k : ℝ) ≤ (k : ℝ) + 2 by linarith) T₀] at hv
  rw [hs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring) T₀,
      hs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring) T₀]
  exact hv

private lemma hs_extreme_interp {f : ℕ → ℝ} (hf_nn : ∀ k, 0 ≤ f k)
    (hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k)
    (hmono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k')
    {B : ℝ} {m₀ : ℕ} (hB : ∀ k, k ≤ m₀ → f k ≤ B)
    {α β γ : ℕ} (hαγ : α ≤ γ) (hβγ : β ≤ γ) (hsum : α + β ≤ m₀ + γ) :
    f α * f β ≤ B * f γ := by
  have hkey : ∀ σ₁ σ₂ : ℕ, σ₁ ≤ σ₂ → σ₁ ≤ γ → σ₂ ≤ γ → σ₁ + σ₂ ≤ m₀ + γ →
      f σ₁ * f σ₂ ≤ B * f γ := by
    intro σ₁ σ₂ hle h1γ h2γ hs
    by_cases hge : γ ≤ σ₁ + σ₂
    · have hex := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.logConvex_extreme_pair
        hf_nn hlc (σ₁ := σ₁) (σ₂ := σ₂) (τ₁ := σ₁ + σ₂ - γ) (τ₂ := γ)
        (by omega) hle (by omega) (by omega)
      have hlowB : f (σ₁ + σ₂ - γ) ≤ B := hB _ (by omega)
      exact le_trans hex (mul_le_mul_of_nonneg_right hlowB (hf_nn γ))
    · have hex := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.logConvex_extreme_pair
        hf_nn hlc (σ₁ := σ₁) (σ₂ := σ₂) (τ₁ := 0) (τ₂ := σ₁ + σ₂)
        (Nat.zero_le _) hle (by omega) (by omega)
      have hf0B : f 0 ≤ B := hB 0 (Nat.zero_le _)
      have hαβγ : f (σ₁ + σ₂) ≤ f γ := hmono (by omega)
      exact le_trans hex (mul_le_mul hf0B hαβγ (hf_nn _) (le_trans (hf_nn 0) hf0B))
  rcases le_total α β with hab | hab
  · exact hkey α β hab hαγ hβγ hsum
  · rw [mul_comm]; exact hkey β α hab hβγ hαγ (by omega)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_norm_comp (g₀ : SmoothRiemannianMetric I M) (r s l m : ℕ)
    (Ψ : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + l) m (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ =
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ := by
  have hnn1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r (s + l) m
      (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ := norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g₀ r (s + l) m
        (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ ^ 2 := by
    simp only [SmoothCcTensor.norm_def]
    rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r ((s + l) + m),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r (s + (l + m))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ r s l m Ψ x
  nlinarith [hsq, hnn1, hnn2,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ r (s + l) m (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ -
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖)]

private lemma iteratedCovGrad_slotExtend_norm_le (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g₀ r s Φ)‖ ≤
      Real.sqrt (Module.finrank ℝ E) * ‖iteratedCovGrad (I := I) g₀ r s i Φ‖ := by
  classical
  set F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
      ((iteratedCovGrad (I := I) g₀ r s i Φ).toSection x) with hF
  have hFint : MeasureTheory.Integrable F
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hF]
    exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r (s + i)
      (iteratedCovGrad (I := I) g₀ r s i Φ)).const_mul _
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
      ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g₀ r s Φ)).toSection x) ≤ F x :=
    fun x => rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r s Φ i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ (r + 1)
    ((s + 1) + i) (iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g₀ r s Φ)) F hFint hpt
  have hint_eq : ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i Φ).toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) =
      ‖iteratedCovGrad (I := I) g₀ r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r (s + i)]
  rw [hF, MeasureTheory.integral_const_mul, hint_eq] at hsq
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ))]
  exact hsq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma appCc_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W₁ - W₂) =
      operatorFieldApply (I := I) (M := M) g r s Φ W₁ - operatorFieldApply (I := I) (M := M) g r s Φ W₂ := by
  have h : operatorFieldApply (I := I) (M := M) g r s Φ (W₁ - W₂) +
      operatorFieldApply (I := I) (M := M) g r s Φ W₂ = operatorFieldApply (I := I) (M := M) g r s Φ W₁ := by
    rw [← appCc_add_right]
    congr 1
    abel
  exact eq_sub_of_add_eq h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma coeffContraction_secondCovGrad_sub (g₀ : SmoothRiemannianMetric I M)
    (C : SmoothCcTensor g₀ (2 + 2) 2) (u v : SmoothCcTensor g₀ 0 2) :
    operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C (iteratedCovGrad (I := I) g₀ 0 2 2 (u - v)) =
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C (iteratedCovGrad (I := I) g₀ 0 2 2 u) -
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C (iteratedCovGrad (I := I) g₀ 0 2 2 v) := by
  rw [iteratedCovGrad_sub, appCc_sub_right]

omit [CompactSpace M] [I.Boundaryless] in
private lemma rawConnLap_oneMinusConnLap_comm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
  rw [oneMinusConnLapSmooth, oneMinusConnLapSmooth, rawTensorConnLapSmooth_sub]

omit [I.Boundaryless] [BoundarylessManifold I M] in
private lemma coeffContraction_slotExtend_l2_le_of_pointwise (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g₀ r s) {B : ℝ} (hB_nn : 0 ≤ B)
    (hC : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Φ.toSection x) ≤ B ^ 2)
    (W : SmoothCcTensor g₀ 0 (r + 1)) :
    ‖operatorFieldApply (I := I) (M := M) g₀ (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g₀ r s Φ) W‖ ≤ B * ‖W‖ := by
  classical
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1) x
          ((operatorFieldApply (I := I) (M := M) g₀ (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g₀ r s Φ) W).toSection x) ≤
        B ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + 1) x (W.toSection x) := by
    intro x
    refine le_trans (riemannianFiberNormSq_comp_slotExtend_le (I := I) (M := M) g₀ r s Φ W x) ?_
    exact mul_le_mul_of_nonneg_right (hC x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (r + 1) x _)
  have hFint : MeasureTheory.Integrable
      (fun x => B ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + 1) x (W.toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (r + 1) W).const_mul _
  have hsq : ‖operatorFieldApply (I := I) (M := M) g₀ (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g₀ r s Φ) W‖ ^ 2 ≤ B ^ 2 * ‖W‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 (s + 1)
      (operatorFieldApply (I := I) (M := M) g₀ (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g₀ r s Φ) W) _ hFint hpt
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 (r + 1) W
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ B * ‖W‖ := mul_nonneg hB_nn (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  rw [mul_pow]
  exact hsq

omit [BoundarylessManifold I M] in
private lemma jet_fibreNormSq_sup_le_sharp (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Cemb : ℕ → ℝ, (∀ l, 0 ≤ Cemb l) ∧ ∀ (Ψ : SmoothCcTensor g₀ r s) (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
          ((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x) ≤
        Cemb l * ∑ m ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ ^ 2 := by
  classical
  have hstep : ∀ l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (Ψ : SmoothCcTensor g₀ r s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
          ((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x) ≤
        c * ∑ m ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ ^ 2 := by
    intro l
    obtain ⟨Csh, hCsh_nn, hCsh⟩ :=
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ r (s + l)
    refine ⟨Csh ^ 2, sq_nonneg _, fun Ψ x => ?_⟩
    refine le_trans (hCsh (iteratedCovGrad (I := I) g₀ r s l Ψ) x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Csh)
    refine le_of_eq (Finset.sum_congr rfl (fun m _ => ?_))
    rw [iteratedCovGrad_norm_comp (I := I) g₀ r s l m Ψ]
  choose Cemb hCemb_nn hCemb using hstep
  exact ⟨Cemb, hCemb_nn, fun Ψ l x => hCemb l Ψ x⟩

set_option maxHeartbeats 3200000 in
private lemma master_appCc_jet_le_sharp
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E + 5 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (b₀ s₀ dc dd : ℕ) (hdc : dc ≤ 3) (hdd : dd ≤ 3)
    (Kc : ℕ → ℝ) (_hKc_nn : ∀ i, 0 ≤ Kc i)
    (Kw : ℕ → ℝ) (_hKw_nn : ∀ l, 0 ≤ Kw l) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (p : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (_hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (Φ : SmoothCcTensor g₀ b₀ s₀)
        (_hΦ : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ≤
          Kc i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + dc : ℕ) : ℝ) T₀‖))
        (W : SmoothCcTensor g₀ 0 b₀)
        (_hW : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ≤
          Kw l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dd : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ≤
          Cm q * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((q + 3 : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
  classical
  set n := Module.finrank ℝ E with hn
  set w := n / 2 + 2 with hwdef
  set t := n / 2 + 3 with htdef
  obtain ⟨CembΦ, hCembΦ_nn, hCembΦ⟩ := jet_fibreNormSq_sup_le_sharp (I := I) (M := M) g₀ b₀ s₀
  obtain ⟨CembW, hCembW_nn, hCembW⟩ := jet_fibreNormSq_sup_le_sharp (I := I) (M := M) g₀ 0 b₀
  set KballΦ : ℕ → ℝ := fun i => CembΦ i *
    ∑ m ∈ Finset.range w, (Kc (i + m)) ^ 2 * (1 + R₀) ^ 2 with hKballΦ
  have hKballΦ_nn : ∀ i, 0 ≤ KballΦ i := fun i => mul_nonneg (hCembΦ_nn i)
    (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  set DW : ℕ → ℝ := fun k => ∑ l ∈ Finset.range (k + 1),
    CembW l * ∑ m ∈ Finset.range w, (Kw (l + m)) ^ 2 with hDW
  have hDW_nn : ∀ k, 0 ≤ DW k := fun k => Finset.sum_nonneg
    (fun l _ => mul_nonneg (hCembW_nn l) (Finset.sum_nonneg (fun m _ => sq_nonneg _)))
  set S1 : ℕ → ℝ := fun q => ∑ i ∈ (Finset.range (q + 1)).filter (· ≤ t),
    KballΦ i * ∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2 with hS1
  set S2 : ℕ → ℝ := fun q => ∑ i ∈ (Finset.range (q + 1)).filter (fun i => ¬ i ≤ t),
    DW (q - i) * (Kc i) ^ 2 * (1 + R₀) ^ 2 with hS2
  have hS1_nn : ∀ q, 0 ≤ S1 q := fun q => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hKballΦ_nn i) (Finset.sum_nonneg (fun l _ => sq_nonneg _)))
  have hS2_nn : ∀ q, 0 ≤ S2 q := fun q => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hDW_nn _) (sq_nonneg _)) (sq_nonneg _))
  refine ⟨fun q => Real.sqrt (diagonalGridGrowthFactor (E := E) q * (S1 q + S2 q)),
    fun q => Real.sqrt_nonneg _, ?_⟩
  intro p T₀ hball Φ hΦ W hW q
  set f : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ with hf
  have hf_nn : ∀ k, 0 ≤ f k := fun k => norm_nonneg _
  have hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k := fun k => hs_logConvex (I := I) (M := M) g₀ T₀ k
  have hmono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k' := by
    intro k k' hk
    exact hs_norm_mono (I := I) (M := M) g₀ (by exact_mod_cast hk) T₀
  have hballf : ∀ k, k ≤ a + 2 → f k ≤ R₀ := by
    intro k hk
    refine le_trans (hs_norm_mono (I := I) (M := M) g₀
      (show ((k : ℕ) : ℝ) ≤ (a : ℝ) + 2 by exact_mod_cast hk) T₀) hball
  have hfam : ∀ σ : ℕ, ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ : ℕ) : ℝ)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ = f (σ + 2 * p) :=
    fun σ => hs_norm_family_shift (I := I) (M := M) g₀ T₀ p σ
  set supΦsq : ℕ → ℝ := fun i => CembΦ i *
    ∑ m ∈ Finset.range w, ‖iteratedCovGrad (I := I) g₀ b₀ s₀ (i + m) Φ‖ ^ 2 with hsupΦsq
  set supWsq : ℕ → ℝ := fun l => CembW l *
    ∑ m ∈ Finset.range w, ‖iteratedCovGrad (I := I) g₀ 0 b₀ (l + m) W‖ ^ 2 with hsupWsq
  have hsupWsq_nn : ∀ l, 0 ≤ supWsq l := fun l => mul_nonneg (hCembW_nn l)
    (Finset.sum_nonneg (fun m _ => sq_nonneg _))
  have hΦpt : ∀ i x, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
      ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x) ≤ supΦsq i := hCembΦ Φ
  have hWpt : ∀ l x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
      ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x) ≤ supWsq l := hCembW W
  have hWl2 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 ≤
      (Kw l) ^ 2 * f (l + dd + 2 * p) ^ 2 := by
    intro l
    have h := hW l
    rw [hfam (l + dd)] at h
    have : ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 ≤ (Kw l * f (l + dd + 2 * p)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [this]
  have hΦl2 : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 ≤
      (Kc i) ^ 2 * (1 + f (i + dc)) ^ 2 := by
    intro i
    have : ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 ≤ (Kc i * (1 + f (i + dc))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hΦ i) 2
    nlinarith [this]
  have hsupΦ_region1 : ∀ i, i ≤ t → supΦsq i ≤ KballΦ i := by
    intro i hi
    rw [hsupΦsq, hKballΦ]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m hm => ?_)) (hCembΦ_nn i)
    have hmw : m ≤ w - 1 := by
      have := Finset.mem_range.mp hm; omega
    have hbound : i + m + dc ≤ a + 2 := by omega
    have hfle : f (i + m + dc) ≤ R₀ := hballf _ hbound
    refine le_trans (hΦl2 (i + m)) ?_
    have hone : (1 + f (i + m + dc)) ^ 2 ≤ (1 + R₀) ^ 2 := by
      have h1 : 0 ≤ 1 + f (i + m + dc) := by linarith [hf_nn (i + m + dc)]
      exact pow_le_pow_left₀ h1 (by linarith [hfle]) 2
    exact mul_le_mul_of_nonneg_left hone (sq_nonneg _)
  have hsupWsum_region2 : ∀ (q' i : ℕ), t < i →
      (∑ l ∈ Finset.range (q' + 1 - i), supWsq l) ≤
        DW (q' - i) * f (q' - i + (w - 1) + dd + 2 * p) ^ 2 := by
    intro q' i hi
    rw [hDW, Finset.sum_mul]
    by_cases hle : i ≤ q'
    · have hrange : q' + 1 - i = (q' - i) + 1 := by omega
      rw [hrange]
      refine Finset.sum_le_sum (fun l hl => ?_)
      have hlqi : l ≤ q' - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [hsupWsq]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hCembW_nn l)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun m hm => ?_)
      have hmw : m ≤ w - 1 := by
        have := Finset.mem_range.mp hm; omega
      refine le_trans (hWl2 (l + m)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine pow_le_pow_left₀ (hf_nn _) (hmono ?_) 2
      omega
    · have : q' + 1 - i = 0 := by omega
      rw [this, Finset.range_zero, Finset.sum_empty]
      exact Finset.sum_nonneg (fun l _ =>
        mul_nonneg (mul_nonneg (hCembW_nn l)
          (Finset.sum_nonneg (fun m _ => sq_nonneg _))) (sq_nonneg _))
  have hintW : ∀ l, ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
      ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) =
      ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by
    intro l
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0 (b₀ + l)]
  have hintΦ : ∀ i, ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
      ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) =
      ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by
    intro i
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ b₀ (s₀ + i)]
  rw [hfam (q + 3)]
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  have hG_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q := appCcGdiag_nonneg (E := E) q
  set flt1 := (Finset.range (q + 1)).filter (· ≤ t) with hflt1
  set flt2 := (Finset.range (q + 1)).filter (fun i => ¬ i ≤ t) with hflt2
  set FW : M → ℝ := fun x => diagonalGridGrowthFactor (E := E) q *
    ((∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
          ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)) +
      (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x))) with hFW
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) x
      ((iteratedCovGrad (I := I) g₀ 0 s₀ q (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)).toSection x) ≤
        FW x := by
    intro x
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀ b₀ s₀ Φ W q x) ?_
    simp only [hFW]
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (q + 1)) (· ≤ t)]
    refine add_le_add ?_ ?_
    · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hΦpt i x)
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (b₀ + l) x _)))
    · refine Finset.sum_le_sum (fun i _ => ?_)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun l _ => hWpt l x))
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ b₀ (s₀ + i) x _)
  have hint1 : MeasureTheory.Integrable (fun x => ∑ i ∈ flt1, supΦsq i *
      ∑ l ∈ Finset.range (q + 1 - i), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
        ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum _ (fun i _ =>
      (MeasureTheory.integrable_finset_sum _ (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (b₀ + l)
          (iteratedCovGrad (I := I) g₀ 0 b₀ l W))).const_mul _)
  have hint2 : MeasureTheory.Integrable (fun x => ∑ i ∈ flt2,
      (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
      riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
        ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum _ (fun i _ =>
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ b₀ (s₀ + i)
        (iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ)).const_mul _)
  have hFint : MeasureTheory.Integrable FW μ := by
    simp only [hFW]; exact (hint1.add hint2).const_mul _
  have hnormsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (s₀ + q)
    (iteratedCovGrad (I := I) g₀ 0 s₀ q (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)) FW hFint hpt
  have hF1eq : (∫ x, (∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
          ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)) ∂μ) =
      ∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by
    rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
      (MeasureTheory.integrable_finset_sum _ (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (b₀ + l)
          (iteratedCovGrad (I := I) g₀ 0 b₀ l W))).const_mul _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _ (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (b₀ + l)
        (iteratedCovGrad (I := I) g₀ 0 b₀ l W))]
    exact congrArg _ (Finset.sum_congr rfl (fun l _ => hintW l))
  have hF2eq : (∫ x, (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)) ∂μ) =
      ∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by
    rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ b₀ (s₀ + i)
        (iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ)).const_mul _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, hintΦ i]
  have hintFW : ∫ x, FW x ∂μ = diagonalGridGrowthFactor (E := E) q *
      ((∑ i ∈ flt1, supΦsq i *
          ∑ l ∈ Finset.range (q + 1 - i), ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) +
       (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
          ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2)) := by
    simp only [hFW]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hint1 hint2, hF1eq, hF2eq]
  have hReg1 : (∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) ≤ S1 q * f (q + 3 + 2 * p) ^ 2 := by
    rw [hS1, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hit : i ≤ t := (Finset.mem_filter.mp hi).2
    have hile : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    have hdata : (∑ l ∈ Finset.range (q + 1 - i), ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) ≤
        (∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2) * f (q + 3 + 2 * p) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      have hlle : l ≤ q - i := by have hlr := Finset.mem_range.mp hl; omega
      refine le_trans (hWl2 l) ?_
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hf_nn _) (hmono ?_) 2) (sq_nonneg _)
      omega
    calc supΦsq i * ∑ l ∈ Finset.range (q + 1 - i), ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2
        ≤ KballΦ i * ((∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2) * f (q + 3 + 2 * p) ^ 2) := by
          refine mul_le_mul (hsupΦ_region1 i hit) hdata
            (Finset.sum_nonneg (fun l _ => sq_nonneg _)) (hKballΦ_nn i)
      _ = KballΦ i * (∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2) * f (q + 3 + 2 * p) ^ 2 := by
          ring
  have hReg2 : (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2) ≤ S2 q * f (q + 3 + 2 * p) ^ 2 := by
    rw [hS2, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hit : t < i := by
      have := (Finset.mem_filter.mp hi).2; omega
    have hile : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    have hβγ : q - i + (w - 1) + dd + 2 * p ≤ q + 3 + 2 * p := by omega
    have hαγ : i + dc ≤ q + 3 + 2 * p := by omega
    have hsum_ok : (i + dc) + (q - i + (w - 1) + dd + 2 * p) ≤ (a + 2) + (q + 3 + 2 * p) := by
      omega
    have hinterp : f (i + dc) * f (q - i + (w - 1) + dd + 2 * p) ≤ R₀ * f (q + 3 + 2 * p) :=
      hs_extreme_interp hf_nn hlc hmono hballf hαγ hβγ hsum_ok
    have hfβγ : f (q - i + (w - 1) + dd + 2 * p) ≤ f (q + 3 + 2 * p) := hmono hβγ
    have hexpand : (1 + f (i + dc)) ^ 2 * f (q - i + (w - 1) + dd + 2 * p) ^ 2 ≤
        (1 + R₀) ^ 2 * f (q + 3 + 2 * p) ^ 2 := by
      have hABB : f (i + dc) * f (q - i + (w - 1) + dd + 2 * p) *
          f (q - i + (w - 1) + dd + 2 * p) ≤
          R₀ * f (q + 3 + 2 * p) * f (q + 3 + 2 * p) :=
        mul_le_mul hinterp hfβγ (hf_nn _) (mul_nonneg hR₀ (hf_nn _))
      have hABAB : (f (i + dc) * f (q - i + (w - 1) + dd + 2 * p)) ^ 2 ≤
          (R₀ * f (q + 3 + 2 * p)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (hf_nn _) (hf_nn _)) hinterp 2
      have hBB : f (q - i + (w - 1) + dd + 2 * p) ^ 2 ≤ f (q + 3 + 2 * p) ^ 2 :=
        pow_le_pow_left₀ (hf_nn _) hfβγ 2
      nlinarith [hABB, hABAB, hBB]
    calc (∑ l ∈ Finset.range (q + 1 - i), supWsq l) * ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
        ≤ (DW (q - i) * f (q - i + (w - 1) + dd + 2 * p) ^ 2) *
            ((Kc i) ^ 2 * (1 + f (i + dc)) ^ 2) := by
          refine mul_le_mul (hsupWsum_region2 q i hit) (hΦl2 i) (sq_nonneg _)
            (mul_nonneg (hDW_nn _) (sq_nonneg _))
      _ = DW (q - i) * (Kc i) ^ 2 *
            ((1 + f (i + dc)) ^ 2 * f (q - i + (w - 1) + dd + 2 * p) ^ 2) := by ring
      _ ≤ DW (q - i) * (Kc i) ^ 2 * ((1 + R₀) ^ 2 * f (q + 3 + 2 * p) ^ 2) :=
          mul_le_mul_of_nonneg_left hexpand (mul_nonneg (hDW_nn _) (sq_nonneg _))
      _ = DW (q - i) * (Kc i) ^ 2 * (1 + R₀) ^ 2 * f (q + 3 + 2 * p) ^ 2 := by ring
  have hfinalsq : ‖iteratedCovGrad (I := I) g₀ 0 s₀ q (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
      (diagonalGridGrowthFactor (E := E) q * (S1 q + S2 q)) * f (q + 3 + 2 * p) ^ 2 := by
    refine le_trans hnormsq (le_trans (le_of_eq hintFW) ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    rw [add_mul]
    exact add_le_add hReg1 hReg2
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (hf_nn _))
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hG_nn (add_nonneg (hS1_nn q) (hS2_nn q)))]
  exact hfinalsq

private lemma coeffContraction_Hs_bound_sharp
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E + 5 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (b₀ dc dd : ℕ) (hdc : dc ≤ 3) (hdd : dd ≤ 3)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (Kw : ℕ → ℝ) (hKw_nn : ∀ l, 0 ≤ Kw l) :
    ∃ CE : ℕ → ℝ, (∀ j, 0 ≤ CE j) ∧
      ∀ (p : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (_hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (Φ : SmoothCcTensor g₀ b₀ 2)
        (_hΦ : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ 2 i Φ‖ ≤
          Kc i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + dc : ℕ) : ℝ) T₀‖))
        (W : SmoothCcTensor g₀ 0 b₀)
        (_hW : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ≤
          Kw l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dd : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖)
        (j : ℕ),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖ ≤
          CE j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
  classical
  obtain ⟨Cm, hCm_nn, hCm⟩ :=
    master_appCc_jet_le_sharp (I := I) (M := M) g₀ a ha hR₀ b₀ 2 dc dd hdc hdd
      Kc hKc_nn Kw hKw_nn
  have hstep : ∀ j, ∃ c, 0 ≤ c ∧ ∀ (p : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
      (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
      (Φ : SmoothCcTensor g₀ b₀ 2)
      (hΦ : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ 2 i Φ‖ ≤
        Kc i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + dc : ℕ) : ℝ) T₀‖))
      (W : SmoothCcTensor g₀ 0 b₀)
      (hW : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ≤
        Kw l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dd : ℕ) : ℝ)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖ ≤
        c * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
    intro j
    obtain ⟨C1, hC1_nn, hC1⟩ := exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general g₀ j
    refine ⟨C1 * ∑ q ∈ Finset.range (j + 1), Cm q,
      mul_nonneg hC1_nn (Finset.sum_nonneg (fun q _ => hCm_nn q)),
      fun p T₀ hball Φ hΦ W hW => ?_⟩
    have hjet := hCm p T₀ hball Φ hΦ W hW
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖
        ≤ C1 * ∑ q ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖ :=
          hC1 (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)
      _ ≤ C1 * ∑ q ∈ Finset.range (j + 1), Cm q *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q hq => ?_)) hC1_nn
          have hqj : q ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
          refine le_trans (hjet q) (mul_le_mul_of_nonneg_left ?_ (hCm_nn q))
          exact hs_norm_mono (I := I) (M := M) g₀
            (by exact_mod_cast (by omega : q + 3 ≤ j + 3)) _
      _ = C1 * (∑ q ∈ Finset.range (j + 1), Cm q) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
          rw [← Finset.sum_mul]; ring
  choose CE hCE_nn hCE using hstep
  exact ⟨CE, hCE_nn, fun p T₀ hball Φ hΦ W hW j => hCE j p T₀ hball Φ hΦ W hW⟩

private lemma coeff_jet_linear_of_sq (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (Cbr : ℕ → ℝ) (hCbr_nn : ∀ m, 0 ≤ Cbr m)
    (hCbr : ∀ (m : ℕ) (Z : SmoothCcTensor g₀ 0 2),
      ∑ j ∈ Finset.range (m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Z‖ ≤
        Cbr m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) Z‖)
    (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (hjets : ∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
      Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2))
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ≤
      Real.sqrt (Kc i) * (1 + Cbr (i + 1)) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ) T₀‖) := by
  set y : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ) T₀‖ with hy_def
  set c : ℝ := Cbr (i + 1) with hc_def
  have hy_nn : 0 ≤ y := norm_nonneg _
  have hc_nn : 0 ≤ c := hCbr_nn (i + 1)
  have hA : (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
      (c * y) ^ 2 := by
    have h1 : (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
    have h2 : (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ≤ c * y :=
      hCbr (i + 1) T₀
    refine le_trans h1 ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) h2 2
  have hsq : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
      Kc i * ((1 + c) * (1 + y)) ^ 2 := by
    have hone : 1 + (∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤ ((1 + c) * (1 + y)) ^ 2 := by
      nlinarith [hA, mul_nonneg hc_nn hy_nn, sq_nonneg (c * y), hc_nn, hy_nn,
        mul_nonneg (mul_nonneg hc_nn hy_nn) (mul_nonneg hc_nn hy_nn)]
    exact le_trans (hjets i) (mul_le_mul_of_nonneg_left hone (hKc_nn i))
  have hrhs_nn : 0 ≤ Real.sqrt (Kc i) * (1 + c) * (1 + y) := by positivity
  refine le_of_sq_le_sq ?_ hrhs_nn
  calc ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2
      ≤ Kc i * ((1 + c) * (1 + y)) ^ 2 := hsq
    _ = (Real.sqrt (Kc i) * (1 + c) * (1 + y)) ^ 2 := by
        rw [show (Real.sqrt (Kc i) * (1 + c) * (1 + y)) ^ 2 =
          Real.sqrt (Kc i) ^ 2 * ((1 + c) * (1 + y)) ^ 2 by ring,
          Real.sq_sqrt (hKc_nn i)]

theorem exists_coeffContraction_covGrad_secondCovGrad_l2_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E + 5 ≤ a) {R₀ : ℝ} (_hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cgrad : ℝ, 0 ≤ Cgrad ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ S : SmoothCcTensor g₀ 0 2,
          ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 1)
              (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
            Cgrad * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
  classical
  set w := Module.finrank ℝ E / 2 + 2 with hwdef
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ := jet_fibreNormSq_sup_le_sharp (I := I) (M := M) g₀ (2 + 2) 2
  obtain ⟨CbrA, hCbrA_nn, hCbrA⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  obtain ⟨Cj0, hCj0_nn, hCj0⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 0
  set Bsq : ℝ := (CbrA * R₀) ^ 2 with hBsq_def
  have hBsq_nn : 0 ≤ Bsq := sq_nonneg _
  set BgradSq : ℝ := Cemb 1 * ∑ m ∈ Finset.range w, Kc (1 + m) * (1 + Bsq) with hBgradSq_def
  have hBgradSq_nn : 0 ≤ BgradSq := mul_nonneg (hCemb_nn 1)
    (Finset.sum_nonneg (fun m _ => mul_nonneg (hKc_nn _) (by linarith [hBsq_nn])))
  set Bgrad : ℝ := Real.sqrt BgradSq with hBgrad_def
  have hBgrad_nn : 0 ≤ Bgrad := Real.sqrt_nonneg _
  refine ⟨Bgrad * (1 + Cj0), mul_nonneg hBgrad_nn (by linarith [hCj0_nn]), ?_⟩
  intro C₂ T₀ hball hjets S
  have hballA : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ ≤ R₀ := by
    rw [hs_norm_order_congr (I := I) (M := M) g₀
      (show ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 by push_cast; ring) T₀]
    exact hball
  have hjetball : ∀ m : ℕ, m ≤ a →
      (∑ j ∈ Finset.range (m + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤ Bsq := by
    intro m hm
    have hsub : (∑ j ∈ Finset.range (m + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        ∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun j _ _ => sq_nonneg _)
    have hsq : (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
    have hbr := hCbrA T₀
    have hchain : (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ≤
        CbrA * R₀ := by
      refine le_trans hbr ?_
      exact mul_le_mul_of_nonneg_left hballA hCbrA_nn
    refine le_trans hsub (le_trans hsq ?_)
    rw [hBsq_def]
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hchain 2
  have hcovGrad_eq : iteratedCovGrad (I := I) g₀ (2 + 2) 2 1 C₂ =
      covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂ := by
    rw [iteratedCovGrad_succ (I := I) (M := M) g₀ (2 + 2) 2 0 C₂,
      iteratedCovGrad_zero (I := I) (M := M) g₀ (2 + 2) 2 C₂]
  have hΦ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + 1) x
      ((covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂).toSection x) ≤ Bgrad ^ 2 := by
    intro x
    rw [← hcovGrad_eq]
    refine le_trans (hCemb C₂ 1 x) ?_
    rw [hBgrad_def, Real.sq_sqrt hBgradSq_nn, hBgradSq_def]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m hm => ?_)) (hCemb_nn 1)
    have hmw : m < w := Finset.mem_range.mp hm
    have hjet := hjets (1 + m)
    have hball_m : (∑ j ∈ Finset.range (1 + m + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤ Bsq := by
      have := hjetball m (by omega)
      rw [show (1 + m + 2 : ℕ) = m + 3 by omega]
      exact this
    have hone : 1 + (∑ j ∈ Finset.range (1 + m + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤ 1 + Bsq := by linarith [hball_m]
    calc ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 (1 + m) C₂‖ ^ 2
        ≤ Kc (1 + m) * (1 + ∑ j ∈ Finset.range (1 + m + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := hjet
      _ ≤ Kc (1 + m) * (1 + Bsq) := mul_le_mul_of_nonneg_left hone (hKc_nn _)
  have hL2 : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 1)
      (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
      Bgrad * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ :=
    operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ (2 + 2) (2 + 1)
      (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)
      (iteratedCovGrad (I := I) g₀ 0 2 2 S) Bgrad hBgrad_nn hΦ
  have hjet := hCj0 S
  have hdrop := hs_rawConnLap_order_le (I := I) (M := M) g₀ 0 S
  have hdrop_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 2 : ℕ) : ℝ) S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ :=
    hs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ :=
    hs_norm_mono (I := I) (M := M) g₀ (by push_cast; norm_num) S
  have hΔ0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
    rw [← hdrop_congr]; exact hdrop
  have h2jet : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤
      (1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
    nlinarith [hjet, hΔ0, hmono, hCj0_nn,
      norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S),
      mul_le_mul_of_nonneg_left hmono hCj0_nn]
  calc ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖
      ≤ Bgrad * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := hL2
    _ ≤ Bgrad * ((1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖) :=
        mul_le_mul_of_nonneg_left h2jet hBgrad_nn
    _ = Bgrad * (1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
        ring

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem exists_rawConnLap_coeffContraction_secondCovGrad_commutator_Hs_family_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E + 5 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ CEcomm : ℕ → ℝ, (∀ j, 0 ≤ CEcomm j) ∧
      ∀ (j : ℕ) (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
          Kc i * (1 + ∑ j' ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j' T₀‖ ^ 2)) →
        ∀ (S : SmoothCcTensor g₀ 0 2),
        (∃ p : ℕ, S = oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 S)) -
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2
                  (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)))‖ ≤
          CEcomm j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by
  classical
  set Cbr : ℕ → ℝ := fun m =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ m).choose
    with hCbrdef
  have hCbr_nn : ∀ m, 0 ≤ Cbr m := fun m =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ m).choose_spec.1
  have hCbr : ∀ (m : ℕ) (Z : SmoothCcTensor g₀ 0 2),
      ∑ j ∈ Finset.range (m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Z‖ ≤
        Cbr m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) Z‖ :=
    fun m Z =>
      (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
        (I := I) (M := M) g₀ m).choose_spec.2 Z
  set KcLin : ℕ → ℝ := fun i => Real.sqrt (Kc i) * (1 + Cbr (i + 1)) with hKcLindef
  have hKcLin_nn : ∀ i, 0 ≤ KcLin i := fun i =>
    mul_nonneg (Real.sqrt_nonneg _) (by linarith [hCbr_nn (i + 1)])
  obtain ⟨Kptc2, hKptc2_nn, hKptc2⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ 2
  obtain ⟨Kptc3, hKptc3_nn, hKptc3⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (2 + 1)
  set BDT : ℝ := ‖DeTurck.cometricDoubleTraceField (I := I) g₀ 2‖ with hBDT
  set KcDT : ℕ → ℝ := fun i => if i = 0 then BDT else 0 with hKcDT
  have hKcDT_nn : ∀ i, 0 ≤ KcDT i := by
    intro i; rw [hKcDT]; dsimp only; split_ifs with h
    · exact norm_nonneg _
    · exact le_refl 0
  obtain ⟨Cm4in, hCm4in_nn, hCm4in⟩ :=
    master_appCc_jet_le_sharp (I := I) (M := M) g₀ a ha hR₀ (2 + 2) (2 + 2) 3 2
      (by omega) (by omega)
      (fun i => KcLin (i + 2)) (fun i => hKcLin_nn _) (fun l => Cbr (l + 2)) (fun l => hCbr_nn _)
  obtain ⟨Cm56in, hCm56in_nn, hCm56in⟩ :=
    master_appCc_jet_le_sharp (I := I) (M := M) g₀ a ha hR₀ (2 + 2 + 1) (2 + 2) 2 3
      (by omega) (by omega)
      (fun i => Real.sqrt (Module.finrank ℝ E) * KcLin (i + 1))
      (fun i => mul_nonneg (Real.sqrt_nonneg _) (hKcLin_nn _)) (fun l => Cbr (l + 3))
      (fun l => hCbr_nn _)
  obtain ⟨CE2, hCE2_nn, hCE2⟩ :=
    coeffContraction_Hs_bound_sharp (I := I) (M := M) g₀ a ha hR₀ (2 + 2) 1 2 (by omega) (by omega)
      KcLin hKcLin_nn (fun l => Kptc2 (1 + l) * Cbr (l + 2))
      (fun l => mul_nonneg (hKptc2_nn _) (hCbr_nn _))
  obtain ⟨CE3, hCE3_nn, hCE3⟩ :=
    coeffContraction_Hs_bound_sharp (I := I) (M := M) g₀ a ha hR₀ (2 + 2) 1 2 (by omega) (by omega)
      KcLin hKcLin_nn (fun l => Kptc3 l * Cbr (l + 2))
      (fun l => mul_nonneg (hKptc3_nn _) (hCbr_nn _))
  obtain ⟨CE4, hCE4_nn, hCE4⟩ :=
    coeffContraction_Hs_bound_sharp (I := I) (M := M) g₀ a ha hR₀ (2 + 2) 0 3 (by omega) (by omega)
      KcDT hKcDT_nn Cm4in hCm4in_nn
  obtain ⟨CE56, hCE56_nn, hCE56⟩ :=
    coeffContraction_Hs_bound_sharp (I := I) (M := M) g₀ a ha hR₀ (2 + 2) 0 3 (by omega) (by omega)
      KcDT hKcDT_nn Cm56in hCm56in_nn
  refine ⟨fun j => CE2 j + CE3 j + CE4 j + CE56 j + CE56 j,
    fun j => by
      have := hCE2_nn j; have := hCE3_nn j; have := hCE4_nn j; have := hCE56_nn j; linarith, ?_⟩
  intro j C₂ T₀ hball hjets S hSfam
  obtain ⟨p, rfl⟩ := hSfam
  set S := oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀ with hSdef
  set DT₂ := DeTurck.cometricDoubleTraceField (I := I) g₀ 2 with hDT₂def
  have hCtame : ∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ≤
      KcLin i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ) T₀‖) :=
    fun i => coeff_jet_linear_of_sq (I := I) (M := M) g₀ Kc hKc_nn Cbr hCbr_nn hCbr C₂ T₀ hjets i
  have hDTzero : ∀ k : ℕ, iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂ = 0 :=
    iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ (2 + 2) 2 DT₂
      (DeTurck.cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2)
  have hDTjet : ∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i DT₂‖ ≤
      KcDT i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 0 : ℕ) : ℝ) T₀‖) := by
    intro i
    simp only [hKcDT]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have h1 : (1 : ℝ) ≤ 1 +
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ) T₀‖ := by
        have := norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ) T₀)
        linarith
      calc ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂‖ = BDT := by
            rw [iteratedCovGrad_zero, hBDT]
        _ ≤ BDT * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ) T₀‖) := by
            nlinarith [norm_nonneg DT₂, h1, hBDT]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [if_neg (Nat.succ_ne_zero k), hDTzero k, norm_zero]
      simp
  have hΦ4jet : ∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + 2) i
      (covGrad (I := I) (M := M) g₀ (2 + 2) (2 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))‖ ≤
      KcLin (i + 2) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) T₀‖) := by
    intro i
    have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + 2) i
        (covGrad (I := I) (M := M) g₀ (2 + 2) (2 + 1)
          (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))‖ =
        ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 (2 + i) C₂‖ :=
      iteratedCovGrad_norm_comp (I := I) g₀ (2 + 2) 2 2 i C₂
    rw [hcomp, show (2 + i : ℕ) = (i + 2 : ℕ) from by omega]
    have h := hCtame (i + 2)
    rw [show ((i + 2 + 1 : ℕ) : ℝ) = ((i + 3 : ℕ) : ℝ) from by push_cast; ring] at h
    exact h
  have hΦ5jet : ∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2 + 1) (2 + 2) i
      (slotExtend (I := I) (M := M) g₀ (2 + 2) (2 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))‖ ≤
      Real.sqrt (Module.finrank ℝ E) * KcLin (i + 1) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 : ℕ) : ℝ) T₀‖) := by
    intro i
    have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + 1) i
        (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)‖ =
        ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 (1 + i) C₂‖ :=
      iteratedCovGrad_norm_comp (I := I) g₀ (2 + 2) 2 1 i C₂
    refine le_trans (iteratedCovGrad_slotExtend_norm_le (I := I) (M := M) g₀ (2 + 2) (2 + 1) i
      (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)) ?_
    rw [hcomp, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h := hCtame (1 + i)
    have hKeq : KcLin (1 + i) = KcLin (i + 1) := by rw [Nat.add_comm]
    have hHeq : ((1 + i + 1 : ℕ) : ℝ) = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hKeq, hHeq] at h
    exact h
  have hΦ6jet : ∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2 + 1) (2 + 2) i
      (covGrad (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂))‖ ≤
      Real.sqrt (Module.finrank ℝ E) * KcLin (i + 1) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 : ℕ) : ℝ) T₀‖) := by
    intro i
    have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2 + 1) (2 + 2) i
        (covGrad (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
          (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂))‖ =
        ‖iteratedCovGrad (I := I) g₀ (2 + 2 + 1) (2 + 1) (1 + i)
          (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂)‖ :=
      iteratedCovGrad_norm_comp (I := I) g₀ (2 + 2 + 1) (2 + 1) 1 i
        (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂)
    rw [hcomp]
    have hslot := iteratedCovGrad_slotExtend_norm_le (I := I) (M := M) g₀ (2 + 2) 2 (1 + i) C₂
    refine le_trans hslot ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h := hCtame (1 + i)
    have hKeq : KcLin (1 + i) = KcLin (i + 1) := by rw [Nat.add_comm]
    have hHeq : ((1 + i + 1 : ℕ) : ℝ) = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hKeq, hHeq] at h
    exact h
  have hSjet : ∀ (m : ℕ), ‖iteratedCovGrad (I := I) g₀ 0 2 m S‖ ≤
      Cbr m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) S‖ := by
    intro m
    refine le_trans ?_ (hCbr m S)
    exact Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖)
      (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hWdata : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
      Cbr (l + 2) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) S‖ := by
    intro l
    have heq : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + l) S‖ :=
      iteratedCovGrad_norm_comp (I := I) g₀ 0 2 2 l S
    rw [heq, show (2 + l : ℕ) = (l + 2 : ℕ) from by omega]
    exact hSjet (l + 2)
  have hWdata3 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2 + 1) l
      (covGrad (I := I) (M := M) g₀ 0 (2 + 2) (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤
      Cbr (l + 3) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ := by
    intro l
    have heq : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2 + 1) l
        (covGrad (I := I) (M := M) g₀ 0 (2 + 2) (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (3 + l) S‖ :=
      iteratedCovGrad_norm_comp (I := I) g₀ 0 2 3 l S
    rw [heq, show (3 + l : ℕ) = (l + 3 : ℕ) from by omega]
    exact hSjet (l + 3)
  have hW2 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
      (covGrad (I := I) (M := M) g₀ 0 (2 + 1) (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S))‖ ≤
      (Kptc2 (1 + l) * Cbr (l + 2)) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) S‖ := by
    intro l
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
        (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) (1 + l)
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S)‖ :=
      iteratedCovGrad_norm_comp (I := I) g₀ 0 (2 + 1) 1 l
        (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S)
    rw [hcomp]
    refine le_trans (hKptc2 (1 + l) S) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hKptc2_nn _)
    rw [show (1 + l + 2 : ℕ) = (l + 2) + 1 from by omega]
    exact hCbr (l + 2) S
  have hW3 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
      (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2 S))‖ ≤
      (Kptc3 l * Cbr (l + 2)) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) S‖ := by
    intro l
    refine le_trans (hKptc3 l (covGrad (I := I) (M := M) g₀ 0 2 S)) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hKptc3_nn _)
    have hstep : (∑ b ∈ Finset.range (l + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) b (covGrad (I := I) (M := M) g₀ 0 2 S)‖) ≤
        ∑ k ∈ Finset.range (l + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖ := by
      have heq : (∑ b ∈ Finset.range (l + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) b (covGrad (I := I) (M := M) g₀ 0 2 S)‖) =
          ∑ b ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 1) S‖ := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hac : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) b
            (covGrad (I := I) (M := M) g₀ 0 2 S)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + b) S‖ :=
          iteratedCovGrad_norm_comp (I := I) g₀ 0 2 1 b S
        rw [hac, show (1 + b : ℕ) = (b + 1 : ℕ) from by omega]
      rw [heq]
      have hsr := Finset.sum_range_succ' (fun k => ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖) (l + 2)
      have h0 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 0 S‖ := norm_nonneg _
      linarith [hsr, h0]
    refine le_trans hstep ?_
    exact hCbr (l + 2) S
  have hINNER4 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 2)
          (covGrad (I := I) (M := M) g₀ (2 + 2) (2 + 1)
            (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))
          (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤
      Cm4in l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ :=
    fun l => hCm4in p T₀ hball _ hΦ4jet _ hWdata l
  have hINNER5 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 2)
          (slotExtend (I := I) (M := M) g₀ (2 + 2) (2 + 1)
            (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))
          (covGrad (I := I) (M := M) g₀ 0 (2 + 2)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)))‖ ≤
      Cm56in l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ :=
    fun l => hCm56in p T₀ hball _ hΦ5jet _ hWdata3 l
  have hINNER6 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) l
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 2)
          (covGrad (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂))
          (covGrad (I := I) (M := M) g₀ 0 (2 + 2)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)))‖ ≤
      Cm56in l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ :=
    fun l => hCm56in p T₀ hball _ hΦ6jet _ hWdata3 l
  have hbt2 := hCE2 p T₀ hball C₂ hCtame _ hW2 j
  have hbt3 := hCE3 p T₀ hball C₂ hCtame _ hW3 j
  have hbt4 := hCE4 p T₀ hball DT₂ hDTjet _ hINNER4 j
  have hbt5 := hCE56 p T₀ hball DT₂ hDTjet _ hINNER5 j
  have hbt6 := hCE56 p T₀ hball DT₂ hDTjet _ hINNER6 j
  have hcomm := rawConnLap_appCc_iteratedCovGrad_two_comm (I := I) g₀ 2 2 C₂ S
  have hdecomp : rawTensorConnLapSmooth (I := I) g₀ 0 2
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)) -
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)) =
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
            (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S)) +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + 1)
            (covGrad (I := I) (M := M) g₀ 0 2 S)) +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 DT₂
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 2) (2 + 1)
              (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 DT₂
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ (2 + 2) (2 + 1)
              (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))
            (covGrad (I := I) (M := M) g₀ 0 (2 + 2)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S))) +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 DT₂
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂))
            (covGrad (I := I) (M := M) g₀ 0 (2 + 2)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S))) := by
    rw [hcomm, hDT₂def]
    abel
  rw [hdecomp]
  have hQS_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  set u2 := operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
    (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
      (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S)) with hu2
  set u3 := operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
    (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 S)) with hu3
  set u4 := operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 DT₂
    (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 2)
      (covGrad (I := I) (M := M) g₀ (2 + 2) (2 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)) with hu4
  set u5 := operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 DT₂
    (operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 2)
      (slotExtend (I := I) (M := M) g₀ (2 + 2) (2 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂))
      (covGrad (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 S))) with hu5
  set u6 := operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 DT₂
    (operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 2)
      (covGrad (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂))
      (covGrad (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 S))) with hu6
  have htri : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
      (u2 + u3 + u4 + u5 + u6)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u2‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u3‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u4‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u5‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u6‖ := by
    rw [smoothCcToTensorHs_add, smoothCcToTensorHs_add, smoothCcToTensorHs_add,
      smoothCcToTensorHs_add]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    exact norm_add_le _ _
  refine le_trans htri ?_
  have e2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u2‖ ≤
      CE2 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := hbt2
  have e3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u3‖ ≤
      CE3 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := hbt3
  have e4 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u4‖ ≤
      CE4 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := hbt4
  have e5 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u5‖ ≤
      CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := hbt5
  have e6 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u6‖ ≤
      CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := hbt6
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u2‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u3‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u4‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u5‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) u6‖
      ≤ CE2 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE3 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE4 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ :=
        add_le_add (add_le_add (add_le_add (add_le_add e2 e3) e4) e5) e6
    _ = (CE2 j + CE3 j + CE4 j + CE56 j + CE56 j) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by ring

set_option maxHeartbeats 1600000 in

theorem exists_coeffContraction_secondCovGrad_smallFibreCoeff_Hs_family_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E + 5 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Clower : ℕ → ℝ, (∀ j, 0 ≤ Clower j) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i, ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
          Kc i * (1 + ∑ j' ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j' T₀‖ ^ 2)) →
        ∀ (j : ℕ) (S : SmoothCcTensor g₀ 0 2),
        (∃ p : ℕ, S = oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤
          εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            Clower j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨CEcomm, hCEcomm_nn, hCEcomm⟩ :=
    exists_rawConnLap_coeffContraction_secondCovGrad_commutator_Hs_family_le (I := I) (M := M) g₀ a ha
      hR₀ Kc hKc_nn
  obtain ⟨Cgrad, hCgrad_nn, hCgrad⟩ :=
    exists_coeffContraction_covGrad_secondCovGrad_l2_le (I := I) (M := M) g₀ a ha hR₀ Kc hKc_nn
  obtain ⟨Cj0, hCj0_nn, hCj0⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 0
  obtain ⟨Cj1, hCj1_nn, hCj1⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 1
  set Mbase : ℝ := εC * (1 + Cj0) + (Cgrad + εC * Cj1) + εC * Cj0 + 1 with hMbase_def
  have hMbase_nn : 0 ≤ Mbase := by rw [hMbase_def]; positivity
  set ClowerFn : ℕ → ℝ := fun j => Mbase + ∑ i ∈ Finset.range j, CEcomm i with hClowerFn_def
  have hClowerFn_nn : ∀ j, 0 ≤ ClowerFn j := fun j => by
    rw [hClowerFn_def]
    exact add_nonneg hMbase_nn (Finset.sum_nonneg fun i _ => hCEcomm_nn i)
  refine ⟨ClowerFn, hClowerFn_nn, ?_⟩
  intro C₂ T₀ hball hsup hjets
  have harm : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
        εC * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := fun S =>
    operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ (2 + 2) 2 C₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 S) εC hεC_nn hsup
  have hG0 : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤
        εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          ClowerFn 0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ := by
    intro S
    have hHs0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ =
        ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ := by
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num, hs_zero_norm_eq,
        SmoothCcTensor.norm_toL2]
    have hjet := hCj0 S
    have hP0_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ := norm_nonneg _
    have hQ1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ :=
      norm_nonneg _
    rw [hHs0]
    have hClf0 : ClowerFn 0 = Mbase := by
      rw [hClowerFn_def]; simp
    rw [hClf0]
    have hstep : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
        εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Cj0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖) :=
      le_trans (harm S) (mul_le_mul_of_nonneg_left hjet hεC_nn)
    have hMbase_ge : εC * Cj0 ≤ Mbase := by
      rw [hMbase_def]; nlinarith [hεC_nn, hCj0_nn, mul_nonneg hεC_nn hCj0_nn]
    nlinarith [hstep, hMbase_ge, hP0_nn, hQ1_nn, hεC_nn, hCj0_nn,
      mul_nonneg hQ1_nn hεC_nn]
  have hG1 : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤
        εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          ClowerFn 1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 + 1 : ℕ) : ℝ) S‖ := by
    intro S
    set Q := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 + 1 : ℕ) : ℝ) S‖ with hQ_def
    set P := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ with hP_def
    have hQ_nn : 0 ≤ Q := norm_nonneg _
    have hP_nn : 0 ≤ P := norm_nonneg _
    have ha2 := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad (I := I) (M := M) g₀ 0
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S))
    simp only [oneMinusConnLapSmoothIter_zero] at ha2
    rw [hs_norm_order_congr (I := I) (M := M) g₀
        (show ((2 * 0 + 1 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) by norm_num)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)),
      SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at ha2
    have hA2jet := hCj0 S
    have hdrop := hs_rawConnLap_order_le (I := I) (M := M) g₀ 0 S
    have hdrop_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 2 : ℕ) : ℝ) S‖ = Q :=
      hs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
    have hmono01 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ ≤ Q :=
      hs_norm_mono (I := I) (M := M) g₀ (by push_cast; norm_num) S
    have hΔ0_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ ≤ Q := by
      rw [← hdrop_congr]; exact hdrop
    have hA2_le : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤ (1 + Cj0) * Q := by
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            Cj0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ := hA2jet
      nlinarith [h1, hΔ0_le, hmono01, hCj0_nn, hQ_nn,
        mul_le_mul_of_nonneg_left hmono01 hCj0_nn]
    have ha_bound : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤ εC * (1 + Cj0) * Q := by
      calc ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖
          ≤ εC * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := harm S
        _ ≤ εC * ((1 + Cj0) * Q) := mul_le_mul_of_nonneg_left hA2_le hεC_nn
        _ = εC * (1 + Cj0) * Q := by ring
    have hcov3 : covGrad (I := I) (M := M) g₀ 0 (2 + 2) (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
        iteratedCovGrad (I := I) g₀ 0 2 3 S :=
      (iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 2 S).symm
    have hcov : covGrad (I := I) (M := M) g₀ 0 2
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) (2 + 1)
            (covGrad (I := I) (M := M) g₀ (2 + 2) 2 C₂)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S) +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂)
            (iteratedCovGrad (I := I) g₀ 0 2 3 S) := by
      rw [covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ (2 + 2) 2 C₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 S), hcov3]
    have hgrad := hCgrad C₂ T₀ hball hjets S
    have hgrad_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ = Q :=
      hs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
    rw [hgrad_congr] at hgrad
    have hprinc := coeffContraction_slotExtend_l2_le_of_pointwise (I := I) (M := M) g₀ (2 + 2) 2 C₂
      hεC_nn hsup (iteratedCovGrad (I := I) g₀ 0 2 3 S)
    have hA3jet := hCj1 S
    have hA3_le : ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ ≤ P + Cj1 * Q := hA3jet
    have hb_bound : ‖covGrad (I := I) (M := M) g₀ 0 2
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤
        εC * P + (Cgrad + εC * Cj1) * Q := by
      rw [hcov]
      refine le_trans (norm_add_le _ _) ?_
      have hprinc' : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂)
            (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖ ≤ εC * P + εC * Cj1 * Q := by
        calc ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ (2 + 2) 2 C₂)
              (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖
            ≤ εC * ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := hprinc
          _ ≤ εC * (P + Cj1 * Q) := mul_le_mul_of_nonneg_left hA3_le hεC_nn
          _ = εC * P + εC * Cj1 * Q := by ring
      have hdist : Cgrad * Q + (εC * P + εC * Cj1 * Q) =
          εC * P + (Cgrad + εC * Cj1) * Q := by ring
      linarith [hgrad, hprinc', hdist]
    have hClf1_ge : εC * (1 + Cj0) + (Cgrad + εC * Cj1) ≤ ClowerFn 1 := by
      have h1 : Mbase ≤ ClowerFn 1 := by
        simp only [hClowerFn_def, Finset.sum_range_one]
        linarith [hCEcomm_nn 0]
      have h2 : εC * (1 + Cj0) + (Cgrad + εC * Cj1) ≤ Mbase := by
        rw [hMbase_def]; linarith [mul_nonneg hεC_nn hCj0_nn]
      linarith [h1, h2]
    set α := εC * (1 + Cj0) with hα_def
    set β := Cgrad + εC * Cj1 with hβ_def
    have hα_nn : 0 ≤ α := mul_nonneg hεC_nn (by linarith [hCj0_nn])
    have hβ_nn : 0 ≤ β := add_nonneg hCgrad_nn (mul_nonneg hεC_nn hCj1_nn)
    have ha_sq : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ^ 2 ≤ (α * Q) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ha_bound 2
    have hb_sq : ‖covGrad (I := I) (M := M) g₀ 0 2
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ^ 2 ≤
        (εC * P + β * Q) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb_bound 2
    have hfinal : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖ ≤ εC * P + (α + β) * Q := by
      refine le_of_sq_le_sq ?_
        (add_nonneg (mul_nonneg hεC_nn hP_nn) (mul_nonneg (add_nonneg hα_nn hβ_nn) hQ_nn))
      rw [ha2]
      nlinarith [ha_sq, hb_sq,
        mul_nonneg (mul_nonneg (mul_nonneg hεC_nn hα_nn) hP_nn) hQ_nn,
        mul_nonneg (mul_nonneg hα_nn hβ_nn) (mul_nonneg hQ_nn hQ_nn)]
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 S))‖
        ≤ εC * P + (α + β) * Q := hfinal
      _ ≤ εC * P + ClowerFn 1 * Q := by
          have hmul := mul_le_mul_of_nonneg_right hClf1_ge hQ_nn
          linarith [hmul]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    match j, IH with
    | 0, _ => exact fun S _ => hG0 S
    | 1, _ => exact fun S _ => hG1 S
    | (i + 2), IH =>
      have ih := IH i (by omega)
      intro S hSfam
      have hA3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ i
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S))
      have hLarm : oneMinusConnLapSmooth (I := I) g₀ 0 2
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2 S)) =
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) -
            (rawTensorConnLapSmooth (I := I) g₀ 0 2
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 S)) -
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2
                  (rawTensorConnLapSmooth (I := I) g₀ 0 2 S))) := by
        rw [oneMinusConnLapSmooth, oneMinusConnLapSmooth, coeffContraction_secondCovGrad_sub]
        abel
      rw [hA3, hLarm, smoothCcToTensorHs_sub]
      refine le_trans (norm_sub_le _ _) ?_
      have hih := ih (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
        (by obtain ⟨p, hp⟩ := hSfam
            exact ⟨p + 1, by rw [hp, oneMinusConnLapSmoothIter_succ]⟩)
      have hcommΔ := rawConnLap_oneMinusConnLap_comm (I := I) (M := M) g₀ S
      have hA3Δ := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ i
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)
      have hprinc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2
              (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ := by
        rw [hcommΔ, ← hA3Δ]
      have hA3S := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀
        (i + 1) S
      have hlower : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ)
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ := by
        rw [← hA3S]
      rw [hprinc, hlower] at hih
      have hE := hCEcomm i C₂ T₀ hball hjets S hSfam
      have hcast_goal : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 + 1 : ℕ) : ℝ) S‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ :=
        hs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
      rw [hcast_goal]
      have hQ3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      have hCl_rec : ClowerFn i + CEcomm i ≤ ClowerFn (i + 2) := by
        have hsub : ∑ k ∈ Finset.range i, CEcomm k + CEcomm i ≤
            ∑ k ∈ Finset.range (i + 2), CEcomm k := by
          calc ∑ k ∈ Finset.range i, CEcomm k + CEcomm i
              = ∑ k ∈ Finset.range (i + 1), CEcomm k := (Finset.sum_range_succ CEcomm i).symm
            _ ≤ ∑ k ∈ Finset.range (i + 2), CEcomm k :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.range_mono (by omega)) (fun k _ _ => hCEcomm_nn k)
        simp only [hClowerFn_def]
        linarith [hsub]
      refine le_trans (add_le_add hih hE) ?_
      have hmul := mul_le_mul_of_nonneg_right hCl_rec hQ3_nn
      have hdist : ClowerFn i *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ +
          CEcomm i * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ =
          (ClowerFn i + CEcomm i) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ := by ring
      linarith [hmul, hdist]

end Connection
end Integral
end DifferentialGeometry

end
