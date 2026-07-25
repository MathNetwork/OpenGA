import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem oneMinusIter_coeff
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g₀ 0 s))
    (S : SmoothCcTensor g₀ 0 s)
    (m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 s) (k : ℕ) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 s k S)) m =
      (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ k *
        tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        oneMinus_coeff (I := I) (M := M) g₀ s h_compact
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 s k S) m,
        ih, pow_succ]
      ring

private theorem ccWeight_even
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ) (S : SmoothCcTensor g₀ 0 s)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g₀ 0 s)) :
    Summable (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s =>
      tensorSobolevWeight (I := I) (M := M) m ((2 * k : ℕ) : ℝ) *
        (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
  classical
  have hterm :
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s =>
        tensorSobolevWeight (I := I) (M := M) m ((2 * k : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) =
        fun m => (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 s k S)) m) ^ 2 := by
    funext m
    rw [oneMinusIter_coeff (I := I) (M := M) g₀ s h_compact S m k, mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [hterm]
  exact tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 s k S))

private theorem ccWeight_sum
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ) (S : SmoothCcTensor g₀ 0 s)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g₀ 0 s)) :
    Summable (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s =>
      tensorSobolevWeight (I := I) (M := M) m σ *
        (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (σ / 2)
  have hσk : σ ≤ ((2 * k : ℕ) : ℝ) := by
    have : σ / 2 ≤ (k : ℝ) := hk
    push_cast
    linarith
  exact summable_tensorSobolevWeight_of_even
    (I := I) (M := M)
    (fun m => tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m)
    hσk (ccWeight_even (I := I) (M := M) g₀ s k S h_compact)

def ccTensorToHs (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 s) :
    tensorHs (I := I) (M := M) g₀ 0 s σ where
  coeff m := tensorL2Coeff (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
    (SmoothCcTensor.toL2 S) m
  weighted_summable := ccWeight_sum (I := I) (M := M) g₀ s σ S
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)

@[simp] theorem ccTensorToHs_coeff
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 s)
    (m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 s) :
    (ccTensorToHs (I := I) (M := M) g₀ s σ S).coeff m =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
      (SmoothCcTensor.toL2 S) m :=
  rfl

@[simp] theorem ccTensorToHs_add
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (sigma : ℝ)
    (S T : SmoothCcTensor g₀ 0 s) :
    ccTensorToHs (I := I) (M := M) g₀ s sigma (S + T) =
      ccTensorToHs (I := I) (M := M) g₀ s sigma S +
        ccTensorToHs (I := I) (M := M) g₀ s sigma T := by
  refine tensorHs.ext ?_
  funext m
  rw [tensorHs.add_coeff]
  simp only [ccTensorToHs_coeff]
  rw [show SmoothCcTensor.toL2 (S + T) =
      SmoothCcTensor.toL2 S + SmoothCcTensor.toL2 T from map_add _ _ _,
    tensorL2Coeff_add]

@[simp] theorem ccTensorToHs_smul
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (sigma c : ℝ)
    (S : SmoothCcTensor g₀ 0 s) :
    ccTensorToHs (I := I) (M := M) g₀ s sigma (c • S) =
      c • ccTensorToHs (I := I) (M := M) g₀ s sigma S := by
  refine tensorHs.ext ?_
  funext m
  rw [tensorHs.smul_coeff]
  simp only [ccTensorToHs_coeff]
  rw [show SmoothCcTensor.toL2 (c • S) = c • SmoothCcTensor.toL2 S from map_smul _ _ _,
    tensorL2Coeff_smul]

theorem ccToHs_norm_sq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g₀ s σ S‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        tensorSobolevWeight (I := I) (M := M) m σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 S) m) ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum]
  exact tsum_congr (fun m => by rw [ccTensorToHs_coeff])

theorem cc_partial_le_norm
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 s)
    (F : Finset
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s)) :
    (∑ m ∈ F,
        tensorSobolevWeight (I := I) (M := M) m σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 S) m) ^ 2) ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s σ S‖ ^ 2 := by
  rw [ccToHs_norm_sq]
  exact (ccTensorToHs (I := I) (M := M) g₀ s σ S).weighted_summable.sum_le_tsum F
    (fun m _ => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) m σ)
      (sq_nonneg _))

theorem ccToHs_norm_mono
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {σ τ : ℝ} (hστ : σ ≤ τ)
    (S : SmoothCcTensor g₀ 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g₀ s σ S‖ ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s τ S‖ := by
  have hnn : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s τ S‖ := norm_nonneg _
  have hsq : ‖ccTensorToHs (I := I) (M := M) g₀ s σ S‖ ^ 2 ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s τ S‖ ^ 2 := by
    rw [ccToHs_norm_sq, ccToHs_norm_sq]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      have hbase : (1 : ℝ) ≤
          1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m := one_le_one_add_lambda (I := I) (M := M) m
      have hw : tensorSobolevWeight (I := I) (M := M) m σ ≤
          tensorSobolevWeight (I := I) (M := M) m τ := by
        unfold tensorSobolevWeight
        exact Real.rpow_le_rpow_of_exponent_le hbase hστ
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    · exact (ccTensorToHs (I := I) (M := M) g₀ s σ S).weighted_summable
    · exact (ccTensorToHs (I := I) (M := M) g₀ s τ S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

private theorem rawIter_coeff
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g₀ 0 s))
    (S : SmoothCcTensor g₀ 0 s)
    (m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 s) (i : ℕ) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)) m =
      (-DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ i *
        tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [rawTensorConnLapIter_succ,
        rawLap_coeff (I := I) (M := M) g₀ s h_compact
          (rawTensorConnLapIter (I := I) g₀ 0 s i S) m,
        ih, pow_succ]
      ring

private theorem rawIter_tsum
    (g₀ : SmoothRiemannianMetric I M) (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ (2 * i) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S))]
  refine tsum_congr (fun m => ?_)
  rw [rawIter_coeff (I := I) (M := M) g₀ s h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m
  set L := DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
    (I := I) (M := M) m
  rw [mul_pow, ← pow_mul, mul_comm i 2, (even_two_mul i).neg_pow L]

private theorem covIter_tsum
    (g₀ : SmoothRiemannianMetric I M) (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖covGrad (I := I) (M := M) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ (2 * i + 1) *
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
  rw [hraw_eq]
  have hinner :
      tensorL2Inner (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S).toFun U.toFun =
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          tensorL2Coeff (I := I) (M := M) h_compact
              (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S)) m *
            tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 U) m := by
    have hsymm := SmoothCcTensor.inner_def (I := I) (M := M)
      (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S) U
    rw [← hsymm]
    rw [← SmoothCcTensor.inner_toL2 (I := I) (M := M)
      (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S) U]
    set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
    have h_par := b.tsum_inner_mul_inner
      (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S))
      (SmoothCcTensor.toL2 U)
    rw [← h_par]
    refine tsum_congr (fun m => ?_)
    rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S)) m,
      tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 U) m]
    rw [show (⟪SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S), b m⟫_ℝ : ℝ) =
        ⟪b m, SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S)⟫_ℝ from
      real_inner_comm _ _]
  rw [hinner, ← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [rawIter_coeff (I := I) (M := M) g₀ s h_compact S m (i + 1),
    hU_def,
    rawIter_coeff (I := I) (M := M) g₀ s h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
    (I := I) (M := M) m with hL_def
  have hpow : ((-L) ^ (i + 1) * c) * ((-L) ^ i * c) = (-L) ^ (2 * i + 1) * c ^ 2 := by
    rw [show (2 * i + 1) = (i + 1) + i by ring, pow_add]
    ring
  rw [hpow, (odd_two_mul_add_one i).neg_pow L]
  ring

private theorem covIter_odd
    (g₀ : SmoothRiemannianMetric I M) (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖covGrad (I := I) (M := M) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i + 1 : ℕ) : ℝ) S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
    with hcompact_def
  have hnn : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i + 1 : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  have hsq :
      ‖covGrad (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 ≤
        ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i + 1 : ℕ) : ℝ) S‖ ^ 2 := by
    rw [covIter_tsum (I := I) (M := M) g₀ s i S,
      ccToHs_norm_sq]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
      have hbase_nn : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m ≤
            1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m := by linarith
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
          (1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m) ^ (2 * i + 1) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg c)
    · have hsummable := (ccTensorToHs (I := I) (M := M) g₀ s
        ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
      refine Summable.of_nonneg_of_le ?_ ?_ hsummable
      · intro m
        have hbase_nn : (0 : ℝ) ≤
            DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        positivity
      · intro m
        have hbase_nn : (0 : ℝ) ≤
            DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        have hbase_le :
            DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m ≤
              1 +
                DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                  (I := I) (M := M) m := by linarith
        have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
            (1 +
                DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                  (I := I) (M := M) m) ^ (2 * i + 1) := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast]
        rw [hweight_eq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg _)
    · exact (ccTensorToHs (I := I) (M := M) g₀ s
        ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

private theorem rawIter_even
    (g₀ : SmoothRiemannianMetric I M) (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i : ℕ) : ℝ) S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s
    with hcompact_def
  have hnn : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  have hsq :
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 ≤
        ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i : ℕ) : ℝ) S‖ ^ 2 := by
    rw [ccToHs_norm_sq,
      ← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S))]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      rw [rawIter_coeff (I := I) (M := M) g₀ s h_compact S m i]
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m
      have hbase_nn : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m ≤
            1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m := by linarith
      have hlhs_eq :
          ((-DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ i * c) ^ 2 =
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ (2 * i) * c ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm i 2,
          (even_two_mul i).neg_pow
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m)]
      rw [hlhs_eq]
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i : ℕ) : ℝ) =
          (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ (2 * i) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le (2 * i)) (sq_nonneg c)
    · exact tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S))
    · exact (ccTensorToHs (I := I) (M := M) g₀ s
        ((2 * i : ℕ) : ℝ) S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

private theorem mode_le_jet
    (g₀ : SmoothRiemannianMetric I M) (s j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 S) m) ^ 2 ≤
          C * (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
  classical
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      exists_iteratedCovGrad_rawConnLapIter_l2Norm_le (I := I) (M := M) g₀ i s
    refine ⟨(Cfun 0) ^ 2, by positivity, fun S => ?_⟩
    have hj : j = 2 * i := by omega
    have htsum :
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
          ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 := by
      rw [rawIter_tsum (I := I) (M := M) g₀ s i S, hj]
    rw [htsum]
    have hnorm_le : ‖SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        Cfun 0 * ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
      have h := hCfun 0 S
      rw [iteratedCovGrad_zero (I := I) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)] at h
      rw [SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)]
      have hrange : 2 * i + 0 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hsum_nn : 0 ≤
        ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hnn : 0 ≤ ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ := norm_nonneg _
    calc ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2
        ≤ (Cfun 0 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg (hCfun_nn 0) hsum_nn]
          · exact hnorm_le
      _ = (Cfun 0) ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by ring
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      exists_iteratedCovGrad_rawConnLapIter_l2Norm_le (I := I) (M := M) g₀ i s
    refine ⟨(Cfun 1) ^ 2, by positivity, fun S => ?_⟩
    have hj : j = 2 * i + 1 := by omega
    have htsum :
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 s,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
          ‖covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 := by
      rw [covIter_tsum (I := I) (M := M) g₀ s i S, hj]
    rw [htsum]
    have hnorm_le : ‖covGrad (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        Cfun 1 * ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
      have h := hCfun 1 S
      have hcov : iteratedCovGrad (I := I) g₀ 0 s 1
            (rawTensorConnLapIter (I := I) g₀ 0 s i S) =
          covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S) := rfl
      rw [hcov] at h
      have hrange : 2 * i + 1 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hsum_nn : 0 ≤
        ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hnn : 0 ≤ ‖covGrad (I := I) (M := M) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ := norm_nonneg _
    calc ‖covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2
        ≤ (Cfun 1 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg (hCfun_nn 1) hsum_nn]
          · exact hnorm_le
      _ = (Cfun 1) ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by ring

private theorem mode_summable
    (g₀ : SmoothRiemannianMetric I M) (s j : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    Summable (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s =>
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ j *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
          (SmoothCcTensor.toL2 S) m) ^ 2) := by
  have hfull := (ccTensorToHs (I := I) (M := M) g₀ s (j : ℝ) S).weighted_summable
  refine Summable.of_nonneg_of_le ?_ ?_ hfull
  · intro m
    have hbase_nn : (0 : ℝ) ≤
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m := tensor_lambda_nonneg (I := I) (M := M) m
    positivity
  · intro m
    have hbase_nn : (0 : ℝ) ≤
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m := tensor_lambda_nonneg (I := I) (M := M) m
    have hbase_le :
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m ≤
          1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m := by linarith
    have hweight : tensorSobolevWeight (I := I) (M := M) m (j : ℝ) =
        (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ j := by
      unfold tensorSobolevWeight
      rw [Real.rpow_natCast]
    rw [hweight, ccTensorToHs_coeff]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbase_nn hbase_le j) (sq_nonneg _)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem icg_comp_norm
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

private theorem jet_even
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ s k
  refine ⟨((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)), by positivity, fun S => ?_⟩
  set Nspec : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hlap_le : ∀ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S).toFun ≤
        Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have heq : tensorL2Norm (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S).toFun =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ :=
      (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀ (rawTensorConnLapIter (I := I) g₀ 0 s i S)).trans
        (SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)).symm
    rw [heq]
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i : ℕ) : ℝ) S‖ :=
      rawIter_even (I := I) (M := M) g₀ s i S
    have h2 : ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * i : ℕ) : ℝ) S‖ ≤
        Nspec := by
      rw [hNspec_def]
      refine ccToHs_norm_mono (I := I) (M := M) g₀ s ?_ S
      have : (2 * i : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  have hlapsum : ∑ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S).toFun ≤
        ((k + 1 : ℕ) : ℝ) * Nspec := by
    calc ∑ i ∈ Finset.range (k + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S).toFun
        ≤ ∑ _i ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hlap_le
      _ = ((k + 1 : ℕ) : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hjet_le : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤ Cg * (((k + 1 : ℕ) : ℝ) * Nspec) := by
    intro j hj
    have hj2k : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgj := hCg j hj2k S
    have heqj : tensorL2Norm (I := I) (M := M) g₀ 0 (s + j)
          (iteratedCovGrad (I := I) g₀ 0 s j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 s j S)).symm
    rw [heqj] at hgj
    exact le_trans hgj (mul_le_mul_of_nonneg_left hlapsum hCg_nn)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖
      ≤ ∑ _j ∈ Finset.range (2 * k + 1), Cg * (((k + 1 : ℕ) : ℝ) * Nspec) :=
        Finset.sum_le_sum hjet_le
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (((k + 1 : ℕ) : ℝ) * Nspec)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)) * Nspec := by push_cast; ring

private theorem jet_odd
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Clow, hClow_nn, hClow⟩ := jet_even (I := I) (M := M) g₀ s k
  obtain ⟨Cgard, hCgard_nn, hCgard⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ (s + 1) k
  obtain ⟨Ceven, hCeven_nn, hCeven⟩ := jet_even (I := I) (M := M) g₀ s k
  have hcommfam : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
          C * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
    fun i => exists_rawConnLapIter_covGrad_commutator_l2Norm_le (I := I) (M := M) g₀ s i
  set Ccomm : ℕ → ℝ := fun i => Classical.choose (hcommfam i) with hCcomm_def
  have hCcomm_nn : ∀ i, 0 ≤ Ccomm i := fun i => (Classical.choose_spec (hcommfam i)).1
  have hCcomm : ∀ i, ∀ S : SmoothCcTensor g₀ 0 s,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
          covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        Ccomm i * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
    fun i => (Classical.choose_spec (hcommfam i)).2
  set Ccommsum : ℝ := ∑ i ∈ Finset.range (k + 1), Ccomm i with hCcommsum_def
  have hCcommsum_nn : 0 ≤ Ccommsum :=
    Finset.sum_nonneg (fun i _ => hCcomm_nn i)
  refine ⟨Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven), by positivity,
    fun S => ?_⟩
  set Nspec : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k + 1 : ℕ) : ℝ) S‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hccmono : ∀ (σ : ℕ), σ ≤ 2 * k + 1 →
      ‖ccTensorToHs (I := I) (M := M) g₀ s ((σ : ℕ) : ℝ) S‖ ≤ Nspec := by
    intro σ hσ
    rw [hNspec_def]
    refine ccToHs_norm_mono (I := I) (M := M) g₀ s ?_ S
    have : (σ : ℕ) ≤ (2 * k + 1 : ℕ) := hσ
    exact_mod_cast this
  have hlow_le : ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ ≤
      Nspec := by
    exact hccmono (2 * k) (by omega)
  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤ Clow * Nspec := by
    refine le_trans (hClow S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hClow_nn
  have heven_le : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤ Ceven * Nspec := by
    refine le_trans (hCeven S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hCeven_nn
  have hccoeff_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
          (covGrad (I := I) (M := M) g₀ 0 s S)‖ ≤
        (1 + Ccomm i * Ceven) * Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit :
        rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) =
          covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S) +
            (rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
              covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)) := by
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hmain : ‖covGrad (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤ Nspec := by
      refine le_trans
        (covIter_odd (I := I) (M := M) g₀ s i S) ?_
      exact hccmono (2 * i + 1) (by omega)
    have hcomm := hCcomm i S
    have hsub_le : 2 * i ≤ 2 * k + 1 := by omega
    have hsubrange : ∑ a ∈ Finset.range (2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤
        ∑ a ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 s a S‖)
        (Finset.range_mono hsub_le) (fun a _ _ => norm_nonneg _)
    have hcommterm :
        ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
          Ccomm i * Ceven * Nspec := by
      calc ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S) -
              covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖
          ≤ Ccomm i * ∑ a ∈ Finset.range (2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := hcomm
        _ ≤ Ccomm i * ∑ a ∈ Finset.range (2 * k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
            mul_le_mul_of_nonneg_left hsubrange (hCcomm_nn i)
        _ ≤ Ccomm i * (Ceven * Nspec) :=
            mul_le_mul_of_nonneg_left heven_le (hCcomm_nn i)
        _ = Ccomm i * Ceven * Nspec := by ring
    calc ‖covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ +
          ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖
        ≤ Nspec + Ccomm i * Ceven * Nspec :=
          add_le_add hmain hcommterm
      _ = (1 + Ccomm i * Ceven) * Nspec := by ring
  have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖ ≤
      Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
    have hbridge : ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 s S)‖ := by
      have h := icg_comp_norm (I := I) (M := M) g₀ s 1 (2 * k) S
      have hcov : covGrad (I := I) (M := M) g₀ 0 s S =
          iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
      have horder : ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (1 + 2 * k) S‖ :=
        norm_iteratedCovGrad_order_eq (I := I) (M := M) g₀ s (by omega) S
      rw [horder, ← h, hcov]
    rw [hbridge]
    have hgard := hCgard (2 * k) (le_refl _) (covGrad (I := I) (M := M) g₀ 0 s S)
    have hgard' : ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 s S)‖ ≤
        Cgard * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
            (covGrad (I := I) (M := M) g₀ 0 s S)‖ := by
      have heq1 : tensorL2Norm (I := I) (M := M) g₀ 0 ((s + 1) + 2 * k)
            (iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
              (covGrad (I := I) (M := M) g₀ 0 s S)).toFun =
          ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
            (covGrad (I := I) (M := M) g₀ 0 s S)‖ :=
        DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
          (iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
            (covGrad (I := I) (M := M) g₀ 0 s S))
      rw [← heq1]
      refine le_trans hgard ?_
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCgard_nn
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
          (covGrad (I := I) (M := M) g₀ 0 s S))
    have hsumcoeff : ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
            (covGrad (I := I) (M := M) g₀ 0 s S)‖ ≤
        (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
      calc ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S)‖
          ≤ ∑ i ∈ Finset.range (k + 1), (1 + Ccomm i * Ceven) * Nspec :=
            Finset.sum_le_sum hccoeff_le
        _ = ∑ i ∈ Finset.range (k + 1), (Nspec + (Ccomm i) * (Ceven * Nspec)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_mul]
            rw [hCcommsum_def]
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 s S)‖
        ≤ Cgard * ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S)‖ := hgard'
      _ ≤ Cgard * ((((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec) :=
          mul_le_mul_of_nonneg_left hsumcoeff hCgard_nn
      _ = Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by ring
  rw [Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 s j S‖) (2 * k + 1)]
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖
      ≤ Clow * Nspec + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec :=
        add_le_add hlowsum htop_le
    _ = (Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven)) * Nspec := by ring

theorem hsJet_le
    (g₀ : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ := by
  classical
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨C, hC_nn, hC⟩ := jet_even (I := I) (M := M) g₀ s k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact hC S
  · obtain ⟨C, hC_nn, hC⟩ := jet_odd (I := I) (M := M) g₀ s k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact hC S

theorem hs_le_jet
    (g₀ : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := mode_le_jet (I := I) (M := M) g₀ s 0
  obtain ⟨Cₙ, hCₙ_nn, hCₙ⟩ := mode_le_jet (I := I) (M := M) g₀ s n
  set F : ℝ := (2 : ℝ) ^ (n - 1) with hF_def
  have hF_nn : 0 ≤ F := by rw [hF_def]; positivity
  have hcoef_nn : 0 ≤ F * (C₀ + Cₙ) :=
    mul_nonneg hF_nn (add_nonneg hC₀_nn hCₙ_nn)
  refine ⟨Real.sqrt (F * (C₀ + Cₙ)), Real.sqrt_nonneg _, fun S => ?_⟩
  set Sall : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ with hSall_def
  have hSall_nn : 0 ≤ Sall := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set term : ℕ →
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s → ℝ := fun j m =>
    (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) m) ^ j *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
        (SmoothCcTensor.toL2 S) m) ^ 2 with hterm_def
  set mass : ℕ → ℝ := fun j => ∑' m, term j m with hmass_def
  have hterm_sum (j : ℕ) : Summable (term j) := by
    simpa only [hterm_def] using mode_summable (I := I) (M := M) g₀ s j S
  have hsum₀ : ∑ a ∈ Finset.range (0 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤ Sall := by
    rw [hSall_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
    exact Finset.range_mono (by omega)
  have hsum₀_nn : 0 ≤ ∑ a ∈ Finset.range (0 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmass₀ : mass 0 ≤ C₀ * Sall ^ 2 := by
    have hbase := hC₀ S
    have hsq : (∑ a ∈ Finset.range (0 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 ≤ Sall ^ 2 :=
      pow_le_pow_left₀ hsum₀_nn hsum₀ 2
    refine (show mass 0 ≤ C₀ * (∑ a ∈ Finset.range (0 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 from ?_).trans ?_
    · simpa only [hmass_def, hterm_def] using hbase
    · exact mul_le_mul_of_nonneg_left hsq hC₀_nn
  have hmassₙ : mass n ≤ Cₙ * Sall ^ 2 := by
    simpa only [hmass_def, hterm_def, hSall_def] using hCₙ S
  have hmass : mass 0 + mass n ≤ (C₀ + Cₙ) * Sall ^ 2 := by
    calc mass 0 + mass n ≤ C₀ * Sall ^ 2 + Cₙ * Sall ^ 2 :=
        add_le_add hmass₀ hmassₙ
      _ = (C₀ + Cₙ) * Sall ^ 2 := by ring
  have hrhs_sum : Summable (fun m => F * (term 0 m + term n m)) :=
    (hterm_sum 0).add (hterm_sum n) |>.mul_left F
  have hsq_le :
      ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ^ 2 ≤
        F * (C₀ + Cₙ) * Sall ^ 2 := by
    rw [ccToHs_norm_sq]
    calc
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        tensorSobolevWeight (I := I) (M := M) m (n : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 S) m) ^ 2
          ≤ ∑' m, F * (term 0 m + term n m) := by
            refine Summable.tsum_le_tsum (fun m => ?_)
              (ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S).weighted_summable
              hrhs_sum
            set L : ℝ :=
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m with hL_def
            set c : ℝ := tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
              (SmoothCcTensor.toL2 S) m with hc_def
            have hL_nn : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) m
            have hpow : (1 + L) ^ n ≤ F * (1 ^ n + L ^ n) := by
              rw [hF_def]
              exact add_pow_le (by norm_num) hL_nn n
            have hc_nn : 0 ≤ c ^ 2 := sq_nonneg c
            have hweight : tensorSobolevWeight (I := I) (M := M) m (n : ℝ) =
                (1 + L) ^ n := by
              unfold tensorSobolevWeight
              rw [Real.rpow_natCast, hL_def]
            rw [hweight]
            calc (1 + L) ^ n * c ^ 2 ≤ (F * (1 ^ n + L ^ n)) * c ^ 2 :=
                mul_le_mul_of_nonneg_right hpow hc_nn
              _ = F * (term 0 m + term n m) := by
                rw [hterm_def, hL_def, hc_def]
                ring
      _ = F * (mass 0 + mass n) := by
          rw [tsum_mul_left, Summable.tsum_add (hterm_sum 0) (hterm_sum n)]
      _ ≤ F * ((C₀ + Cₙ) * Sall ^ 2) :=
          mul_le_mul_of_nonneg_left hmass hF_nn
      _ = F * (C₀ + Cₙ) * Sall ^ 2 := by ring
  have hrhs_nn : 0 ≤ Real.sqrt (F * (C₀ + Cₙ)) * Sall :=
    mul_nonneg (Real.sqrt_nonneg _) hSall_nn
  have hsqrt_sq : (Real.sqrt (F * (C₀ + Cₙ)) * Sall) ^ 2 =
      F * (C₀ + Cₙ) * Sall ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcoef_nn]
  have hnorm_nn : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ :=
    norm_nonneg _
  have hsquare : ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ^ 2 ≤
      (Real.sqrt (F * (C₀ + Cₙ)) * Sall) ^ 2 := by
    rw [hsqrt_sq]
    exact hsq_le
  have hsqrt := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_sq hnorm_nn, Real.sqrt_sq hrhs_nn] at hsqrt
  simpa only [hSall_def] using hsqrt

theorem ccGrad_le
    (g₀ : SmoothRiemannianMetric I M) (s j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖ccTensorToHs (I := I) (M := M) g₀ (s + j) (k : ℝ)
            (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((k + j : ℕ) : ℝ) S‖ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := hs_le_jet (I := I) (M := M) g₀ (s + j) k
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := hsJet_le (I := I) (M := M) g₀ s (k + j)
  refine ⟨C₁ * (((k + 1 : ℕ) : ℝ) * C₂), by positivity, fun S => ?_⟩
  set Full : ℝ := ∑ b ∈ Finset.range (k + j + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFull_def
  have hFull_nn : 0 ≤ Full := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hterm : ∀ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) a
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ≤ Full := by
    intro a ha
    rw [icg_comp_norm (I := I) (M := M) g₀ s j a S, hFull_def]
    refine Finset.single_le_sum
      (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 s b S‖)
      (fun _ _ => norm_nonneg _) ?_
    rw [Finset.mem_range] at ha ⊢
    omega
  have hshift : ∑ a ∈ Finset.range (k + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + j) a
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ≤
      ((k + 1 : ℕ) : ℝ) * Full := by
    calc ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (s + j) a
            (iteratedCovGrad (I := I) g₀ 0 s j S)‖
        ≤ ∑ _a ∈ Finset.range (k + 1), Full := Finset.sum_le_sum hterm
      _ = ((k + 1 : ℕ) : ℝ) * Full := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have houter := hC₁ (iteratedCovGrad (I := I) g₀ 0 s j S)
  have hfull : Full ≤ C₂ *
      ‖ccTensorToHs (I := I) (M := M) g₀ s ((k + j : ℕ) : ℝ) S‖ := by
    rw [hFull_def]
    exact hC₂ S
  calc
    ‖ccTensorToHs (I := I) (M := M) g₀ (s + j) (k : ℝ)
        (iteratedCovGrad (I := I) g₀ 0 s j S)‖
      ≤ C₁ * ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (s + j) a
            (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := houter
    _ ≤ C₁ * (((k + 1 : ℕ) : ℝ) * Full) :=
      mul_le_mul_of_nonneg_left hshift hC₁_nn
    _ ≤ C₁ * (((k + 1 : ℕ) : ℝ) *
        (C₂ * ‖ccTensorToHs (I := I) (M := M) g₀ s ((k + j : ℕ) : ℝ) S‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₁_nn
      exact mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = (C₁ * (((k + 1 : ℕ) : ℝ) * C₂)) *
        ‖ccTensorToHs (I := I) (M := M) g₀ s ((k + j : ℕ) : ℝ) S‖ := by ring

theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ := by
  obtain ⟨C, hC_nn, hC⟩ := hsJet_le (I := I) (M := M) g₀ 2 n
  refine ⟨C, hC_nn, fun S => ?_⟩
  have heq : ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S :=
    tensorHs.ext (funext (fun _ => rfl))
  rw [← heq]
  exact hC S

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
