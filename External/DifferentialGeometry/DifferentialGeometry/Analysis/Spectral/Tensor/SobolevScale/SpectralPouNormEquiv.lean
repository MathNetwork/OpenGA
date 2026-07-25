import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Order2SpectralIterateEquiv

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def ccSpectralEmbed (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    tensorHs (I := I) (M := M) g 0 2 σ where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g σ T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)

@[simp] theorem ccSpectralEmbed_coeff (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (ccSpectralEmbed (I := I) (M := M) g σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 T) i :=
  rfl

theorem ccSpectralEmbed_norm_sq_eq_tsum (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g σ T‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 T) i) ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)
    (ccSpectralEmbed (I := I) (M := M) g σ T)]
  exact tsum_congr (fun i => by rw [ccSpectralEmbed_coeff])

theorem ccSpectralEmbed_norm_mono (g : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (T : SmoothCcTensor g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g σ T‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g τ T‖ := by
  have hnn_τ : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g τ T‖ := norm_nonneg _
  have hsq : ‖ccSpectralEmbed (I := I) (M := M) g σ T‖ ^ 2 ≤
      ‖ccSpectralEmbed (I := I) (M := M) g τ T‖ ^ 2 := by
    rw [ccSpectralEmbed_norm_sq_eq_tsum, ccSpectralEmbed_norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro i
      have hbase : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        one_le_one_add_lambda (I := I) (M := M) i
      have hw : tensorSobolevWeight (I := I) (M := M) i σ ≤
          tensorSobolevWeight (I := I) (M := M) i τ := by
        unfold tensorSobolevWeight
        exact Real.rpow_le_rpow_of_exponent_le hbase hστ
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    · exact (ccSpectralEmbed (I := I) (M := M) g σ T).weighted_summable
    · exact (ccSpectralEmbed (I := I) (M := M) g τ T).weighted_summable
  exact le_of_sq_le_sq hsq hnn_τ

theorem ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g ((2 * k : ℕ) : ℝ) T‖ ^ 2 =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)‖ ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2
    with hcompact_def
  rw [ccSpectralEmbed_norm_sq_eq_tsum]
  have h_term :
      (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 T) i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2
            (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i) ^ 2 := by
    funext i
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
      (I := I) (M := M) g h_compact T i k]
    rw [mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [h_term]
  exact tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))

theorem tensorL2Coeff_ofCompact_rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2) (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i := by
  have hraw_eq : rawTensorConnLapSmooth (I := I) g 0 2 T =
      T - oneMinusConnLapSmooth (I := I) g 0 2 T := by
    rw [show oneMinusConnLapSmooth (I := I) g 0 2 T =
        T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl]
    abel
  rw [hraw_eq, map_sub, sub_eq_add_neg,
    show (- SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T)) =
      (-1 : ℝ) • SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T) by
      rw [neg_one_smul],
    tensorL2Coeff_add, tensorL2Coeff_smul,
    tensorL2Coeff_ofCompact_oneMinusConnLapSmooth (I := I) (M := M) g h_compact T i]
  ring

theorem tensorL2Coeff_ofCompact_rawTensorConnLapIter
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2) (i : TensorEigenIdx (I := I) (M := M) g 0 2) (j : ℕ) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rawTensorConnLapIter_succ,
        tensorL2Coeff_ofCompact_rawTensorConnLapSmooth
          (I := I) (M := M) g h_compact (rawTensorConnLapIter (I := I) g 0 2 j T) i,
        ih, pow_succ]
      ring

theorem rawConnLapIter_l2_le_ccSpectralEmbed_even
    (g : SmoothRiemannianMetric I M) (j : ℕ) (T : SmoothCcTensor g 0 2) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2
    with hcompact_def
  have hnn : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ :=
    norm_nonneg _
  have hsq :
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ^ 2 ≤
        ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ ^ 2 := by
    rw [ccSpectralEmbed_norm_sq_eq_tsum,
      ← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T))]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro i
      rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g h_compact T i j]
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i with hc_def
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) i ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) i := by linarith
      have hlhs_eq : ((- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j * c) ^ 2 =
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * c ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm j 2,
          (even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]
      rw [hlhs_eq]
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) i ((2 * j : ℕ) : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      have hpow_le : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) :=
        pow_le_pow_left₀ hbase_nn hbase_le (2 * j)
      exact mul_le_mul_of_nonneg_right hpow_le (sq_nonneg c)
    · exact tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T))
    · exact (ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T).weighted_summable
  exact le_of_sq_le_sq hsq hnn

theorem tensorPouSobolevHsNorm_le_ccSpectralEmbed (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * ‖ccSpectralEmbed (I := I) (M := M) g ((2 * k : ℕ) : ℝ) T‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hGarding⟩ :=
    DifferentialGeometry.Integral.Connection.exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
      (I := I) (M := M) g 2 k
  refine ⟨Cg * (k + 1), by positivity, fun T => ?_⟩
  set Nspec : ℝ := ‖ccSpectralEmbed (I := I) (M := M) g ((2 * k : ℕ) : ℝ) T‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hterm : ∀ j ∈ Finset.range (k + 1),
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤ Nspec := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ :=
      rawConnLapIter_l2_le_ccSpectralEmbed_even (I := I) (M := M) g j T
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ ≤ Nspec := by
      rw [hNspec_def]
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g ?_ T
      have : (2 * j : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  have hsum_le :
      ∑ j ∈ Finset.range (k + 1),
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
      (k + 1 : ℝ) * Nspec := by
    calc ∑ j ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖
        ≤ ∑ _j ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hterm
      _ = (k + 1 : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
      ≤ Cg * ∑ j ∈ Finset.range (k + 1),
          ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := hGarding T
    _ ≤ Cg * ((k + 1 : ℝ) * Nspec) := mul_le_mul_of_nonneg_left hsum_le hCg_nn
    _ = (Cg * (k + 1)) * Nspec := by ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
