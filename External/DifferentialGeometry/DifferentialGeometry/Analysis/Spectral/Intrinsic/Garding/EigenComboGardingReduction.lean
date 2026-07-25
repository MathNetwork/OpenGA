import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M)

open scoped Classical in

theorem finiteEigenCombo_iterRawConnLap_l2NormSq_le_spectral
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    {j k : ℕ} (hjk : j ≤ k) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ^ 2 ≤
      ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ ^ 2 := by
  classical
  rw [finiteEigenCombo_iterRawConnLap_l2NormSq (I := I) (M := M) g F c j,
    finiteEigenCombo_spectral_normSq (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    tensor_lambda_nonneg (I := I) (M := M) i
  have h_one_le : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    linarith
  have h_base_le : TensorEigenIdx.lambda (I := I) (M := M) i ≤
      1 + TensorEigenIdx.lambda (I := I) (M := M) i := by linarith
  have h1 : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) :=
    pow_le_pow_left₀ hlam_nn h_base_le (2 * j)
  have h2 : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) :=
    pow_le_pow_right₀ h_one_le (Nat.mul_le_mul_left 2 hjk)
  have h_lam_le : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) :=
    le_trans h1 h2
  have h_rpow_eq : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
    rw [Real.rpow_natCast]
  rw [h_rpow_eq]
  exact mul_le_mul_of_nonneg_right h_lam_le (sq_nonneg (c i))

theorem finiteEigenCombo_iterRawConnLap_l2Norm_le_spectral
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    {j k : ℕ} (hjk : j ≤ k) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ≤
      ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ := by
  have h_sq := finiteEigenCombo_iterRawConnLap_l2NormSq_le_spectral
    (I := I) (M := M) g F c hjk
  exact le_of_sq_le_sq h_sq (norm_nonneg _)

open scoped Classical in

theorem eigenSpan_pouHs_le_spectral_of_elliptic
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (k : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (h_elliptic :
      (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
        C * ∑ j ∈ Finset.range (k + 1),
          ‖SmoothCcTensor.toL2
            (rawTensorConnLapIter (I := I) g 0 2 j
              (finiteEigenCombo (I := I) (M := M) g F c))‖) :
    (tensorPouSobolevHsNorm (I := I) (M := M) g k
        (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
      (C * (k + 1)) * ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ := by
  classical
  set Nspec : ℝ := ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have h_term : ∀ j ∈ Finset.range (k + 1),
      ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ≤ Nspec := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact finiteEigenCombo_iterRawConnLap_l2Norm_le_spectral
      (I := I) (M := M) g F c hjk
  have h_sum_le :
      ∑ j ∈ Finset.range (k + 1),
        ‖SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g 0 2 j
            (finiteEigenCombo (I := I) (M := M) g F c))‖ ≤
      (k + 1 : ℝ) * Nspec := by
    calc ∑ j ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2
              (rawTensorConnLapIter (I := I) g 0 2 j
                (finiteEigenCombo (I := I) (M := M) g F c))‖
        ≤ ∑ _j ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum h_term
      _ = (Finset.range (k + 1)).card • Nspec := by rw [Finset.sum_const]
      _ = (k + 1 : ℝ) * Nspec := by
            rw [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (finiteEigenCombo (I := I) (M := M) g F c)).toReal
      ≤ C * ∑ j ∈ Finset.range (k + 1),
          ‖SmoothCcTensor.toL2
            (rawTensorConnLapIter (I := I) g 0 2 j
              (finiteEigenCombo (I := I) (M := M) g F c))‖ := h_elliptic
    _ ≤ C * ((k + 1 : ℝ) * Nspec) := by
          exact mul_le_mul_of_nonneg_left h_sum_le hC
    _ = (C * (k + 1)) * Nspec := by ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem finiteEigenComboHs_norm_eq_sqrt_spectral
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (k : ℕ) :
    ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ =
      Real.sqrt
        (∑ i ∈ F,
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
            (c i) ^ 2) := by
  have h_sq := finiteEigenCombo_spectral_normSq (I := I) (M := M) g F c
    ((2 * k : ℕ) : ℝ)
  rw [← h_sq, Real.sqrt_sq (norm_nonneg _)]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
