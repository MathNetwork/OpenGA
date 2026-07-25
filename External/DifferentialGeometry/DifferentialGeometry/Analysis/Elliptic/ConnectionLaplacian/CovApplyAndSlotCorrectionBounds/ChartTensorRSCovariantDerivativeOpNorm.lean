import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSIntrinsicChartCLMOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotChristoffelCorrectionOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartLeviCivitaParallelCLMOpNorm

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma slot_factor_le_const_mul_one_plus_X
    {Φ_norm : ℝ}
    {C_LC X_b_norm : ℝ} (_hC_LC_nn : 0 ≤ C_LC) (hX_nn : 0 ≤ X_b_norm)
    (hΦ : Φ_norm ≤ C_LC * X_b_norm) :
    max Φ_norm 1 ≤ (max C_LC 1 + 1) * (1 + X_b_norm) := by
  have hmaxC_nn : 0 ≤ max C_LC 1 := le_trans zero_le_one (le_max_right _ _)
  have hmaxC_ge_one : (1 : ℝ) ≤ max C_LC 1 := le_max_right _ _
  have h_1X_nn : (0 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_1X_ge_one : (1 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_Φ_le_step :
      Φ_norm ≤ max C_LC 1 * (1 + X_b_norm) := by
    have h_a : C_LC * X_b_norm ≤ max C_LC 1 * X_b_norm :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX_nn
    have h_b : max C_LC 1 * X_b_norm ≤ max C_LC 1 * (1 + X_b_norm) := by
      have : X_b_norm ≤ 1 + X_b_norm := by linarith
      exact mul_le_mul_of_nonneg_left this hmaxC_nn
    linarith
  have h_one_le_step :
      (1 : ℝ) ≤ max C_LC 1 * (1 + X_b_norm) := by
    have h_a : (1 : ℝ) * 1 ≤ max C_LC 1 * (1 + X_b_norm) :=
      mul_le_mul hmaxC_ge_one h_1X_ge_one (by norm_num) hmaxC_nn
    linarith
  have h_max_step : max Φ_norm 1 ≤ max C_LC 1 * (1 + X_b_norm) :=
    max_le h_Φ_le_step h_one_le_step
  have h_expand : max C_LC 1 * (1 + X_b_norm) ≤
      (max C_LC 1 + 1) * (1 + X_b_norm) := by
    have h1 : max C_LC 1 ≤ max C_LC 1 + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h1 h_1X_nn
  linarith

private lemma slot_factor_pow_le_const_mul_one_plus_X_pow (n : ℕ)
    {Φ_norm : ℝ}
    {C_LC X_b_norm : ℝ} (hC_LC_nn : 0 ≤ C_LC) (hX_nn : 0 ≤ X_b_norm)
    (hΦ : Φ_norm ≤ C_LC * X_b_norm) :
    (max Φ_norm 1) ^ n ≤
      (max C_LC 1 + 1) ^ n * (1 + X_b_norm) ^ n := by
  have h_max_nn : 0 ≤ max Φ_norm 1 := le_trans zero_le_one (le_max_right _ _)
  have h_step :=
    slot_factor_le_const_mul_one_plus_X (Φ_norm := Φ_norm)
      (C_LC := C_LC) (X_b_norm := X_b_norm) hC_LC_nn hX_nn hΦ
  have h_pow :
      (max Φ_norm 1) ^ n ≤ ((max C_LC 1 + 1) * (1 + X_b_norm)) ^ n :=
    pow_le_pow_left₀ h_max_nn h_step n
  rw [mul_pow] at h_pow
  exact h_pow

private lemma one_plus_X_pow_le_max_pow
    {X_b_norm : ℝ} (hX_nn : 0 ≤ X_b_norm) {n N : ℕ} (hn : n ≤ N) :
    (1 + X_b_norm) ^ n ≤ (max (1 + X_b_norm) 1) ^ N := by
  have h_1X_nn : (0 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_1X_le_max : (1 + X_b_norm) ≤ max (1 + X_b_norm) 1 := le_max_left _ _
  have h_max_ge_one : (1 : ℝ) ≤ max (1 + X_b_norm) 1 := by
    have h_1X_ge_one : (1 : ℝ) ≤ 1 + X_b_norm := by linarith
    exact le_trans h_1X_ge_one h_1X_le_max
  have h_step1 :
      (1 + X_b_norm) ^ n ≤ (max (1 + X_b_norm) 1) ^ n :=
    pow_le_pow_left₀ h_1X_nn h_1X_le_max n
  have h_step2 :
      (max (1 + X_b_norm) 1) ^ n ≤ (max (1 + X_b_norm) 1) ^ N :=
    pow_le_pow_right₀ h_max_ge_one hn
  linarith

private lemma const_pow_le_max_pow
    {C_LC : ℝ} (_hC_LC_nn : 0 ≤ C_LC) {n N : ℕ} (hn : n ≤ N) :
    (max C_LC 1 + 1) ^ n ≤ (max C_LC 1 + 1) ^ N := by
  have h_one_le : (1 : ℝ) ≤ max C_LC 1 + 1 := by
    have : (1 : ℝ) ≤ max C_LC 1 := le_max_right _ _
    linarith
  exact pow_le_pow_right₀ h_one_le hn

end Connection
end Integral
end DifferentialGeometry

end
