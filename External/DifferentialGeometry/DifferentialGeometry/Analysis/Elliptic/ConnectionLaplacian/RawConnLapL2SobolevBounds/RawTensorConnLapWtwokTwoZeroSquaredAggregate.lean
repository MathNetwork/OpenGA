import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.TensorSectionL2WtwokTwoZeroBound
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.TensorChartTwistUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sq_eLpNorm_two_eq_lintegral_ofReal_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  classical
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
    rw [show ((f x) ^ 2 : ℝ) = ‖f x‖ ^ 2 from by
      rw [Real.norm_eq_abs, sq_abs]]
    rw [← ofReal_norm_eq_enorm]
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

private lemma ennreal_sq_finset_sum_le_card_mul_finset_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  by_cases h_top : ∃ j ∈ s, f j = ⊤
  · obtain ⟨j, hj, hj_top⟩ := h_top
    have h_sum_top : ∑ i ∈ s, f i = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨j, hj, hj_top⟩
    rw [h_sum_top]
    rw [show ((⊤ : ℝ≥0∞)) ^ 2 = ⊤ from by
      rw [sq]; exact ENNReal.top_mul_top]
    by_cases hs : s.card = 0
    · rw [Finset.card_eq_zero] at hs
      subst hs
      simp at hj
    · have h_card_pos : 0 < s.card := Nat.pos_of_ne_zero hs
      have h_card_ne : ((s.card : ℝ≥0∞)) ≠ 0 := by
        rw [Ne, Nat.cast_eq_zero]; exact hs
      have h_sum_sq_top : ∑ i ∈ s, (f i) ^ 2 = ⊤ := by
        rw [ENNReal.sum_eq_top]
        refine ⟨j, hj, ?_⟩
        rw [hj_top]
        rw [show ((⊤ : ℝ≥0∞)) ^ 2 = ⊤ from by rw [sq]; exact ENNReal.top_mul_top]
      rw [h_sum_sq_top]
      rw [ENNReal.mul_top h_card_ne]
  · have hf_ne_top : ∀ i ∈ s, f i ≠ ⊤ := by
      intro i hi h_eq_top
      exact h_top ⟨i, hi, h_eq_top⟩
    have h_sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ := by
      intro h_sum_top
      rw [ENNReal.sum_eq_top] at h_sum_top
      obtain ⟨i, hi, h_eq_top⟩ := h_sum_top
      exact hf_ne_top i hi h_eq_top
    have hf_sq_ne_top : ∀ i ∈ s, (f i) ^ 2 ≠ ⊤ := by
      intro i hi
      rw [sq]
      exact ENNReal.mul_ne_top (hf_ne_top i hi) (hf_ne_top i hi)
    have h_sum_sq_ne_top : ∑ i ∈ s, (f i) ^ 2 ≠ ⊤ := by
      intro h_eq_top
      rw [ENNReal.sum_eq_top] at h_eq_top
      obtain ⟨i, hi, h_top⟩ := h_eq_top
      exact hf_sq_ne_top i hi h_top
    set a : ι → ℝ := fun i => (f i).toReal with ha_def
    have ha_nn : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
    have hfi_eq : ∀ i ∈ s, f i = ENNReal.ofReal (a i) := by
      intro i hi
      rw [ha_def]
      exact (ENNReal.ofReal_toReal (hf_ne_top i hi)).symm
    have h_sum_eq : ∑ i ∈ s, f i = ENNReal.ofReal (∑ i ∈ s, a i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha_nn i)]
      exact Finset.sum_congr rfl hfi_eq
    have hfsq_eq : ∀ i ∈ s, (f i) ^ 2 = ENNReal.ofReal ((a i) ^ 2) := by
      intro i hi
      rw [hfi_eq i hi]
      rw [← ENNReal.ofReal_pow (ha_nn i) 2]
    have h_sumsq_eq : ∑ i ∈ s, (f i) ^ 2 = ENNReal.ofReal (∑ i ∈ s, (a i) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
      exact Finset.sum_congr rfl hfsq_eq
    rw [h_sum_eq]
    rw [← ENNReal.ofReal_pow (Finset.sum_nonneg (fun i _ => ha_nn i)) 2]
    rw [h_sumsq_eq]
    have h_card_eq :
        (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    rw [h_card_eq]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h_double_sum : ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
        2 * ((s.card : ℝ) * (∑ i ∈ s, (a i) ^ 2) -
              (∑ i ∈ s, a i) ^ 2) := by
      classical
      set S₀ : ℝ := ∑ i ∈ s, a i with hS₀_def
      set Q₀ : ℝ := ∑ i ∈ s, (a i) ^ 2 with hQ₀_def
      have h_inner : ∀ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
          (s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀ := by
        intro i _
        have hexp : ∀ j, (a i - a j) ^ 2 =
            (a i) ^ 2 - 2 * (a i) * (a j) + (a j) ^ 2 := by
          intro j; ring
        calc ∑ j ∈ s, (a i - a j) ^ 2
            = ∑ j ∈ s, ((a i) ^ 2 - 2 * (a i) * (a j) + (a j) ^ 2) :=
              Finset.sum_congr rfl (fun j _ => hexp j)
          _ = (∑ _j ∈ s, (a i) ^ 2) - (∑ j ∈ s, 2 * (a i) * (a j))
              + (∑ j ∈ s, (a j) ^ 2) := by
                rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          _ = (s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀ := by
                rw [Finset.sum_const]
                rw [show (∑ j ∈ s, 2 * (a i) * (a j)) = 2 * (a i) * S₀ from by
                  rw [show (fun j => 2 * (a i) * (a j)) =
                    (fun j => (2 * (a i)) * (a j)) from by funext j; ring]
                  rw [← Finset.mul_sum, ← hS₀_def]]
                rw [← hQ₀_def, nsmul_eq_mul]
      calc ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2
          = ∑ i ∈ s, ((s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀) :=
            Finset.sum_congr rfl h_inner
        _ = (∑ i ∈ s, (s.card : ℝ) * (a i) ^ 2)
            - (∑ i ∈ s, 2 * (a i) * S₀) + (∑ i ∈ s, Q₀) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ = (s.card : ℝ) * Q₀ - 2 * S₀ * S₀ + (s.card : ℝ) * Q₀ := by
              rw [show (∑ i ∈ s, (s.card : ℝ) * (a i) ^ 2) =
                  (s.card : ℝ) * Q₀ from by
                rw [← Finset.mul_sum, ← hQ₀_def]]
              rw [show (∑ i ∈ s, 2 * (a i) * S₀) = 2 * S₀ * S₀ from by
                rw [show (fun i => 2 * (a i) * S₀) =
                  (fun i => (2 * S₀) * (a i)) from by funext i; ring]
                rw [← Finset.mul_sum, ← hS₀_def]]
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = 2 * ((s.card : ℝ) * Q₀ - S₀ ^ 2) := by ring
    have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [h_double_sum] at h_nn
    nlinarith

end Connection
end Integral
end DifferentialGeometry

end
