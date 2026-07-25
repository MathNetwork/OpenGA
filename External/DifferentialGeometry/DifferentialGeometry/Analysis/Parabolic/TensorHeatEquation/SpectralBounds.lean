import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private noncomputable def tensorHeatPowerCoeffBound (k : ℕ) (t : ℝ) : ℝ :=
  (k / t : ℝ) ^ k * Real.exp (-(k : ℝ))

private lemma tensorHeatPowerCoeffBound_nonneg (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ tensorHeatPowerCoeffBound k t := by
  unfold tensorHeatPowerCoeffBound
  apply mul_nonneg
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) ht.le) k
  · exact (Real.exp_pos _).le

private lemma tensor_lambda_pow_mul_exp_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam ^ k * Real.exp (-(lam * t)) ≤ tensorHeatPowerCoeffBound k t := by
  unfold tensorHeatPowerCoeffBound
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, Real.exp_zero,
      mul_one]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ lam * t := mul_nonneg hlam ht.le
    linarith
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have h_tk_pos : (0 : ℝ) < t / k := div_pos ht hk_real_pos
  have h_aux : lam * Real.exp (-((t / (k : ℝ)) * lam)) ≤
      (k / t : ℝ) * Real.exp (-1) := by
    set s : ℝ := (t / k : ℝ) * lam with hs_def
    have hs_nn : 0 ≤ s := mul_nonneg h_tk_pos.le hlam
    have hs_bound : s * Real.exp (-s) ≤ Real.exp (-1) := by
      have h1 : s ≤ Real.exp (s - 1) := by
        have h := Real.add_one_le_exp (s - 1)
        linarith
      have hexp_pos : 0 < Real.exp (-s) := Real.exp_pos _
      have h_mul : s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right h1 hexp_pos.le
      rw [← Real.exp_add] at h_mul
      have h_sum : s - 1 + -s = -1 := by ring
      rw [h_sum] at h_mul
      exact h_mul
    have h_lam_eq : lam = (k / t : ℝ) * s := by
      simp only [hs_def]
      have ht_ne : (t : ℝ) ≠ 0 := ht.ne'
      have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
      field_simp
    have h_arg_eq : -((t / k : ℝ) * lam) = -s := by
      simp only [hs_def]
    rw [h_arg_eq, h_lam_eq]
    have h_kt_nn : 0 ≤ (k / t : ℝ) := div_nonneg hk_real_pos.le ht.le
    calc (k / t : ℝ) * s * Real.exp (-s)
        = (k / t : ℝ) * (s * Real.exp (-s)) := by ring
      _ ≤ (k / t : ℝ) * Real.exp (-1) :=
            mul_le_mul_of_nonneg_left hs_bound h_kt_nn
  have h_lhs_nn : 0 ≤ lam * Real.exp (-((t / (k : ℝ)) * lam)) :=
    mul_nonneg hlam (Real.exp_pos _).le
  have h_pow_le : (lam * Real.exp (-((t / (k : ℝ)) * lam))) ^ k ≤
      ((k / t : ℝ) * Real.exp (-1)) ^ k :=
    pow_le_pow_left₀ h_lhs_nn h_aux k
  have h_lhs_eq : (lam * Real.exp (-((t / (k : ℝ)) * lam))) ^ k =
      lam ^ k * Real.exp (-(lam * t)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have h_arg : (k : ℝ) * -((t / (k : ℝ)) * lam) = -(lam * t) := by
      have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
      field_simp
    rw [h_arg]
  have h_rhs_eq : ((k / t : ℝ) * Real.exp (-1)) ^ k =
      (k / t : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  rw [h_lhs_eq] at h_pow_le
  rw [h_rhs_eq] at h_pow_le
  exact h_pow_le

private lemma tensor_lambda_pow_mul_exp_sq_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    (lam ^ k * Real.exp (-(lam * t))) ^ 2 ≤
      (tensorHeatPowerCoeffBound k t) ^ 2 := by
  have h_lhs_nn : 0 ≤ lam ^ k * Real.exp (-(lam * t)) :=
    mul_nonneg (pow_nonneg hlam k) (Real.exp_pos _).le
  have h_le : lam ^ k * Real.exp (-(lam * t)) ≤
      tensorHeatPowerCoeffBound k t :=
    tensor_lambda_pow_mul_exp_le k ht hlam
  exact pow_le_pow_left₀ h_lhs_nn h_le 2

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
