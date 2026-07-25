import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SpectralBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

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

private noncomputable def tensorHeatPowerCoeffBoundCalc (k : ℕ) (t : ℝ) : ℝ :=
  (k / t : ℝ) ^ k * Real.exp (-(k : ℝ))

private lemma tensorHeatPowerCoeffBoundCalc_nonneg (k : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ tensorHeatPowerCoeffBoundCalc k t := by
  unfold tensorHeatPowerCoeffBoundCalc
  apply mul_nonneg
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) ht.le) k
  · exact (Real.exp_pos _).le

private lemma tensor_lambda_pow_mul_exp_le_calc
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam ^ k * Real.exp (-(lam * t)) ≤ tensorHeatPowerCoeffBoundCalc k t := by
  unfold tensorHeatPowerCoeffBoundCalc
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

private lemma tensor_exp_neg_taylor_bound
    (k : ℕ) {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : |h| ≤ t / 2)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    |lam ^ k * (Real.exp (-(lam * (t + h))) - Real.exp (-(lam * t)) +
        lam * h * Real.exp (-(lam * t)))| ≤
      tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) * h ^ 2 := by
  have h_factor :
      Real.exp (-(lam * (t + h))) - Real.exp (-(lam * t)) +
          lam * h * Real.exp (-(lam * t)) =
        Real.exp (-(lam * t)) *
          (Real.exp (-(lam * h)) - 1 - (-(lam * h))) := by
    rw [show -(lam * (t + h)) = -(lam * t) + -(lam * h) from by ring,
      Real.exp_add]
    ring
  rw [h_factor]
  have h_taylor : ∀ s : ℝ, |Real.exp s - 1 - s| ≤ s ^ 2 * Real.exp |s| := by
    intro s
    have hc :=
      Complex.norm_exp_sub_sum_le_norm_mul_exp (s : ℂ) 2
    have h_sum : ∑ m ∈ Finset.range 2, (s : ℂ) ^ m / (m.factorial : ℂ) =
        1 + (s : ℂ) := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [h_sum] at hc
    have hc' : ‖Complex.exp (s : ℂ) - (1 + (s : ℂ))‖ ≤
        ‖(s : ℂ)‖ ^ 2 * Real.exp ‖(s : ℂ)‖ := hc
    have h_eq : Complex.exp (s : ℂ) - (1 + (s : ℂ)) =
        ((Real.exp s - 1 - s : ℝ) : ℂ) := by
      have h_exp_real : Complex.exp (s : ℂ) = ((Real.exp s : ℝ) : ℂ) :=
        (Complex.ofReal_exp s).symm
      rw [h_exp_real]
      push_cast
      ring
    rw [h_eq] at hc'
    have h_lhs_norm : ‖((Real.exp s - 1 - s : ℝ) : ℂ)‖ =
        |Real.exp s - 1 - s| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h_lhs_norm] at hc'
    have h_rhs_norm : ‖(s : ℂ)‖ = |s| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h_rhs_norm] at hc'
    convert hc' using 1
    rw [sq_abs]
  have h_step1 :
      |Real.exp (-(lam * h)) - 1 - (-(lam * h))| ≤
        (-(lam * h)) ^ 2 * Real.exp |-(lam * h)| :=
    h_taylor (-(lam * h))
  have h_neg_sq : (-(lam * h)) ^ 2 = (lam * h) ^ 2 := by ring
  have h_neg_abs : |-(lam * h)| = |lam * h| := abs_neg _
  have h_lam_h_abs : |lam * h| = lam * |h| := by
    rw [abs_mul, abs_of_nonneg hlam]
  rw [h_neg_sq, h_neg_abs, h_lam_h_abs] at h_step1
  have h_exp_t_pos : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
  rw [show lam ^ k * (Real.exp (-(lam * t)) *
      (Real.exp (-(lam * h)) - 1 - (-(lam * h)))) =
      Real.exp (-(lam * t)) *
      (lam ^ k * (Real.exp (-(lam * h)) - 1 - (-(lam * h)))) from by ring]
  rw [abs_mul]
  rw [abs_of_pos h_exp_t_pos]
  rw [abs_mul]
  rw [show |lam ^ k| = lam ^ k from abs_of_nonneg (pow_nonneg hlam k)]
  have h_step2 :
      Real.exp (-(lam * t)) *
        (lam ^ k * |Real.exp (-(lam * h)) - 1 - (-(lam * h))|) ≤
      Real.exp (-(lam * t)) *
        (lam ^ k * ((lam * h) ^ 2 * Real.exp (lam * |h|))) := by
    apply mul_le_mul_of_nonneg_left _ h_exp_t_pos.le
    apply mul_le_mul_of_nonneg_left h_step1 (pow_nonneg hlam k)
  refine le_trans h_step2 ?_
  have h_t_minus_h_pos : 0 < t - |h| := by
    have ht_half_pos : 0 < t / 2 := by linarith
    have : |h| ≤ t / 2 := hh
    linarith
  have h_t_minus_h_ge : t / 2 ≤ t - |h| := by linarith
  have h_combine : Real.exp (-(lam * t)) *
      (lam ^ k * ((lam * h) ^ 2 * Real.exp (lam * |h|))) =
      lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) := by
    rw [show -(lam * (t - |h|)) = -(lam * t) + lam * |h| from by ring]
    rw [Real.exp_add]
    rw [show (lam * h) ^ 2 = lam ^ 2 * h ^ 2 from by ring]
    rw [pow_add]
    ring
  rw [h_combine]
  have h_lam_pow_exp_le :
      lam ^ (k + 2) * Real.exp (-(lam * (t - |h|))) ≤
        lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
    apply Real.exp_le_exp.mpr
    have : -(lam * (t - |h|)) ≤ -(lam * (t / 2)) := by
      have hlt : lam * (t / 2) ≤ lam * (t - |h|) :=
        mul_le_mul_of_nonneg_left h_t_minus_h_ge hlam
      linarith
    exact this
  have h_h_sq_nn : 0 ≤ h ^ 2 := sq_nonneg _
  have h_step3 : lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) ≤
      lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) * h ^ 2 := by
    have hp : lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) =
        lam ^ (k + 2) * Real.exp (-(lam * (t - |h|))) * h ^ 2 := by ring
    rw [hp]
    exact mul_le_mul_of_nonneg_right h_lam_pow_exp_le h_h_sq_nn
  refine le_trans h_step3 ?_
  have h_t2_pos : 0 < t / 2 := by linarith
  have h_final :
      lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) ≤
        tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) :=
    tensor_lambda_pow_mul_exp_le_calc (k + 2) h_t2_pos hlam
  exact mul_le_mul_of_nonneg_right h_final h_h_sq_nn

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
