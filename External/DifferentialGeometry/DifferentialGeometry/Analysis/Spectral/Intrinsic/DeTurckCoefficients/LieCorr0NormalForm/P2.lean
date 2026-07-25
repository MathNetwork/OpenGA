import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Basic








noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma p2_h1 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga1 : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga1 i j a * ga1 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  ring

private lemma p2_h2 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 : Fin n → Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga0 c d a * ga1 i j b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma p2_h3 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga0 i j a * ga1 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  ring

private lemma p2_h4 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga0 i j a * ga0 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  ring


theorem nf_p2 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 : Fin n → Fin n → Fin n → ℝ)
    (hfs : ∀ a b, f a b = f b a) (i j : Fin n) :
    p2B ig ga1 ga0 f i j =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga1 i j a * ga1 c d b * ig c d)) := by
  have h1 : p2B ig ga1 ga0 f i j =
      (∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) -
      (∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) -
      ((∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) -
      (∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1)))) := by
    simp only [p2B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul,
      mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h1, p2_h1 ig f ga1 hfs i j, p2_h2 ig f ga0 ga1 i j,
    p2_h3 ig f ga0 ga1 hfs i j, p2_h4 ig f ga0 hfs i j]
  ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
