import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Basic








noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma four_right {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (A B : Fin n → Fin n → Fin n → ℝ)
    (hfs : ∀ a b, f a b = f b a) (hAs : ∀ a b k, A a b k = A b a k)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      ig b2 b3 * B b2 b3 b0 * (A b0 i b1 * f b1 j)) =
      ∑ a, ∑ b, ∑ c, ∑ d, f j a * A i b a * B c d b * ig c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hAs b i a, hfs a j]
  ring

private lemma four_left {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (A B : Fin n → Fin n → Fin n → ℝ)
    (hAs : ∀ a b k, A a b k = A b a k) (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      ig b2 b3 * B b2 b3 b0 * (A b0 j b1 * f i b1)) =
      ∑ a, ∑ b, ∑ c, ∑ d, f i a * A j b a * B c d b * ig c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hAs b j a]
  ring


theorem nf_p4 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (hfs : ∀ a b, f a b = f b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k) (i j : Fin n) :
    p4B ig ga1 ga0 gbg f i j =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d)
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d) := by
  have h1 : p4B ig ga1 ga0 gbg f i j =
      -((∑ b0, ∑ b1, ∑ b2, ∑ b3,
        ig b2 b3 * ga1 b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) -
        (∑ b0, ∑ b1, ∑ b2, ∑ b3,
          ig b2 b3 * gbg b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) -
        ((∑ b0, ∑ b1, ∑ b2, ∑ b3,
          ig b2 b3 * ga1 b2 b3 b0 * (ga0 b0 i b1 * f b1 j)) -
        (∑ b0, ∑ b1, ∑ b2, ∑ b3,
          ig b2 b3 * gbg b2 b3 b0 * (ga0 b0 i b1 * f b1 j)))) +
      (-((∑ b0, ∑ b1, ∑ b2, ∑ b3,
        ig b2 b3 * ga1 b2 b3 b0 * (ga1 b0 j b1 * f i b1)) -
        (∑ b0, ∑ b1, ∑ b2, ∑ b3,
          ig b2 b3 * gbg b2 b3 b0 * (ga1 b0 j b1 * f i b1)) -
        ((∑ b0, ∑ b1, ∑ b2, ∑ b3,
          ig b2 b3 * ga1 b2 b3 b0 * (ga0 b0 j b1 * f i b1)) -
        (∑ b0, ∑ b1, ∑ b2, ∑ b3,
          ig b2 b3 * gbg b2 b3 b0 * (ga0 b0 j b1 * f i b1))))) := by
    simp only [p4B]
    simp (config := { maxSteps := 10000000 }) only [Finset.sum_mul, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [h1,
    four_right ig f ga1 ga1 hfs hga1s i j,
    four_right ig f ga1 gbg hfs hga1s i j,
    four_right ig f ga0 ga1 hfs hga0s i j,
    four_right ig f ga0 gbg hfs hga0s i j,
    four_left ig f ga1 ga1 hga1s i j,
    four_left ig f ga1 gbg hga1s i j,
    four_left ig f ga0 ga1 hga0s i j,
    four_left ig f ga0 gbg hga0s i j]
  ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
