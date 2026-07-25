import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Basic









noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma triple_right {n : ℕ} (f P : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (j : Fin n) :
    (∑ c, ∑ a, ∑ b, P a b * Q a b c * f c j) =
      ∑ a, ∑ b, ∑ c, P a b * f j c * Q a b c := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ (_ : _ ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  ring

private lemma triple_right_swap {n : ℕ} (f P : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (j : Fin n) :
    (∑ c, ∑ a, ∑ b, P a b * Q a b c * f c j) =
      ∑ a, ∑ b, ∑ c, Q a b c * f j c * P a b := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ (_ : _ ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  ring

private lemma triple_left {n : ℕ} (f P : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ c, ∑ a, ∑ b, P a b * Q a b c * f i c) =
      ∑ a, ∑ b, ∑ c, P a b * f i c * Q a b c := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ (_ : _ ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma triple_left_swap {n : ℕ} (f P : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ c, ∑ a, ∑ b, P a b * Q a b c * f i c) =
      ∑ a, ∑ b, ∑ c, Q a b c * f i c * P a b := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ (_ : _ ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma four_right {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (A B : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d, A i b a * (ig c d * B c d b) * f a j) =
      ∑ a, ∑ b, ∑ c, ∑ d, f j a * A i b a * B c d b * ig c d := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  ring

private lemma four_left {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (A B : Fin n → Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d, A j b a * (ig c d * B c d b) * f i a) =
      ∑ a, ∑ b, ∑ c, ∑ d, f i a * A j b a * B c d b * ig c d := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring


theorem nf_p1 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (dig ga0 ga1 : Fin n → Fin n → Fin n → ℝ)
    (dga0 dga1 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hfs : ∀ a b, f a b = f b a) (i j : Fin n) :
    p1B ig dig ga1 ga0 dga1 dga0 f i j =
      (∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga0 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga0 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d)) := by
  have h1 : p1B ig dig ga1 ga0 dga1 dga0 f i j =
      -((∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga1 b1 b2 b0 * f b0 j) -
        (∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga0 b1 b2 b0 * f b0 j) +
        ((∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga1 i b1 b2 b0 * f b0 j) -
          (∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga0 i b1 b2 b0 * f b0 j)) +
        ((∑ b0, ∑ b3, ∑ b4, ∑ b5,
          ga0 i b3 b0 * (ig b4 b5 * ga1 b4 b5 b3) * f b0 j) -
          (∑ b0, ∑ b3, ∑ b4, ∑ b5,
            ga0 i b3 b0 * (ig b4 b5 * ga0 b4 b5 b3) * f b0 j))) +
      (-((∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga1 b7 b8 b6 * f i b6) -
        (∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga0 b7 b8 b6 * f i b6) +
        ((∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga1 j b7 b8 b6 * f i b6) -
          (∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga0 j b7 b8 b6 * f i b6)) +
        ((∑ b6, ∑ b9, ∑ b10, ∑ b11,
          ga0 j b9 b6 * (ig b10 b11 * ga1 b10 b11 b9) * f i b6) -
          (∑ b6, ∑ b9, ∑ b10, ∑ b11,
            ga0 j b9 b6 * (ig b10 b11 * ga0 b10 b11 b9) * f i b6)))) := by
    simp only [p1B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul,
      add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    try ring
  rw [h1,
    triple_right f (fun a b => dig i a b) ga1 hfs j,
    triple_right f (fun a b => dig i a b) ga0 hfs j,
    triple_right_swap f ig (fun a b c => dga1 i a b c) hfs j,
    triple_right_swap f ig (fun a b c => dga0 i a b c) hfs j,
    four_right ig f ga0 ga1 hfs i j,
    four_right ig f ga0 ga0 hfs i j,
    triple_left f (fun a b => dig j a b) ga1 i,
    triple_left f (fun a b => dig j a b) ga0 i,
    triple_left_swap f ig (fun a b c => dga1 j a b c) i,
    triple_left_swap f ig (fun a b c => dga0 j a b c) i,
    four_left ig f ga0 ga1 i j,
    four_left ig f ga0 ga0 i j]
  ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
