import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Basic








noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma six_reindex {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (A B : Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hBs : ∀ a b k, B a b k = B b a k) (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5,
      ig b0 b1 * (ig b2 b3 * (A i b1 b4 * (f b4 b3 * (B b0 b2 b5 * cg b5 j))))) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg j a * f b c * A i d b * B e r a * ig c e * ig d r := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
      Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
      Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
      Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
      Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
      Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hBs r e a, hcgs a j]
  ring


theorem nf_p3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (ga0 ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k) (i j : Fin n) :
    p3HalfB ig cg ga1 ga0 gbg f i j =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg j a * f b c * ga1 i d b * ga1 e r a * ig c e * ig d r)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg j a * f b c * ga1 i d b * gbg e r a * ig c e * ig d r)) := by
  have h1 : p3HalfB ig cg ga1 ga0 gbg f i j =
      (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5,
        ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 *
          (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) -
      (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5,
        ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 *
          (f b4 b3 * (gbg b0 b2 b5 * cg b5 j))))) -
      ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5,
        ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 *
          (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) -
      (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5,
        ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 *
          (f b4 b3 * (gbg b0 b2 b5 * cg b5 j)))))) := by
    simp only [p3HalfB]
    simp (config := { maxSteps := 10000000 }) only [mul_sub, sub_mul,
      Finset.sum_sub_distrib]
    ring
  rw [h1, six_reindex ig cg f ga1 ga1 higs hcgs hga1s i j,
    six_reindex ig cg f ga1 gbg higs hcgs hgbgs i j,
    six_reindex ig cg f ga0 ga1 higs hcgs hga1s i j,
    six_reindex ig cg f ga0 gbg higs hcgs hgbgs i j]
  ring


theorem nf_p3_swap {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (ga0 ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k) (i j : Fin n) :
    p3HalfB ig cg ga1 ga0 gbg f j i =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg i a * f b c * ga1 j d b * ga1 e r a * ig c e * ig d r)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r,
        cg i a * f b c * ga1 j d b * gbg e r a * ig c e * ig d r)) :=
  nf_p3 ig cg f ga0 ga1 gbg higs hcgs hga1s hgbgs j i

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
