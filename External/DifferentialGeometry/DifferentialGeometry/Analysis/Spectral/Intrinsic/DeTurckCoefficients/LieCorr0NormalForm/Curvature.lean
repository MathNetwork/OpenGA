import Mathlib









noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

variable {n : ℕ}


def rchB (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ) (l i j ρ : Fin n) : ℝ :=
  dga0 i l j ρ - dga0 j l i ρ +
    ∑ c, (ga0 i c ρ * ga0 l j c - ga0 j c ρ * ga0 l i c)


def p5B (ig : Fin n → Fin n → ℝ) (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  -(∑ m, ∑ ml, ig m ml * ∑ ρ, rchB ga0 dga0 ml i j ρ * f ρ m)


theorem nf_p5 (ig : Fin n → Fin n → ℝ) (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (i j : Fin n) :
    p5B ig ga0 dga0 f i j =
      (-(∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c))
      + (∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  rw [p5B]
  have hcomb : ∀ m ml : Fin n, ig m ml * ∑ ρ, rchB ga0 dga0 ml i j ρ * f ρ m =
      ∑ ρ, ((ig m ml * (dga0 i ml j ρ * f ρ m) - ig m ml * (dga0 j ml i ρ * f ρ m))
        + ∑ c, (ig m ml * (ga0 i c ρ * (ga0 ml j c * f ρ m))
            - ig m ml * (ga0 j c ρ * (ga0 ml i c * f ρ m)))) := by
    intro m ml
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [rchB]
    rw [show (dga0 i ml j ρ - dga0 j ml i ρ +
        ∑ c, (ga0 i c ρ * ga0 ml j c - ga0 j c ρ * ga0 ml i c)) * f ρ m =
      (dga0 i ml j ρ * f ρ m - dga0 j ml i ρ * f ρ m)
        + ∑ c, (ga0 i c ρ * ga0 ml j c - ga0 j c ρ * ga0 ml i c) * f ρ m from by
      rw [add_mul, sub_mul, Finset.sum_mul]]
    rw [mul_add, Finset.mul_sum]
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (by ring)
      (Finset.sum_congr rfl (fun c _ => by ring))
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => hcomb m ml))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ m, ∑ ml, ∑ ρ, ig m ml * (dga0 i ml j ρ * f ρ m)) =
      ∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ml _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [hdga0s i ml j ρ, higs m ml]
    ring
  have h2 : (∑ m, ∑ ml, ∑ ρ, ig m ml * (dga0 j ml i ρ * f ρ m)) =
      ∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ml _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [hdga0s j ml i ρ, higs m ml]
    ring
  have h3 : (∑ m, ∑ ml, ∑ ρ, ∑ c, ig m ml * (ga0 i c ρ * (ga0 ml j c * f ρ m))) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d := by
    rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun ml _ => ?_))
    rw [hga0s ml j c, higs m ml]
    ring
  have h4 : (∑ m, ∑ ml, ∑ ρ, ∑ c, ig m ml * (ga0 j c ρ * (ga0 ml i c * f ρ m))) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c := by
    rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ =>
      Finset.sum_congr rfl (fun ml _ => Finset.sum_congr rfl (fun c _ => ?_))))
    rw [hga0s ml i c, higs m ml]
    ring
  rw [h1, h2, h3, h4]
  ring


def r4F (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (f3 : Fin n → Fin n → Fin n → ℝ)
    (a b c d : Fin n) : ℝ :=
  (((- ∑ r, dga0 a c b r * f r d) + (- ∑ r, dga0 a d b r * f c r)) +
      ((- ∑ r, ga0 c b r * f3 a r d) + (- ∑ r, ga0 d b r * f3 a c r))) +
    ((- ∑ r, ga0 a b r * (f3 r c d +
        ((- ∑ t, ga0 r c t * f t d) + (- ∑ t, ga0 r d t * f c t)))) +
      ((- ∑ r, ga0 a c r * (f3 b r d +
          ((- ∑ t, ga0 b r t * f t d) + (- ∑ t, ga0 b d t * f r t)))) +
        (- ∑ r, ga0 a d r * (f3 b c r +
          ((- ∑ t, ga0 b c t * f t r) + (- ∑ t, ga0 b r t * f c t))))))


def r4pfB (ga0 : Fin n → Fin n → Fin n → ℝ)
    (f3 : Fin n → Fin n → Fin n → ℝ) (d a b c : Fin n) : ℝ :=
  - ∑ r, (ga0 a b r * f3 d r c + ga0 a c r * f3 d b r + ga0 d a r * f3 r b c +
      ga0 d b r * f3 a r c + ga0 d c r * f3 a b r)


def r4hB (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  ((- ∑ r, dga0 a c b r * f r d) + (- ∑ r, dga0 a d b r * f c r)) +
    ((∑ r, ∑ t, ga0 a b r * (ga0 r c t * f t d)) +
      (∑ r, ∑ t, ga0 a b r * (ga0 r d t * f c t)) +
      (∑ r, ∑ t, ga0 a c r * (ga0 b r t * f t d)) +
      (∑ r, ∑ t, ga0 a c r * (ga0 b d t * f r t)) +
      (∑ r, ∑ t, ga0 a d r * (ga0 b c t * f t r)) +
      (∑ r, ∑ t, ga0 a d r * (ga0 b r t * f c t)))


def t2F (ig : Fin n → Fin n → ℝ) (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (f3 : Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∑ k1, ∑ l, ig k1 l * (r4F ga0 dga0 f f3 i l j k1 + r4F ga0 dga0 f f3 j l i k1 -
    r4F ga0 dga0 f f3 i j l k1)


def tpfF (ig : Fin n → Fin n → ℝ) (ga0 : Fin n → Fin n → Fin n → ℝ)
    (f3 : Fin n → Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k1, ∑ l, ig k1 l * (r4pfB ga0 f3 i l j k1 + r4pfB ga0 f3 j l i k1 -
    r4pfB ga0 f3 i j l k1)

private lemma r4_split (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (f3 : Fin n → Fin n → Fin n → ℝ)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k) (a b c d : Fin n) :
    r4F ga0 dga0 f f3 a b c d - r4pfB ga0 f3 a b c d = r4hB ga0 dga0 f a b c d := by
  rw [r4F, r4pfB, r4hB]
  have e1 : (∑ r, ga0 a b r * (f3 r c d +
      ((- ∑ t, ga0 r c t * f t d) + (- ∑ t, ga0 r d t * f c t)))) =
      (∑ r, ga0 a b r * f3 r c d) - (∑ r, ∑ t, ga0 a b r * (ga0 r c t * f t d)) -
        (∑ r, ∑ t, ga0 a b r * (ga0 r d t * f c t)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have e2 : (∑ r, ga0 a c r * (f3 b r d +
      ((- ∑ t, ga0 b r t * f t d) + (- ∑ t, ga0 b d t * f r t)))) =
      (∑ r, ga0 a c r * f3 b r d) - (∑ r, ∑ t, ga0 a c r * (ga0 b r t * f t d)) -
        (∑ r, ∑ t, ga0 a c r * (ga0 b d t * f r t)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have e3 : (∑ r, ga0 a d r * (f3 b c r +
      ((- ∑ t, ga0 b c t * f t r) + (- ∑ t, ga0 b r t * f c t)))) =
      (∑ r, ga0 a d r * f3 b c r) - (∑ r, ∑ t, ga0 a d r * (ga0 b c t * f t r)) -
        (∑ r, ∑ t, ga0 a d r * (ga0 b r t * f c t)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [e1, e2, e3]
  have hpf : (∑ r, (ga0 b c r * f3 a r d + ga0 b d r * f3 a c r + ga0 a b r * f3 r c d +
      ga0 a c r * f3 b r d + ga0 a d r * f3 b c r)) =
      (∑ r, ga0 c b r * f3 a r d) + (∑ r, ga0 d b r * f3 a c r) +
        (∑ r, ga0 a b r * f3 r c d) + (∑ r, ga0 a c r * f3 b r d) +
        (∑ r, ga0 a d r * f3 b c r) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hga0s c b r, hga0s d b r]
  rw [hpf]
  ring

private lemma t2_block (ig : Fin n → Fin n → ℝ) (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (f3 : Fin n → Fin n → Fin n → ℝ)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k) (i j : Fin n) :
    t2F ig ga0 dga0 f f3 i j - tpfF ig ga0 f3 i j =
      ∑ k1, ∑ l, ig k1 l * (r4hB ga0 dga0 f i l j k1 + r4hB ga0 dga0 f j l i k1 -
        r4hB ga0 dga0 f i j l k1) := by
  rw [t2F, tpfF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← mul_sub]
  refine congrArg (fun t : ℝ => ig k1 l * t) ?_
  rw [show r4F ga0 dga0 f f3 i l j k1 + r4F ga0 dga0 f f3 j l i k1 -
      r4F ga0 dga0 f f3 i j l k1 -
      (r4pfB ga0 f3 i l j k1 + r4pfB ga0 f3 j l i k1 - r4pfB ga0 f3 i j l k1) =
    (r4F ga0 dga0 f f3 i l j k1 - r4pfB ga0 f3 i l j k1) +
      (r4F ga0 dga0 f f3 j l i k1 - r4pfB ga0 f3 j l i k1) -
      (r4F ga0 dga0 f f3 i j l k1 - r4pfB ga0 f3 i j l k1) from by ring]
  rw [r4_split ga0 dga0 f f3 hga0s i l j k1, r4_split ga0 dga0 f f3 hga0s j l i k1,
    r4_split ga0 dga0 f f3 hga0s i j l k1]


theorem nf_t2h (ig : Fin n → Fin n → ℝ) (ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (f3 : Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    t2F ig ga0 dga0 f f3 i j - tpfF ig ga0 f3 i j =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c)
      + (-(∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c))
      + (-(∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c)) := by
  rw [t2_block ig ga0 dga0 f f3 hga0s i j]
  have hcomb : ∀ k1 l : Fin n, ig k1 l * (r4hB ga0 dga0 f i l j k1 +
      r4hB ga0 dga0 f j l i k1 - r4hB ga0 dga0 f i j l k1) =
      -(ig k1 l * (∑ r, dga0 i j l r * f r k1))
          - ig k1 l * (∑ r, dga0 i k1 l r * f j r)
          + ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r j t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r k1 t * f j t))
          + ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l r t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l k1 t * f r t))
          + ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l j t * f t r))
          + ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l r t * f j t))
          - ig k1 l * (∑ r, dga0 j i l r * f r k1)
          - ig k1 l * (∑ r, dga0 j k1 l r * f i r)
          + ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r i t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r k1 t * f i t))
          + ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l r t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l k1 t * f r t))
          + ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l i t * f t r))
          + ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l r t * f i t))
          + ig k1 l * (∑ r, dga0 i l j r * f r k1)
          + ig k1 l * (∑ r, dga0 i k1 j r * f l r)
          - ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r l t * f t k1))
          - ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r k1 t * f l t))
          - ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j r t * f t k1))
          - ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j k1 t * f r t))
          - ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j l t * f t r))
          - ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j r t * f l t)) := by
    intro k1 l
    simp only [r4hB]
    ring
  rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun l _ => hcomb k1 l))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have ht1 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i j l r * f r k1)) =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_)))
    rw [higs k1 l]
    ring
  have ht2 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i k1 l r * f j r)) =
      (∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_)))
    ring
  have ht3 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r j t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_))))
    rw [hga0s r j t]
    ring
  have ht4 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r k1 t * f j t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l]
    ring
  have ht5 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l r t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l r t]
    ring
  have ht6 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l k1 t * f r t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l k1 t]
    ring
  have ht7 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l j t * f t r))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l j t, hfs t r]
    ring
  have ht8 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l r t * f j t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l r t]
    ring
  have ht9 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 j i l r * f r k1)) =
      (∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_)))
    rw [higs k1 l]
    ring
  have ht10 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 j k1 l r * f i r)) =
      (∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_)))
    ring
  have ht11 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r i t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s r i t]
    ring
  have ht12 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r k1 t * f i t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l]
    ring
  have ht13 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l r t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s j i r, hga0s l r t]
    ring
  have ht14 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l k1 t * f r t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s j i r, hga0s l k1 t]
    ring
  have ht15 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l i t * f t r))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l, hga0s l i t]
    ring
  have ht16 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l r t * f i t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l r t]
    ring
  have ht17 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i l j r * f r k1)) =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_)))
    rw [higs k1 l, hdga0s i l j r]
    ring
  have ht18 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i k1 j r * f l r)) =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_)))
    rw [hdga0s i k1 j r, hfs l r]
    ring
  have ht19 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r l t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring
  have ht20 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r k1 t * f l t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l, hfs l t]
    ring
  have ht21 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j r t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_))))
    ring
  have ht22 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j k1 t * f r t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l]
    ring
  have ht23 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j l t * f t r))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hfs t r]
    ring
  have ht24 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j r t * f l t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => ?_))))
    rw [higs k1 l, hfs l t]
    ring
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ht14, ht15,
    ht16, ht17, ht18, ht19, ht20, ht21, ht22, ht23, ht24]
  ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
