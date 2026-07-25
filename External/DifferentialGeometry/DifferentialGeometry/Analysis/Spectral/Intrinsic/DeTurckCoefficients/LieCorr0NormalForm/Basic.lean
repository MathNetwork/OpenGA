import Mathlib









noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

variable {n : ℕ}


def p1B (ig : Fin n → Fin n → ℝ)
    (dig ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (- ∑ ρ, (∑ a, ∑ b, (dig i a b * (ga1 a b ρ - ga0 a b ρ) +
      ig a b * (dga1 i a b ρ - dga0 i a b ρ)) +
    ∑ σ, ga0 i σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * f ρ j) +
  (- ∑ ρ, (∑ a, ∑ b, (dig j a b * (ga1 a b ρ - ga0 a b ρ) +
      ig a b * (dga1 j a b ρ - dga0 j a b ρ)) +
    ∑ σ, ga0 j σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * f i ρ)


def p2B (ig : Fin n → Fin n → ℝ) (ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * ∑ ρ, ∑ σ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) *
    ((ga1 i j σ - ga0 i j σ) * f ρ σ)


def p3B (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k j)))) +
    ∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 j p ρ - ga0 j p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k i)))))


def p4B (ig : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
      ((ga1 m i ρ - ga0 m i ρ) * f ρ j)) +
  (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
      ((ga1 m j ρ - ga0 m j ρ) * f i ρ))


def nscB (ig : Fin n → Fin n → ℝ) (dig ga1 ga0 gbg :
    Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ) (i p : Fin n) : ℝ :=
  ∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)) * (ga1 i m p - ga0 i m p) -
    ∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) * (ga1 i m p - ga0 i m p) -
    ((∑ a, ∑ b, (dig i a b * (ga1 a b p - ga0 a b p) +
        ig a b * (dga1 i a b p - dga0 i a b p))) +
      ∑ m, ga1 i m p * (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)))


def insertB (ig : Fin n → Fin n → ℝ) (dig ga1 ga0 gbg :
    Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (∑ p, nscB ig dig ga1 ga0 gbg dga1 dga0 i p * f p j) +
    (∑ p, nscB ig dig ga1 ga0 gbg dga1 dga0 j p * f i p)

private lemma a1_ga1_symm
    (ig : Fin n → Fin n → ℝ) (dg gb ga1 : Fin n → Fin n → Fin n → ℝ)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (a b k : Fin n) : ga1 a b k = ga1 b a k := by
  rw [hga1, hga1]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl (fun l _ => ?_))
  rw [hgb, hgb, hdgs a l b, hdgs b l a, hdgs l a b]
  ring


theorem stage_a1
    (ig : Fin n → Fin n → ℝ) (dg gb dig ga1 ga0 gbg :
      Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (i j : Fin n) :
    insertB ig dig ga1 ga0 gbg dga1 dga0 f i j =
      p1B ig dig ga1 ga0 dga1 dga0 f i j + p4B ig ga1 ga0 gbg f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  have hhalf : ∀ (u : Fin n) (F : Fin n → ℝ),
      (∑ p, nscB ig dig ga1 ga0 gbg dga1 dga0 u p * F p) =
        (- ∑ ρ, (∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
            ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
          ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * F ρ) +
        (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
            ((ga1 m u ρ - ga0 m u ρ) * F ρ)) := by
    intro u F
    have hswap2 : (∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
        ((ga1 m u ρ - ga0 m u ρ) * F ρ)) =
        ∑ ρ, (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)) * F ρ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hga1s m u ρ, hga0s m u ρ]
      ring
    have hcomb : (- ∑ ρ, (∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
          ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
        ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * F ρ) +
        (- ∑ ρ, (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)) * F ρ) =
      ∑ ρ, (((-((∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
          ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
        ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ)))))
        + (-(∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)))) * F ρ) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      ring
    rw [hswap2, hcomb]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => t * F p) ?_
    rw [nscB]
    have hkey : (∑ m, ga1 u m p * (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m))) -
        (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)) * (ga1 u m p - ga0 u m p)) =
        ∑ σ, ga0 u σ p * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    linarith [hkey]
  rw [insertB, hhalf i (fun p => f p j), hhalf j (fun p => f i p)]
  rw [p1B, p4B]
  ring


def vbB (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * ∑ k, ∑ l, ig k l *
    ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
      (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))

private lemma collapse_sum
    (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (X : Fin n → ℝ) (c : Fin n) :
    (∑ k, (∑ l, ig k l * cg c l) * X k) = X c := by
  have hone : ∀ k, (∑ l, ig k l * cg c l) = if k = c then (1 : ℝ) else 0 := by
    intro k
    rw [show (∑ l, ig k l * cg c l) = ∑ l, cg l c * ig l k from
      Finset.sum_congr rfl (fun l _ => by rw [higs k l, hcgs c l]; ring)]
    exact hcol k c
  rw [Finset.sum_congr rfl (fun k _ => by rw [hone k])]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_mul]
  · intro k _ hk
    rw [if_neg hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h


theorem stage_a2
    (ig cg : Fin n → Fin n → ℝ) (dg gb ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (i j : Fin n) :
    vbB ig cg ga1 ga0 f i j = p2B ig ga1 ga0 f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  rw [vbB, p2B]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  have hstep1 : (∑ k, ∑ l, ig k l *
      ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))) =
    ∑ c, (ga1 j i c - ga0 j i c) *
      ∑ k, (∑ l, ig k l * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k) := by
    have h1 : ∀ k, (∑ l, ig k l *
        ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
          (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))) =
        ∑ c, ∑ l, (ga1 j i c - ga0 j i c) *
          ((ig k l * cg c l) *
            (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) := by
      intro k
      have h2 : ∀ l, ig k l *
          ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
            (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) =
          ∑ c, (ga1 j i c - ga0 j i c) *
            ((ig k l * cg c l) *
              (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) := by
        intro l
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      rw [Finset.sum_congr rfl (fun l _ => h2 l)]
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl (fun k _ => h1 k)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [hstep1]
  have hstep2 : (∑ c, (ga1 j i c - ga0 j i c) *
      ∑ k, (∑ l, ig k l * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) =
      ∑ c, (ga1 j i c - ga0 j i c) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c) :=
    Finset.sum_congr rfl (fun c _ => by
      rw [collapse_sum ig cg hcol higs hcgs
        (fun k => (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) c])
  rw [hstep2]
  have hdist : (∑ c, (ga1 j i c - ga0 j i c) *
      (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c)) =
      ∑ c, ∑ ρ, (ga1 j i c - ga0 j i c) *
        ((∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c) :=
    Finset.sum_congr rfl (fun c _ => Finset.mul_sum _ _ _)
  rw [hdist, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hga1s j i σ, hga0s j i σ]
  ring


def amixHalfB (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ m, ∑ ml, ig m ml *
    (∑ a, ∑ al, ig a al *
      ((∑ k, ∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) *
        (∑ d, (ga1 m a d - gbg m a d) * cg d j)))


def p3HalfB (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
    ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
      ((ga1 a b k - gbg a b k) * cg k j))))


theorem stage_a3
    (ig cg : Fin n → Fin n → ℝ) (dg gb ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (i j : Fin n) :
    amixHalfB ig cg ga1 ga0 gbg f i j = p3HalfB ig cg ga1 ga0 gbg f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  have hinner : ∀ ml al : Fin n,
      (∑ k, ∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) =
      ∑ c, (ga1 al i c - ga0 al i c) * f c ml := by
    intro ml al
    have h1 : ∀ k, (∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) =
        ∑ c, (ga1 al i c - ga0 al i c) * ((∑ kl, ig k kl * cg c kl) * f k ml) := by
      intro k
      have h2 : ∀ kl, ig k kl *
          (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl)) =
          ∑ c, (ga1 al i c - ga0 al i c) * ((ig k kl * cg c kl) * f k ml) := by
        intro kl
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      rw [Finset.sum_congr rfl (fun kl _ => h2 kl), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.mul_sum]
    refine congrArg (fun t : ℝ => (ga1 al i c - ga0 al i c) * t) ?_
    exact collapse_sum ig cg hcol higs hcgs (fun k => f k ml) c
  have hmid : amixHalfB ig cg ga1 ga0 gbg f i j =
      ∑ m, ∑ ml, ig m ml *
        (∑ a, ∑ al, ig a al *
          ((∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
            (∑ d, (ga1 m a d - gbg m a d) * cg d j))) := by
    rw [amixHalfB]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine congrArg (fun t : ℝ => ig m ml * t) ?_
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
    refine congrArg (fun t : ℝ => ig a al * t) ?_
    rw [hinner ml al]
  rw [hmid, p3HalfB]
  have hL : (∑ m, ∑ ml, ig m ml *
      (∑ a, ∑ al, ig a al *
        ((∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
          (∑ d, (ga1 m a d - gbg m a d) * cg d j)))) =
      ∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
        ig m ml * (ig a al * (((ga1 al i c - ga0 al i c) * f c ml) *
          ((ga1 m a d - gbg m a d) * cg d j))) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun al _ => ?_)
    have hprod : (∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
        (∑ d, (ga1 m a d - gbg m a d) * cg d j) =
        ∑ c, ∑ d, ((ga1 al i c - ga0 al i c) * f c ml) *
          ((ga1 m a d - gbg m a d) * cg d j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.mul_sum]
    rw [hprod, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  have hR : (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ b, ∑ q, ∑ a, ∑ p, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) := by
    rw [show (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ a, ∑ b, ∑ p, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [show (∑ a, ∑ p, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ a, ∑ q, ∑ p, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  rw [hL, hR]
  rw [show (∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
      ig m ml * (ig a al * (((ga1 al i c - ga0 al i c) * f c ml) *
        ((ga1 m a d - gbg m a d) * cg d j)))) =
    ∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
      ig a al * (ig m ml * ((ga1 i al c - ga0 i al c) * (f c ml *
        ((ga1 a m d - gbg a m d) * cg d j)))) from by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hga1s al i c, hga0s al i c, hga1s m a d, hgbgs m a d]
    ring]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
