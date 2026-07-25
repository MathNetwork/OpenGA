import Mathlib









noncomputable section

set_option linter.style.setOption false
set_option linter.unusedVariables false

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF


lemma collapse {n : ℕ} (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (X : Fin n → ℝ) (e : Fin n) :
    (∑ u, ∑ d, cg d e * ig d u * X u) = X e := by
  have h1 : ∀ u : Fin n, (∑ d, cg d e * ig d u * X u) =
      (if u = e then (1 : ℝ) else 0) * X u := by
    intro u
    rw [← Finset.sum_mul, hcol u e]
  rw [Finset.sum_congr rfl (fun u _ => h1 u)]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h


lemma collapse_rev {n : ℕ} (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (X : Fin n → ℝ) (e : Fin n) :
    (∑ w, ∑ d, cg d w * ig d e * X w) = X e := by
  have h1 : ∀ w : Fin n, (∑ d, cg d w * ig d e * X w) =
      (if e = w then (1 : ℝ) else 0) * X w := by
    intro w
    rw [← Finset.sum_mul, hcol e w]
  rw [Finset.sum_congr rfl (fun w _ => h1 w)]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h


def r3B {n : ℕ} (_ig _cg f : Fin n → Fin n → ℝ)
    (_dg _dig ga0 _ga1 _gbg _gb _f3 : Fin n → Fin n → Fin n → ℝ)
    (_ddg _dga0 _dga1 _dgbg _dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c : Fin n) : ℝ :=
  -(∑ r, ga0 a b r * f r c) + (-(∑ r, ga0 a c r * f b r))


def chrCorrF {n : ℕ} (ig _cg f : Fin n → Fin n → ℝ)
    (_dg _dig _ga0 _ga1 _gbg gb _f3 : Fin n → Fin n → Fin n → ℝ)
    (_ddg _dga0 _dga1 _dgbg _dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * (∑ l, (-(∑ q, ∑ p, ig k p * f p q * ig q l)) * gb a b l)


def wcF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (k : Fin n) : ℝ :=
  ∑ a, ∑ b, ((-(∑ q, ∑ p, ig a p * f p q * ig q b)) * (ga1 a b k - gbg a b k) +
    ig a b * chrCorrF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb a b k)


def dvfbF {n : ℕ} (ig _cg _f : Fin n → Fin n → ℝ)
    (_dg dig _ga0 ga1 gbg _gb _f3 : Fin n → Fin n → Fin n → ℝ)
    (_ddg _dga0 dga1 dgbg _dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k : Fin n) : ℝ :=
  ∑ a, ∑ b, (dig m a b * (ga1 a b k - gbg a b k) +
    ig a b * (dga1 m a b k - dgbg m a b k))


def d0F {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k : Fin n) : ℝ :=
  ∑ a, ∑ b, ((-(∑ q, ∑ p, (dig m a p * f p q * ig q b + ig a p * f p q * dig m q b))) * (ga1 a b k - gbg a b k) + (-(∑ q, ∑ p, ig a p * f p q * ig q b)) * (dga1 m a b k - dgbg m a b k) + dig m a b * chrCorrF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb a b k + ig a b * ((1 / 2 : ℝ) * (∑ l, ((-(∑ q, ∑ p, (dig m k p * f p q * ig q l + ig k p * f p q * dig m q l))) * gb a b l + (-(∑ q, ∑ p, ig k p * f p q * ig q l)) * dgb m a b l))))


def o0F {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (∑ k, wcF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb k * dg k i j) +
    (∑ k, f k j * dvfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i k) +
    (∑ k, f i k * dvfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j k) +
    (∑ k, cg k j * d0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i k) +
    (∑ k, cg i k * d0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j k)


def vfbF {n : ℕ} (ig _cg _f : Fin n → Fin n → ℝ)
    (_dg _dig _ga0 ga1 gbg _gb _f3 : Fin n → Fin n → Fin n → ℝ)
    (_ddg _dga0 _dga1 _dgbg _dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (k : Fin n) : ℝ :=
  ∑ a, ∑ b, ig a b * (ga1 a b k - gbg a b k)


def covAF {n : ℕ} (_ig _cg _f : Fin n → Fin n → ℝ)
    (_dg _dig _ga0 ga1 gbg _gb _f3 : Fin n → Fin n → Fin n → ℝ)
    (_ddg _dga0 dga1 dgbg _dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a m k p : Fin n) : ℝ :=
  dga1 a k m p - dgbg a k m p +
    (∑ c, ga1 a c p * (ga1 k m c - gbg k m c)) -
    (∑ c, ga1 a m c * (ga1 k c p - gbg k c p)) -
    (∑ c, ga1 a k c * (ga1 c m p - gbg c m p))


def covWF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a p : Fin n) : ℝ :=
  dvfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb a p +
    ∑ c, ga1 a c p * vfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb c


def v0F {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  -(∑ m, ∑ ml, ig m ml * (∑ k, ∑ kl, ig k kl *
      (((∑ p, covAF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i m k p * cg p j) +
        (∑ p, covAF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j m k p * cg p i)) *
        f ml kl))) +
    ((∑ p, covWF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i p * f p j) +
      (∑ p, covWF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j p * f i p))


def d1RF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (∑ w, vfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb w *
      r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb w i j) +
  ((∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i m p *
        (∑ q, (ga1 l1 j q - ga0 l1 j q) * cg q k1)))) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i m p *
        (∑ q, (ga1 k1 l1 q - gbg k1 l1 q) * cg q j)))) -
    (∑ w, (∑ a, ∑ b, ig a b * (ga1 a b w - ga0 a b w)) *
      r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j w) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m j p *
        (∑ q, (ga1 k1 i q - ga0 k1 i q) * cg q l1)))) -
    (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 j i q - ga0 j i q) *
      r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb p q k1)) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m j p *
        (∑ q, (ga1 l1 i q - ga0 l1 i q) * cg q k1))))) +
  ((∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j m p *
        (∑ q, (ga1 l1 i q - ga0 l1 i q) * cg q k1)))) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j m p *
        (∑ q, (ga1 k1 l1 q - gbg k1 l1 q) * cg q i)))) -
    (∑ w, (∑ a, ∑ b, ig a b * (ga1 a b w - ga0 a b w)) *
      r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j i w) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m i p *
        (∑ q, (ga1 k1 j q - ga0 k1 j q) * cg q l1)))) -
    (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 i j q - ga0 i j q) *
      r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb p q k1)) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m i p *
        (∑ q, (ga1 l1 j q - ga0 l1 j q) * cg q k1))))) +
  (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 j i q - ga0 j i q) *
    r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb q p k1))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
