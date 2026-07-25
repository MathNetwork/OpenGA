import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Defs








noncomputable section

set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma nf_V0_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dga1 i b2 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdga1s i c b a, hcgs a j]
  try ring

private lemma nf_V0_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dgbg i b2 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdgbgs i c b a, hcgs a j]
  try ring

private lemma nf_V0_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * ga1 b2 b0 b5 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * ga1 e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hga1s r e d, hcgs a j]
  try ring

private lemma nf_V0_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * gbg b2 b0 b5 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * gbg e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hgbgs r e d, hcgs a j]
  try ring

private lemma nf_V0_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * ga1 b2 b6 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hga1s r e a, hcgs a j]
  try ring

private lemma nf_V0_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * gbg b2 b6 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hgbgs r e a, hcgs a j]
  try ring

private lemma nf_V0_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * ga1 b7 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a j, hfs c b]
  try ring

private lemma nf_V0_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * gbg b7 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a j, hfs c b]
  try ring

private lemma nf_V0_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dga1 j b2 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdga1s j c b a, hcgs a i]
  try ring

private lemma nf_V0_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dgbg j b2 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdgbgs j c b a, hcgs a i]
  try ring

private lemma nf_V0_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * ga1 b2 b0 b9 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * ga1 e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hga1s r e d, hcgs a i]
  try ring

private lemma nf_V0_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * gbg b2 b0 b9 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * gbg e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hgbgs r e d, hcgs a i]
  try ring

private lemma nf_V0_h13 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * ga1 b2 b10 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hga1s r e a, hcgs a i]
  try ring

private lemma nf_V0_h14 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * gbg b2 b10 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hgbgs r e a, hcgs a i]
  try ring

private lemma nf_V0_h15 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * ga1 b11 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a i, hfs c b]
  try ring

private lemma nf_V0_h16 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * gbg b11 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a i, hfs c b]
  try ring

private lemma nf_V0_h17 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * ga1 b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h18 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * gbg b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h19 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dga1 i b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h20 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dgbg i b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h21 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * ga1 b16 b17 b15) * f b12 j) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  try ring

private lemma nf_V0_h22 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * gbg b16 b17 b15) * f b12 j) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  try ring

private lemma nf_V0_h23 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * ga1 b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h24 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * gbg b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h25 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dga1 j b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h26 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dgbg j b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h27 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * ga1 b22 b23 b21) * f i b18) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_V0_h28 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * gbg b22 b23 b21) * f i b18) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring


theorem nf_v0 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    v0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r))
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d)) := by
  have h1 : v0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      -((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dga1 i b2 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dgbg i b2 b0 b4 * cg b4 j * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * ga1 b2 b0 b5 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * gbg b2 b0 b5 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * ga1 b2 b6 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * gbg b2 b6 b4 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * ga1 b7 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * gbg b7 b0 b4 * cg b4 j * f b1 b3)))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dga1 j b2 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dgbg j b2 b0 b8 * cg b8 i * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * ga1 b2 b0 b9 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * gbg b2 b0 b9 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * ga1 b2 b10 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * gbg b2 b10 b8 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * ga1 b11 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * gbg b11 b0 b8 * cg b8 i * f b1 b3)))))) + ((∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * ga1 b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * gbg b13 b14 b12 * f b12 j) + ((∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dga1 i b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dgbg i b13 b14 b12 * f b12 j)) + ((∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * ga1 b16 b17 b15) * f b12 j) - (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * gbg b16 b17 b15) * f b12 j)) + ((∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * ga1 b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * gbg b19 b20 b18 * f i b18) + ((∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dga1 j b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dgbg j b19 b20 b18 * f i b18)) + ((∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * ga1 b22 b23 b21) * f i b18) - (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * gbg b22 b23 b21) * f i b18)))) := by
    simp only [v0F, covAF, covWF, dvfbF, vfbF]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dga1 i b2 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dgbg i b2 b0 b4 * cg b4 j * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * ga1 b2 b0 b5 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * gbg b2 b0 b5 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * ga1 b2 b6 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * gbg b2 b6 b4 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * ga1 b7 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * gbg b7 b0 b4 * cg b4 j * f b1 b3)))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dga1 j b2 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dgbg j b2 b0 b8 * cg b8 i * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * ga1 b2 b0 b9 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * gbg b2 b0 b9 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * ga1 b2 b10 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * gbg b2 b10 b8 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * ga1 b11 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * gbg b11 b0 b8 * cg b8 i * f b1 b3)))))) + ((∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * ga1 b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * gbg b13 b14 b12 * f b12 j) + ((∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dga1 i b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dgbg i b13 b14 b12 * f b12 j)) + ((∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * ga1 b16 b17 b15) * f b12 j) - (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * gbg b16 b17 b15) * f b12 j)) + ((∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * ga1 b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * gbg b19 b20 b18 * f i b18) + ((∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dga1 j b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dgbg j b19 b20 b18 * f i b18)) + ((∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * ga1 b22 b23 b21) * f i b18) - (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * gbg b22 b23 b21) * f i b18)))) =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r))
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d)) := by
    linear_combination - nf_V0_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h13 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h14 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h15 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h16 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h17 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h18 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h19 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h20 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h21 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h22 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h23 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h24 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h25 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h26 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h27 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h28 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2


end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
