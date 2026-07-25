import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Defs








noncomputable section

set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma nf_D1R_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i a, hfs a j]
  try ring
private lemma nf_D1R_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i a, hfs a j]
  try ring
private lemma nf_D1R_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 j b4 * f i b4)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j a]
  try ring
private lemma nf_D1R_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 j b4 * f i b4)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j a]
  try ring
private lemma nf_D1R_h5' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga1 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d j b]
  try ring
private lemma nf_D1R_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga1 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b9 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga1 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga1 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h5' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h6' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga0 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s d j b]
  try ring
private lemma nf_D1R_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga0 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b9 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga0 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga0 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h6' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h7' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga1 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hfs b a, hga1s d j c]
  try ring
private lemma nf_D1R_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga1 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b10 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga1 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga1 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h7' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h8' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga0 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hfs b a, hga0s d j c]
  try ring
private lemma nf_D1R_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga0 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b10 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga0 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga0 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h8' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (ga1 b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a j]
  try ring
private lemma nf_D1R_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (gbg b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a j]
  try ring
private lemma nf_D1R_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (ga1 b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hga1s r e a, hcgs a j]
  try ring
private lemma nf_D1R_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (gbg b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hgbgs r e a, hcgs a j]
  try ring
private lemma nf_D1R_h13 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring
private lemma nf_D1R_h14 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring
private lemma nf_D1R_h15 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring
private lemma nf_D1R_h16 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring
private lemma nf_D1R_h17' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga1 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s c j a, hga1s d i c]
  try ring
private lemma nf_D1R_h17 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga1 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b28 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga1 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga1 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h17' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h18' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga0 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs c b, hga0s d j a, hga0s c i d]
  try ring
private lemma nf_D1R_h18 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga0 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b28 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga0 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga0 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h18' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h19' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga1 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d i b]
  try ring
private lemma nf_D1R_h19 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga1 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b29 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga1 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga1 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h19' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h20' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga0 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i c]
  try ring
private lemma nf_D1R_h20 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga0 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b29 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga0 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga0 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h20' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h21 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s j i c, hga0s d c a]
  try ring
private lemma nf_D1R_h22 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i c, hga0s d c a]
  try ring
private lemma nf_D1R_h23 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s j i b, hga0s d c a, hfs b a]
  try ring
private lemma nf_D1R_h24 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i a, hga0s d c b]
  try ring
private lemma nf_D1R_h25' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga1 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c j a, hga1s d i b]
  try ring
private lemma nf_D1R_h25 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga1 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b40 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga1 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga1 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h25' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h26' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga0 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d j b, hfs b a, hga0s c i a]
  try ring
private lemma nf_D1R_h26 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga0 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b40 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga0 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga0 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h26' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h27' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga1 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c b a, hga1s d i b]
  try ring
private lemma nf_D1R_h27 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga1 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b41 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga1 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga1 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h27' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h28' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga0 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a, hga0s b i c]
  try ring
private lemma nf_D1R_h28 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga0 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b41 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga0 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga0 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h28' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h29' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga1 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d i b]
  try ring
private lemma nf_D1R_h29 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga1 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b47 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga1 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga1 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h29' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h30' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga0 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a, hga0s c i a]
  try ring
private lemma nf_D1R_h30 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga0 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b47 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga0 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga0 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h30' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h31' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga1 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hfs b a, hga1s d i c]
  try ring
private lemma nf_D1R_h31 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga1 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b48 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga1 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga1 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h31' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h32' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga0 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs c b, hfs b a, hga0s c i d]
  try ring
private lemma nf_D1R_h32 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga0 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b48 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga0 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga0 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h32' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h33 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (ga1 b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a i]
  try ring
private lemma nf_D1R_h34 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (gbg b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a i]
  try ring
private lemma nf_D1R_h35 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (ga1 b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hga1s r e a, hcgs a i]
  try ring
private lemma nf_D1R_h36 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (gbg b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hgbgs r e a, hcgs a i]
  try ring
private lemma nf_D1R_h37 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i a]
  try ring
private lemma nf_D1R_h38 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i a]
  try ring
private lemma nf_D1R_h39 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring
private lemma nf_D1R_h40 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring
private lemma nf_D1R_h41' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga1 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s c i a, hga1s d j c]
  try ring
private lemma nf_D1R_h41 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga1 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b66 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga1 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga1 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h41' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h42' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga0 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s c i a, hga0s d j c]
  try ring
private lemma nf_D1R_h42 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga0 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b66 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga0 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga0 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h42' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h43' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga1 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d j b]
  try ring
private lemma nf_D1R_h43 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga1 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b67 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga1 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga1 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h43' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h44' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga0 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j c]
  try ring
private lemma nf_D1R_h44 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga0 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b67 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga0 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga0 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h44' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h45 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a]
  try ring
private lemma nf_D1R_h46 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a]
  try ring
private lemma nf_D1R_h47 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a, hfs b a]
  try ring
private lemma nf_D1R_h48 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c b]
  try ring
private lemma nf_D1R_h49' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga1 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c i a, hga1s d j b]
  try ring
private lemma nf_D1R_h49 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga1 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b78 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga1 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga1 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h49' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h50' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga0 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c i a, hga0s d j b]
  try ring
private lemma nf_D1R_h50 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga0 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b78 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga0 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga0 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h50' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h51' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga1 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c b a, hga1s d j b]
  try ring
private lemma nf_D1R_h51 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga1 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b79 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga1 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga1 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h51' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h52' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga0 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a, hga0s b j c]
  try ring
private lemma nf_D1R_h52 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga0 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b79 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga0 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga0 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h52' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
private lemma nf_D1R_h53 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s j i c]
  try ring
private lemma nf_D1R_h54 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i c]
  try ring
private lemma nf_D1R_h55 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga1s j i c, hfs b a]
  try ring
private lemma nf_D1R_h56 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ) (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
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
    (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s j i c, hfs b a]
  try ring

theorem nf_d1r {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    d1RF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d))
      + ((-4 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d)) := by
  have h1 : d1RF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      -((∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) - (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 i b3 * f b3 j))) + (-((∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 j b4 * f i b4)) - (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 j b4 * f i b4)))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5))))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))))) - (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (gbg b12 b14 b18 * cg b18 j))))) + (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (gbg b12 b14 b18 * cg b18 j))))))) - (-((∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) - (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i j b22 * f b22 b19))) + (-((∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) - (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i b19 b23 * f j b23))))) - (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26))))) + (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26))))))) - (-((∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) - (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b33 b34 * f b34 b31)))) + (-((∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) - (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b31 b35 * f b33 b35)))))) - (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36))))) + (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))))) - (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (gbg b50 b52 b56 * cg b56 i))))) + (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (gbg b50 b52 b56 * cg b56 i))))))) - (-((∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) - (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j i b60 * f b60 b57))) + (-((∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) - (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j b57 b61 * f i b61))))) - (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64))))) + (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64))))))) - (-((∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) - (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b71 b72 * f b72 b69)))) + (-((∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) - (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b69 b73 * f b71 b73)))))) - (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74))))) + (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))))))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) - (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b82 b84 * f b84 b81)))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) - (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b81 b85 * f b82 b85)))))) := by
    simp only [d1RF, vfbF, r3B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -((∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) - (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 i b3 * f b3 j))) + (-((∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 j b4 * f i b4)) - (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 j b4 * f i b4)))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5))))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))))) - (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (gbg b12 b14 b18 * cg b18 j))))) + (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (gbg b12 b14 b18 * cg b18 j))))))) - (-((∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) - (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i j b22 * f b22 b19))) + (-((∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) - (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i b19 b23 * f j b23))))) - (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26))))) + (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26))))))) - (-((∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) - (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b33 b34 * f b34 b31)))) + (-((∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) - (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b31 b35 * f b33 b35)))))) - (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36))))) + (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))))) - (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (gbg b50 b52 b56 * cg b56 i))))) + (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (gbg b50 b52 b56 * cg b56 i))))))) - (-((∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) - (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j i b60 * f b60 b57))) + (-((∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) - (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j b57 b61 * f i b61))))) - (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64))))) + (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64))))))) - (-((∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) - (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b71 b72 * f b72 b69)))) + (-((∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) - (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b69 b73 * f b71 b73)))))) - (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74))))) + (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))))))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) - (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b82 b84 * f b84 b81)))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) - (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b81 b85 * f b82 b85)))))) =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d))
      + ((-4 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d)) := by
    linear_combination - nf_D1R_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h13 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h14 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h15 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h16 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h17 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h18 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h19 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h20 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h21 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h22 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h23 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h24 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h25 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h26 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h27 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h28 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h29 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h30 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h31 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h32 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h33 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h34 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h35 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h36 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h37 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h38 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h39 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h40 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h41 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h42 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h43 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h44 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h45 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h46 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h47 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h48 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h49 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h50 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h51 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h52 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h53 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h54 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h55 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h56 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
