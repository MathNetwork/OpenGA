import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.Defs








noncomputable section

set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF

private lemma nf_O0_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * ga1 b1 b2 b0 * dg b0 i j) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * ga1 d e a * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs d b]
  try ring

private lemma nf_O0_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * gbg b1 b2 b0 * dg b0 i j) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * gbg d e a * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs d b]
  try ring

private lemma nf_O0_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b0, ∑ b1, ∑ b2, ∑ b5, ∑ b6, ∑ b7, ig b1 b2 * ((1 / 2 : ℝ) * (ig b0 b7 * f b7 b6 * ig b6 b5 * gb b1 b2 b5)) * dg b0 i j) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, dg a i j * f b c * gb d e r * ig a b * ig c r * ig d e) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  ring

private lemma nf_O0_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * ga1 b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * gbg b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dga1 i b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dgbg i b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * ga1 b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * gbg b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dga1 j b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dgbg j b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * ga1 b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, hdigs i c b]
  try ring

private lemma nf_O0_h13 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * ga1 b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e d, hfs d b, hga1s e c a]
  try ring

private lemma nf_O0_h14 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * gbg b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, hdigs i c b]
  try ring

private lemma nf_O0_h15 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * gbg b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e d, hfs d b, hgbgs e c a]
  try ring

private lemma nf_O0_h16 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dga1 i b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e c]
  try ring

private lemma nf_O0_h17 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dgbg i b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e c]
  try ring

private lemma nf_O0_h18' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b15, ∑ b16, ∑ b21, ∑ b22, (1 / 2 : ℝ) * dig i b15 b16 * f j b22 * ig b22 b21 * gb b15 b16 b21) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h18 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d) := by
  have hstep : (∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)))) =
      (∑ b15, ∑ b16, ∑ b21, ∑ b22, (1 / 2 : ℝ) * dig i b15 b16 * f j b22 * ig b22 b21 * gb b15 b16 b21) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b15 _ => Finset.sum_congr rfl (fun b16 _ => Finset.sum_congr rfl (fun b21 _ => Finset.sum_congr rfl (fun b22 _ => ?_))))
    rw [show (∑ b23, ∑ b14, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)))) = (∑ b23, ∑ b14, cg b14 j * ig b14 b23 * ((1 / 2 : ℝ) * dig i b15 b16 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)) from Finset.sum_congr rfl (fun b23 _ => Finset.sum_congr rfl (fun b14 _ => by ring))]
    exact collapse ig cg hcol (fun b23 => (1 / 2 : ℝ) * dig i b15 b16 * f b23 b22 * ig b22 b21 * gb b15 b16 b21) j
  rw [hstep]
  exact nf_O0_h18' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h19 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (dig i b14 b26 * f b26 b25 * ig b25 b24 * gb b15 b16 b24)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * dig i a b * f b c * gb d e r * ig c r * ig d e) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [hcgs a j]
  try ring

private lemma nf_O0_h20' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b15, ∑ b16, ∑ b24, ∑ b25, (1 / 2 : ℝ) * ig b15 b16 * f j b25 * dig i b25 b24 * gb b15 b16 b24) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h20 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d) := by
  have hstep : (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)))) =
      (∑ b15, ∑ b16, ∑ b24, ∑ b25, (1 / 2 : ℝ) * ig b15 b16 * f j b25 * dig i b25 b24 * gb b15 b16 b24) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b15 _ => Finset.sum_congr rfl (fun b16 _ => Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => ?_))))
    rw [show (∑ b26, ∑ b14, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)))) = (∑ b26, ∑ b14, cg b14 j * ig b14 b26 * ((1 / 2 : ℝ) * ig b15 b16 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)) from Finset.sum_congr rfl (fun b26 _ => Finset.sum_congr rfl (fun b14 _ => by ring))]
    exact collapse ig cg hcol (fun b26 => (1 / 2 : ℝ) * ig b15 b16 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24) j
  rw [hstep]
  exact nf_O0_h20' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h21' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b15, ∑ b16, ∑ b24, ∑ b27, (1 / 2 : ℝ) * ig b15 b16 * f j b27 * ig b27 b24 * dgb i b15 b16 b24) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c]
  try ring

private lemma nf_O0_h21 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d) := by
  have hstep : (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)))) =
      (∑ b15, ∑ b16, ∑ b24, ∑ b27, (1 / 2 : ℝ) * ig b15 b16 * f j b27 * ig b27 b24 * dgb i b15 b16 b24) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b15 _ => Finset.sum_congr rfl (fun b16 _ => Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b27 _ => ?_))))
    rw [show (∑ b28, ∑ b14, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)))) = (∑ b28, ∑ b14, cg b14 j * ig b14 b28 * ((1 / 2 : ℝ) * ig b15 b16 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)) from Finset.sum_congr rfl (fun b28 _ => Finset.sum_congr rfl (fun b14 _ => by ring))]
    exact collapse ig cg hcol (fun b28 => (1 / 2 : ℝ) * ig b15 b16 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24) j
  rw [hstep]
  exact nf_O0_h21' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h22 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * ga1 b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdigs j c b]
  try ring

private lemma nf_O0_h23 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * ga1 b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e d, hfs d b, hga1s e c a]
  try ring

private lemma nf_O0_h24 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * gbg b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdigs j c b]
  try ring

private lemma nf_O0_h25 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * gbg b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e d, hfs d b, hgbgs e c a]
  try ring

private lemma nf_O0_h26 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dga1 j b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e c]
  try ring

private lemma nf_O0_h27 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dgbg j b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e c]
  try ring

private lemma nf_O0_h28' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b30, ∑ b31, ∑ b36, ∑ b37, (1 / 2 : ℝ) * dig j b30 b31 * f i b37 * ig b37 b36 * gb b30 b31 b36) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h28 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d) := by
  have hstep : (∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)))) =
      (∑ b30, ∑ b31, ∑ b36, ∑ b37, (1 / 2 : ℝ) * dig j b30 b31 * f i b37 * ig b37 b36 * gb b30 b31 b36) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b31 _ => Finset.sum_congr rfl (fun b36 _ => Finset.sum_congr rfl (fun b37 _ => ?_))))
    rw [show (∑ b38, ∑ b29, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)))) = (∑ b38, ∑ b29, cg b29 i * ig b29 b38 * ((1 / 2 : ℝ) * dig j b30 b31 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)) from Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b29 _ => by rw [hcgs i b29]; try ring))]
    exact collapse ig cg hcol (fun b38 => (1 / 2 : ℝ) * dig j b30 b31 * f b38 b37 * ig b37 b36 * gb b30 b31 b36) i
  rw [hstep]
  exact nf_O0_h28' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h29 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (dig j b29 b41 * f b41 b40 * ig b40 b39 * gb b30 b31 b39)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * dig j a b * f b c * gb d e r * ig c r * ig d e) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  ring

private lemma nf_O0_h30' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b30, ∑ b31, ∑ b39, ∑ b40, (1 / 2 : ℝ) * ig b30 b31 * f i b40 * dig j b40 b39 * gb b30 b31 b39) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h30 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d) := by
  have hstep : (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)))) =
      (∑ b30, ∑ b31, ∑ b39, ∑ b40, (1 / 2 : ℝ) * ig b30 b31 * f i b40 * dig j b40 b39 * gb b30 b31 b39) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b31 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b40 _ => ?_))))
    rw [show (∑ b41, ∑ b29, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)))) = (∑ b41, ∑ b29, cg b29 i * ig b29 b41 * ((1 / 2 : ℝ) * ig b30 b31 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)) from Finset.sum_congr rfl (fun b41 _ => Finset.sum_congr rfl (fun b29 _ => by rw [hcgs i b29]; try ring))]
    exact collapse ig cg hcol (fun b41 => (1 / 2 : ℝ) * ig b30 b31 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39) i
  rw [hstep]
  exact nf_O0_h30' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h31' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b30, ∑ b31, ∑ b39, ∑ b42, (1 / 2 : ℝ) * ig b30 b31 * f i b42 * ig b42 b39 * dgb j b30 b31 b39) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c]
  try ring

private lemma nf_O0_h31 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d) := by
  have hstep : (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)))) =
      (∑ b30, ∑ b31, ∑ b39, ∑ b42, (1 / 2 : ℝ) * ig b30 b31 * f i b42 * ig b42 b39 * dgb j b30 b31 b39) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b31 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => ?_))))
    rw [show (∑ b43, ∑ b29, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)))) = (∑ b43, ∑ b29, cg b29 i * ig b29 b43 * ((1 / 2 : ℝ) * ig b30 b31 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)) from Finset.sum_congr rfl (fun b43 _ => Finset.sum_congr rfl (fun b29 _ => by rw [hcgs i b29]; try ring))]
    exact collapse ig cg hcol (fun b43 => (1 / 2 : ℝ) * ig b30 b31 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39) i
  rw [hstep]
  exact nf_O0_h31' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j


theorem nf_o0 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
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
    o0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * dig j a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * dig i a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * ga1 d e a * ig b d * ig c e))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, dg a i j * f b c * gb d e r * ig a b * ig c r * ig d e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * gbg d e a * ig b d * ig c e)
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c)) := by
  have h1 : o0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      -(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * ga1 b1 b2 b0 * dg b0 i j) - (-(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * gbg b1 b2 b0 * dg b0 i j)) + (-(∑ b0, ∑ b1, ∑ b2, ∑ b5, ∑ b6, ∑ b7, ig b1 b2 * ((1 / 2 : ℝ) * (ig b0 b7 * f b7 b6 * ig b6 b5 * gb b1 b2 b5)) * dg b0 i j)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * ga1 b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * gbg b9 b10 b8)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dga1 i b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dgbg i b9 b10 b8)))) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * ga1 b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * gbg b12 b13 b11)) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dga1 j b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dgbg j b12 b13 b11)))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * ga1 b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * ga1 b15 b16 b14))) - (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * gbg b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * gbg b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dga1 i b15 b16 b14)) - (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dgbg i b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21))))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (dig i b14 b26 * f b26 b25 * ig b25 b24 * gb b15 b16 b24)))) + (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24))))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24))))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * ga1 b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * ga1 b30 b31 b29))) - (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * gbg b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * gbg b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dga1 j b30 b31 b29)) - (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dgbg j b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (dig j b29 b41 * f b41 b40 * ig b40 b39 * gb b30 b31 b39)))) + (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39))))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39))))))) := by
    simp only [o0F, wcF, d0F, dvfbF, chrCorrF]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * ga1 b1 b2 b0 * dg b0 i j) - (-(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * gbg b1 b2 b0 * dg b0 i j)) + (-(∑ b0, ∑ b1, ∑ b2, ∑ b5, ∑ b6, ∑ b7, ig b1 b2 * ((1 / 2 : ℝ) * (ig b0 b7 * f b7 b6 * ig b6 b5 * gb b1 b2 b5)) * dg b0 i j)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * ga1 b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * gbg b9 b10 b8)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dga1 i b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dgbg i b9 b10 b8)))) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * ga1 b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * gbg b12 b13 b11)) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dga1 j b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dgbg j b12 b13 b11)))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * ga1 b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * ga1 b15 b16 b14))) - (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * gbg b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * gbg b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dga1 i b15 b16 b14)) - (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dgbg i b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21))))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (dig i b14 b26 * f b26 b25 * ig b25 b24 * gb b15 b16 b24)))) + (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24))))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24))))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * ga1 b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * ga1 b30 b31 b29))) - (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * gbg b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * gbg b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dga1 j b30 b31 b29)) - (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dgbg j b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (dig j b29 b41 * f b41 b40 * ig b40 b39 * gb b30 b31 b39)))) + (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39))))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39))))))) =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * dig j a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * dig i a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * ga1 d e a * ig b d * ig c e))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, dg a i j * f b c * gb d e r * ig a b * ig c r * ig d e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * gbg d e a * ig b d * ig c e)
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c)) := by
    linear_combination - nf_O0_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h13 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h14 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h15 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h16 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h17 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h18 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h19 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h20 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h21 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h22 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h23 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h24 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h25 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h26 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h27 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h28 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h29 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h30 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h31 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieCorr0NF
