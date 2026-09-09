import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar lower bounds across upward jumps

The normalized lower bound `-6 / (1 + 4 * t)` is preserved by the scalar
differential inequality on continuous time intervals and by upward jumps.
The proof uses a strict comparison function, then induction over the intervals.

This formalizes the analytic comparison step in Kleiner-Lott, *Notes on
Perelman's Papers*, arXiv:math/0605667v5, proof of Lemma 79.11 (p. 154),
using Appendix B, equations (B.1)-(B.2) (p. 202). The connection to the
scalar-curvature minimum of a geometric Ricci flow is a separate task.
Source: https://arxiv.org/pdf/math/0605667v5#page=154
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace OpenGA

/-- **Eng.** Derivative of the perturbed upper comparison function for the negative profile. -/
private lemma scalar_barrier_hasDerivAt (ε x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => 6 / (1 + 4 * t) + ε)
      (-(24 : ℝ) / (1 + 4 * x) ^ 2) x := by
  have hd : HasDerivAt (fun t : ℝ => 1 + 4 * t) 4 x := by
    simpa using ((hasDerivAt_id x).const_mul (4 : ℝ)).const_add (1 : ℝ)
  have hden : 1 + 4 * x ≠ 0 := ne_of_gt (by linarith)
  convert! ((hasDerivAt_const x (6 : ℝ)).fun_div hd hden).add_const ε using 1
  norm_num

/-- **Math.** The normalized scalar lower bound on one continuous time interval.
The lower right Dini derivative is expressed using eventual slope bounds. -/
theorem scalar_lower_bound_on_interval {a b : ℝ} {f : ℝ → ℝ}
    (ha : 0 ≤ a) (hf : ContinuousOn f (Icc a b))
    (hinitial : -(6 : ℝ) / (1 + 4 * a) ≤ f a)
    (hslope : ∀ t ∈ Ico a b, ∀ q : ℝ,
      q < (2 / 3 : ℝ) * (f t) ^ 2 → ∀ᶠ s in 𝓝[>] t, q < slope f t s) :
    ∀ t ∈ Icc a b, -(6 : ℝ) / (1 + 4 * t) ≤ f t := by
  have hneg : ∀ x ∈ Ico a b, ∀ r : ℝ,
      -((2 / 3 : ℝ) * (f x) ^ 2) < r →
        ∃ᶠ s in 𝓝[>] x, slope (fun t => -f t) x s < r := by
    intro x hx r hr
    have h := hslope x hx (-r) (by linarith)
    apply Filter.Eventually.frequently
    filter_upwards [h] with s hs
    rw [slope_neg]
    linarith
  have hbound : ∀ ε > (0 : ℝ), ∀ t ∈ Icc a b,
      -f t ≤ 6 / (1 + 4 * t) + ε := by
    intro ε hε t ht
    apply image_le_of_liminf_slope_right_lt_deriv_boundary'
      (f := fun t => -f t) (f' := fun t => -((2 / 3 : ℝ) * (f t) ^ 2))
      hf.neg hneg (B := fun t => 6 / (1 + 4 * t) + ε)
      (B' := fun t => -(24 : ℝ) / (1 + 4 * t) ^ 2) ?_ ?_ ?_ ?_ ht
    · rw [neg_div] at hinitial
      linarith
    · intro x hx
      exact (scalar_barrier_hasDerivAt ε x (ha.trans hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      exact (scalar_barrier_hasDerivAt ε x (ha.trans hx.1)).hasDerivWithinAt
    · intro x hx hcontact
      have hden : 0 < 1 + 4 * x := by
        have := ha.trans hx.1
        linarith
      have hpos : 0 < (6 : ℝ) / (1 + 4 * x) := div_pos (by norm_num) hden
      have hid : (24 : ℝ) / (1 + 4 * x) ^ 2 =
          (2 / 3 : ℝ) * (6 / (1 + 4 * x)) ^ 2 := by
        field_simp
        ring
      have hvalue : f x = -(6 / (1 + 4 * x) + ε) := by linarith
      rw [neg_div, hid, hvalue, neg_sq]
      nlinarith [mul_pos hpos hε, sq_nonneg ε]
  intro t ht
  have hle : -f t ≤ (6 : ℝ) / (1 + 4 * t) := by
    by_contra! hlt
    have := hbound ((-f t - 6 / (1 + 4 * t)) / 2) (by linarith) t ht
    linarith
  rw [neg_div]
  linarith

end OpenGA

/-- **Math.** A finite sequence of continuous profiles satisfying the normalized scalar
differential inequality, joined by upward jumps, stays above `-6 / (1 + 4 * t)`.
Both endpoint values at every joining time satisfy the bound. -/
theorem OpenGA.scalar_lower_bound_across_upward_jumps
    (n : ℕ) (hn : 0 < n) (times : ℕ → ℝ) (profiles : ℕ → ℝ → ℝ)
    (hzero : times 0 = 0)
    (htimes : ∀ i < n, times i < times (i + 1))
    (hcont : ∀ i < n, ContinuousOn (profiles i) (Icc (times i) (times (i + 1))))
    (hinitial : -6 ≤ profiles 0 (times 0))
    (hslope : ∀ i < n, ∀ t ∈ Ico (times i) (times (i + 1)), ∀ q : ℝ,
      q < (2 / 3 : ℝ) * (profiles i t) ^ 2 →
        ∀ᶠ s in 𝓝[>] t, q < slope (profiles i) t s)
    (hjumps : ∀ i, i + 1 < n →
      profiles i (times (i + 1)) ≤ profiles (i + 1) (times (i + 1))) :
    ∀ i < n, ∀ t ∈ Icc (times i) (times (i + 1)),
      -(6 : ℝ) / (1 + 4 * t) ≤ profiles i t := by
  have hnonneg : ∀ i ≤ n, 0 ≤ times i := by
    intro i
    induction i with
    | zero => intro _; simp [hzero]
    | succ i ih =>
      intro hi
      exact (ih (by omega)).trans (htimes i (by omega)).le
  have hfirst := OpenGA.scalar_lower_bound_on_interval
    (by simp [hzero] : 0 ≤ times 0) (hcont 0 hn)
    (by simpa [hzero] using hinitial) (hslope 0 hn)
  intro i
  induction i with
  | zero => intro _; exact hfirst
  | succ i ih =>
    intro hi
    have hprev : i < n := by omega
    have hstart := (ih hprev (times (i + 1)) ⟨(htimes i hprev).le, le_rfl⟩).trans
      (hjumps i hi)
    exact OpenGA.scalar_lower_bound_on_interval (hnonneg (i + 1) (by omega))
      (hcont (i + 1) hi) hstart (hslope (i + 1) hi)
