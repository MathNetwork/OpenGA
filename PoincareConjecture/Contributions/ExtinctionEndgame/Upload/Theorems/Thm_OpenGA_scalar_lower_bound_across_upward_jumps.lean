import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Topology

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
      -(6 : ℝ) / (1 + 4 * t) ≤ profiles i t := by sorry
