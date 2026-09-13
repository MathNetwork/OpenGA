import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

open Set Topology
open scoped Topology

theorem OpenGA.le_width_deadline_across_downward_jumps
    {C W₀ : ℝ} (hC : 0 < C)
    (n : ℕ) (hn : 0 < n) (times : ℕ → ℝ) (widths : ℕ → ℝ → ℝ)
    (hzero : times 0 = 0)
    (htimes : ∀ i < n, times i < times (i + 1))
    (hcont : ∀ i < n, ContinuousOn (widths i) (Icc (times i) (times (i + 1))))
    (hinitial : widths 0 (times 0) ≤ W₀)
    (hfinal : 0 ≤ widths (n - 1) (times n))
    (hslope : ∀ i < n, ∀ x ∈ Ico (times i) (times (i + 1)), ∀ r : ℝ,
      -(4 * Real.pi) + 3 / (4 * (x + C)) * widths i x < r →
        ∃ᶠ z in 𝓝[>] x, slope (widths i) x z < r)
    (hjumps : ∀ i, i + 1 < n →
      widths (i + 1) (times (i + 1)) ≤ widths i (times (i + 1))) :
    times n ≤ (C ^ ((1 : ℝ) / 4) + W₀ / (16 * Real.pi * C ^ ((3 : ℝ) / 4))) ^ (4 : ℕ) - C := by sorry
