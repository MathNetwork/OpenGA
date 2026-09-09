import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace OpenGA

/-- Finite analytic data for the scalar-minimum and width argument on `[0, T]`.
This structure records inequalities and jumps only. It is not a definition of
Ricci flow, surgery, scalar curvature, or sweepout width. Supplying it from
geometric data is a separate theorem. -/
structure ScalarWidthTrace (W₀ T : ℝ) where
  count : ℕ
  count_pos : 0 < count
  times : ℕ → ℝ
  first_time : times 0 = 0
  last_time : times count = T
  times_strict : ∀ i < count, times i < times (i + 1)
  scalar : ℕ → ℝ → ℝ
  width : ℕ → ℝ → ℝ
  scalar_cont : ∀ i < count, ContinuousOn (scalar i) (Icc (times i) (times (i + 1)))
  width_cont : ∀ i < count, ContinuousOn (width i) (Icc (times i) (times (i + 1)))
  scalar_initial : -6 ≤ scalar 0 (times 0)
  width_initial : width 0 (times 0) ≤ W₀
  width_nonneg : ∀ i < count, ∀ t ∈ Icc (times i) (times (i + 1)), 0 ≤ width i t
  scalar_slope : ∀ i < count, ∀ t ∈ Ico (times i) (times (i + 1)), ∀ q : ℝ,
    q < (2 / 3 : ℝ) * (scalar i t) ^ 2 →
      ∀ᶠ s in 𝓝[>] t, q < slope (scalar i) t s
  width_slope : ∀ i < count, ∀ t ∈ Ico (times i) (times (i + 1)), ∀ q : ℝ,
    -(4 * Real.pi) - scalar i t / 2 * width i t < q →
      ∃ᶠ s in 𝓝[>] t, slope (width i) t s < q
  scalar_jump : ∀ i, i + 1 < count →
    scalar i (times (i + 1)) ≤ scalar (i + 1) (times (i + 1))
  width_jump : ∀ i, i + 1 < count →
    width (i + 1) (times (i + 1)) ≤ width i (times (i + 1))

end OpenGA
