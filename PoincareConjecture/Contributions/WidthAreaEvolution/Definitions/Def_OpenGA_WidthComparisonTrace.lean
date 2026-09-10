import Definitions.Def_OpenGA_WidthComparisonData
import Definitions.Def_OpenGA_ScalarWidthTrace

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace OpenGA

/-- Finite scalar and width data with area-energy comparison witnesses in
place of an assumed width slope bound. This is an analytic interface, not a
definition of Ricci flow, surgery, or a geometric sweepout. -/
structure WidthComparisonTrace (initialWidth finalTime : ℝ) where
  count : ℕ
  count_pos : 0 < count
  times : ℕ → ℝ
  first_time : times 0 = 0
  last_time : times count = finalTime
  times_strict : ∀ i < count, times i < times (i + 1)
  scalar : ℕ → ℝ → ℝ
  width : ℕ → ℝ → ℝ
  scalar_cont : ∀ i < count, ContinuousOn (scalar i) (Icc (times i) (times (i + 1)))
  width_cont : ∀ i < count, ContinuousOn (width i) (Icc (times i) (times (i + 1)))
  scalar_initial : -6 ≤ scalar 0 (times 0)
  width_initial : width 0 (times 0) ≤ initialWidth
  width_nonneg : ∀ i < count, ∀ t ∈ Icc (times i) (times (i + 1)), 0 ≤ width i t
  scalar_slope : ∀ i < count, ∀ t ∈ Ico (times i) (times (i + 1)), ∀ q : ℝ,
    q < (2 / 3 : ℝ) * (scalar i t) ^ 2 →
      ∀ᶠ s in 𝓝[>] t, q < slope (scalar i) t s
  comparison : ∀ i < count, ∀ t ∈ Ico (times i) (times (i + 1)),
    Nonempty (WidthComparisonData (width i) t (scalar i t))
  scalar_jump : ∀ i, i + 1 < count →
    scalar i (times (i + 1)) ≤ scalar (i + 1) (times (i + 1))
  width_jump : ∀ i, i + 1 < count →
    width (i + 1) (times (i + 1)) ≤ width i (times (i + 1))

end OpenGA
