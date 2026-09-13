import OpenGALib.Analysis.ComparisonTrace
import OpenGALib.Analysis.ScalarLowerBound
import OpenGALib.Analysis.WidthExtinction

/-!
# The lifetime bound for scalar and width comparison traces

This packages the existing scalar lower bound, area-energy width comparison,
and finite-jump deadline into one reusable theorem. No geometric existence
claim is made: the trace is an explicit input.
-/

namespace OpenGA

open Set Filter
open scoped Topology

/-- **Math.** A normalized finite scalar/width comparison trace cannot
extend beyond the Colding-Minicozzi deadline. -/
theorem WidthComparisonTrace.le_extinctionTime {W T : ℝ} (F : WidthComparisonTrace W T) :
    T ≤ widthExtinctionTime (1 / 4) W := by
  have hscalar := scalar_lower_bound_across_upward_jumps
    F.count F.count_pos F.times F.scalar F.first_time F.times_strict
    F.scalar_cont F.scalar_initial F.scalar_slope F.scalar_jump
  have hslope : ∀ i < F.count, ∀ x ∈ Ico (F.times i) (F.times (i + 1)), ∀ q : ℝ,
      -(4 * Real.pi) + 3 / (4 * (x + (1 / 4 : ℝ))) * F.width i x < q →
        ∃ᶠ s in 𝓝[>] x, slope (F.width i) x s < q := by
    intro i hi x hx q hq
    obtain ⟨data⟩ := F.comparison i hi x hx
    apply (eventually_width_slope_lt_of_comparison data q ?_).frequently
    have hs := hscalar i hi x (Ico_subset_Icc_self hx)
    have hw := F.width_nonneg i hi x (Ico_subset_Icc_self hx)
    have hm := mul_le_mul_of_nonneg_right hs hw
    have hid : (-(6 : ℝ) / (1 + 4 * x)) * F.width i x / 2 =
        -(3 / (4 * (x + (1 / 4 : ℝ))) * F.width i x) := by
      have hden : 1 + 4 * x = 4 * (x + (1 / 4 : ℝ)) := by ring
      rw [hden]
      ring
    nlinarith
  have hlast : F.count - 1 + 1 = F.count := by have := F.count_pos; omega
  have hfinal : 0 ≤ F.width (F.count - 1) (F.times F.count) := by
    apply F.width_nonneg (F.count - 1) (by have := F.count_pos; omega)
    constructor
    · simpa [hlast] using (F.times_strict (F.count - 1) (by have := F.count_pos; omega)).le
    · simp [hlast]
  have hbound := le_widthExtinctionTime_across_downward_jumps
    (C := (1 / 4 : ℝ)) (W₀ := W) (by norm_num)
    F.count F.count_pos F.times F.width F.first_time F.times_strict
    F.width_cont F.width_initial hfinal hslope F.width_jump
  simpa only [F.last_time] using hbound

end OpenGA
