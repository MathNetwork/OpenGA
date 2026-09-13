import Definitions.Def_OpenGA_WidthComparisonData

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open OpenGA

theorem OpenGA.eventually_width_slope_lt_of_comparison
    {width : ℝ → ℝ} {time scalar : ℝ}
    (data : WidthComparisonData width time scalar) (q : ℝ)
    (hq : -(4 * Real.pi) - scalar / 2 * width time < q) :
    ∀ᶠ s in 𝓝[>] time, slope width time s < q := by sorry
