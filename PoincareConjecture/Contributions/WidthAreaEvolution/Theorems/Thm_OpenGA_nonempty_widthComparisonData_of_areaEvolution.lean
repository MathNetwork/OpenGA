import Definitions.Def_OpenGA_WidthAreaEvolutionData
set_option autoImplicit false
open Set Filter
open scoped Topology
open OpenGA


theorem OpenGA.nonempty_widthComparisonData_of_areaEvolution {width : ℝ → ℝ} {time scalar : ℝ}
    (D : WidthAreaEvolutionData width time scalar) :
    Nonempty (WidthComparisonData width time scalar) := by sorry
