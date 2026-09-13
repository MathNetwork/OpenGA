import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Definitions.Def_OpenGA_AreaEnergyDensities

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
open OpenGA

theorem OpenGA.areaDensity_eq_energyDensity_iff (v w : F) :
    areaDensity v w = energyDensity v w ↔ ⟪v, w⟫_ℝ = 0 ∧ ‖v‖ = ‖w‖ := by sorry
