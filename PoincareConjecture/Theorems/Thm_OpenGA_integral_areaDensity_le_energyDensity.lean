import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Definitions.Def_OpenGA_AreaEnergyDensities

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v w : X → F}
open OpenGA

theorem OpenGA.integral_areaDensity_le_energyDensity (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ)
    (hE : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    (∫ x, areaDensity (v x) (w x) ∂μ) ≤ ∫ x, energyDensity (v x) (w x) ∂μ := by sorry
