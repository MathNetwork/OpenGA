import Definitions.Def_OpenGA_RadialSurgeryVolumeBudget
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open OpenGA

theorem OpenGA.RadialSurgeryVolumeBudget.removedVolume_lower (B : RadialSurgeryVolumeBudget)
    {t : ℝ} (ht : t ∈ B.events) :
    B.anchor * hypRadVol B.modelParameter 2 B.removalRadius ≤ B.removedVolume t := by sorry
