import Definitions.Def_DifferentialGeometry_ModelRadialVolume
import Definitions.Def_DifferentialGeometry_RadialCrossComparison
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

namespace OpenGA

/-- **Math.** Uniform radial comparison data and a finite volume-loss budget.
No finiteness or discreteness is assumed for the set of event times. -/
structure RadialSurgeryVolumeBudget where
  events : Set ℝ
  modelParameter : ℝ
  modelParameter_nonneg : 0 ≤ modelParameter
  referenceRadius : ℝ
  removalRadius : ℝ
  removalRadius_pos : 0 < removalRadius
  radius_le : removalRadius ≤ referenceRadius
  anchor : ℝ
  anchor_pos : 0 < anchor
  totalBudget : ℝ
  density : ℝ → ℝ → ℝ≥0∞
  density_measurable : ∀ t ∈ events,
    AEMeasurable (density t) (volume.restrict (Ioc 0 referenceRadius))
  density_comparison : ∀ t ∈ events, CrossAnti referenceRadius (density t)
    (fun r => ENNReal.ofReal (hypDensity modelParameter 2 r))
  reference_lower : ∀ t ∈ events, ENNReal.ofReal anchor ≤
    (∫⁻ r in Ioc (0 : ℝ) referenceRadius, density t r) /
      ENNReal.ofReal (hypRadVol modelParameter 2 referenceRadius)
  removedVolume : ℝ → ℝ
  removedVolume_nonneg : ∀ t ∈ events, 0 ≤ removedVolume t
  removal_contains : ∀ t ∈ events,
    (∫⁻ r in Ioc (0 : ℝ) removalRadius, density t r) ≤ ENNReal.ofReal (removedVolume t)
  volume_budget : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ events →
    ∑ t ∈ s, removedVolume t ≤ totalBudget

end OpenGA
