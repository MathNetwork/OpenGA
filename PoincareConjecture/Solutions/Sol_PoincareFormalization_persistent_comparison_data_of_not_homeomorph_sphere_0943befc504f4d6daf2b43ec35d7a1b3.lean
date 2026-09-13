import Definitions.Def_OpenGA_WidthComparisonTrace
import Theorems.Thm_PoincareFormalization_surgery_comparison_process_of_not_homeomorph_sphere
import Theorems.Thm_OpenGA_nonempty_widthComparisonTrace_of_surgeryComparisonProcess
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

open PoincareFormalization in
/-- The finite-trace construction follows from the geometric process and the
proved volume-loss nonaccumulation argument. Only the geometric child is open. -/
theorem solution
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (hnot : ¬ Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))) :
    ∃ initialWidth : ℝ, 0 ≤ initialWidth ∧ ∀ finalTime : ℝ, 0 < finalTime →
      Nonempty (OpenGA.WidthComparisonTrace initialWidth finalTime) := by
  obtain ⟨W, hW, hprocess⟩ := surgery_comparison_process_of_not_homeomorph_sphere M hnot
  refine ⟨W, hW, ?_⟩
  intro T hT
  obtain ⟨P⟩ := hprocess T hT
  exact OpenGA.nonempty_widthComparisonTrace_of_surgeryComparisonProcess P
