import Theorems.Thm_PoincareFormalization_measured_surgery_data_of_not_homeomorph_sphere
import Theorems.Thm_OpenGA_nonempty_surgeryComparisonProcess_of_measuredData
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Definitions.Def_OpenGA_SurgeryComparisonProcess
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

theorem solution
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (hnot : ¬ Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))) :
    ∃ initialWidth : ℝ, 0 ≤ initialWidth ∧ ∀ finalTime : ℝ, 0 < finalTime →
      Nonempty (OpenGA.SurgeryComparisonProcess initialWidth finalTime) := by
  obtain ⟨W, hW, hdata⟩ := PoincareFormalization.measured_surgery_data_of_not_homeomorph_sphere M hnot
  refine ⟨W, hW, ?_⟩
  intro T hT
  obtain ⟨D⟩ := hdata T hT
  exact OpenGA.nonempty_surgeryComparisonProcess_of_measuredData D
