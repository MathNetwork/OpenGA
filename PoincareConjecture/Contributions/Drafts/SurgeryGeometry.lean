import OpenGALib.Analysis.SurgeryComparison
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

namespace PoincareFormalization

/-- Open geometric construction for the volume-controlled width route.
The process records analytic inputs; producing them from the manifold still
requires smoothability, normalized surgery flow, uniform radial comparison
and volume budgets, and geometric sweepout comparison. -/
theorem surgery_comparison_process_of_not_homeomorph_sphere
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (hnot : ¬ Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))) :
    ∃ initialWidth : ℝ, 0 ≤ initialWidth ∧ ∀ finalTime : ℝ, 0 < finalTime →
      Nonempty (OpenGA.SurgeryComparisonProcess initialWidth finalTime) := by
  sorry

/-- The finite-trace construction follows from the geometric process and the
proved volume-loss nonaccumulation argument. Only the geometric child is open. -/
theorem comparison_trace_of_surgery_geometry
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

end PoincareFormalization
