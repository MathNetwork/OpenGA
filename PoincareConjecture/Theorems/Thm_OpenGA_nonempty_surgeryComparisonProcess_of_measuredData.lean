import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open OpenGA


theorem OpenGA.nonempty_surgeryComparisonProcess_of_measuredData {W T : ℝ} (D : MeasuredSurgeryComparisonData W T) : Nonempty (SurgeryComparisonProcess W T) := by sorry
