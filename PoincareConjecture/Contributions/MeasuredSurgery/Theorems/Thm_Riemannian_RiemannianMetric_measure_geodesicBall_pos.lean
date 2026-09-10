import Definitions.Def_OpenGA_GeodesicBall
import Mathlib.MeasureTheory.Measure.Restrict
noncomputable section
set_option autoImplicit false
open Bundle Set DifferentialGeometry MeasureTheory
open scoped Manifold ContDiff ENNReal
open Riemannian Riemannian.RiemannianMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {μ : Measure M}


theorem Riemannian.RiemannianMetric.measure_geodesicBall_pos
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) {r : ℝ}
    (hμ : ∀ s : Set M, IsOpen s → s.Nonempty → 0 < μ s)
    (hopen : IsOpen (g.geodesicBall p r)) (hr : 0 < r) :
    0 < μ (g.geodesicBall p r) := by sorry
