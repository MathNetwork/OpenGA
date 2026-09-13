import OpenGALib.ComparisonGeometry.MetricBall
import Mathlib.MeasureTheory.Measure.Restrict

set_option autoImplicit false
open MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open Riemannian

/-- **Math.** An open-positive measure assigns positive measure to an open
positive-radius geodesic ball. The openness assumption can be discharged by
`RiemannianMetric.isOpen_geodesicBall`. -/
theorem Riemannian.RiemannianMetric.measure_geodesicBall_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {μ : Measure M}
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) {r : ℝ}
    (hμ : ∀ s : Set M, IsOpen s → s.Nonempty → 0 < μ s)
    (hopen : IsOpen (g.geodesicBall p r)) (hr : 0 < r) :
    0 < μ (g.geodesicBall p r) := by
  exact hμ _ hopen (g.geodesicBall_nonempty p hr)
