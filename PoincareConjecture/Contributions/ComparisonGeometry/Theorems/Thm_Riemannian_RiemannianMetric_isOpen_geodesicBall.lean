import Definitions.Def_OpenGA_GeodesicBall
import Mathlib.Geometry.Manifold.Metrizable

noncomputable section
set_option autoImplicit false

open Bundle Set DifferentialGeometry
open scoped Manifold ContDiff ENNReal

open Riemannian Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem Riemannian.RiemannianMetric.isOpen_geodesicBall [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    IsOpen (g.geodesicBall p r) := by sorry
