import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivita
import DifferentialGeometry.Geometry.Connection.MLieBracket
import DifferentialGeometry.Geometry.Connection.LeviCivita.PullbackConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling








namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]













omit [NeZero (Module.finrank ℝ E)] in
theorem riemann_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
