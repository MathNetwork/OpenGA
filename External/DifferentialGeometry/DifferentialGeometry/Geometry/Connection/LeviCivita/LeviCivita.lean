import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.PullbackConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

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
theorem levi_civita_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem levi_civita_pullback_conjugation_symm
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    pullback_connection_construct g Φ
      = LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ) := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
