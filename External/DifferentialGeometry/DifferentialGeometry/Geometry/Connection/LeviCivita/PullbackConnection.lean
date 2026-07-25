import DifferentialGeometry.Geometry.Metric.Defs
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

noncomputable def pullback_connection_construct
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_connection_torsion_free
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    (pullback_connection_construct g Φ).torsion = 0 :=
  LeviCivita_torsion_eq_zero (I := I) (Diffeomorph.pullbackMetric g Φ)

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_connection_metric_compatible
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    IsMetricCompatible (pullback_connection_construct g Φ)
      (Diffeomorph.pullbackMetric g Φ) :=
  LeviCivita_isMetricCompatible (I := I) (Diffeomorph.pullbackMetric g Φ)

end DifferentialGeometry.PDE.RicciFlow.Pullback
