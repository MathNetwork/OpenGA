import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivita
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciTrace
import DifferentialGeometry.Geometry.Connection.MLieBracket
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem ricci_tensor_pullback_natural_under_diffeomorphism
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (Diffeomorph.pullbackMetric g Φ) x v w
      = ricciTensor (I := I) g (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) :=
  ricciTensor_pullback_conjugation (I := I) g Φ x v w

end DifferentialGeometry.PDE.RicciFlow.Pullback
