import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity










noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]





def RicciBoundedBelow (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
