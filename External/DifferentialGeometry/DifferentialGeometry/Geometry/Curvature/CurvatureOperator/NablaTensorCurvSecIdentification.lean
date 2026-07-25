import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    nablaTensorCurvSec (I := I) g
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Y b) (fun b => Z b) A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x :=
  rfl

omit [CompleteSpace E] in
theorem nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        nablaTensorCurvSec (I := I) g
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun b => Z b) A x =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A x :=
  Finset.sum_congr rfl fun i _ =>
    nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv (I := I) g s
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) Z A x

end Connection
end Integral
end DifferentialGeometry
