import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannSec_tensorCov_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) b (A b)))
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (fun b => X b) (fun b => W b) A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) :=
  riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g s X W A hA x u

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem smoothOrthoFrame_riemannOp_trace_eq_ricci
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x
          (smoothOrthoFrame (I := I) g x i x) v w)
          (smoothOrthoFrame (I := I) g x i x) =
      ricciTensor (I := I) g x v w :=
  (ricciTensor_eq_orthonormal_trace (I := I) g x v w
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)).symm

end Connection
end Integral
end DifferentialGeometry

end
