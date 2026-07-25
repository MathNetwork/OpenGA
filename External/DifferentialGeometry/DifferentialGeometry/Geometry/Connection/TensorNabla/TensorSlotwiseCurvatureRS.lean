import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature


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

omit [I.Boundaryless] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem riemannSec_tensorCov_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (Y : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            riemannSec (tensorCov (I := I) g r s)
              (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x)) u =
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from τ b) (Y b)) x) u -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
            (riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
              (fun b => X b) (fun b => W b) (fun b => Y b) x)) u := by
  classical
  have hkey :=
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M
      (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
      (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
      (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
      (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      X W τ Y x

  have heq :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          riemannSec (tensorCov (I := I) g r s)
            (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x) =
        riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (HomConnectionGen.pairedSection (M := M)
              (U := fun x : M => Tensor0SSpace r I x) (V := fun x : M => Tensor0SSpace s I x)
              (fun b => τ b) (fun b => Y b)) x -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
            (riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
              (fun b => X b) (fun b => W b) (fun b => Y b) x) := hkey
  rw [heq, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rfl

end Connection
end Integral
end DifferentialGeometry

end
