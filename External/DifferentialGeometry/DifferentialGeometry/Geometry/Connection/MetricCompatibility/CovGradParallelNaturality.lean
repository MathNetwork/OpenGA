import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapSecondGradientL2Bound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def unitZeroSec :
    Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
  ⟨fun _ : M => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
    contMDiff_unitZeroSection (I := I) (M := M)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma unitZeroSec_apply (y : M) :
    unitZeroSec (I := I) (M := M) y =
      Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_apply_unit_eval
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (y : M)
    (v : Fin 3 → TangentSpace I y) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
          (unitZeroSec (I := I) (M := M) y)) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (v 0))
          (unitZeroSec (I := I) (M := M) y))
        (Matrix.vecTail v) := by
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 2 T₀ y
    (unitZeroSec (I := I) (M := M) y) v

omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_covDeriv_at_unit_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
            (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) (covGrad (I := I) (M := M) g 0 2 T₀).toSection
    (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

end Connection
end Integral
end DifferentialGeometry

end
