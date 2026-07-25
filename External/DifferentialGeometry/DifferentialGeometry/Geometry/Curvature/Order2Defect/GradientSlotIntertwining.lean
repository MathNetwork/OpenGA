import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

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

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensor0S_curry_covGradBundleEquiv_unit
    (x : M) (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 2 I x)
    (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Φ v)
        (unitZeroSec (I := I) (M := M) x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
            (unitZeroSec (I := I) (M := M) x)) v) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v u) from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2) (b := x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
        (unitZeroSec (I := I) (M := M) x)) v u)]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 2 x Φ
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v u)]
  have hzero : (Fin.cons v u : Fin 3 → TangentSpace I x) 0 = v := by rw [Fin.cons_zero]
  have htail : Matrix.vecTail (Fin.cons v u : Fin 3 → TangentSpace I x) = u := by
    funext k; rw [Matrix.vecTail, Function.comp_apply, Fin.cons_succ]
  rw [hzero, htail]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGradBundleEquiv_tensorCov_unit_curry_eq_abstractCovDeriv
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          covGradBundleEquiv (I := I) (M := M) 0 2 x
            (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
              (fun y : M => σ y) x))
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  rw [tensor0S_curry_covGradBundleEquiv_unit (I := I) (M := M) x
    (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) (fun y : M => σ y) x) v]
  exact tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g 2 σ x v

end Connection
end Integral
end DifferentialGeometry

end
