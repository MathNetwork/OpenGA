import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false








noncomputable section

namespace Tensor0SBundle

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]



theorem connOut_norm_le
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothMetric_gen I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M} (alpha : Tensor0SSpace 1 I x) :
    Real.sqrt (normSq0S (I := I) g x 2
      (connectionDifferenceOutput (I := I)
        (CovariantDerivative.difference cov cov' x) alpha)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x)) *
        Real.sqrt (normSq0S (I := I) g x 1 alpha) := by
  change Real.sqrt (normSq0S (I := I) g x 2
      (connectionDifferenceTensorAt (I := I) cov cov' x alpha)) <= _
  exact sqrt_normSqRS_apply (I := I) g
    (connectionDifferenceTensorAt (I := I) cov cov' x) alpha

end Tensor0SBundle
