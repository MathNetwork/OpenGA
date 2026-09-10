import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_CotangentRiemannian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_TangentMetric
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Riemannian

set_option autoImplicit false

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def cotangentToCLMGen {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real :=
  continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) 1 x α)

def cotangentToDualGen {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLMGen (I := I) α).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDual_apply_gen {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDualGen (I := I) α X = α (fun _ : Fin 1 => X) := by
  let hM : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  change continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
      (@tensor0SSpaceFiberContinuousLinearEquiv Real _ E _ _ H _ I M _ _ hM 1 x α) X =
      α (fun _ : Fin 1 => X)
  rw [continuousMultilinearCurryFin1_apply,
    @tensor0SSpaceFiberContinuousLinearEquiv_apply Real _ E _ _ H _ I M _ _ hM]
  congr 1

def dualToCotangentGen {x : M} (α : Module.Dual Real (TangentSpace I x)) :
    Tensor0SSpace 1 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (LinearMap.toContinuousLinearMap α))

@[simp] theorem dualToCotangent_apply_gen {x : M}
    (α : Module.Dual Real (TangentSpace I x)) (X : TangentSpace I x) :
    Tensor0SSpace.eval (dualToCotangentGen (I := I) α) (fun _ : Fin 1 => X) = α X := by
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (LinearMap.toContinuousLinearMap α)) (fun _ : Fin 1 => X) = α X
  rfl

@[simp] theorem cotangentToDual_dualToCotangent_gen {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    cotangentToDualGen (I := I) (dualToCotangentGen (I := I) α) = α := by
  ext X
  change Tensor0SSpace.eval (dualToCotangentGen (I := I) α) (fun _ : Fin 1 => X) = α X
  exact dualToCotangent_apply_gen α X

end

end Tensor0SBundle

end DifferentialGeometry
