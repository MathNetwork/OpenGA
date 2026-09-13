import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Riemannian
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_CotangentRiemannian
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_CotangentRiemannian
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_TangentMetric

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

variable [FiniteDimensional Real E]

variable {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev Tensor13Section :=
  TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 1 3

abbrev Tensor04Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 4

abbrev Tensor02Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 2

abbrev Tensor02At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x

abbrev Tensor04At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

abbrev Tensor13At (x : M) :=
  TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x

def scalarOne0S (x : M) : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 0 x :=
  ContinuousMultilinearMap.constOfIsEmpty Real
    (fun _ : Fin 0 => TangentSpace I x) 1

def ricciFromRm13At {x : M} (Rm13 : Tensor13At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  (contractTrace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
    (scalarOne0S (I := I) x)

def vec2 {x : M} (X Y : TangentSpace I x) : Fin 2 -> TangentSpace I x :=
  fun i => if i = 0 then X else Y

def vec3 {x : M} (X Y Z : TangentSpace I x) : Fin 3 -> TangentSpace I x :=
  fun i => if i = 0 then X else if i = 1 then Y else Z

def vec4 {x : M} (W X Y Z : TangentSpace I x) : Fin 4 -> TangentSpace I x :=
  fun i => if i = 0 then W else if i = 1 then X else if i = 2 then Y else Z

def tensor04StdToOutPerm : Equiv.Perm (Fin 4) where
  toFun i := if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else 2
  invFun i := if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0
  left_inv i := by
    fin_cases i <;> simp
  right_inv i := by
    fin_cases i <;> simp

def tensor04StdOfOutAt {x : M} (Rm04Out : Tensor04At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  Rm04Out.domDomCongr tensor04StdToOutPerm

omit [FiniteDimensional ℝ E] in
@[simp]
theorem tensor04StdOfOutAt_apply
    {x : M} (Rm04Out : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StdOfOutAt (I := I) (M := M) Rm04Out (vec4 X Y Z W) =
      Rm04Out (vec4 W X Y Z) := by
  change Rm04Out (fun i => (vec4 X Y Z W) (tensor04StdToOutPerm i)) =
    Rm04Out (vec4 W X Y Z)
  congr 1
  funext i
  fin_cases i <;> simp [tensor04StdToOutPerm, vec4]

end DifferentialGeometry.Geometry.Curvature

end
