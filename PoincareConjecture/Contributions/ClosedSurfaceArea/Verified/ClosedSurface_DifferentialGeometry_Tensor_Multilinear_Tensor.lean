import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Logic.Equiv.Fin.Basic
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
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

open DifferentialGeometry.Tensor.Multilinear

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {B : Type*} [TopologicalSpace B]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]

variable [TopologicalSpace (TotalSpace F E)]

variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable def productFun {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  ofModel (F := F) (E := E)
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv)

scoped infixl:70 " ⊗ₘ " => productFun

noncomputable def modelProduct (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  (f.smulRight g).uncurrySum.domDomCongr finSumFinEquiv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem modelProduct_apply (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (v : Fin (s + q) → F) :
    modelProduct s q f g v = f (v ∘ Fin.castAdd q) * g (v ∘ Fin.natAdd s) := by
  simp only [modelProduct, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  congr 1

end Bundle.continuousMultilinearMap

end
