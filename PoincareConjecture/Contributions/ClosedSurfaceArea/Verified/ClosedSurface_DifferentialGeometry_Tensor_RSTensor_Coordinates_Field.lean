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
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

open DifferentialGeometry.Tensor.Multilinear

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I 1 M]

variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

abbrev TensorRSField (r s : ℕ) :=
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

abbrev Tensor0SField (s : ℕ) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiffSection I
    (Tensor0SModel s 𝕜 E)
    n
    (fun x : M => Tensor0SSpace s I x)

noncomputable def Tensor0SField.fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  ⟨fun x => ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (f x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) n b _).mpr
      fun σ x₀ => ?_
    have hcoord : ∀ x, (continuousMultilinearMapBasis b 0).repr
        (trivializationAt (Tensor0SModel 0 𝕜 E)
          (fun x => Tensor0SSpace 0 I x) x₀
          ⟨x, ContinuousMultilinearMap.constOfIsEmpty 𝕜
            (fun _ : Fin 0 => TangentSpace I x) (f x)⟩).2 σ = f x := by
      intro x
      simp_rw [continuousMultilinearMap_basis_repr]
      rfl
    exact (hf.contMDiffAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => hcoord x)⟩

end

end Tensor0SBundle

end DifferentialGeometry
