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
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

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

section ApplyInput

variable {r s : ℕ} [CompleteSpace 𝕜]

noncomputable def modelApplyInputBilinear (r s : ℕ) :
    Tensor0SModel r 𝕜 E →L[𝕜]
      (TensorRSModel r s 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (ContinuousLinearMap.id 𝕜 (TensorRSModel r s 𝕜 E))

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_applyInput_eq
    (r s : ℕ) {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (θ : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T θ⟩).2 =
      (((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2)
        (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ext v
  rw [Tensor0SSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) s]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) r s hx]
  have hθ :
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
        (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) = θ := by
    have hcoord :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt 𝕜 x θ =
          ((trivializationAt (Tensor0SModel r 𝕜 E)
            (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      exact congrFun ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx) θ
    rw [← hcoord]
    exact (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx θ
  rw [hθ]

noncomputable def tensorRSFieldApplyInputFun
    (T : (x : M) ->
      TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (θ : (x : M) ->
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x) :
    (x : M) ->
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x :=
  fun x => T x (θ x)

noncomputable def tensorRSFieldApplyInput
    (T : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (θ : Tensor0SField n r (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨tensorRSFieldApplyInputFun (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) (r := r) (s := s) (fun x => T x) (fun x => θ x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have hθ := θ.contMDiff x₀
  rw [contMDiffAt_section] at hθ
  have hcombine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x : M =>
          modelApplyInputBilinear (𝕜 := 𝕜) (E := E) r s
            (((trivializationAt (Tensor0SModel r 𝕜 E)
                (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ x⟩).2)
            (((trivializationAt (TensorRSModel r s 𝕜 E)
                (fun x => TensorRSSpace r s I x) x₀) ⟨x, T x⟩).2)) x₀ := by
    exact ((contMDiffAt_const
      (c := modelApplyInputBilinear (𝕜 := 𝕜) (E := E) r s)).clm_apply hθ).clm_apply hT
  refine hcombine.congr_of_eventuallyEq ?_
  filter_upwards
    [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
  exact tensor0SModelAt_applyInput_eq (𝕜 := 𝕜) (E := E) (I := I)
    (M := M) r s hx (T x) (θ x)

end ApplyInput

noncomputable def Tensor0SField.one0 [CompleteSpace 𝕜] :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  Tensor0SField.fromScalarField n (fun _ : M => (1 : 𝕜)) contMDiff_const

end

end Tensor0SBundle

end DifferentialGeometry
