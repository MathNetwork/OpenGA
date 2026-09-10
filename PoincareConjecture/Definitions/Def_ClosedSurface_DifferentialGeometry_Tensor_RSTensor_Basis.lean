import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

open DifferentialGeometry.Tensor.Multilinear

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

section HomBasis

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

variable [FiniteDimensional 𝕜 U]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

noncomputable def continuousLinearMapHomBasis
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W) :
    Module.Basis (κ × ι) 𝕜 (U →L[𝕜] W) :=
  (bU.linearMap bW).map
    (LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W)

theorem continuousLinearMap_homBasis_repr
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W)
    (A : U →L[𝕜] W) (i : ι) (j : κ) :
    (continuousLinearMapHomBasis (𝕜 := 𝕜) bU bW).repr A (j, i) =
      bW.repr (A (bU i)) j := by
  change (bU.linearMap bW).repr
      ((LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W).symm A)
      (j, i) =
    bW.repr (A (bU i)) j
  change LinearMap.toMatrix bU bW (A : U →ₗ[𝕜] W) j i =
    bW.repr (A (bU i)) j
  rw [LinearMap.toMatrix_apply]
  rfl

end HomBasis

noncomputable def tensorRSModelBasis {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ) :
    Module.Basis ((Fin r → Fin d) × (Fin s → Fin d)) 𝕜 (TensorRSModel r s 𝕜 E) :=
  let bR := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r
  let bS := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE s
  (continuousLinearMapHomBasis (𝕜 := 𝕜) bR bS).reindex
    (Equiv.prodComm (Fin s → Fin d) (Fin r → Fin d))

theorem tensorRSModel_basis_repr {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ)
    (A : TensorRSModel r s 𝕜 E)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    (tensorRSModelBasis (𝕜 := 𝕜) (E := E) bE r s).repr A (ρ, σ) =
      (A ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) := by
  unfold tensorRSModelBasis
  rw [Module.Basis.repr_reindex_apply]
  rw [continuousLinearMap_homBasis_repr]
  rw [continuousMultilinearMap_basis_repr]
  rfl

section SmoothCriterion

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
    {d r s : ℕ} (bE : Module.Basis (Fin d) 𝕜 E)
    {G : M → TensorRSModel r s 𝕜 E} {x₀ : M} {n : WithTop ℕ∞}
    (hcoord :
      ∀ ρ : Fin r → Fin d, ∀ σ : Fin s → Fin d,
        ContMDiffAt I 𝓘(𝕜, 𝕜) n
          (fun p : M =>
            (G p ((continuousMultilinearMapBasis
              (𝕜 := 𝕜) (F := E) bE r) ρ))
              (fun a : Fin s => bE (σ a))) x₀) :
    ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n G x₀ := by
  classical
  let B := tensorRSModelBasis (𝕜 := 𝕜) (E := E) bE r s
  have hcoords :
      ContMDiffAt I 𝓘(𝕜, ((Fin r → Fin d) × (Fin s → Fin d) → 𝕜)) n
        (fun p : M => B.equivFunL (G p)) x₀ := by
    rw [contMDiffAt_pi_space]
    intro idx
    rcases idx with ⟨ρ, σ⟩
    simpa [B, tensorRSModel_basis_repr] using hcoord ρ σ
  have hsmooth :=
    ((B.equivFunL.symm :
        (((Fin r → Fin d) × (Fin s → Fin d) → 𝕜) →L[𝕜]
          TensorRSModel r s 𝕜 E)).contMDiff.contMDiffAt.comp x₀ hcoords)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards with p
  simp [B]

end SmoothCriterion

section Trivialization

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I 1 M]

variable {x₀ x : M}

namespace Tensor0SSpace

noncomputable def constInChart (s : ℕ) (x₀ : M)
    (β : Tensor0SModel s 𝕜 E) (x : M) : Tensor0SSpace s I x := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  exact (trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀).symmL 𝕜 x β

omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (s : ℕ)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  change (((trivializationAt E (TangentSpace I) x₀).continuousMultilinearMap 𝕜 s)
      ⟨x, T⟩).2 v =
    T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl

omit [CompleteSpace 𝕜] in
theorem continuousLinearEquivAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x
          (show x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
            (fun x => Tensor0SSpace s I x) x₀).baseSet from hx) T) v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  change ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s T v

end Tensor0SSpace

namespace TensorRSSpace

omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (r s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2 β) v =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a)) := by
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  let : FiberBundle (Tensor0SModel r 𝕜 E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundleFiber r
  let : FiberBundle (Tensor0SModel s 𝕜 E) (fun y : M => Tensor0SSpace s I y) :=
    tensor0SBundleFiber s
  let : VectorBundle 𝕜 (Tensor0SModel r 𝕜 E) (fun y : M => Tensor0SSpace r I y) :=
    tensor0SBundle_vector r
  let : VectorBundle 𝕜 (Tensor0SModel s 𝕜 E) (fun y : M => Tensor0SSpace s I y) :=
    tensor0SBundle_vector s
  have hxR : x ∈ (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).baseSet := hx
  have hxS : x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).baseSet := hx
  rw [hom_trivializationAt_apply (RingHom.id 𝕜)
    (F₁ := Tensor0SModel r 𝕜 E) (E₁ := fun y => Tensor0SSpace r I y)
    (F₂ := Tensor0SModel s 𝕜 E) (E₂ := fun y => Tensor0SSpace s I y)]
  rw [ContinuousLinearMap.inCoordinates_eq hxR hxS]
  change (((trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x hxS)
        (T (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearEquivAt 𝕜 x hxR).symm β))) v =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a))
  have hβ :
      ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearEquivAt 𝕜 x hxR).symm β =
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β :=
    congrFun ((trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symm_continuousLinearEquivAt_eq hxR) β
  rw [hβ]
  exact Tensor0SSpace.continuousLinearEquivAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s hx _ v

theorem trivializationAt_basis_coord {d r s : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
          ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ)))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (bE (σ a))) := by
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) r s hx T
    ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ)
    (fun a : Fin s => bE (σ a))

end TensorRSSpace

end Trivialization

end

end Tensor0SBundle

end DifferentialGeometry
