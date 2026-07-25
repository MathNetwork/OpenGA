import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension










namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

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




noncomputable def continuousLinearMap_homBasis
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W) :
    Module.Basis (κ × ι) 𝕜 (U →L[𝕜] W) :=
  (bU.linearMap bW).map
    (LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W)



theorem continuousLinearMap_homBasis_repr
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W)
    (A : U →L[𝕜] W) (i : ι) (j : κ) :
    (continuousLinearMap_homBasis (𝕜 := 𝕜) bU bW).repr A (j, i) =
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




noncomputable def tensorRSModel_basis {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ) :
    Module.Basis ((Fin r → Fin d) × (Fin s → Fin d)) 𝕜 (TensorRSModel r s 𝕜 E) :=
  let bR := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r
  let bS := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE s
  (continuousLinearMap_homBasis (𝕜 := 𝕜) bR bS).reindex
    (Equiv.prodComm (Fin s → Fin d) (Fin r → Fin d))




theorem tensorRSModel_basis_repr {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ)
    (A : TensorRSModel r s 𝕜 E)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    (tensorRSModel_basis (𝕜 := 𝕜) (E := E) bE r s).repr A (ρ, σ) =
      (A ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) := by
  unfold tensorRSModel_basis
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
            (G p ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) bE r) ρ))
              (fun a : Fin s => bE (σ a))) x₀) :
    ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n G x₀ := by
  classical
  let B := tensorRSModel_basis (𝕜 := 𝕜) (E := E) bE r s
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
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  exact (trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀).symmL 𝕜 x β



omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (s : ℕ)
    (_hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  change (((trivializationAt E (TangentSpace I) x₀).continuousMultilinearMap 𝕜 s)
      ⟨x, T⟩).2 v =
    T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl




omit [CompleteSpace 𝕜] in
theorem continuousLinearEquivAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x
          (show x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
            (fun x => Tensor0SSpace s I x) x₀).baseSet from hx) T) v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  change ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s hx T v




omit [CompleteSpace 𝕜] in
theorem continuousLinearMapAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
      fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
  rfl





omit [CompleteSpace 𝕜] in
theorem constInChart_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (β : Tensor0SModel s 𝕜 E) (v : Fin s → TangentSpace I x) :
    (constInChart (𝕜 := 𝕜) (I := I) s x₀ β x) v =
      β (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  let eT := trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀
  let e := trivializationAt E (TangentSpace I) x₀
  have hxT : x ∈ eT.baseSet := hx
  have hcoord := congrArg
    (fun A : Tensor0SModel s 𝕜 E => A (fun i => e.continuousLinearMapAt 𝕜 x (v i)))
    (eT.continuousLinearMapAt_symmL (R := 𝕜) hxT β)
  unfold constInChart
  dsimp only [eT, e] at hcoord ⊢
  rw [continuousLinearMapAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) s hx] at hcoord
  have hcancel : (fun i => e.symmL 𝕜 x (e.continuousLinearMapAt 𝕜 x (v i))) = v := by
    funext i
    exact e.symmL_continuousLinearMapAt (R := 𝕜) hx (v i)
  rw [hcancel] at hcoord
  exact hcoord

end Tensor0SSpace

namespace TensorRSSpace



omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (r s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2 β) v =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a)) := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  have hxR : x ∈ (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).baseSet := hx
  have hxS : x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).baseSet := hx
  rw [hom_trivializationAt_apply]
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
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β := rfl
  rw [hβ]
  exact Tensor0SSpace.continuousLinearEquivAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s hx _ v




theorem trivializationAt_basis_coord {d r s : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
          ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ)))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (bE (σ a))) := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) r s hx T
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ)
    (fun a : Fin s => bE (σ a))

end TensorRSSpace

end Trivialization

end

end Tensor0SBundle
