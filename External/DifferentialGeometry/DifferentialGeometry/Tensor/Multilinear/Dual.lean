


import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Bundle.Dual
import DifferentialGeometry.Bundle.Equiv
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Topology.VectorBundle.FiniteDimensional


noncomputable section

open Module

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

noncomputable def tensorOfDualLinearForms (r : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
  ContinuousMultilinearMap.compContinuousLinearMapLRight (E := fun _ : Fin r => F)
    (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin r) 𝕜)

variable {𝕜 F}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp]
theorem tensorOfDualLinearForms_apply (r : ℕ) (α : Fin r → (F →L[𝕜] 𝕜))
    (v : Fin r → F) :
    tensorOfDualLinearForms 𝕜 F r α v = ∏ i, α i (v i) := by
  simp [tensorOfDualLinearForms,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

variable (𝕜 F)

noncomputable def dualMultilinearLinearMap (r : ℕ) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 where
  toFun φ := φ.compContinuousMultilinearMap (tensorOfDualLinearForms 𝕜 F r)
  map_add' φ ψ := by
    ext α
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      Function.comp_apply]
  map_smul' c φ := by
    ext α
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
      Function.comp_apply, RingHom.id_apply]

variable {𝕜 F}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp]
theorem dualMultilinearLinearMap_apply (r : ℕ)
    (φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜)
    (α : Fin r → (F →L[𝕜] 𝕜)) :
    dualMultilinearLinearMap 𝕜 F r φ α =
      φ ((tensorOfDualLinearForms 𝕜 F r) α) := rfl

variable (𝕜 F)

theorem basisElem_eq_tensorOfDualLinearForms {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (r : ℕ) (σ : Fin r → Fin d) :
    continuousMultilinearMap_basisElem (𝕜 := 𝕜) (F := F) b r σ
      = tensorOfDualLinearForms 𝕜 F r
        (fun i => LinearMap.toContinuousLinearMap (b.coord (σ i))) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensorOfDualLinearForms_apply]
  simp [continuousMultilinearMap_basisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply]

private noncomputable def dualMultilinearInverseAux (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜 :=
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  LinearMap.toContinuousLinearMap
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r).constr 𝕜
      (fun σ => Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i)))))

variable {𝕜 F}

private theorem dualMultilinearInverseAux_basisElem (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (σ : Fin r → Fin (Module.finrank 𝕜 F)) :
    dualMultilinearInverseAux 𝕜 F r Ψ
        (continuousMultilinearMap_basisElem (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r σ) =
      Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i))) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  let b := Module.finBasis 𝕜 F
  let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r

  have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
      continuousMultilinearMap_basisElem b r σ :=
    congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ

  change LinearMap.toContinuousLinearMap
      (bMLF.constr 𝕜 (fun σ => Ψ (fun i =>
        LinearMap.toContinuousLinearMap (b.coord (σ i)))))
      (continuousMultilinearMap_basisElem b r σ) = _
  rw [LinearMap.coe_toContinuousLinearMap', ← hb_eq, Basis.constr_basis]

variable (𝕜 F)

noncomputable def dualMultilinearInverseMap (r : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 →ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) where
  toFun := dualMultilinearInverseAux 𝕜 F r
  map_add' Ψ₁ Ψ₂ := by
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    apply ContinuousLinearMap.ext
    intro x
    let b := Module.finBasis 𝕜 F
    let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
    have h_basis : ∀ σ,
        dualMultilinearInverseAux 𝕜 F r (Ψ₁ + Ψ₂) (bMLF σ) =
          (dualMultilinearInverseAux 𝕜 F r Ψ₁ + dualMultilinearInverseAux 𝕜 F r Ψ₂)
            (bMLF σ) := by
      intro σ
      have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
          continuousMultilinearMap_basisElem b r σ :=
        congr_fun (Module.Basis.coe_mk
          (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
      rw [hb_eq, ContinuousLinearMap.add_apply,
        dualMultilinearInverseAux_basisElem,
        dualMultilinearInverseAux_basisElem,
        dualMultilinearInverseAux_basisElem]
      rfl
    have hLHS : ∀ x, dualMultilinearInverseAux 𝕜 F r (Ψ₁ + Ψ₂) x =
        (dualMultilinearInverseAux 𝕜 F r Ψ₁ + dualMultilinearInverseAux 𝕜 F r Ψ₂) x := by
      have := bMLF.ext (f₁ := (dualMultilinearInverseAux 𝕜 F r (Ψ₁ + Ψ₂)).toLinearMap)
        (f₂ := ((dualMultilinearInverseAux 𝕜 F r Ψ₁ +
          dualMultilinearInverseAux 𝕜 F r Ψ₂).toLinearMap)) h_basis
      intro x
      exact congrFun (congrArg DFunLike.coe this) x
    exact hLHS x
  map_smul' c Ψ := by
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    apply ContinuousLinearMap.ext
    intro x
    let b := Module.finBasis 𝕜 F
    let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
    have h_basis : ∀ σ,
        dualMultilinearInverseAux 𝕜 F r (c • Ψ) (bMLF σ) =
          (c • dualMultilinearInverseAux 𝕜 F r Ψ) (bMLF σ) := by
      intro σ
      have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
          continuousMultilinearMap_basisElem b r σ :=
        congr_fun (Module.Basis.coe_mk
          (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
      rw [hb_eq, ContinuousLinearMap.smul_apply,
        dualMultilinearInverseAux_basisElem,
        dualMultilinearInverseAux_basisElem]
      rfl
    have hLHS : ∀ x, dualMultilinearInverseAux 𝕜 F r (c • Ψ) x =
        (c • dualMultilinearInverseAux 𝕜 F r Ψ) x := by
      have := bMLF.ext (f₁ := (dualMultilinearInverseAux 𝕜 F r (c • Ψ)).toLinearMap)
        (f₂ := ((c • dualMultilinearInverseAux 𝕜 F r Ψ).toLinearMap)) h_basis
      intro x
      exact congrFun (congrArg DFunLike.coe this) x
    exact hLHS x

variable {𝕜 F}

theorem dualMultilinearInverseMap_basisElem (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (σ : Fin r → Fin (Module.finrank 𝕜 F)) :
    dualMultilinearInverseMap 𝕜 F r Ψ
        (continuousMultilinearMap_basisElem (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r σ) =
      Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i))) :=
  dualMultilinearInverseAux_basisElem r Ψ σ

variable (𝕜 F)

theorem dualMultilinearInverseMap_dualMultilinearLinearMap (r : ℕ) :
    (dualMultilinearInverseMap 𝕜 F r).comp (dualMultilinearLinearMap 𝕜 F r) =
      LinearMap.id := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  apply LinearMap.ext
  intro φ
  change ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) : _ →L[𝕜] _)
    = φ
  apply ContinuousLinearMap.ext
  intro x
  let b := Module.finBasis 𝕜 F
  let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
  have h_basis : ∀ σ,
      ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) :
          _ →L[𝕜] _) (bMLF σ) = φ (bMLF σ) := by
    intro σ
    have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
        continuousMultilinearMap_basisElem b r σ :=
      congr_fun (Module.Basis.coe_mk
        (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
    rw [hb_eq, dualMultilinearInverseMap_basisElem,
      show (dualMultilinearLinearMap 𝕜 F r φ) (fun i =>
          LinearMap.toContinuousLinearMap (b.coord (σ i))) =
        φ ((tensorOfDualLinearForms 𝕜 F r) (fun i =>
            LinearMap.toContinuousLinearMap (b.coord (σ i)))) from rfl,
      ← basisElem_eq_tensorOfDualLinearForms]
  have hAll : ∀ x, ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) :
        _ →L[𝕜] _) x = φ x := by
    have :=
      bMLF.ext (f₁ := ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ)
          : _ →L[𝕜] _).toLinearMap)
        (f₂ := (φ : _ →L[𝕜] _).toLinearMap) h_basis
    intro y
    exact congrFun (congrArg DFunLike.coe this) y
  exact hAll x

theorem dualMultilinearLinearMap_dualMultilinearInverseMap (r : ℕ) :
    (dualMultilinearLinearMap 𝕜 F r).comp (dualMultilinearInverseMap 𝕜 F r) =
      LinearMap.id := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  apply LinearMap.ext
  intro Ψ
  apply ContinuousMultilinearMap.ext
  intro α
  let b := Module.finBasis 𝕜 F
  have hα : ∀ i, α i = ∑ k, α i (b k) •
      LinearMap.toContinuousLinearMap (b.coord k) := fun i =>
    (cdual_sum_repr (𝕜 := 𝕜) (E := F) b (α i)).symm
  have hα_funext : α = (fun i => ∑ k, α i (b k) •
      LinearMap.toContinuousLinearMap (b.coord k)) := funext hα
  change ((dualMultilinearLinearMap 𝕜 F r) ((dualMultilinearInverseMap 𝕜 F r) Ψ)) α = Ψ α
  rw [dualMultilinearLinearMap_apply]
  change (dualMultilinearInverseAux 𝕜 F r Ψ : _ →L[𝕜] _)
      ((tensorOfDualLinearForms 𝕜 F r) α) = Ψ α
  change LinearMap.toContinuousLinearMap
      ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r).constr 𝕜
        (fun σ => Ψ (fun i => LinearMap.toContinuousLinearMap (b.coord (σ i)))))
      ((tensorOfDualLinearForms 𝕜 F r) α) = Ψ α
  rw [LinearMap.coe_toContinuousLinearMap',
    Basis.constr_apply_fintype]
  set bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
  have hcoord : ∀ σ, bMLF.equivFun ((tensorOfDualLinearForms 𝕜 F r) α) σ
      = ∏ i, α i (b (σ i)) := by
    intro σ
    rw [Basis.equivFun_apply, continuousMultilinearMap_basis_repr,
      tensorOfDualLinearForms_apply]
  simp_rw [hcoord]
  conv_rhs => rw [hα_funext, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show (fun i => α i (b (σ i)) •
        LinearMap.toContinuousLinearMap (b.coord (σ i))) =
      (fun i => (α i (b (σ i))) •
        (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j))) i) from rfl,
    ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

noncomputable def dualMultilinearEquivMultilinearOfDual (r : ℕ) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 :=
  LinearEquiv.ofLinear
    (dualMultilinearLinearMap 𝕜 F r)
    (dualMultilinearInverseMap 𝕜 F r)
    (dualMultilinearLinearMap_dualMultilinearInverseMap 𝕜 F r)
    (dualMultilinearInverseMap_dualMultilinearLinearMap 𝕜 F r)

end ContinuousMultilinearMap

open Bundle

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

noncomputable def dualMultilinearLinearEquivAt (r : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜 :=
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 (E x) r

theorem dualMultilinearLinearEquivAt_apply (r : ℕ) (x : B)
    (φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜)
    (α : Fin r → (E x →L[𝕜] 𝕜)) :
    dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x φ α =
      φ ((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (E x) r) α) := rfl

end Bundle.continuousMultilinearMap

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {r : ℕ}

noncomputable instance dualBundleTopology (r : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

noncomputable instance dualBundleFiberBundle (r : ℕ) :
    @FiberBundle B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      _ (by infer_instance : TopologicalSpace _)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      (dualBundleTopology r) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

noncomputable instance dualBundleVectorBundle (r : ℕ) :
    @VectorBundle 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      _
      (fun x => by infer_instance) (fun x => by infer_instance)
      inferInstance inferInstance _
      (dualBundleTopology r) _
      (dualBundleFiberBundle r) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

section smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]

noncomputable instance dualBundleSmoothVectorBundle (r : ℕ) :
    @ContMDiffVectorBundle n 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      _ EB _ _ HB _ IB _ _ _ _ _ _
      (dualBundleTopology r) _
      (dualBundleFiberBundle r)
      (dualBundleVectorBundle r) :=
  ContMDiffVectorBundle.continuousLinearMap

end smooth

private theorem dualBundleFiber_type_eq (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜 →L[𝕜] 𝕜) := by
  unfold Bundle.continuousMultilinearMap
  congr 1
  exact topology_eq (𝕜 := 𝕜) (F := F) (E := E) _ x

private def dualBundleFiber_normedInstances (r : ℕ) (x : B) :
    Σ' (ng : NormedAddCommGroup
          (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)),
      @NormedSpace 𝕜
        (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
        _ ng.toSeminormedAddCommGroup :=
  (dualBundleFiber_type_eq (𝕜 := 𝕜) (F := F) (E := E) r x) ▸ ⟨inferInstance, inferInstance⟩

instance dualBundleFiber_instNormedAddCommGroup (r : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  (dualBundleFiber_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r x).1

instance dualBundleFiber_instNormedSpace (r : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  (dualBundleFiber_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r x).2

instance dualBundleFiber_instContinuousSMul (r : ℕ) (x : B) :
    ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜))

def dualBundleContinuousLinearEquivAt (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).arrowCongr
    (ContinuousLinearEquiv.refl 𝕜 𝕜)

theorem dualBundle_triv_symmL_eq_comp (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (ζ : F →L[𝕜] 𝕜) (v : E x) :
    ((trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).symmL 𝕜 x ζ) v =
      ζ ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) := by
  set e := trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀ with he_def
  have hbase : x ∈ e.baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp [trivializationAt, FiberBundle.trivializationAt']⟩
  have hsymmL : (e.symmL 𝕜 x ζ : Bundle.dual 𝕜 E x) = e.symm x ζ := by
    simp [Trivialization.symmL_apply]
  rw [hsymmL]
  have h_rt : (e ⟨x, e.symm x ζ⟩ : B × _) = (x, ζ) := e.apply_mk_symm hbase ζ
  have h_snd : (e ⟨x, e.symm x ζ⟩ : B × _).2 = ζ := congrArg Prod.snd h_rt
  have hxTriv : x ∈ (trivializationAt 𝕜 (fun _ : B => 𝕜) x₀).baseSet := by
    change x ∈ Set.univ; trivial
  have h_fwd : (e ⟨x, e.symm x ζ⟩).2
      ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) =
    ((Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv)
      ((e.symm x ζ)
        ((Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt F E x₀) x hx).symm
          ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v)))) := by
    rw [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates_eq hx hxTriv]
    rfl
  rw [h_snd] at h_fwd
  have h_triv : ∀ (z : 𝕜),
      ((Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv
        : 𝕜 →L[𝕜] 𝕜) : 𝕜 → 𝕜) z = z := by intro z; rfl
  conv at h_fwd => rhs; rw [show (Trivialization.continuousLinearEquivAt 𝕜
    (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv) _ = _ from h_triv _]
  conv_lhs => rw [show v = ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm
    ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) from
    ((trivializationAt F E x₀).symmL_continuousLinearMapAt hx v).symm]
  exact h_fwd.symm

end Bundle.continuousMultilinearMap

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

local notation "MLF" => fun r => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜

local notation "MLF_dual" => fun r =>
  ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in

theorem tensorOfDualLinearForms_compContinuousLinearMap_naturality
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (r : ℕ) (L : G →L[𝕜] F)
    (β : Fin r → (F →L[𝕜] 𝕜)) :
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β).compContinuousLinearMap
        (fun _ : Fin r => L) =
      ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 G r (fun i => (β i).comp L) := by
  apply ContinuousMultilinearMap.ext
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.tensorOfDualLinearForms_apply,
      ContinuousMultilinearMap.tensorOfDualLinearForms_apply]
  rfl

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def dualLiftFiber (r : ℕ) (x : B)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :
    Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜 :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a))

theorem dualLiftFiber_apply (r : ℕ) (x : B)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x) :
    dualLiftFiber (F := F) r x a T =
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x T) := by
  rfl

noncomputable def dualUnliftFiber (r : ℕ) (x : B)
    (ψ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x ψ))

end Bundle.continuousMultilinearMap

abbrev DualBundleSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) (r : ℕ) :=
  @ContMDiffSection 𝕜 _ EB _ _ HB _ IB B _ _
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
    _ _ n
    (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
    (Bundle.continuousMultilinearMap.dualBundleTopology r)
    (fun _ => inferInstance)
    (Bundle.continuousMultilinearMap.dualBundleFiberBundle r)

namespace MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]
variable {r : ℕ}

local instance dualMultilinear_instNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

local instance dualMultilinear_instNormedSpace :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

local instance dualOfMultilinear_instNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  inferInstance

local instance dualOfMultilinear_instNormedSpace :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  inferInstance

noncomputable def Bundle.continuousMultilinearMap.modelDualInvCLM (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) r
  LinearMap.toContinuousLinearMap
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).symm.toLinearMap

theorem dualLiftFiber_triv_eq {r : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :
    (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) x₀
        ⟨x, Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a⟩).2 =
    Bundle.continuousMultilinearMap.modelDualInvCLM 𝕜 F r
      ((trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
        ⟨x, a⟩).2) := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  apply (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
    (𝕜 := 𝕜) (F := F) r).injective
  rw [show (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual (𝕜 := 𝕜) (F := F) r)
        ((Bundle.continuousMultilinearMap.modelDualInvCLM 𝕜 F r) _) = _ from
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
        (𝕜 := 𝕜) (F := F) r).apply_symm_apply _]
  apply ContinuousMultilinearMap.ext
  intro β
  change (ContinuousMultilinearMap.dualMultilinearLinearMap 𝕜 F r
    (_ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)) β = _
  rw [ContinuousMultilinearMap.dualMultilinearLinearMap_apply]
  rw [hom_trivializationAt_apply]
  have hxTriv : x ∈ (trivializationAt 𝕜 (fun _ : B => 𝕜) x₀).baseSet := by
    change x ∈ Set.univ; trivial
  have hxMlb : x ∈ (trivializationAt
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x) x₀).baseSet := hx
  rw [ContinuousLinearMap.inCoordinates_eq hxMlb hxTriv]
  change ((Trivialization.continuousLinearEquivAt 𝕜
      (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv : 𝕜 →L[𝕜] 𝕜).comp
    ((Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a).comp
      ((Trivialization.continuousLinearEquivAt 𝕜
        (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 r F E) x₀) x hxMlb).symm : _ →L[𝕜] _)))
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β) =
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
      ⟨x, a⟩).2 β
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h_cle_triv : ∀ (z : 𝕜),
      ((Trivialization.continuousLinearEquivAt 𝕜
        (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv : 𝕜 →L[𝕜] 𝕜) : 𝕜 → 𝕜) z = z := by
    intro z; rfl
  rw [h_cle_triv]
  change (Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a)
    ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 r F E) x₀).symmL 𝕜 x
      (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β)) = _
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx]
  rw [Bundle.continuousMultilinearMap.dualLiftFiber_apply]
  conv_lhs =>
    rw [show Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x
          (((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r) β).compContinuousLinearMap
            (fun _ => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x)) =
        ((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r) β).compContinuousLinearMap
          (fun _ => ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
            ((trivializationAt F E x).symmL 𝕜 x)) from rfl]
  rw [Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality]
  show (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
    (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r
      (fun i => (β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
        ((trivializationAt F E x).symmL 𝕜 x)))) = _
  have h_rt : ∀ (m : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (γ : Fin r → (F →L[𝕜] 𝕜)),
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm m
        (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r γ) = m γ := by
    intro m γ
    have := (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).apply_symm_apply m
    have h2 := congr_fun (congr_arg DFunLike.coe this) γ
    exact h2
  rw [h_rt]
  change (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
    (fun i => (β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((trivializationAt F E x).symmL 𝕜 x))) = _
  change a (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmL 𝕜 x
    ((β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((trivializationAt F E x).symmL 𝕜 x)))) = _
  change a (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmL 𝕜 x
    ((β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((trivializationAt F E x).symmL 𝕜 x)))) =
    a (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).symmL 𝕜 x (β i))
  congr 1
  funext i
  apply ContinuousLinearMap.ext
  intro v
  rw [Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp x₀ x hx,
    Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp x x
      (mem_baseSet_trivializationAt F E x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [(trivializationAt F E x).symmL_continuousLinearMapAt
    (mem_baseSet_trivializationAt F E x)]

noncomputable def Bundle.continuousMultilinearMap.modelDualFwdCLM (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := by
    haveI : FiniteDimensional 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
      continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) r
    exact (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).symm.finiteDimensional
  LinearMap.toContinuousLinearMap
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).toLinearMap

theorem dualUnliftFiber_triv_eq {r : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (ψ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
        ⟨x, Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ⟩).2 =
    Bundle.continuousMultilinearMap.modelDualFwdCLM 𝕜 F r
      ((trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) x₀
        ⟨x, ψ⟩).2) := by
  have h_rt_fiber : Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x
      (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ) = ψ := by
    change (Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x).symm
        ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
          ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
              (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x)
            ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
                (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
              ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
                ((Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
                    (𝕜 := 𝕜) (F := F) (E := E) r x) ψ))))) = ψ
    simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  have h_triv := dualLiftFiber_triv_eq x₀ x hx
    (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ)
  rw [h_rt_fiber] at h_triv
  set triv_mlbdual := (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
    ⟨x, Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ⟩).2
  rw [h_triv]
  exact ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
    (𝕜 := 𝕜) (F := F) r).apply_symm_apply triv_mlbdual).symm

end MultilinearSection

section BundleEquiv

open MultilinearSection

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]
variable {r : ℕ}

local instance : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
local instance : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
local instance : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance

noncomputable def dualMultilinearFiberwiseEquiv (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).toLinearEquiv.trans
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).trans
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
        (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv)

omit [ContMDiffVectorBundle n F E IB] in
theorem dualMultilinearFiberwiseEquiv_smooth (r : ℕ)
    [ContMDiffVectorBundle n F E IB] :
    ContMDiff
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜))
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
      n
      (fun p : TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) =>
        (⟨p.1, dualMultilinearFiberwiseEquiv (𝕜 := 𝕜) (F := F) (E := E) r p.1 p.2⟩ :
          TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r
              (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x))) := by
  letI := dualBundleSmoothVectorBundle (𝕜 := 𝕜) (B := B) (F := F) (E := E) IB n r
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜))
        𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) n
        (fun p => (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelDualFwdCLM 𝕜 F r)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact dualUnliftFiber_triv_eq p₀.proj p.proj hp p.snd

omit [ContMDiffVectorBundle n F E IB] in
theorem dualMultilinearFiberwiseEquiv_symm_smooth (r : ℕ)
    [ContMDiffVectorBundle n F E IB] :
    ContMDiff
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜))
      n
      (fun q : TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r
            (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) =>
        (⟨q.1, (dualMultilinearFiberwiseEquiv (𝕜 := 𝕜) (F := F) (E := E) r q.1).symm q.2⟩ :
          TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜))) := by
  haveI : ContMDiffVectorBundle n (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) IB :=
    ContMDiffVectorBundle.continuousLinearMap
  haveI : ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)) IB :=
    SmoothVectorBundle.continuousMultilinearMap
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) (IB := IB) (s := r) n
  intro q₀
  refine contMDiffAt_totalSpace.mpr ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
        (Bundle.dual 𝕜 E) x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
        𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) n
        (fun q => (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
            (Bundle.dual 𝕜 E) x) q₀.proj q).2) q₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelDualInvCLM 𝕜 F r)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E q₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E q₀.proj)
    ] with q hq
    exact dualLiftFiber_triv_eq q₀.proj q.proj hq q.snd

end Bundle.continuousMultilinearMap

noncomputable def dualBundle_multilinearOfDual_equiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    {IB : ModelWithCorners 𝕜 EB HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]
    (r : ℕ) :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x)
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth r)
    (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth r)

end BundleEquiv

namespace MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def fromDualBundleSection {r : ℕ}
    (ψ : DualBundleSection 𝕜 F IB E n r) :
    MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r :=
  ⟨fun x => Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x (ψ x),
   (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_smooth r |>.comp
     ψ.contMDiff).congr fun _ => rfl⟩

noncomputable def toDualBundleSection {r : ℕ}
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) :
    DualBundleSection 𝕜 F IB E n r :=
  ⟨fun x => (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x).symm (α x),
   (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv_symm_smooth r |>.comp
     α.contMDiff).congr fun _ => rfl⟩

@[simp]
theorem toDualBundleSection_fromDualBundleSection {r : ℕ}
    (ψ : DualBundleSection 𝕜 F IB E n r) :
    toDualBundleSection n (fromDualBundleSection n ψ) = ψ := by
  apply ContMDiffSection.ext; intro x
  exact (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x).symm_apply_apply (ψ x)

@[simp]
theorem fromDualBundleSection_toDualBundleSection {r : ℕ}
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) :
    fromDualBundleSection n (toDualBundleSection n α) = α := by
  apply ContMDiffSection.ext; intro x
  exact (Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv r x).apply_symm_apply (α x)

theorem fromDualBundleSection_add {r : ℕ}
    (ψ₁ ψ₂ : DualBundleSection 𝕜 F IB E n r) (x : B) :
    (fromDualBundleSection n (ψ₁ + ψ₂)).1 x =
    (fromDualBundleSection n ψ₁).1 x + (fromDualBundleSection n ψ₂).1 x :=
  map_add _ (ψ₁ x) (ψ₂ x)

theorem fromDualBundleSection_smul {r : ℕ}
    (c : 𝕜) (ψ : DualBundleSection 𝕜 F IB E n r) (x : B) :
    (fromDualBundleSection n (c • ψ)).1 x =
    c • (fromDualBundleSection n ψ).1 x :=
  map_smul _ c (ψ x)

theorem toDualBundleSection_add {r : ℕ}
    (α β : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) (x : B) :
    (toDualBundleSection n (α + β)).1 x =
    (toDualBundleSection n α).1 x + (toDualBundleSection n β).1 x :=
  map_add _ (α x) (β x)

theorem toDualBundleSection_smulByFun {r : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) (x : B) :
    (toDualBundleSection n (MultilinearSection.smulByFun n φ hφ α)).1 x =
    φ x • (toDualBundleSection n α).1 x :=
  map_smul _ (φ x) (α x)

end MultilinearSection

end
