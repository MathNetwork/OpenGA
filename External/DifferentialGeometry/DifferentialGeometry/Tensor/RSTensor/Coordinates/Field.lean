


import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Tensor


namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

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
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

abbrev Tensor0SField (s : ℕ) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiffSection I
    (Tensor0SModel s 𝕜 E)
    n
    (fun x : M => Tensor0SSpace s I x)

section SmulByFun

variable {r s : ℕ} [CompleteSpace 𝕜]

def tensorRSField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨fun x => φ x • α x, by
    letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    intro x₀
    rw [contMDiffAt_section]
    have hα := α.contMDiff x₀
    rw [contMDiffAt_section] at hα
    set e := trivializationAt (TensorRSModel r s 𝕜 E) (fun x => TensorRSSpace r s I x) x₀
    refine ((hφ x₀).smul hα).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀))
      fun x hx => (e.linear 𝕜 hx).2 _ _⟩

omit [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
@[simp]
theorem tensorRSField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensorRSField_smulByFun n φ hφ α x = φ x • α x :=
  rfl

def tensor0SField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨fun x => φ x • α x, hφ.smul_section α.contMDiff⟩

omit [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
@[simp]
theorem tensor0SField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensor0SField_smulByFun n φ hφ α x = φ x • α x :=
  rfl

end SmulByFun

noncomputable def Tensor0SField.fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  ⟨fun x => ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (f x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) n b _).mpr
      fun σ x₀ => ?_

    have hcoord : ∀ x, (continuousMultilinearMap_basis b 0).repr
        (trivializationAt (Tensor0SModel 0 𝕜 E)
          (fun x => Tensor0SSpace 0 I x) x₀
          ⟨x, ContinuousMultilinearMap.constOfIsEmpty 𝕜
            (fun _ : Fin 0 => TangentSpace I x) (f x)⟩).2 σ = f x := by
      intro x
      simp_rw [continuousMultilinearMap_basis_repr]
      rfl
    simp_rw [hcoord]
    exact hf.contMDiffAt⟩

omit [IsManifold I (n + 1) M] in
@[simp]
theorem Tensor0SField.fromScalarField_apply [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) (x : M) (v : Fin 0 → TangentSpace I x) :
    Tensor0SSpace.toModel (Tensor0SField.fromScalarField n f hf x) v = f x := by
  unfold Tensor0SField.fromScalarField Tensor0SSpace.toModel tensor0SSpace_continuousLinearEquiv
  exact ContinuousMultilinearMap.constOfIsEmpty_apply _ _ _ _

noncomputable def Tensor0SField.toScalarField
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : M → 𝕜 :=
  fun x => Tensor0SSpace.toModel (α x) Fin.elim0


omit [IsManifold I (n + 1) M] in
theorem Tensor0SField.toScalarField_contMDiff [CompleteSpace 𝕜]
    (_hM : IsManifold I (n + 1) M)
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) n α.toScalarField := by
  letI := _hM
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hα := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
    (fun x => (α x : Tensor0SSpace 0 I x))).mp α.contMDiff)
  intro x₀
  refine (hα Fin.elim0 x₀).congr_of_eventuallyEq ?_
  have hbase := (trivializationAt (Tensor0SModel 0 𝕜 E)
    (fun x => Tensor0SSpace 0 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx

  have hα_const : α x = ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (Tensor0SField.toScalarField n α x) := by
    ext v

    simp only [tensor0SSpace_continuousLinearEquiv, ContinuousLinearEquiv.coe_mk,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id,
      Tensor0SField.toScalarField, Tensor0SSpace.toModel]

    change DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
      (α x) v =
      DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
      (α x) Fin.elim0
    exact congrArg _ (Subsingleton.elim v Fin.elim0)
  simp only [Tensor0SField.toScalarField]
  conv_rhs => rw [hα_const]
  simp_rw [continuousMultilinearMap_basis_repr]
  rfl

omit [IsManifold I (n + 1) M] in
@[simp]
theorem Tensor0SField.toScalarField_fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField.toScalarField n (Tensor0SField.fromScalarField n f hf) = f := by
  ext x
  exact Tensor0SField.fromScalarField_apply n f hf x Fin.elim0

@[simp]
theorem Tensor0SField.fromScalarField_toScalarField [CompleteSpace 𝕜]
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.fromScalarField n (Tensor0SField.toScalarField n α)
      (Tensor0SField.toScalarField_contMDiff n
        (inferInstance : IsManifold I (n + 1) M) α) = α := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  apply ContMDiffSection.ext; intro x

  simp only [Tensor0SField.fromScalarField]

  symm; ext v
  simp only [tensor0SSpace_continuousLinearEquiv, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id,
    Tensor0SField.toScalarField, Tensor0SSpace.toModel]
  change DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
    (α x) v =
    DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
    (α x) Fin.elim0
  exact congrArg _ (Subsingleton.elim v Fin.elim0)

omit [IsManifold I (n + 1) M] in
@[simp]
theorem Tensor0SField.toScalarField_add [CompleteSpace 𝕜]
    (α β : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (α + β).toScalarField n = α.toScalarField n + β.toScalarField n := by
  ext x
  simp only [Tensor0SField.toScalarField, Pi.add_apply]

  rw [show (α + β) x = α x + β x from rfl, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]

omit [IsManifold I (n + 1) M] in
@[simp]
theorem Tensor0SField.toScalarField_smulByFun [CompleteSpace 𝕜]
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (tensor0SField_smulByFun n φ hφ α).toScalarField n = φ * α.toScalarField n := by
  ext x
  simp only [Tensor0SField.toScalarField, tensor0SField_smulByFun_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Pi.mul_apply, smul_eq_mul]

omit n in

noncomputable def tensor0SSpace_evalScalar (x : M) :
    Tensor0SSpace 0 I x →L[𝕜] 𝕜 :=
  (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 => E) 𝕜 Fin.elim0).comp
    (Tensor0SSpace.toModelL 0 x)

omit n in
omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.evalScalar_apply (x : M) (c : Tensor0SSpace 0 I x) :
    tensor0SSpace_evalScalar x c = c Fin.elim0 := by
  change Tensor0SSpace.toModel c Fin.elim0 = c Fin.elim0
  exact congrArg c (Subsingleton.elim _ _)

omit n in
noncomputable def Tensor0SSpace.toRS0 {s : ℕ} {x : M} (A : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor0SSpace_evalScalar x).smulRight A

omit n in
omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.toRS0_apply {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (c : Tensor0SSpace 0 I x) :
    Tensor0SSpace.toRS0 A c = tensor0SSpace_evalScalar x c • A :=
  rfl

noncomputable def Tensor0SField.toTensorRSField {s : ℕ} [CompleteSpace 𝕜]
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0 s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  exact ⟨fun x => (tensor0SSpace_evalScalar x).smulRight (α x), by
    intro x₀
    rw [contMDiffAt_section x₀]
    have hα := (contMDiffAt_section x₀).mp α.contMDiff.contMDiffAt
    refine ((contMDiffAt_const
      (c := ContinuousLinearMap.smulRightL 𝕜
        (Tensor0SModel 0 𝕜 E)
        (Tensor0SModel s 𝕜 E)
        (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 => E) 𝕜 Fin.elim0))).clm_apply
      hα).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
    have hx_s : x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun y => Tensor0SSpace s I y) x₀).baseSet := hx
    apply ContinuousLinearMap.ext
    intro c₀
    apply ContinuousMultilinearMap.ext
    intro m
    rw [hom_trivializationAt_apply]
    simp only [ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousMultilinearMap.smul_apply,
      map_smul,
      Tensor0SSpace.evalScalar_apply]
    have hc₀ :
        ((trivializationAt (Tensor0SModel 0 𝕜 E)
          (fun y => Tensor0SSpace 0 I y) x₀).symmL 𝕜 x c₀) Fin.elim0 =
          (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 => E) 𝕜 Fin.elim0) c₀ := by
      change (Tensor0SSpace.constInChart (𝕜 := 𝕜) (I := I) 0 x₀ c₀ x) Fin.elim0 =
        c₀ Fin.elim0
      rw [Tensor0SSpace.constInChart_apply (𝕜 := 𝕜) (I := I)
        (x₀ := x₀) (x := x) 0 hx c₀ Fin.elim0]
      exact congrArg c₀ (Subsingleton.elim _ _)
    rw [hc₀]
    have hαx :
        ((trivializationAt (Tensor0SModel s 𝕜 E)
          (fun y => Tensor0SSpace s I y) x₀).continuousLinearMapAt 𝕜 x (α x)) m =
          (trivializationAt (Tensor0SModel s 𝕜 E)
            (fun y => Tensor0SSpace s I y) x₀ ⟨x, α x⟩).2 m := by
      rw [(trivializationAt (Tensor0SModel s 𝕜 E)
        (fun y => Tensor0SSpace s I y) x₀).continuousLinearMapAt_apply 𝕜]
      exact congrArg (fun A : Tensor0SModel s 𝕜 E => A m)
        (congrFun ((trivializationAt _ (fun y => Tensor0SSpace s I y) x₀
          ).coe_linearMapAt_of_mem (R := 𝕜) hx_s) (α x))
    rw [hαx]
    ⟩

omit [IsManifold I (n + 1) M] in
@[simp]
theorem Tensor0SField.toRS0_apply {s : ℕ} [CompleteSpace 𝕜]
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) (c : Tensor0SSpace 0 I x) :
    α.toTensorRSField n x c = tensor0SSpace_evalScalar x c • α x :=
  rfl


omit [IsManifold I (n + 1) M] in
theorem Tensor0SField.toRS0_eq {s : ℕ} [CompleteSpace 𝕜]
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    α.toTensorRSField n x = Tensor0SSpace.toRS0 (α x) := by
  ext c
  rw [Tensor0SField.toRS0_apply, Tensor0SSpace.toRS0_apply]

end
end Tensor0SBundle

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
variable {s q : ℕ}

variable (n : WithTop ℕ∞)

noncomputable def tensor0SField_product
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (β : Tensor0SField n q (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n (s + q) (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + q)
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) q
  ⟨fun x => (α x).product_fun (β x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    rw [contMDiff_multilinearSection_iff_coord (TangentSpace I) n b]
    intro σ x₀

    have hα := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
      (fun x => (α x : Tensor0SSpace s I x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
      (fun x => (β x : Tensor0SSpace q I x))).mp β.contMDiff)

    simp_rw [Bundle.continuousMultilinearMap.triv_coord_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

end
end Tensor0SBundle
