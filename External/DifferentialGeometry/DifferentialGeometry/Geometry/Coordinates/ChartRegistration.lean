import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option linter.style.longLine false








noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace OpenPartialHomeomorph






private theorem model_mem_contDiffGroupoid_of_contMDiffOn
    {n : WithTop ℕ∞} {e : OpenPartialHomeomorph H H}
    (he : ContMDiffOn I I n e e.source)
    (he_symm : ContMDiffOn I I n e.symm e.target) :
    e ∈ contDiffGroupoid n I := by
  have hlocal :
      ChartedSpace.LiftPropOn
        (contDiffGroupoid n I).IsLocalStructomorphWithinAt e e.source := by
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    exact ⟨he, he_symm⟩
  refine (contDiffGroupoid n I).locality ?_
  intro x hx
  have hxlocal := hlocal x hx
  rw [StructureGroupoid.liftPropWithinAt_self] at hxlocal
  have hxstruct :
      (contDiffGroupoid n I).IsLocalStructomorphWithinAt e e.source x :=
    hxlocal.2
  rw [e.isLocalStructomorphWithinAt_source_iff] at hxstruct
  obtain ⟨e', he'G, he'_sub, heq, hx_e'⟩ := hxstruct hx
  refine ⟨e'.source, e'.open_source, hx_e', ?_⟩
  have heq_on : Set.EqOn e e' (e.source ∩ e'.source) := by
    intro y hy
    exact heq hy.2
  have hrestr : e.restr e'.source ≈ e'.restr e.source :=
    OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source heq_on
  exact (contDiffGroupoid n I).mem_of_eqOnSource
    (closedUnderRestriction' he'G e.open_source) hrestr



theorem mem_maximalAtlas_of_contMDiffOn
    {n : WithTop ℕ∞}
    [IsManifold I n M]
    (e : OpenPartialHomeomorph M H)
    (he : ContMDiffOn I I n e e.source)
    (he_symm : ContMDiffOn I I n e.symm e.target) :
    e ∈ IsManifold.maximalAtlas I n M := by
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro c hc
  have hcmax : c ∈ IsManifold.maximalAtlas I n M := by
    rw [IsManifold.mem_maximalAtlas_iff]
    exact (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n I)) hc
  let f : OpenPartialHomeomorph H H := e.symm.trans c
  have hf : ContMDiffOn I I n f f.source := by
    change ContMDiffOn I I n (c ∘ e.symm) f.source
    exact (contMDiffOn_of_mem_maximalAtlas hcmax).comp
      (he_symm.mono (by intro y hy; simpa [f, mfld_simps] using hy.1))
      (by intro y hy; simpa [f, mfld_simps] using hy.2)
  have hf_symm : ContMDiffOn I I n f.symm f.target := by
    change ContMDiffOn I I n (e ∘ c.symm) f.target
    exact he.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hcmax).mono
        (by intro y hy; simpa [f, mfld_simps] using hy.1))
      (by intro y hy; simpa [f, mfld_simps] using hy.2)
  have hfG : f ∈ contDiffGroupoid n I :=
    model_mem_contDiffGroupoid_of_contMDiffOn (I := I) hf hf_symm
  refine ⟨?_, ?_⟩
  · simpa [f] using hfG
  · simpa [f] using (contDiffGroupoid n I).symm hfG

end OpenPartialHomeomorph

namespace PartialDiffeomorph




def ofOpenPartialHomeomorphRestr
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace Real E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {J : ModelWithCorners Real E₁ H₁}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₁ N]
    {n : WithTop ℕ∞}
    (e : OpenPartialHomeomorph M N)
    (s : Set M) (hs : IsOpen s) (hse : s ⊆ e.source)
    (he : ContMDiffOn I J n e s)
    (he_symm : ContMDiffOn J I n e.symm (e '' s)) :
    PartialDiffeomorph I J M N n where
  toFun := e
  invFun := e.symm
  source := s
  target := e '' s
  map_source' := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  map_target' := by
    rintro y ⟨x, hx, rfl⟩
    simpa [e.left_inv (hse hx)] using hx
  left_inv' := by
    intro x hx
    exact e.left_inv (hse hx)
  right_inv' := by
    rintro y ⟨x, hx, rfl⟩
    simp [e.left_inv (hse hx)]
  open_source := hs
  open_target := e.isOpen_image_of_subset_source hs hse
  contMDiffOn_toFun := he
  contMDiffOn_invFun := he_symm


def transDiffeomorph
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace Real E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {J : ModelWithCorners Real E₁ H₁}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₁ N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
    {n : WithTop ℕ∞}
    (Φ : PartialDiffeomorph I J M N n)
    (Ψ : N ≃ₘ^n⟮J, I⟯ P) :
    PartialDiffeomorph I I M P n where
  toPartialEquiv := Φ.toPartialEquiv.transEquiv Ψ.toEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target.preimage Ψ.symm.continuous
  contMDiffOn_toFun := by
    change ContMDiffOn I I n (Ψ ∘ Φ) Φ.source
    exact Ψ.contMDiff.comp_contMDiffOn Φ.contMDiffOn_toFun
  contMDiffOn_invFun := by
    change ContMDiffOn I I n (Φ.toPartialEquiv.symm ∘ Ψ.symm) (Ψ.symm ⁻¹' Φ.target)
    exact Φ.contMDiffOn_invFun.comp Ψ.symm.contMDiff.contMDiffOn (by intro y hy; exact hy)

@[simp]
theorem transDiffeomorph_toOpenPartialHomeomorph
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace Real E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {J : ModelWithCorners Real E₁ H₁}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₁ N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
    {n : WithTop ℕ∞}
    (Φ : PartialDiffeomorph I J M N n)
    (Ψ : N ≃ₘ^n⟮J, I⟯ P) :
    (transDiffeomorph (I := I) Φ Ψ).toOpenPartialHomeomorph =
      Φ.toOpenPartialHomeomorph.transHomeomorph Ψ.toHomeomorph := by
  rfl



theorem toOpenPartialHomeomorph_mem_maximalAtlas
    {n : WithTop ℕ∞}
    [IsManifold I n M]
    (Φ : PartialDiffeomorph I I M H n) :
    Φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas I n M := by
  exact OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn (I := I)
    Φ.toOpenPartialHomeomorph
    (by simpa using Φ.contMDiffOn_toFun)
    (by simpa using Φ.contMDiffOn_invFun)

end PartialDiffeomorph

end DifferentialGeometry.Tensor.Coordinates
