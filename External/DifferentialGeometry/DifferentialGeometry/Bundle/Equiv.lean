


import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Bundle.Zero
import Mathlib.Geometry.Manifold.VectorBundle.Basic


open Bundle

structure VectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where

  baseMap : B₁ → B₂

  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂

  continuous_toFun : Continuous toFun

  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)

  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace VectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂) (hΦ : Continuous Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  continuous_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B := by
  obtain ⟨f_A, Φ_A, _, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, _, φ_B, hB⟩ := B
  simp only at h
  subst h
  have hf : f_A = f_B := by
    ext x
    have h1 := hA x 0; have h2 := hB x 0
    simp only [map_zero] at h1 h2
    rw [h1] at h2
    exact congrArg TotalSpace.proj h2
  subst hf
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext x v
  have h1 := hA x v; rw [hB] at h1
  exact TotalSpace.mk_inj.mp h1.symm

theorem baseMap_eq (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj := by
  simp [f.fiber_compat, map_zero]

theorem baseMapContinuous
    [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : Continuous f.baseMap := by
  have h : f.baseMap = TotalSpace.proj ∘ f.toFun ∘ zeroSection F₁ E₁ := by
    ext x; simp [baseMap_eq, zeroSection]
  rw [h]
  exact (FiberBundle.continuous_proj F₂ E₂).comp
    (f.continuous_toFun.comp (continuous_zeroSection 𝕜))

@[simp]
theorem proj_eq (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [f.fiber_compat]

@[simp]
theorem toFun_apply (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩ :=
  f.fiber_compat x v

def id : VectorBundleHom 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  continuous_toFun := continuous_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

def comp (g : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃) (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat]
    congr 1

end VectorBundleHom

structure VectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where

  baseMap : B₁ → B₂

  toHomeomorph : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂

  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)

  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toHomeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace VectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

def mk'
    (Φ : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toHomeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toHomeomorph = B.toHomeomorph) : A = B := by
  obtain ⟨f_A, Φ_A, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

theorem baseMap_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toHomeomorph ⟨x, 0⟩).proj := by
  simp [e.fiber_compat, map_zero]

theorem baseMapBijective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap := by
  constructor
  · intro x₁ x₂ h
    have h₁ := e.fiber_compat x₁ 0
    have h₂ := e.fiber_compat x₂ 0
    simp only [map_zero] at h₁ h₂
    have hinj := e.toHomeomorph.injective (h₁.trans (by rw [h]) |>.trans h₂.symm)
    exact congrArg TotalSpace.proj hinj
  · intro y
    obtain ⟨⟨x, v⟩, hxv⟩ := e.toHomeomorph.surjective ⟨y, 0⟩
    have := e.fiber_compat x v
    rw [this] at hxv
    exact ⟨x, congrArg TotalSpace.proj hxv⟩

@[simp]
theorem proj_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (e.toHomeomorph p).proj = e.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [e.fiber_compat]

@[simp]
theorem toHomeomorph_apply (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    e.toHomeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩ :=
  e.fiber_compat x v

def toVectorBundleHom (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toHomeomorph
  continuous_toFun := e.toHomeomorph.continuous
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

def refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toHomeomorph := Homeomorph.refl _
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

def symm (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₂ E₂ F₁ E₁ where
  baseMap y := (e.toHomeomorph.symm ⟨y, 0⟩).proj
  toHomeomorph := e.toHomeomorph.symm
  fiberLinearEquiv y :=

    let x := (e.toHomeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toHomeomorph.symm ⟨y, 0⟩)
      rw [e.toHomeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by
    have key : ∀ (x : B₁) (hx : e.baseMap x = y),
        (⟨y, v⟩ : TotalSpace F₂ E₂) =
        ⟨e.baseMap x, e.fiberLinearEquiv x ((hx ▸ e.fiberLinearEquiv x).symm v)⟩ := by
      intro x hx; subst hx; simp [LinearEquiv.apply_symm_apply]
    apply e.toHomeomorph.injective
    rw [e.toHomeomorph.apply_symm_apply, e.toHomeomorph_apply]
    exact key _ _

def trans (e₁₂ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (e₂₃ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toHomeomorph := e₁₂.toHomeomorph.trans e₂₃.toHomeomorph
  fiberLinearEquiv x := (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Homeomorph.trans_apply, e₁₂.fiber_compat, e₂₃.fiber_compat, Function.comp]
    congr 1

end VectorBundleEquiv

section TrivializationCoord

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

noncomputable def trivializationCoord (baseMap : B₁ → B₂)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)) (x : B₁) : B₁ → (F₁ →L[𝕜] F₂) := by
  classical
  exact fun q =>
    if hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
        baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet then
      LinearMap.toContinuousLinearMap
        (((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
          𝕜 (baseMap q) hq.2).toLinearMap.comp
          ((φ q).comp
            ((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq.1).symm.toLinearMap))
    else 0

lemma trivializationCoord_apply
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (x q : B₁)
    (hq₁ : q ∈ (trivializationAt F₁ E₁ x).baseSet)
    (hq₂ : baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet)
    (v : F₁) :
    trivializationCoord baseMap φ x q v =
      ((trivializationAt F₂ E₂ (baseMap x))
        (Φ ((trivializationAt F₁ E₁ x).toOpenPartialHomeomorph.symm (q, v)))).2 := by
  simp only [trivializationCoord,
    dif_pos (show q ∈ _ ∧ baseMap q ∈ _ from ⟨hq₁, hq₂⟩)]
  conv_rhs =>
    rw [(trivializationAt F₁ E₁ x).symm_apply_eq_mk_continuousLinearEquivAt_symm
          (R := 𝕜) q hq₁ v,
        hcompat,
        congrArg Prod.snd
          ((trivializationAt F₂ E₂ (baseMap x)).apply_eq_prod_continuousLinearEquivAt
            𝕜 (baseMap q) hq₂ _)]
  rfl

lemma trivializationCoord_isInvertible
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hφ_bij : ∀ x, Function.Bijective (φ x))
    (x q : B₁)
    (hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
      baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet) :
    (trivializationCoord baseMap φ x q : F₁ →L[𝕜] F₂).IsInvertible := by
  obtain ⟨hq₁, hq₂⟩ := hq
  simp only [trivializationCoord,
    dif_pos (show q ∈ _ ∧ baseMap q ∈ _ from ⟨hq₁, hq₂⟩)]
  have hbij_lm : Function.Bijective
      (((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
          𝕜 (baseMap q) hq₂).toLinearMap.comp
        ((φ q).comp
          ((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq₁).symm.toLinearMap)) :=
    (((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq₁).symm.toLinearEquiv.trans
      (LinearEquiv.ofBijective (φ q) (hφ_bij q)) |>.trans
      ((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
        𝕜 (baseMap q) hq₂).toLinearEquiv).bijective
  exact ⟨(LinearEquiv.ofBijective _ hbij_lm).toContinuousLinearEquiv, by ext; rfl⟩

lemma trivializationCoord_inverse_eventuallyEq
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (baseMap : B₁ ≃ₜ B₂)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x))
    (x : B₁) (w : E₂ (baseMap x)) :
    (fun p : B₂ × F₂ =>
        ContinuousLinearMap.inverse
          (trivializationCoord baseMap φ x (baseMap.symm p.1)) p.2)
      =ᶠ[nhds ((trivializationAt F₂ E₂ (baseMap x)) ⟨baseMap x, w⟩)]
    (fun p : B₂ × F₂ => ((trivializationAt F₁ E₁ x)
      ((Equiv.ofBijective Φ hbij).symm
        ((trivializationAt F₂ E₂ (baseMap x)).toOpenPartialHomeomorph.symm p))).2) := by
  set e₁ := trivializationAt F₁ E₁ x
  set e₂ := trivializationAt F₂ E₂ (baseMap x)
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
  have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
  have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source :=
    e₂.mem_source.mpr hx₂
  have hproj : ∀ p, (Φ_equiv.symm p).proj = baseMap.symm p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    have h := congrArg TotalSpace.proj h1
    simp only at h
    rw [← h, baseMap.symm_apply_apply]
  have hU : ((baseMap '' e₁.baseSet) ∩ e₂.baseSet) ×ˢ (Set.univ : Set F₂) ∈
      nhds (e₂ ⟨baseMap x, w⟩) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact ((baseMap.isOpenMap _ e₁.open_baseSet).inter e₂.open_baseSet).prod isOpen_univ
    · refine ⟨⟨⟨x, hx₁, ?_⟩, ?_⟩, Set.mem_univ _⟩
      · exact (e₂.coe_fst he₂_source).symm
      · exact e₂.coe_fst he₂_source ▸ hx₂
  filter_upwards [hU] with ⟨q', v⟩ ⟨⟨⟨q, hq₁, hq_eq⟩, hq₂'⟩, _⟩
  simp only at hq_eq hq₂'
  have hq : baseMap.symm q' = q := by rw [← hq_eq]; exact baseMap.symm_apply_apply q
  have hq₂ : baseMap (baseMap.symm q') ∈ e₂.baseSet := by
    rw [baseMap.apply_symm_apply]; exact hq₂'
  have hA_inv_q := trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x
    (baseMap.symm q') ⟨hq ▸ hq₁, hq₂⟩
  have hAG : trivializationCoord baseMap φ x (baseMap.symm q')
      ((e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q', v)))).2) = v := by
    set p := Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q', v))
    have hp_proj : p.proj = baseMap.symm q' := by
      have h1 := hproj (e₂.toOpenPartialHomeomorph.symm (q', v))
      have h2 : (e₂.toOpenPartialHomeomorph.symm (q', v)).proj = q' :=
        e₂.proj_symm_apply (e₂.mem_target.mpr hq₂')
      rw [h2] at h1; exact h1
    have hp_mem : p ∈ e₁.source := e₁.mem_source.mpr (hp_proj ▸ hq ▸ hq₁)
    rw [trivializationCoord_apply hcompat x (baseMap.symm q') (hq ▸ hq₁) hq₂,
        show e₁.toOpenPartialHomeomorph.symm (baseMap.symm q', (e₁ p).2) = p from by
          conv_rhs => rw [← e₁.toOpenPartialHomeomorph.left_inv hp_mem]
          congr 1; exact Prod.ext (e₁.coe_fst hp_mem ▸ hp_proj).symm rfl,
        show Φ p = e₂.toOpenPartialHomeomorph.symm (q', v) from
          Φ_equiv.apply_symm_apply _,
        congrArg Prod.snd (e₂.apply_symm_apply' hq₂')]
  exact hA_inv_q.inverse_apply_eq.mpr hAG.symm

end TrivializationCoord

section ToVectorBundleEquivGeneral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] in

private lemma fiberBijective_of_bijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ)
    (hbase_inj : Function.Injective baseMap)
    (x : B₁) :
    Function.Bijective (φ x) := by
  refine ⟨fun v w hvw => TotalSpace.mk_inj.mp
    (hbij.1 (by rw [hcompat x v, hcompat x w, hvw])), fun w => ?_⟩
  obtain ⟨⟨y, v⟩, hv⟩ := hbij.2 (⟨baseMap x, w⟩ : TotalSpace F₂ E₂)
  rw [hcompat y v] at hv
  have hy : y = x := hbase_inj (congrArg TotalSpace.proj hv)
  subst hy
  exact ⟨v, TotalSpace.mk_inj.mp hv⟩

private lemma continuousAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContinuousAt (fun q => A q v) x) :
    ContinuousAt A x := by
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  rw [(LinearMap.isClosedEmbedding_of_injective (f := evalBasis.toLinearMap)
    (LinearMap.ker_eq_bot.mpr evalBasis_inj)).isEmbedding.continuousAt_iff]
  exact continuousAt_pi.mpr fun i => h (bF₁ i)

private lemma continuous_symm_of_fiberBijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} (hΦ_cont : Continuous Φ)
    (baseMap : B₁ ≃ₜ B₂)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    Continuous (Equiv.ofBijective Φ hbij).symm := by
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hproj : ∀ p, (Φ_equiv.symm p).proj = baseMap.symm p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    have h := congrArg TotalSpace.proj h1
    simp only at h
    rw [← h, baseMap.symm_apply_apply]
  rw [continuous_iff_continuousAt]
  rintro ⟨y, w⟩
  obtain ⟨x, rfl⟩ : ∃ x, baseMap x = y :=
    ⟨baseMap.symm y, baseMap.apply_symm_apply y⟩
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨?_, ?_⟩
  · simp only [hproj]
    exact (baseMap.symm.continuous.comp
      (FiberBundle.continuous_proj F₂ E₂)).continuousAt
  · simp only [hproj, Homeomorph.symm_apply_apply]
    set e₁ := trivializationAt F₁ E₁ x
    set e₂ := trivializationAt F₂ E₂ (baseMap x)
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
    have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source :=
      e₂.mem_source.mpr hx₂
    set A : B₁ → (F₁ →L[𝕜] F₂) := trivializationCoord baseMap φ x with hA_def
    have hΦ_proj : ∀ p, (Φ p).proj = baseMap p.proj := fun p => by
      obtain ⟨a, b⟩ := p; simp [hcompat]
    have hA_cont : ContinuousAt A x := by
      apply continuousAt_clm_of_pointwise
      intro v
      suffices h : ContinuousAt
          (fun q => (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2) x by
        refine h.congr (Filter.eventually_of_mem
          (IsOpen.mem_nhds (e₁.open_baseSet.inter
            (baseMap.continuous.isOpen_preimage _ e₂.open_baseSet)) ⟨hx₁, ?_⟩) ?_)
        · exact hx₂
        · intro q ⟨hq₁, hq₂⟩
          exact (trivializationCoord_apply hcompat x q hq₁ hq₂ v).symm
      have he₁_symm_cont : ContinuousAt
          (fun q => e₁.toOpenPartialHomeomorph.symm (q, v)) x :=
        (e₁.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
          (e₁.toOpenPartialHomeomorph.open_target.mem_nhds
            (by rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩))).comp
          (ContinuousAt.prodMk continuousAt_id continuousAt_const)
      have hpΦ : Φ (e₁.toOpenPartialHomeomorph.symm (x, v)) ∈ e₂.source := by
        rw [e₂.mem_source, hΦ_proj,
          e₁.proj_symm_apply (by rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩)]
        exact hx₂
      have he₂_at : ContinuousAt e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (x, v))) :=
        e₂.continuousOn.continuousAt (e₂.open_source.mem_nhds hpΦ)
      have hcomp1 : ContinuousAt
          (fun q => Φ (e₁.toOpenPartialHomeomorph.symm (q, v))) x := by
        refine ContinuousAt.comp ?_ he₁_symm_cont
        exact hΦ_cont.continuousAt
      have hcomp2 : ContinuousAt
          (fun q => e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))) x := by
        refine ContinuousAt.comp ?_ hcomp1
        exact he₂_at
      exact hcomp2.snd
    haveI : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
    have hA_inv_at_x : (A x : F₁ →L[𝕜] F₂).IsInvertible :=
      trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x x ⟨hx₁, hx₂⟩
    have hA_inv_cont : ContinuousAt (ContinuousLinearMap.inverse ∘ A) x :=
      (hA_inv_at_x.contDiffAt_map_inverse (n := 0)).continuousAt.comp hA_cont

    have hNice_cont : ContinuousAt
        (fun p : B₂ × F₂ =>
          ContinuousLinearMap.inverse (A (baseMap.symm p.1)) p.2) (e₂ ⟨baseMap x, w⟩) := by
      have h1 : ContinuousAt
          (fun p : B₂ × F₂ =>
            ContinuousLinearMap.inverse (A (baseMap.symm p.1))) (e₂ ⟨baseMap x, w⟩) := by
        change ContinuousAt
          ((ContinuousLinearMap.inverse ∘ A) ∘ (baseMap.symm ∘ Prod.fst)) (e₂ ⟨baseMap x, w⟩)
        refine ContinuousAt.comp ?_
          (baseMap.symm.continuous.continuousAt.comp continuousAt_fst)
        convert hA_inv_cont using 1
        simp [e₂.coe_fst he₂_source]
      exact h1.clm_apply continuousAt_snd
    have hG_snd_cont : ContinuousAt
        (fun p : B₂ × F₂ => (e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm p))).2)
        (e₂ ⟨baseMap x, w⟩) :=
      hNice_cont.congr
        (trivializationCoord_inverse_eventuallyEq baseMap hcompat hbij hφ_bij x w)
    exact (hG_snd_cont.comp (e₂.toOpenPartialHomeomorph.continuousAt he₂_source)).congr
      (by filter_upwards [e₂.open_source.mem_nhds he₂_source] with p hp
          exact congrArg (fun q => (e₁ (Φ_equiv.symm q)).2)
            (e₂.toOpenPartialHomeomorph.left_inv hp))

noncomputable def VectorBundleHom.toVectorBundleEquiv
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (baseMap : B₁ ≃ₜ B₂)
    (hbase : f.baseMap = baseMap)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ := by
  obtain ⟨bm, Φ, hΦ_cont, φ, hcompat⟩ := f
  simp only at hbase
  subst hbase
  change Function.Bijective Φ at hbij
  have hcompat' : ∀ x v, Φ ⟨x, v⟩ = (⟨baseMap x, φ x v⟩ : TotalSpace F₂ E₂) := hcompat
  have hφ_bij : ∀ x, Function.Bijective (φ x) :=
    fiberBijective_of_bijective' hcompat' hbij baseMap.injective
  exact {
    baseMap := baseMap
    toHomeomorph := ⟨Equiv.ofBijective Φ hbij, hΦ_cont,
      continuous_symm_of_fiberBijective' hΦ_cont baseMap hcompat' hbij hφ_bij⟩
    fiberLinearEquiv := fun x => LinearEquiv.ofBijective (φ x) (hφ_bij x)
    fiber_compat := fun x v => hcompat' x v
  }

end ToVectorBundleEquivGeneral

section ToVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

private lemma continuous_symm_of_fiberBijective
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} (hΦ_cont : Continuous Φ)
    {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    Continuous (Equiv.ofBijective Φ hbij).symm :=
  continuous_symm_of_fiberBijective' hΦ_cont (Homeomorph.refl B) hcompat hbij hφ_bij

noncomputable def VectorBundleHom.toVectorBundleEquivId
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  f.toVectorBundleEquiv (Homeomorph.refl B) hid hbij

end ToVectorBundleEquiv

open scoped Manifold

structure ContMDiffVectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toDiffeomorph : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toDiffeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace ContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

def mk'
    (Φ : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
      (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toDiffeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toDiffeomorph = B.toDiffeomorph) : A = B := by
  obtain ⟨f_A, Φ_A, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

theorem baseMap_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toDiffeomorph ⟨x, 0⟩).proj := by
  simp [e.fiber_compat, map_zero]

theorem baseMapBijective (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap := by
  constructor
  · intro x₁ x₂ h
    have h₁ := e.fiber_compat x₁ 0
    have h₂ := e.fiber_compat x₂ 0
    simp only [map_zero] at h₁ h₂
    have hinj := e.toDiffeomorph.injective (h₁.trans (by rw [h]) |>.trans h₂.symm)
    exact congrArg TotalSpace.proj hinj
  · intro y
    obtain ⟨⟨x, v⟩, hxv⟩ := e.toDiffeomorph.surjective ⟨y, 0⟩
    have h := e.fiber_compat x v
    have : (e.toDiffeomorph.toEquiv ⟨x, v⟩) = e.toDiffeomorph ⟨x, v⟩ := rfl
    rw [this, h] at hxv
    exact ⟨x, congrArg TotalSpace.proj hxv⟩

def toVectorBundleEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toHomeomorph := e.toDiffeomorph.toHomeomorph
  fiberLinearEquiv := e.fiberLinearEquiv
  fiber_compat x v := e.fiber_compat x v

@[simp]
theorem proj_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) : (e.toDiffeomorph p).proj = e.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [e.fiber_compat]

@[simp]
theorem toDiffeomorph_apply (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    e.toDiffeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩ :=
  e.fiber_compat x v

def refl : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toDiffeomorph := Diffeomorph.refl (IB.prod 𝓘(𝕜, F₁)) (TotalSpace F₁ E₁) n
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

def symm (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₁ E₁ where
  baseMap y := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
  toDiffeomorph := e.toDiffeomorph.symm
  fiberLinearEquiv y :=
    let x := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toDiffeomorph.symm ⟨y, 0⟩)
      simp [e.toDiffeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by exact e.toVectorBundleEquiv.symm.fiber_compat y v

def trans (e₁₂ : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (e₂₃ : ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₃ E₃) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toDiffeomorph := e₁₂.toDiffeomorph.trans e₂₃.toDiffeomorph
  fiberLinearEquiv x :=
    (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, e₁₂.fiber_compat, e₂₃.fiber_compat]
    congr 1

end ContMDiffVectorBundleEquiv

structure ContMDiffVectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  contMDiff_toFun : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n toFun
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace ContMDiffVectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂)
    (hΦ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  contMDiff_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B := by
  obtain ⟨f_A, Φ_A, _, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, _, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

theorem baseMap_eq (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj := by
  simp [f.fiber_compat, map_zero]

theorem baseMapContMDiff [ContMDiffVectorBundle n F₁ E₁ IB]
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiff IB IB n f.baseMap := by
  have h : f.baseMap = TotalSpace.proj ∘ f.toFun ∘ zeroSection F₁ E₁ := by
    ext x; simp [baseMap_eq, zeroSection]
  rw [h]
  have h₁ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁)) n (zeroSection F₁ E₁) :=
    contMDiff_zeroSection 𝕜 E₁
  have h₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) IB n (TotalSpace.proj (F := F₂) (E := E₂)) :=
    (contMDiff_proj E₂).of_le le_top
  exact h₂.comp (f.contMDiff_toFun.comp h₁)

def toVectorBundleHom (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := f.baseMap
  toFun := f.toFun
  continuous_toFun := f.contMDiff_toFun.continuous
  fiberLinearMap := f.fiberLinearMap
  fiber_compat x v := f.fiber_compat x v

@[simp]
theorem proj_eq (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [f.fiber_compat]

@[simp]
theorem toFun_apply (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩ :=
  f.fiber_compat x v

def id : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  contMDiff_toFun := contMDiff_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

def comp (g : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₃ E₃)
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  contMDiff_toFun := g.contMDiff_toFun.comp f.contMDiff_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat]
    congr 1

def ofEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toDiffeomorph
  contMDiff_toFun := e.toDiffeomorph.contMDiff
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

end ContMDiffVectorBundleHom

section ToContMDiffVectorBundleEquivGeneral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]

lemma contMDiffAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  haveI : FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let g : (Fin (Module.finrank 𝕜 F₁) → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ x, g (evalBasis x) = x := fun x => congr($(hgLM) x)
  have hEA : ContMDiffAt IB 𝓘(𝕜, Fin _ → F₂) n (evalBasis ∘ A) x :=
    contMDiffAt_pi_space.mpr fun i => h (bF₁ i)
  have : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [this]
  exact g.contDiff.contMDiff.contMDiffAt.comp _ hEA

private lemma contMDiff_symm_of_fiberBijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (baseMap : Diffeomorph IB IB B₁ B₂ n)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (Equiv.ofBijective Φ hbij).symm := by
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hproj : ∀ p, (Φ_equiv.symm p).proj = baseMap.symm p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    have h := congrArg TotalSpace.proj h1
    simp only at h
    rw [← h, baseMap.symm_apply_apply]
  intro ⟨y, w⟩
  obtain ⟨x, rfl⟩ : ∃ x, baseMap x = y :=
    ⟨baseMap.symm y, baseMap.apply_symm_apply y⟩
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · simp only [hproj]
    have hbm_symm : ContMDiff (IB.prod 𝓘(𝕜, F₂)) IB n
        (fun p : TotalSpace F₂ E₂ => baseMap.symm p.proj) :=
      baseMap.symm.contMDiff.comp ((contMDiff_proj E₂).of_le le_top)
    exact hbm_symm.contMDiffAt
  · simp only [hproj, Diffeomorph.symm_apply_apply]
    set e₁ := trivializationAt F₁ E₁ x
    set e₂ := trivializationAt F₂ E₂ (baseMap x)
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
    have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source :=
      e₂.mem_source.mpr hx₂
    set A : B₁ → (F₁ →L[𝕜] F₂) := trivializationCoord baseMap φ x with hA_def
    have hΦ_proj : ∀ p, (Φ p).proj = baseMap p.proj := fun p => by
      obtain ⟨a, b⟩ := p; simp [hcompat]
    have hA_contMDiff : ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
      apply contMDiffAt_clm_of_pointwise
      intro v
      suffices h : ContMDiffAt IB 𝓘(𝕜, F₂) n
          (fun q => (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2) x by
        refine h.congr_of_eventuallyEq (Filter.eventually_of_mem
          (IsOpen.mem_nhds (e₁.open_baseSet.inter
            (baseMap.continuous.isOpen_preimage _ e₂.open_baseSet)) ⟨hx₁, ?_⟩) ?_)
        · exact hx₂
        · intro q ⟨hq₁, hq₂⟩
          exact trivializationCoord_apply hcompat x q hq₁ hq₂ v
      have he₁_tgt : (x, v) ∈ e₁.target := by
        rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩
      have he₁_symm : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n
          (fun q => e₁.toOpenPartialHomeomorph.symm (q, v)) x := by
        have h1 := e₁.contMDiffOn_symm (n := n) (IB := IB) |>.contMDiffAt
          (e₁.toOpenPartialHomeomorph.open_target.mem_nhds he₁_tgt)
        have h2 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n (fun q => (q, v)) x :=
          contMDiffAt_id.prodMk contMDiffAt_const
        exact h1.comp x h2
      have hpΦ : Φ (e₁.toOpenPartialHomeomorph.symm (x, v)) ∈ e₂.source := by
        rw [e₂.mem_source, hΦ_proj, e₁.proj_symm_apply he₁_tgt]; exact hx₂
      have hΦ_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ
          (e₁.toOpenPartialHomeomorph.symm (x, v)) := hΦ_smooth.contMDiffAt
      have he₂_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂)) n e₂
          (Φ (e₁.toOpenPartialHomeomorph.symm (x, v))) :=
        e₂.contMDiffOn (n := n) (IB := IB) |>.contMDiffAt
          (e₂.open_source.mem_nhds hpΦ)
      have hcomp1 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
          (fun q => Φ (e₁.toOpenPartialHomeomorph.symm (q, v))) x := by
        refine hΦ_at.comp x he₁_symm
      have hcomp2 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
          (fun q => e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))) x := by
        refine he₂_at.comp x hcomp1
      exact hcomp2.snd
    haveI : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
    have hA_inv_at_x : (A x : F₁ →L[𝕜] F₂).IsInvertible :=
      trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x x ⟨hx₁, hx₂⟩
    have hA_inv_contMDiff : ContMDiffAt IB 𝓘(𝕜, F₂ →L[𝕜] F₁) n
        (ContinuousLinearMap.inverse ∘ A) x :=
      (hA_inv_at_x.contDiffAt_map_inverse (n := n)).contMDiffAt.comp x hA_contMDiff
    have hNice_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₁) n
        (fun p : B₂ × F₂ =>
          ContinuousLinearMap.inverse (A (baseMap.symm p.1)) p.2) (e₂ ⟨baseMap x, w⟩) := by
      have h1 : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₂ →L[𝕜] F₁) n
          (fun p : B₂ × F₂ =>
            ContinuousLinearMap.inverse (A (baseMap.symm p.1))) (e₂ ⟨baseMap x, w⟩) := by
        have hfst_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) IB n
            (fun p : B₂ × F₂ => p.1) (e₂ ⟨baseMap x, w⟩) := contMDiffAt_fst
        have hbm_at : ContMDiffAt IB IB n baseMap.symm
            ((fun p : B₂ × F₂ => p.1) (e₂ ⟨baseMap x, w⟩)) :=
          baseMap.symm.contMDiff.contMDiffAt
        have hcomp_bm : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) IB n
            (baseMap.symm ∘ (fun p : B₂ × F₂ => p.1)) (e₂ ⟨baseMap x, w⟩) :=
          hbm_at.comp _ hfst_at
        have hbm_eq : (baseMap.symm ∘ (fun p : B₂ × F₂ => p.1)) (e₂ ⟨baseMap x, w⟩) = x := by
          simp [e₂.coe_fst he₂_source, baseMap.symm_apply_apply]
        have hAinv_at : ContMDiffAt IB 𝓘(𝕜, F₂ →L[𝕜] F₁) n
            (ContinuousLinearMap.inverse ∘ A)
            ((baseMap.symm ∘ (fun p : B₂ × F₂ => p.1)) (e₂ ⟨baseMap x, w⟩)) := by
          rw [hbm_eq]; exact hA_inv_contMDiff
        exact hAinv_at.comp _ hcomp_bm
      exact h1.clm_apply contMDiffAt_snd
    have hG_snd_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₁) n
        (fun p : B₂ × F₂ =>
          (e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm p))).2) (e₂ ⟨baseMap x, w⟩) :=
      hNice_smooth.congr_of_eventuallyEq
        (trivializationCoord_inverse_eventuallyEq baseMap.toHomeomorph
          hcompat hbij hφ_bij x w).symm
    have he₂_smooth := (e₂.contMDiffOn (n := n) (IB := IB)).contMDiffAt
      (e₂.open_source.mem_nhds he₂_source)
    exact (hG_snd_smooth.comp _ he₂_smooth).congr_of_eventuallyEq
      (by filter_upwards [e₂.open_source.mem_nhds he₂_source] with p hp
          exact congrArg (fun q => (e₁ (Φ_equiv.symm q)).2)
            (e₂.toOpenPartialHomeomorph.left_inv hp).symm)

noncomputable def ContMDiffVectorBundleHom.toContMDiffVectorBundleEquiv
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (baseMap : Diffeomorph IB IB B₁ B₂ n)
    (hbase : f.baseMap = baseMap)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ := by
  obtain ⟨bm, Φ, hΦ_smooth, φ, hcompat⟩ := f
  simp only at hbase
  subst hbase
  change Function.Bijective Φ at hbij
  have hcompat' : ∀ x v, Φ ⟨x, v⟩ = (⟨baseMap x, φ x v⟩ : TotalSpace F₂ E₂) := hcompat
  have hφ_bij : ∀ x, Function.Bijective (φ x) :=
    fiberBijective_of_bijective' hcompat' hbij baseMap.injective
  exact {
    baseMap := baseMap
    toDiffeomorph :=
      { toEquiv := Equiv.ofBijective Φ hbij
        contMDiff_toFun := hΦ_smooth
        contMDiff_invFun :=
          contMDiff_symm_of_fiberBijective' hΦ_smooth baseMap hcompat' hbij hφ_bij }
    fiberLinearEquiv := fun x => LinearEquiv.ofBijective (φ x) (hφ_bij x)
    fiber_compat := fun x v => hcompat' x v
  }

end ToContMDiffVectorBundleEquivGeneral

section ToContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]

private lemma contMDiff_symm_of_fiberBijective
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (Equiv.ofBijective Φ hbij).symm :=
  contMDiff_symm_of_fiberBijective' hΦ_smooth (Diffeomorph.refl IB B n) hcompat hbij hφ_bij

noncomputable def ContMDiffVectorBundleHom.toContMDiffVectorBundleEquivId
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  f.toContMDiffVectorBundleEquiv (Diffeomorph.refl IB B n) hid hbij

section FiberwiseEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

def ContMDiffVectorBundleHom.ofFiberwiseLinearMap
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (f : B → B₂)
    (φ : ∀ x : B, E₁ x →ₗ[𝕜] E₂ (f x))
    (h_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨f p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂))) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := f
  toFun p := ⟨f p.1, φ p.1 p.2⟩
  contMDiff_toFun := h_smooth
  fiberLinearMap := φ
  fiber_compat _ _ := rfl

noncomputable def ContMDiffVectorBundleEquiv.ofMutualInverseHoms
    (Φ : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (Ψ : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₁ E₁)
    (hΦ : Φ.baseMap = _root_.id)
    (hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p)
    (hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  have hΨ : Ψ.baseMap = _root_.id := by
    funext y
    have h := congrArg TotalSpace.proj (hΦΨ ⟨y, 0⟩)
    rwa [Φ.proj_eq, Ψ.proj_eq, hΦ] at h
  match Φ, Ψ, hΦ, hΨ, hΨΦ, hΦΨ with
  | ⟨_, toFunΦ, hcΦ, φ, compatΦ⟩, ⟨_, toFunΨ, hcΨ, ψ, compatΨ⟩,
    rfl, rfl, hΨΦ, hΦΨ =>
    { baseMap := _root_.id
      toDiffeomorph :=
        { toEquiv := ⟨toFunΦ, toFunΨ, hΨΦ, hΦΨ⟩
          contMDiff_toFun := hcΦ
          contMDiff_invFun := hcΨ }
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofLinear (φ x) (ψ x)
          (LinearMap.ext fun v => by
            have h := hΦΨ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
          (LinearMap.ext fun v => by
            have h := hΨΦ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
      fiber_compat := compatΦ }

noncomputable def ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (φ : ∀ x : B, E₁ x ≃ₗ[𝕜] E₂ x)
    (h_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂)))
    (h_smooth_inv : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (fun p : TotalSpace F₂ E₂ => (⟨p.1, (φ p.1).symm p.2⟩ : TotalSpace F₁ E₁))) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := _root_.id
  toDiffeomorph :=
    { toEquiv :=
        { toFun := fun p => ⟨p.1, φ p.1 p.2⟩
          invFun := fun p => ⟨p.1, (φ p.1).symm p.2⟩
          left_inv := fun ⟨_, v⟩ => by simp
          right_inv := fun ⟨_, v⟩ => by simp }
      contMDiff_toFun := h_smooth
      contMDiff_invFun := h_smooth_inv }
  fiberLinearEquiv := φ
  fiber_compat _ _ := rfl

end FiberwiseEquiv

end ToContMDiffVectorBundleEquiv
