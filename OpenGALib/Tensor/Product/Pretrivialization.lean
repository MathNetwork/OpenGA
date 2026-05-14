import OpenGALib.Tensor.Product.Defs
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Pretrivialization for tensor-product bundles
# Pretrivialization for Tensor Product Bundles

This file constructs the pretrivialization and coordinate change maps for the tensor product
of two vector bundles.

## Main Definitions

* `Pretrivialization.tensorProductCoordChange` : the coordinate change function for tensor
  product bundles, given by factor-wise coordinate change via `TensorProduct.mapL`.
* `Pretrivialization.tensorProduct e₁ e₂` : the pretrivialization for the tensor product
  bundle induced by trivializations `e₁` and `e₂`.

## Main Results

* `continuousOn_tensorProductCoordChange` : the coordinate change map of the tensor product
  bundle is continuous on the overlap of base sets.
* `tensorProductCoordChange_apply` : the coordinate change equals re-trivializing via the
  new pair after un-trivializing via the old pair.

## Tags

tensor product, pretrivialization, coordinate change, vector bundle
-/

open scoped Topology
open scoped TensorProduct

noncomputable section

open Bundle Set Topology
open scoped Bundle TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Pretrivialization

/-! ## Pretrivialization for tensor product bundle -/

/-- The coordinate change function for tensor product bundles.

Compare with `continuousLinearMapCoordChange` for Hom bundles:
- Hom: `L ↦ (coordChange e₂ e₂') ∘ L ∘ (coordChange e₁' e₁)` (note reversed order on first factor)
- Tensor: `v ⊗ w ↦ (coordChange e₁ e₁' v) ⊗ (coordChange e₂ e₂' w)` (same direction)
-/
def tensorProductCoordChange [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]
    (b : B) : (F₁ ⊗[𝕜] F₂) →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
  TensorProduct.mapL (e₁.coordChangeL 𝕜 e₁' b) (e₂.coordChangeL 𝕜 e₂' b)

variable {e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

/-- The coordinate change map for the tensor product bundle varies continuously over the
overlap of the base sets of any two pairs of trivializations. -/
theorem continuousOn_tensorProductCoordChange
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContinuousOn (tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  classical
  have h₁ := continuousOn_coordChange 𝕜 e₁ e₁'
  have h₂ := continuousOn_coordChange 𝕜 e₂ e₂'
  let s : Set B := (e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have hs1 : s ⊆ (e₁.baseSet ∩ e₁'.baseSet) := fun b hb => ⟨hb.1.1, hb.2.1⟩
  have hs2 : s ⊆ (e₂.baseSet ∩ e₂'.baseSet) := fun b hb => ⟨hb.1.2, hb.2.2⟩
  have h₁' : ContinuousOn (fun b => (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)) s :=
    h₁.mono hs1
  have h₂' : ContinuousOn (fun b => (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)) s :=
    h₂.mono hs2
  -- The uncurried bilinear map (L₁, L₂) ↦ mapLBilinear L₁ L₂ is continuous
  have huncurry : Continuous (fun p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂) =>
                              TensorProduct.mapLBilinear p.1 p.2) :=
    (TensorProduct.mapLBilinear (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂)
      (G₁ := F₁) (G₂ := F₂)).continuous₂
  have hprod : ContinuousOn (fun b =>
        ((e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁),
         (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂))) s :=
    h₁'.prodMk h₂'
  refine (huncurry.comp_continuousOn hprod).congr ?_
  intro b hb
  simp only [Function.comp_apply]
  exact rfl

variable (𝕜 e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.tensorProduct e₁ e₂` is the induced pretrivialization for the
tensor product `E₁ ⊗ E₂`. -/
def tensorProduct :
    Pretrivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) where
  toFun p := ⟨p.1, TensorProduct.map
    (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
    (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩
  invFun p := ⟨p.1, TensorProduct.map
    (e₁.symmL 𝕜 p.1).toLinearMap
    (e₂.symmL 𝕜 p.1).toLinearMap p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, v⟩ ⟨h₁, h₂⟩ ↦ by
      simp only [TotalSpace.mk_inj]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have eq1 : (e₁.symmL 𝕜 x).toLinearMap.comp (e₁.continuousLinearMapAt 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        -- 'apply' handles the def-eq between x and (⟨x,v⟩).proj automatically
        apply Trivialization.symmL_continuousLinearMapAt e₁ h₁
      have eq2 : (e₂.symmL 𝕜 x).toLinearMap.comp (e₂.continuousLinearMapAt 𝕜 x).toLinearMap =
        LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.symmL_continuousLinearMapAt e₂ h₂
      rw [eq1, eq2, TensorProduct.map_id, LinearMap.id_apply]

  right_inv' := fun ⟨x, t⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
      simp only [Prod.mk.injEq, true_and]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have eq1 : (e₁.continuousLinearMapAt 𝕜 x).toLinearMap.comp (e₁.symmL 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.continuousLinearMapAt_symmL e₁ h₁
      have eq2 : (e₂.continuousLinearMapAt 𝕜 x).toLinearMap.comp (e₂.symmL 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.continuousLinearMapAt_symmL e₂ h₂
      rw [eq1, eq2, TensorProduct.map_id, LinearMap.id_apply]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

omit [FiniteDimensional 𝕜 F₂] in
/-- Evaluating the tensor product pretrivialization applies the local trivializations of
`E₁` and `E₂` factor-wise via `TensorProduct.map`. -/
theorem tensorProduct_apply (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    (tensorProduct 𝕜 e₁ e₂) p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

/-- The tensor product pretrivialization is linear on each fiber, since it applies
the fiber isomorphisms of `E₁` and `E₂` linearly factor-wise. -/
instance tensorProduct.isLinear
    [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.tensorProduct 𝕜 e₁ e₂).IsLinear 𝕜 where
  linear x hx :=
  by
    classical
    refine
      { map_add := ?_
        map_smul := ?_ }
    · intro t t'
      -- after unfolding, goal is about `TensorProduct.map ... (t + t')`
      -- and `simp` can use the generic `map_add`
      simp [Pretrivialization.tensorProduct_apply]
    · intro c t
      simp [Pretrivialization.tensorProduct_apply]

omit [FiniteDimensional 𝕜 F₂] in
/-- The inverse of the tensor product pretrivialization reconstructs fiber elements using
the inverse local trivializations `symmL` of each factor. -/
theorem tensorProduct_symm_apply (p : B × (F₁ ⊗[𝕜] F₂)) :
    (tensorProduct 𝕜 e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, TensorProduct.map
        (e₁.symmL 𝕜 p.1).toLinearMap
        (e₂.symmL 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

omit [FiniteDimensional 𝕜 F₂] in
/-- Alternative form of the inverse pretrivialization: for `b` in the base set,
`symm b t` applies `symmL` factor-wise to `t`. -/
theorem tensorProduct_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (t : F₁ ⊗[𝕜] F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b t =
      TensorProduct.map
        (e₁.symmL 𝕜 b).toLinearMap
        (e₂.symmL 𝕜 b).toLinearMap t := by
  -- This is the key: use `symm_apply` instead of unfolding `Pretrivialization.symm`.
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

/-- The coordinate change for the tensor product bundle equals re-trivializing via `e₁', e₂'`
after un-trivializing via `e₁, e₂`, confirming it is the factor-wise coordinate change. -/
theorem tensorProductCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (t : F₁ ⊗[𝕜] F₂) :
    tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂' b t =
      (tensorProduct 𝕜 e₁' e₂' ⟨b, (tensorProduct 𝕜 e₁ e₂).symm b t⟩).2 := by
  -- Step A: rewrite RHS using the helper lemma, so no `dif` / `cast` appears.
  -- First unfold coord change and `mapL` once.
  simp only [tensorProductCoordChange, TensorProduct.mapL]
  -- Now expand the RHS pretrivialization using your `tensorProduct_apply`
  -- and rewrite `.symm b t` using `tensorProduct_symm_apply'`.
  -- This should turn RHS into a `TensorProduct.map ... (TensorProduct.map ... t)`.
  simp only [LinearMap.coe_toContinuousLinearMap',
    tensorProduct_symm_apply' (𝕜 := 𝕜) (e₁ := e₁) (e₂ := e₂) hb.1,
    tensorProduct_apply]
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  -- Step C: identify the composed linear maps with coordChange maps.
  -- You'll now have two component goals, one for F₁ and one for F₂.
  congr 1 ; ext v
  rename_i v x
  have hb1 : b ∈ e₁.baseSet ∩ e₁'.baseSet := ⟨hb.1.1, hb.2.1⟩
  have hb2 : b ∈ e₂.baseSet ∩ e₂'.baseSet := ⟨hb.1.2, hb.2.2⟩
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, LinearMap.coe_comp, Trivialization.continuousLinearMapAt_apply,
    Trivialization.symmL_apply, Function.comp_apply]
  rw [Trivialization.coordChangeL_apply (R := 𝕜) (e := e₁) (e' := e₁') (b := b) hb1 (y := v)]
  rw [Trivialization.coordChangeL_apply (R := 𝕜) (e := e₂) (e' := e₂') (b := b) hb2 (y := x)]
  simp [TensorProduct.tmul, Trivialization.linearMapAt]
  simp [Pretrivialization.linearMapAt]
  have hb1' : b ∈ e₁'.toPretrivialization.baseSet := by simpa using hb.2.1
  have hb2' : b ∈ e₂'.toPretrivialization.baseSet := by simpa using hb.2.2
  simp [ hb1', hb2']
  rfl

end Pretrivialization

/-! ## Smoothness of tensor product coordinate change -/

section

open Pretrivialization

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
variable (n : WithTop ℕ∞)

/-- The coordinate change function for the tensor product bundle is `C^n`. -/
theorem contMDiffOn_tensorProductCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ ⊗[𝕜] F₂) →L[𝕜] (F₁ ⊗[𝕜] F₂)) n
      (Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  sorry

end
