import OpenGALib.Tensor.Product.Pretrivialization
import OpenGALib.Tensor.Product.Fiber

/-!
# The vector bundle of tensor products
# The Vector Bundle of Tensor Products

This file constructs the tensor product of two vector bundles as a vector bundle.

Given vector bundles `E₁ : B → Type*` and `E₂ : B → Type*` with finite-dimensional model
fibers `F₁` and `F₂` over a complete nontrivially normed field `𝕜`, we define a vector bundle
with fiber `E₁ x ⊗[𝕜] E₂ x` and model fiber `F₁ ⊗[𝕜] F₂`.

## Main Definitions

* `Bundle.TensorProduct.vectorPrebundle` : the `VectorPrebundle` for the tensor product bundle,
  with atlas given by all pairs of trivializations from the atlases of `E₁` and `E₂`.
* `Bundle.Trivialization.tensorProduct e₁ e₂` : the trivialization of the tensor
  product bundle induced by atlas trivializations `e₁` and `e₂`.

## Main Results

* `Bundle.TensorProduct.fiberBundle` : the tensor product of two fiber bundles is a fiber bundle.
* `Bundle.TensorProduct.vectorBundle` : the tensor product of two vector bundles is a vector bundle.
* `ContMDiffVectorBundle.tensorProduct`: the tensor product of two `C^n` vector bundles
  is a `C^n` vector bundle.

## Tags

tensor product, vector bundle, fiber bundle, trivialization, smooth, coordinate change,
differential geometry
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
variable [TopologicalSpace B]

section
section TensorFiberTopology

open scoped TensorProduct
open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Fiber topology on `E₁ x ⊗ E₂ x`, induced from the model `F₁ ⊗ F₂`. -/
@[reducible] noncomputable def tensorFiberTopologicalSpace (x : B) :
    TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := by
  classical
  -- ensure model tensor has a topology
  letI : TopologicalSpace (F₁ ⊗[𝕜] F₂) := inferInstance
  let L₁ : E₁ x ≃L[𝕜] F₁ :=
    (trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₁ E₁ x)
  let L₂ : E₂ x ≃L[𝕜] F₂ :=
    (trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₂ E₂ x)
  exact TopologicalSpace.induced
    (fun t : E₁ x ⊗[𝕜] E₂ x =>
      TensorProduct.map L₁.toLinearMap L₂.toLinearMap t)
    inferInstance

/-- Explicit version of `tensorFiberTopologicalSpace` with all arguments given, to avoid
instance synthesis ordering issues. -/
@[reducible] noncomputable def tensorFiberTopologicalSpaceInst
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type*) [TopologicalSpace B]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
  tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂) x

/-- The explicit and implicit versions of the fiber topology on `E₁ x ⊗ E₂ x` agree. -/
theorem tensorFiberTopologicalSpaceInst_eq
    (x : B) :
    tensorFiberTopologicalSpaceInst 𝕜 B F₁ F₂ E₁ E₂ x =
      tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
        (E₁ := E₁) (E₂ := E₂) x := rfl



end TensorFiberTopology
end

section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂
namespace Bundle.TensorProduct

open Bundle Set Topology Pretrivialization
open scoped Manifold Bundle TensorProduct

/-- A typeclass packaging a choice of topology on each fiber `E₁ x ⊗[𝕜] E₂ x`, needed
to avoid universe-level and instance-synthesis issues when building the tensor product bundle. -/
class TensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    Type (max uB (max (uE₁+1) (uE₂+1))) where
  (fiberTop : ∀ x : B, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x))

attribute [reducible, instance] TensorFiberTopologies.fiberTop

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
     [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    [VectorBundle 𝕜 F₂ E₂] [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]


/-- Normed additive commutative group on the model fiber `F₁ ⊗[𝕜] F₂` for the bundle
namespace, pulled back via `clmEquiv`. -/
noncomputable instance instNormedAddCommGroup_tensor :
    NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  -- pick 𝓕 := AddMonoidHom
  refine NormedAddCommGroup.induced
    (𝓕 := (F₁ ⊗[𝕜] F₂) →+ (cDual 𝕜 F₁ →L[𝕜] F₂))
    (E := (F₁ ⊗[𝕜] F₂))
    (F := (cDual 𝕜 F₁ →L[𝕜] F₂))
    (f := e.toLinearMap.toAddMonoidHom)
    ?_
  -- injectivity of the underlying function
  exact e.injective

/-- Normed `𝕜`-module structure on the model fiber `F₁ ⊗[𝕜] F₂`, pulled back via `clmEquiv`. -/
noncomputable instance instNormedSpace_model_tensor :
    NormedSpace 𝕜 (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  refine NormedSpace.induced
    (F := (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂))
    (𝕜 := 𝕜)
    (E := (F₁ ⊗[𝕜] F₂))
    (G := (cDual 𝕜 F₁ →L[𝕜] F₂))
    e.toLinearMap

/-- Provides a `TensorFiberTopologies` instance by using `tensorFiberTopology` at each point. -/
noncomputable instance tensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    TensorFiberTopologies 𝕜 B F₁ F₂ E₁ E₂ :=
  ⟨fun x =>
    tensorFiberTopology (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x⟩
-- noncomputable def tensorFiberTopology (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
--   tensorFiberTopologicalSpace (F₁ := F₁) (F₂ := F₂) E₁ E₂ x


/-- The `VectorPrebundle` for the tensor product bundle, whose atlas consists of all
tensor products of trivializations from the atlases of `E₁` and `E₂`. -/
noncomputable def vectorPrebundle :
    @VectorPrebundle
      𝕜                                  -- R
      B                                  -- B
      (F₁ ⊗[𝕜] F₂)                       -- F
      (fun x ↦ E₁ x ⊗[𝕜] E₂ x)           -- E
      _                                  -- [NontriviallyNormedField 𝕜]
      _                                  -- [∀ x, AddCommMonoid (E x)]
      _                                  -- [∀ x, Module 𝕜 (E x)]
      instNormedAddCommGroup_tensor -- [NormedAddCommGroup F]
      instNormedSpace_model_tensor        -- [NormedSpace 𝕜 F]
      _                                  -- [TopologicalSpace B]
      (fun x => tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) x)
      -- [∀ x, TopologicalSpace (E x)]
      :=
  letI := tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂)
  {
    pretrivializationAtlas :=
      {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
          e = Pretrivialization.tensorProduct (𝕜 := 𝕜) e₁ e₂}
    pretrivialization_linear' := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
      apply Pretrivialization.tensorProduct.isLinear


    pretrivializationAt := fun x =>
      Pretrivialization.tensorProduct (𝕜 := 𝕜) (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
    mem_base_pretrivializationAt := fun x =>
      ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
    pretrivialization_mem_atlas := fun x =>
      ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
    exists_coordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      refine ⟨Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) (e₁ := e₁) (e₁' := e₁')
                (e₂ := e₂) (e₂' := e₂'),
              ?_, Pretrivialization.tensorProductCoordChange_apply (𝕜 := 𝕜)
                (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂')⟩
      simpa using
        (Pretrivialization.continuousOn_tensorProductCoordChange (𝕜 := 𝕜)
          (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂'))
    totalSpaceMk_isInducing := by
      intro b
      -- 1. Setup local definitions
      letI : TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
         tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) b
      let L₁ : E₁ b ≃L[𝕜] F₁ :=
        (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
          (mem_baseSet_trivializationAt _ _ _)
      let L₂ : E₂ b ≃L[𝕜] F₂ :=
        (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
          (mem_baseSet_trivializationAt _ _ _)
      -- 2. Prove induction
      have hind : IsInducing (TensorProduct.map L₁.toLinearMap L₂.toLinearMap) := ⟨rfl⟩
      have : IsInducing fun x ↦ (b, TensorProduct.map L₁.toLinearMap L₂.toLinearMap x) :=
        isInducing_const_prod.mpr hind
      convert this using 1
      funext x
      simp only [Function.comp_apply, Pretrivialization.tensorProduct_apply,
                  Prod.mk.injEq, true_and]
      have hL1 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (trivializationAt F₁ E₁ b) b) :
              E₁ b →ₗ[𝕜] F₁) =
            (↑L₁.toLinearEquiv : E₁ b →ₗ[𝕜] F₁) := by
        ext w
 -- `L₁` is defined as `continuousLinearEquivAt`, and its underlying map is `continuousLinearMapAt`
        simpa [L₁] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (trivializationAt F₁ E₁ b)
              (mem_baseSet_trivializationAt F₁ E₁ b)).symm
      have hL2 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (trivializationAt F₂ E₂ b) b) :
              E₂ b →ₗ[𝕜] F₂) =
            (↑L₂.toLinearEquiv : E₂ b →ₗ[𝕜] F₂) := by
        ext w
        simpa [L₂] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (trivializationAt F₂ E₂ b)
              (mem_baseSet_trivializationAt F₂ E₂ b)).symm
      -- now the two `TensorProduct.map`'s are definitionally the same
      simp [hL1, hL2]

  }


/-- Topology on the total space of the tensor product bundle. -/
noncomputable instance Bundle.TensorProduct.topologicalSpaceTotalSpace :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  -- provide fiber topologies locally
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x
  -- now identical to the sample
  exact
    (Bundle.TensorProduct.vectorPrebundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology


/-- A dependent function assigning to each base point its fiber topology on `E₁ b ⊗ E₂ b`. -/
@[reducible] noncomputable def tensorFiberTop :
    (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
  fun b =>
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) b


/-- The topology on the total space of the tensor product bundle, assembled from the
`VectorPrebundle` via the fiber topologies from `tensorFiberTop`. -/
@[reducible] noncomputable def tensorTotalSpaceTop :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)) :=
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology
attribute [local instance] tensorTotalSpaceTop



/-- The tensor product of two vector bundles forms a fiber bundle. -/
noncomputable instance fiberBundle :
    @FiberBundle
      B
      (F₁ ⊗[𝕜] F₂)
      inferInstance
      inferInstance
      (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)
      (tensorTotalSpaceTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂))
      (tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)) := by
  classical
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toFiberBundle
attribute [local instance] fiberBundle



/-- The tensor product of two vector bundles forms a vector bundle. -/
noncomputable instance vectorBundle :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toVectorBundle

variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂`,
the induced trivialization for the tensor product bundle. -/
noncomputable def _root_.Bundle.Trivialization.tensorProduct :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    VectorPrebundle.trivializationOfMemPretrivializationAtlas _
      ⟨e₁, e₂, he₁, he₂, rfl⟩

/-- The trivialization of the tensor product bundle induced by `e₁` and `e₂` belongs to
the trivialization atlas. -/
noncomputable instance memTrivializationAtlas :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    MemTrivializationAtlas
      (e₁.tensorProduct (𝕜 := 𝕜) e₂ :
        Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))) := by
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) := fun b ↦ inferInstance
  exact ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩, rfl⟩

/-- The base set of the tensor product trivialization is the intersection of the two
factor base sets. -/
@[simp]
theorem _root_.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct (𝕜 := 𝕜) e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

/-- Evaluating the tensor product trivialization applies the factor trivializations
via `TensorProduct.map`, matching the pretrivialization. -/
theorem _root_.Trivialization.tensorProduct_apply
    (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    e₁.tensorProduct (𝕜 := 𝕜) e₂ p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

/-- The canonical trivialization of the tensor product bundle at `x₀` equals the
tensor product of the canonical trivializations of `E₁` and `E₂` at `x₀`. -/
theorem tensorProduct_trivializationAt (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ =
      (trivializationAt F₁ E₁ x₀).tensorProduct (𝕜 := 𝕜) (trivializationAt F₂ E₂ x₀) := rfl

/-- The source of the canonical trivialization at `x₀` is the preimage of the intersection
of the base sets of the factor trivializations. -/
@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_source (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).source =
      π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

/-- The target of the canonical trivialization at `x₀` is the product of the intersection
of base sets with the full model fiber. -/
@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_target (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

/-- The base set of the canonical trivialization at `x₀` equals the intersection of the
base sets of the factor trivializations. -/
@[simp]
theorem tensorProduct_trivializationAt_baseSet (x₀ : B) :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

end Bundle.TensorProduct

end

open Bundle Set

open scoped Manifold Topology Bundle TensorProduct

/-! ## `ContMDiffVectorBundle` instance -/

section Smooth

open Pretrivialization

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
variable (n : WithTop ℕ∞)
variable [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

/-- The tensor product `VectorPrebundle` is `C^n`. -/
instance Bundle.TensorProduct.vectorPrebundle.isContMDiff :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).IsContMDiff IB n := by
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact {
    exists_contMDiffCoordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      haveI := he₁; haveI := he₂; haveI := he₁'; haveI := he₂'
      refine ⟨tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂',
        contMDiffOn_tensorProductCoordChange IB n, ?_⟩
      rintro b hb v
      exact tensorProductCoordChange_apply (𝕜 := 𝕜) e₁ e₁' e₂ e₂' b hb v
  }

/-- If `E₁` and `E₂` are `C^n` vector bundles, then their tensor product bundle
`fun x => E₁ x ⊗[𝕜] E₂ x` is also a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.tensorProduct :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    ContMDiffVectorBundle n (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) IB := by
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂)).contMDiffVectorBundle IB

end Smooth
