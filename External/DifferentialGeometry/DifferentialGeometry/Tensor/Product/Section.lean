


import DifferentialGeometry.Tensor.Product.Bundle


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle TensorProduct

section TmulCLM

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

noncomputable def TensorProduct.mkCLM :
    F₁ →L[𝕜] (F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂)) := by
  haveI : FiniteDimensional 𝕜 (F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂)) :=
    ContinuousLinearMap.finiteDimensional
  exact
    ({ toFun := fun v => (TensorProduct.mk 𝕜 F₁ F₂ v).toContinuousLinearMap
       map_add' := by intro v₁ v₂; ext w; simp [LinearMap.toContinuousLinearMap]
       map_smul' := by intro c v; ext w; simp [LinearMap.toContinuousLinearMap] }
      : F₁ →ₗ[𝕜] (F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂))).toContinuousLinearMap

@[simp]
theorem TensorProduct.mkCLM_apply (v : F₁) (w : F₂) :
    TensorProduct.mkCLM F₁ F₂ v w = v ⊗ₜ[𝕜] w := rfl

end TmulCLM

section TmulSmooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable {n : WithTop ℕ∞}

theorem ContMDiffAt.tmul {f : B → F₁} {g : B → F₂} {x₀ : B}
    (hf : ContMDiffAt IB 𝓘(𝕜, F₁) n f x₀)
    (hg : ContMDiffAt IB 𝓘(𝕜, F₂) n g x₀) :
    ContMDiffAt IB 𝓘(𝕜, F₁ ⊗[𝕜] F₂) n (fun x => f x ⊗ₜ[𝕜] g x) x₀ :=
  (ContMDiffAt.comp x₀
    ((TensorProduct.mkCLM (𝕜 := 𝕜) F₁ F₂).contMDiff (f x₀)) hf).clm_apply hg

theorem ContMDiff.tmul {f : B → F₁} {g : B → F₂}
    (hf : ContMDiff IB 𝓘(𝕜, F₁) n f)
    (hg : ContMDiff IB 𝓘(𝕜, F₂) n g) :
    ContMDiff IB 𝓘(𝕜, F₁ ⊗[𝕜] F₂) n (fun x => f x ⊗ₜ[𝕜] g x) :=
  fun x₀ => (hf x₀).tmul (hg x₀)

end TmulSmooth

section SectionProduct

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
variable [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

noncomputable def ContMDiffSection.tensorProduct
    (g : ContMDiffSection IB F₁ n E₁)
    (h : ContMDiffSection IB F₂ n E₂) :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    ContMDiffSection IB (F₁ ⊗[𝕜] F₂) n (fun x => E₁ x ⊗[𝕜] E₂ x) :=
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  letI : TopologicalSpace (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x)) :=
    Bundle.TensorProduct.tensorTotalSpaceTop
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI : ContMDiffVectorBundle n (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) IB :=
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
      (E₁ := E₁) (E₂ := E₂)).contMDiffVectorBundle IB
  ⟨fun x => g x ⊗ₜ[𝕜] h x, by
    intro x₀
    rw [contMDiffAt_section x₀]
    set e₁ := trivializationAt F₁ E₁ x₀
    set e₂ := trivializationAt F₂ E₂ x₀

    have hg₀ := (contMDiffAt_section x₀).mp (g.contMDiff x₀)
    have hh₀ := (contMDiffAt_section x₀).mp (h.contMDiff x₀)

    refine (hg₀.tmul hh₀).congr_of_eventuallyEq ?_
    have hbase : e₁.baseSet ∩ e₂.baseSet ∈ 𝓝 x₀ :=
      (e₁.open_baseSet.inter e₂.open_baseSet).mem_nhds
        ⟨mem_baseSet_trivializationAt F₁ E₁ x₀, mem_baseSet_trivializationAt F₂ E₂ x₀⟩
    filter_upwards [hbase] with x hx

    simp only [Bundle.TensorProduct.tensorProduct_trivializationAt]
    change (Pretrivialization.tensorProduct 𝕜 e₁ e₂ ⟨x, g x ⊗ₜ[𝕜] h x⟩).2 =
      (e₁ ⟨x, g x⟩).2 ⊗ₜ[𝕜] (e₂ ⟨x, h x⟩).2
    simp only [Pretrivialization.tensorProduct_apply, TensorProduct.map_tmul]
    congr 1 <;> simp [Trivialization.continuousLinearMapAt,
      e₁.coe_linearMapAt_of_mem hx.1, e₂.coe_linearMapAt_of_mem hx.2]⟩

omit [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB] in
@[simp]
theorem ContMDiffSection.tensorProduct_apply
    (g : ContMDiffSection IB F₁ n E₁)
    (h : ContMDiffSection IB F₂ n E₂)
    (x : B) :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    ContMDiffSection.tensorProduct IB n g h x = g x ⊗ₜ[𝕜] h x := rfl

end SectionProduct

end
