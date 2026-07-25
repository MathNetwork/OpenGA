





import DifferentialGeometry.Tensor.Multilinear.Comp
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open ContinuousAlternatingMap

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' := by
  let F₁ : MultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') := MultilinearMap.mk
    (toFun := fun v => (f (g v)).compContinuousAlternatingMap h)
    (map_update_add' := fun m i x y => by
      simp only [ContinuousAlternatingMap.map_update_add, map_add]
      congr)
    (map_update_smul' := fun m i c x => by
      dsimp
      rw [ContinuousAlternatingMap.map_update_smul, ContinuousLinearMap.map_smul]
      congr)
  let F₂ : ContinuousMultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') :=
    F₁.mkContinuous (‖f‖ * ‖g‖ * ‖h‖) (H := by
      intro m
      unfold F₁
      simp only [MultilinearMap.coe_mk]
      apply ContinuousAlternatingMap.opNorm_le_bound
      · positivity
      intro m'
      simp only [compContinuousAlternatingMap_coe, Function.comp_apply]
      calc
        ‖(f (g m)) (h m')‖ ≤ ‖f (g m)‖ * ‖h m'‖ := ContinuousLinearMap.le_opNorm (f (g m)) (h m')
        _ ≤ ‖f (g m)‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousAlternatingMap.le_opNorm h m'
          positivity
        _ ≤ ‖f‖ * ‖g m‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact ContinuousLinearMap.le_opNorm f (g m)
          positivity
        _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖m i‖) * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact ContinuousAlternatingMap.le_opNorm g m
            positivity
          positivity
        _ = (‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
  exact ContinuousAlternatingMap.mk F₂ (map_eq_zero_of_eq' := by
    intro v i j h₁ h₂
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk, F₂, F₁]
    have : g v = 0 := g.map_eq_zero_of_eq' v i j h₁ h₂
    rw [this, ContinuousLinearMap.map_zero]
    ext v'
    rfl)

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

noncomputable def _root_.LinearIsometry.compLeft {𝕜 : Type*} {𝕜₂ : Type*}
    {𝕜₃ : Type*} (E : Type*) {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] (σ₁₂ : 𝕜 →+* 𝕜₂) {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]
    [RingHomIsometric σ₁₃] (f : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) :=
  { ContinuousLinearMap.compSL _ _ _ _ _ f.toContinuousLinearMap with
    norm_map' := fun _ ↦ f.norm_toContinuousLinearMap_comp }

theorem compContinuousAlternatingMapCLM_cont :
    Continuous (ContinuousAlternatingMap.compContinuousLinearMapCLM :
    (M →L[𝕜] M') → (M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N)) := by
  let φ : (M [⋀^ι]→L[𝕜] N) →ₗᵢ[𝕜] _ := ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]
  change Continuous (fun p : M →L[𝕜] M' ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N).comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜))
  exact Continuous.clm_comp compContinuousMultilinearMapL_diag_continuous continuous_const

end ContinuousLinearMap

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι ι' : Type*}
variable
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  [Fintype ι] [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' :=
  f.compContinuousAlternatingMap₂ g h

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

end ContinuousAlternatingMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Fintype ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

theorem ContinuousAlternatingMap.compContinuousLinearMapL_continuous :
    Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousAlternatingMap.compContinuousLinearMapCLM p :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by

  let φ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] _ := ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]

  change Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂).comp
    (toContinuousMultilinearMapCLM 𝕜))

  exact (ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous 𝕜 ι F₁ F₂).clm_comp
    continuous_const

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [ntnf : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

open scoped Bundle Manifold

variable [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff :
    let F : (F₁ →L[𝕜] F₁) → (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁))) (𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  let F : (F₁ →L[𝕜] F₁) → (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
    := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
  letI domNACG : NormedAddCommGroup ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI codNACG : NormedAddCommGroup (F₁ [⋀^ι]→L[𝕜] F₂ →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) := ContinuousLinearMap.toNormedAddCommGroup
  let φ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) →ₗᵢ[𝕜]
      (F₁ [⋀^ι]→L[𝕜] F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) :=
    φ.compLeft _ (RingHom.id _)

  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
    := FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  haveI : FiniteDimensional 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂)
    := FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
      ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  haveI : FiniteDimensional 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂ →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) := inferInstance
  have h1 : ContDiff 𝕜 ⊤ (Φ ∘ F) := by
    change ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
      ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜))
    apply ContDiff.clm_comp
    · exact ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff
    · exact contDiff_const
  let cdiff : ContDiff 𝕜 ⊤ (⇑Φ ∘ F) ↔ ContDiff 𝕜 ⊤ F := @LinearIsometry.comp_contDiff_iff 𝕜
    (F₁ [⋀^ι]→L[𝕜] F₂ →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂)
    (F₁ [⋀^ι]→L[𝕜] F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
    (F₁ →L[𝕜] F₁) ntnf _ domNACG codNACG inferInstance inferInstance inferInstance inferInstance
    inferInstance Φ F ⊤
  rw [cdiff] at h1
  exact h1

end Smooth

end Comp
