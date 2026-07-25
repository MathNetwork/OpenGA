


import DifferentialGeometry.Tensor.Mixed.DualFiber

noncomputable section

open TensorProduct

theorem dualTensorHomEquiv_symm_naturality
    {𝕜 : Type*} [CommRing 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module.Free 𝕜 V] [Module.Finite 𝕜 V]
    {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    (φ : V ≃ₗ[𝕜] V) (ψ : W ≃ₗ[𝕜] W) (T : V →ₗ[𝕜] W) :
    (dualTensorHomEquiv 𝕜 V W).symm (ψ.toLinearMap.comp (T.comp φ.symm.toLinearMap)) =
      TensorProduct.map φ.symm.toLinearMap.dualMap ψ.toLinearMap
        ((dualTensorHomEquiv 𝕜 V W).symm T) := by
  apply (dualTensorHomEquiv 𝕜 V W).injective
  rw [LinearEquiv.apply_symm_apply]
  set t := (dualTensorHomEquiv 𝕜 V W).symm T
  rw [show T = dualTensorHomEquiv 𝕜 V W t from (LinearEquiv.apply_symm_apply _ T).symm]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | tmul f w =>
    ext v
    simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis, LinearEquiv.ofLinear_apply,
      dualTensorHom_apply, TensorProduct.map_tmul, LinearMap.dualMap_apply,
      LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, map_smul]

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem dualMultilinearEquivMultilinearOfDual_compCCLM (r : ℕ) (L : F →L[𝕜] F)
    (ω : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
    (α : Fin r → (F →L[𝕜] 𝕜)) :
    dualMultilinearEquivMultilinearOfDual 𝕜 F r
        (ω.comp (compContinuousLinearMapL (fun _ : Fin r => L))) α =
      dualMultilinearEquivMultilinearOfDual 𝕜 F r ω (fun i => (α i).comp L) := by
  change ω (compContinuousLinearMapL (fun _ : Fin r => L)
      (tensorOfDualLinearForms 𝕜 F r α)) =
    ω (tensorOfDualLinearForms 𝕜 F r (fun i => (α i).comp L))
  congr 1

theorem dualMultilinearEquivMultilinearOfDual_compCCLM_ext (r : ℕ) (L : F →L[𝕜] F)
    (ω : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :
    dualMultilinearEquivMultilinearOfDual 𝕜 F r
        (ω.comp (compContinuousLinearMapL (fun _ : Fin r => L))) =
      compContinuousLinearMapL (fun _ : Fin r => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip L)
        (dualMultilinearEquivMultilinearOfDual 𝕜 F r ω) := by
  ext α
  rw [dualMultilinearEquivMultilinearOfDual_compCCLM r L ω α,
    compContinuousLinearMapL_apply, compContinuousLinearMap_apply]
  rfl

theorem homEquivCDualTensor_symm_tmul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (η : V →L[𝕜] 𝕜) (w : W) (v : V) :
    (homEquivCDualTensor 𝕜 V W).symm (η ⊗ₜ[𝕜] w) v = η v • w := by
  simp only [homEquivCDualTensor, LinearEquiv.symm_trans_apply,
    TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  have h_inner : (dualTensorHomEquiv 𝕜 V W
        (LinearMap.toContinuousLinearMap.symm η ⊗ₜ[𝕜] w)) v = η v • w := by
    simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis, LinearEquiv.ofLinear_apply,
      dualTensorHom_apply]
    rfl
  exact h_inner

set_option maxHeartbeats 800000 in

theorem multilinearHomEquivDualMultilinearTensor_naturality
    (r s : ℕ) (Φ : F ≃L[𝕜] F)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    multilinearHomEquivDualMultilinearTensor 𝕜 F r s
        ((compContinuousLinearMapL (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).comp
          (f.comp (compContinuousLinearMapL
            (fun _ : Fin r => Φ.toContinuousLinearMap)))) =
      TensorProduct.map
        (compContinuousLinearMapL (fun _ : Fin r =>
          (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)).toLinearMap
        (compContinuousLinearMapL
          (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).toLinearMap
        (multilinearHomEquivDualMultilinearTensor 𝕜 F r s f) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  set MHE := multilinearHomEquivDualMultilinearTensor 𝕜 F r s with hMHE_def
  set t := MHE f with ht_def
  have hf_eq : f = MHE.symm t := (LinearEquiv.symm_apply_apply _ _).symm
  suffices h : ∀ (u : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
                     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜),
      MHE ((compContinuousLinearMapL (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).comp
          ((MHE.symm u).comp (compContinuousLinearMapL
            (fun _ : Fin r => Φ.toContinuousLinearMap)))) =
        TensorProduct.map
          (compContinuousLinearMapL (fun _ : Fin r =>
            (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)).toLinearMap
          (compContinuousLinearMapL
            (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).toLinearMap u by
    have := h t
    rw [ht_def] at this
    rw [LinearEquiv.symm_apply_apply] at this
    convert this using 2
  intro u
  induction u using TensorProduct.induction_on with
  | zero =>
    rw [LinearEquiv.map_zero MHE.symm, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, LinearEquiv.map_zero MHE,
      (TensorProduct.map _ _).map_zero]
  | add t₁ t₂ ih₁ ih₂ =>
    rw [LinearEquiv.map_add MHE.symm, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add, LinearEquiv.map_add MHE, ih₁, ih₂,
      (TensorProduct.map _ _).map_add]
  | tmul α β =>
    set η := (dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm α with hη_def

    have hMHE_symm_tmul : MHE.symm (α ⊗ₜ[𝕜] β) =
        (homEquivCDualTensor 𝕜
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)).symm (η ⊗ₜ[𝕜] β) := by
      change ((homEquivCDualTensor 𝕜 _ _).trans (TensorProduct.congr
          (dualMultilinearEquivMultilinearOfDual 𝕜 F r) (LinearEquiv.refl 𝕜 _))).symm
            (α ⊗ₜ[𝕜] β) = _
      simp only [LinearEquiv.symm_trans_apply, TensorProduct.congr_symm_tmul,
        LinearEquiv.refl_symm, LinearEquiv.refl_apply]
      rfl
    rw [hMHE_symm_tmul]

    have hconj :
        (compContinuousLinearMapL (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).comp
            (((homEquivCDualTensor 𝕜 _ _).symm (η ⊗ₜ[𝕜] β)).comp
              (compContinuousLinearMapL (fun _ : Fin r => Φ.toContinuousLinearMap))) =
          (homEquivCDualTensor 𝕜 _ _).symm
            ((η.comp (compContinuousLinearMapL
                (fun _ : Fin r => Φ.toContinuousLinearMap))) ⊗ₜ[𝕜]
              ((compContinuousLinearMapL
                (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) β)) := by
      ext M'
      simp only [ContinuousLinearMap.comp_apply, homEquivCDualTensor_symm_tmul, map_smul]
    rw [hconj]

    have hMHE_apply_h_symm :
        MHE ((homEquivCDualTensor 𝕜 _ _).symm
            ((η.comp (compContinuousLinearMapL
                (fun _ : Fin r => Φ.toContinuousLinearMap))) ⊗ₜ[𝕜]
              ((compContinuousLinearMapL
                (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) β))) =
          dualMultilinearEquivMultilinearOfDual 𝕜 F r
              (η.comp (compContinuousLinearMapL
                (fun _ : Fin r => Φ.toContinuousLinearMap))) ⊗ₜ[𝕜]
            ((compContinuousLinearMapL
              (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) β) := by
      change ((homEquivCDualTensor 𝕜 _ _).trans (TensorProduct.congr
          (dualMultilinearEquivMultilinearOfDual 𝕜 F r) (LinearEquiv.refl 𝕜 _))) _ = _
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rw [hMHE_apply_h_symm,
      dualMultilinearEquivMultilinearOfDual_compCCLM_ext r Φ.toContinuousLinearMap η,
      hη_def, LinearEquiv.apply_symm_apply]
    rfl

end ContinuousMultilinearMap

end
