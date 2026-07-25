





import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Tensor.Alternating.Flip

open ContinuousAlternatingMap

noncomputable section Congr

namespace DifferentialForm

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m : ℕ}

noncomputable def domDomCongr (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) : Ω^m⟮E, F⟯ :=
  ⟨fun e => (ω e).domDomCongr σ, by
    let L : (E [⋀^Fin n]→L[ℝ] F) →L[ℝ] (E [⋀^Fin m]→L[ℝ] F) :=
      LinearMap.mkContinuous
        { toFun := ContinuousAlternatingMap.domDomCongr σ
          map_add' := fun f g => by ext v; simp [domDomCongr_apply]
          map_smul' := fun c f => by ext v; simp [domDomCongr_apply] }
        1
        (fun f => by
          simp only [one_mul, LinearMap.coe_mk, AddHom.coe_mk]
          exact ContinuousAlternatingMap.opNorm_le_bound _ (norm_nonneg f) fun v => by
            simp only [domDomCongr_apply]
            calc ‖f (v ∘ ↑σ)‖ ≤ ‖f‖ * ∏ j, ‖(v ∘ ↑σ) j‖ := f.le_opNorm _
              _ = ‖f‖ * ∏ i, ‖v i‖ := by congr 1; exact Equiv.prod_comp σ (fun i => ‖v i‖))
    exact L.contDiff.comp ω.smooth⟩

@[simp]
theorem domDomCongr_apply (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) (e : E) :
    (domDomCongr σ ω) e = (ω e).domDomCongr σ :=
  rfl

@[simp]
theorem domDomCongr_refl (ω : Ω^n⟮E, F⟯) :
    domDomCongr (Equiv.refl _) ω = ω := by
  ext e
  rfl

end DifferentialForm

end Congr
