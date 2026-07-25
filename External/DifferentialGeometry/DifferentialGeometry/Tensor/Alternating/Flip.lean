






import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Alternating.Basic

open ContinuousAlternatingMap

noncomputable section Flip

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

def _root_.LinearIsometryEquiv.flipAlternating :
    (M' →L[𝕜] (M [⋀^ι]→L[𝕜] N)) ≃ₗᵢ[𝕜] (M [⋀^ι]→L[𝕜] (M' →L[𝕜] N)) where
  toFun := ContinuousLinearMap.flipAlternating
  invFun f :=
    LinearMap.mkContinuous
      { toFun := fun m ↦ ContinuousAlternatingMap.mk
          (LinearIsometryEquiv.flipMultilinear.symm f.toContinuousMultilinearMap m)
          (fun v i j h₁ h₂ ↦ by
            change (f v) m = 0
            rw [f.map_eq_zero_of_eq _ h₁ h₂, ContinuousLinearMap.zero_apply])
        map_add' := fun x y ↦ by ext; exact ContinuousLinearMap.map_add _ _ _
        map_smul' := fun c x ↦ by ext; exact ContinuousLinearMap.map_smul _ _ _ }
      ‖f‖ (fun x ↦ ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun m ↦ calc
        ‖f m x‖ ≤ ‖f m‖ * ‖x‖ := (f m).le_opNorm x
        _ ≤ (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (f.le_opNorm m) (by positivity)
        _ = ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := mul_right_comm ..)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  norm_map' := fun f => by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    have : ‖f.flipAlternating‖ = ‖f.flipAlternating.toContinuousMultilinearMap‖ := rfl
    rw [this]
    rw [←LinearIsometryEquiv.flipMultilinear.symm.norm_map
      f.flipAlternating.toContinuousMultilinearMap]
    rfl

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def flipAlternating (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) (M' [⋀^ι']→L[𝕜] N)) :
    M' [⋀^ι']→L[𝕜] (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) N) :=
  AlternatingMap.mkContinuous
    { toFun := fun m =>
        MultilinearMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := fun m' i x y ↦ by
              change (f (Function.update m' i (x + y))) m
                = (f (Function.update m' i x)) m + (f (Function.update m' i y)) m
              rw [ContinuousMultilinearMap.map_update_add, ContinuousAlternatingMap.add_apply]
            map_update_smul' := fun m' i c x ↦ by
              change (f (Function.update m' i (c • x))) m = c • (f (Function.update m' i x)) m
              rw [ContinuousMultilinearMap.map_update_smul, ContinuousAlternatingMap.smul_apply] }
          (‖f‖ * ∏ i, ‖m i‖) (fun m' ↦ calc
            ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
            _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm m')
              (by positivity)
            _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
      map_update_add' := fun m i x y
        ↦ by ext m'; exact ContinuousAlternatingMap.map_update_add (f m') m i x y
      map_update_smul' := fun m i c x
        ↦ by ext m'; exact ContinuousAlternatingMap.map_update_smul (f m') m i c x
      map_eq_zero_of_eq' := fun m i j h₁ h₂ ↦ by ext m'; exact (f m').map_eq_zero_of_eq m h₁ h₂ }
    ‖f‖ (fun m ↦ ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg f)
        (by positivity)) fun m' ↦ calc
      ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
      _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm m')
        (by positivity)
      _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)

theorem flipAlternating_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) (M' [⋀^ι']→L[𝕜] N))
    (m : ι → M) (m' : ι' → M') : flipAlternating f m' m = f m m' :=
  rfl

end ContinuousMultilinearMap

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

def flipAlternating (f : M [⋀^ι]→L[𝕜] (M' [⋀^ι']→L[𝕜] N)) :
    M' [⋀^ι']→L[𝕜] M [⋀^ι]→L[𝕜] N :=
  AlternatingMap.mkContinuous
    { toFun := fun m =>
        AlternatingMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := fun m' i x y ↦ by
              change (f (Function.update m' i (x + y))) m
                = (f (Function.update m' i x)) m + (f (Function.update m' i y)) m
              rw [ContinuousAlternatingMap.map_update_add, ContinuousAlternatingMap.add_apply]
            map_update_smul' := fun m' i c x ↦ by
              change (f (Function.update m' i (c • x))) m = c • (f (Function.update m' i x)) m
              rw [ContinuousAlternatingMap.map_update_smul, ContinuousAlternatingMap.smul_apply]
            map_eq_zero_of_eq' := fun m' i j h₁ h₂ ↦ by
              change (f m') m = 0
              rw [f.map_eq_zero_of_eq _ h₁ h₂]
              rfl }
          (‖f‖ * ∏ i, ‖m i‖) (fun m' ↦ calc
            ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
            _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm m')
              (by positivity)
            _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
      map_update_add' := fun m i x y
        ↦ by ext m'; exact ContinuousAlternatingMap.map_update_add (f m') m i x y
      map_update_smul' := fun m i c x
        ↦ by ext m'; exact ContinuousAlternatingMap.map_update_smul (f m') m i c x
      map_eq_zero_of_eq' := fun m i j h₁ h₂ ↦ by ext m'; exact (f m').map_eq_zero_of_eq m h₁ h₂ }
    ‖f‖ (fun m ↦ ContinuousAlternatingMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg f) (by positivity)) fun m' ↦ calc
        ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
        _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm m')
          (by positivity)
        _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)

theorem flipAlternating_apply (f : M [⋀^ι]→L[𝕜] (M' [⋀^ι']→L[𝕜] N))
    (m : ι → M) (m' : ι' → M') : flipAlternating f m' m = f m m' :=
  rfl

end ContinuousAlternatingMap
end Flip
