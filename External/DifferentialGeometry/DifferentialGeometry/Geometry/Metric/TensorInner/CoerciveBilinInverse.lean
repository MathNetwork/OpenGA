import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false










noncomputable section

open RealInnerProductSpace

class CoerciveBilinInverse (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] : Prop where
  surjective : ∀ {B : E →L[Real] E →L[Real] Real},
    IsCoercive B → Function.Surjective B

class ContinuousDualEquiv (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] where
  equiv : E ≃L[Real] (E →L[Real] Real)

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem bilin_injective {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : Function.Injective B := by
  intro u v huv
  rcases hco with ⟨c, hc, hB⟩
  have hzeroMap : B (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hbound := hB (u - v)
  have hzero : B (u - v) (u - v) = 0 := by rw [hzeroMap]; rfl
  rw [hzero] at hbound
  have hsub : u - v = 0 := by
    by_contra hne
    have hn : 0 < ‖u - v‖ := norm_pos_iff.mpr hne
    exact (not_lt_of_ge hbound) (mul_pos (mul_pos hc hn) hn)
  exact sub_eq_zero.mp hsub

noncomputable instance coerciveBilinInverseOfFiniteDimensional
    [FiniteDimensional Real E] : CoerciveBilinInverse E where
  surjective := by
    intro B hco
    exact (LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap
      (bilin_injective hco) (by
        rw [← LinearEquiv.finrank_eq LinearMap.toContinuousLinearMap]
        exact Subspace.dual_finrank_eq.symm)).surjective

noncomputable instance continuousDualEquivOfFiniteDimensional
    [FiniteDimensional Real E] : ContinuousDualEquiv E where
  equiv := ContinuousLinearEquiv.ofFinrankEq (by
    rw [← LinearEquiv.finrank_eq LinearMap.toContinuousLinearMap]
    exact Subspace.dual_finrank_eq.symm)

noncomputable instance (priority := 900) coerciveBilinInverseOfInnerProduct
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] : CoerciveBilinInverse F where
  surjective := by
    intro B hco eta
    refine ⟨hco.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual Real F).symm eta), ?_⟩
    apply ContinuousLinearMap.ext
    intro w
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp

noncomputable instance (priority := 900) continuousDualEquivOfInnerProduct
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] : ContinuousDualEquiv F where
  equiv := (InnerProductSpace.toDual Real F).toContinuousLinearEquiv

variable [CompleteSpace E] [CoerciveBilinInverse E]



theorem symm_norm_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] {B : F →L[Real] F →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : F, c * ‖v‖ * ‖v‖ ≤ B v v) (xi : F) :
    ‖hco.continuousLinearEquivOfBilin.symm xi‖ ≤ c⁻¹ * ‖xi‖ := by
  let u := hco.continuousLinearEquivOfBilin.symm xi
  have heu : hco.continuousLinearEquivOfBilin u = xi :=
    hco.continuousLinearEquivOfBilin.apply_symm_apply xi
  change ‖u‖ ≤ c⁻¹ * ‖xi‖
  by_cases hu : u = 0
  · rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg xi)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖xi‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = inner Real (hco.continuousLinearEquivOfBilin u) u :=
          (hco.continuousLinearEquivOfBilin_apply u u).symm
        _ = inner Real xi u := by rw [heu]
        _ ≤ ‖xi‖ * ‖u‖ := real_inner_le_norm xi u
    calc
      ‖u‖ ≤ ‖xi‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖xi‖ := by rw [div_eq_mul_inv, mul_comm]



private noncomputable def toDualEquiv {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : E ≃L[Real] (E →L[Real] Real) :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr (bilin_injective hco))
    (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective hco))

noncomputable def sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) : E :=
  (toDualEquiv hco).symm eta



theorem sharp_eq_inverse
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] {B : F →L[Real] F →L[Real] Real}
    (hco : IsCoercive B) (eta : F →L[Real] Real) :
    hco.sharp eta =
      Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B)
        ((InnerProductSpace.toDual Real F).symm eta) := by
  have heq : hco.sharp eta = hco.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual Real F).symm eta) := by
    apply bilin_injective hco
    change B ((toDualEquiv hco).symm eta) = _
    have hlhs := (toDualEquiv hco).apply_symm_apply eta
    change B ((toDualEquiv hco).symm eta) = eta at hlhs
    rw [hlhs]
    symm
    apply ContinuousLinearMap.ext
    intro w
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp
  rw [heq]
  change hco.continuousLinearEquivOfBilin.symm _ =
    Ring.inverse
      (↑hco.continuousLinearEquivOfBilin.toUnit : F →L[Real] F) _
  rw [Ring.inverse_unit]
  rfl


@[simp] theorem apply_sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    B (hco.sharp eta) = eta := by
  exact (toDualEquiv hco).apply_symm_apply eta


@[simp] theorem sharp_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (u : E) :
    hco.sharp (B u) = u := by
  exact (toDualEquiv hco).symm_apply_apply u


theorem sharp_sub {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta theta : E →L[Real] Real) :
    hco.sharp (eta - theta) = hco.sharp eta - hco.sharp theta := by
  simp [sharp]



theorem sharp_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (eta : E →L[Real] Real) :
    ‖hco.sharp eta‖ ≤ c⁻¹ * ‖eta‖ := by
  let u := hco.sharp eta
  have heu : B u = eta := hco.apply_sharp eta
  by_cases hu : u = 0
  · change ‖u‖ ≤ c⁻¹ * ‖eta‖
    rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg eta)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖eta‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = eta u := by rw [heu]
        _ ≤ ‖eta u‖ := by simpa [Real.norm_eq_abs] using le_abs_self (eta u)
        _ ≤ ‖eta‖ * ‖u‖ := eta.le_opNorm u
    calc
      ‖u‖ ≤ ‖eta‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖eta‖ := by rw [div_eq_mul_inv, mul_comm]




theorem sharp_sub_le
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (eta : E →L[Real] Real) :
    ‖hBco.sharp eta - hCco.sharp eta‖ ≤
      cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
  have heq :
      hBco.sharp eta - hCco.sharp eta =
        hBco.sharp ((C - B) (hCco.sharp eta)) := by
    calc
      hBco.sharp eta - hCco.sharp eta =
          hBco.sharp (B (hBco.sharp eta - hCco.sharp eta)) :=
        (hBco.sharp_apply _).symm
      _ = hBco.sharp (B (hBco.sharp eta) - B (hCco.sharp eta)) := by
        rw [map_sub]
      _ = hBco.sharp (eta - B (hCco.sharp eta)) := by
        rw [hBco.apply_sharp]
      _ = hBco.sharp (C (hCco.sharp eta) - B (hCco.sharp eta)) := by
        rw [hCco.apply_sharp]
      _ = hBco.sharp ((C - B) (hCco.sharp eta)) := by
        rw [ContinuousLinearMap.sub_apply]
  rw [heq]
  calc
    ‖hBco.sharp ((C - B) (hCco.sharp eta))‖ ≤
        cB⁻¹ * ‖(C - B) (hCco.sharp eta)‖ :=
      hBco.sharp_norm_le hcB hB _
    _ ≤ cB⁻¹ * (‖C - B‖ * ‖hCco.sharp eta‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm (C - B) (hCco.sharp eta)
    _ ≤ cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
      gcongr
      exact hCco.sharp_norm_le hcC hC eta

end IsCoercive
