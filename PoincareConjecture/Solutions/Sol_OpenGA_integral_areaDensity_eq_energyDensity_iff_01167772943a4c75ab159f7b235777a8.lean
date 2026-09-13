import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Definitions.Def_OpenGA_AreaEnergyDensities
import Theorems.Thm_OpenGA_areaDensity_eq_energyDensity_iff
/-!
# Area and energy densities

For the images `v`, `w` of an orthonormal tangent frame under a differential,
the area density is the square root of the Gram determinant and the energy
density is half the sum of the squared norms. The area is bounded by the
energy, with equality precisely for orthogonal vectors of equal norm.

The integral results assume measurable vector fields and integrable energy;
integrability of the area is a conclusion, not an additional assumption.
They apply on any measure space, including a restricted domain measure.
Identifying these fields with a Sobolev differential on a surface remains a
separate geometric interface. No global frame on the sphere is asserted.

Reference: Colding-Minicozzi, *Width and Finite Extinction Time of Ricci Flow*,
arXiv:0707.0108v1, equation (1.4) and the following equality discussion, p. 3.
https://arxiv.org/pdf/0707.0108v1#page=3
-/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace OpenGA

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]





lemma areaDensity_nonneg (v w : F) : 0 ≤ areaDensity v w :=
  Real.sqrt_nonneg _

omit [InnerProductSpace ℝ F] in
lemma energyDensity_nonneg (v w : F) : 0 ≤ energyDensity v w := by
  unfold energyDensity
  positivity

lemma areaDensity_sq (v w : F) :
    areaDensity v w ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 := by
  apply Real.sq_sqrt
  have h := real_inner_mul_inner_self_le v w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith

/-- **Math.** The squared density gap separates the two conformality defects. -/
theorem energyDensity_sq_sub_areaDensity_sq (v w : F) :
    energyDensity v w ^ 2 - areaDensity v w ^ 2 =
      (‖v‖ ^ 2 - ‖w‖ ^ 2) ^ 2 / 4 + ⟪v, w⟫_ℝ ^ 2 := by
  rw [areaDensity_sq, energyDensity]
  ring

/-- **Math.** The two-dimensional area density is bounded by the energy density. -/
theorem areaDensity_le_energyDensity (v w : F) :
    areaDensity v w ≤ energyDensity v w := by
  have h := energyDensity_sq_sub_areaDensity_sq v w
  have he := energyDensity_nonneg v w
  nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖w‖ ^ 2), sq_nonneg ⟪v, w⟫_ℝ]



lemma continuous_areaDensity : Continuous (fun p : F × F => areaDensity p.1 p.2) := by
  unfold areaDensity
  fun_prop

section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v w : X → F}

/-- **Math.** Finite energy implies integrable area density. -/
theorem integrable_areaDensity (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ)
    (hE : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    Integrable (fun x => areaDensity (v x) (w x)) μ := by
  apply hE.mono_nonneg (continuous_areaDensity.comp_aestronglyMeasurable (hv.prodMk hw))
  · exact Filter.Eventually.of_forall fun x => areaDensity_nonneg (v x) (w x)
  · exact Filter.Eventually.of_forall fun x => areaDensity_le_energyDensity (v x) (w x)





end Integral

end OpenGA

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v w : X → F}
open OpenGA

/-- **Math.** Equality of the integrals is equivalent to weak conformality
almost everywhere in the supplied orthonormal-frame representation. -/
theorem solution (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ)
    (hE : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    (∫ x, areaDensity (v x) (w x) ∂μ) = (∫ x, energyDensity (v x) (w x) ∂μ) ↔
      ∀ᵐ x ∂μ, ⟪v x, w x⟫_ℝ = 0 ∧ ‖v x‖ = ‖w x‖ := by
  rw [integral_eq_iff_of_ae_le (integrable_areaDensity hv hw hE) hE
    (Filter.Eventually.of_forall fun x => areaDensity_le_energyDensity (v x) (w x))]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun x =>
    areaDensity_eq_energyDensity_iff (v x) (w x))
