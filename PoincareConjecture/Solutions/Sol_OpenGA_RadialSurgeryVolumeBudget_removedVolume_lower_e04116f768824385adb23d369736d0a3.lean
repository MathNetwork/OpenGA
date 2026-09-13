/-
Includes unchanged model-positivity helper proofs from qinz1yang/differential-geometry,
Copyright 2026 The DifferentialGeometry contributors, Apache-2.0.
Source commit: 1b535dd102b94cc42b107cca27059687888f08b3.
The volume-loss and finite-trace arguments are OpenGA results.
-/

import Definitions.Def_OpenGA_RadialSurgeryVolumeBudget
import Theorems.Thm_OpenGA_antitoneOn_lintegral_div_hypRadVol
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

theorem hasDerivAt_hypSn (q r : ℝ) :
    HasDerivAt (hypSn q) (hypSnDeriv q r) r := by
  by_cases hq : q = 0
  · subst q
    have hfun : hypSn 0 = fun x : ℝ => x := by
      funext x
      simp [hypSn]
    rw [hfun]
    simp only [hypSnDeriv]
    exact hasDerivAt_id r
  · have h := ((hasDerivAt_id r).const_mul q).sinh.div_const q
    have hfun : hypSn q = fun x : ℝ => Real.sinh (q * x) / q := by
      funext x
      simp [hypSn, hq]
    rw [hfun]
    simpa [hypSnDeriv, hq] using h

theorem hypSn_continuous (q : ℝ) : Continuous (hypSn q) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hypSn q r).continuousAt

theorem hypSn_pos {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) :
    0 < hypSn q r := by
  by_cases hq0 : q = 0
  · simpa [hypSn, hq0] using hr
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [hypSn, if_neg hq0]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hqpos hr)) hqpos

theorem hasDerivAt_hypDen (q : ℝ) (d : ℕ) (r : ℝ) :
    HasDerivAt (hypDensity q d) (hypDensityDeriv q d r) r := by
  change HasDerivAt (hypSn q ^ d)
    ((d : ℝ) * hypSn q r ^ (d - 1) * hypSnDeriv q r) r
  exact (hasDerivAt_hypSn q r).pow d

theorem hypDen_continuous (q : ℝ) (d : ℕ) : Continuous (hypDensity q d) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hypDen q d r).continuousAt

theorem hypDensity_pos {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) :
    0 < hypDensity q d r := by
  exact pow_pos (hypSn_pos hq hr) d

theorem hypRadVol_pos {q R : Real} {d : Nat} (hq : 0 ≤ q) (hR : 0 < R) :
    0 < hypRadVol q d R := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hypDen_continuous q d).intervalIntegrable (0 : Real) R)
    (fun t ht => hypDensity_pos hq ht.1) hR

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open OpenGA in
/-- **Math.** Model-volume monotonicity supplies a uniform positive lower
bound for the volume removed at each event. -/
theorem solution (B : RadialSurgeryVolumeBudget)
    {t : ℝ} (ht : t ∈ B.events) :
    B.anchor * hypRadVol B.modelParameter 2 B.removalRadius ≤ B.removedVolume t := by
  have hR : 0 < B.referenceRadius := B.removalRadius_pos.trans_le B.radius_le
  have hm := antitoneOn_lintegral_div_hypRadVol B.modelParameter_nonneg
    (B.density_measurable t ht) (B.density_comparison t ht)
    ⟨B.removalRadius_pos, B.radius_le⟩ ⟨hR, le_rfl⟩ B.radius_le
  have hle := (B.reference_lower t ht).trans hm
  have hmul := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr
      (hypRadVol_pos B.modelParameter_nonneg B.removalRadius_pos)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mp hle
  have hbound := hmul.trans (B.removal_contains t ht)
  rw [← ENNReal.ofReal_mul B.anchor_pos.le] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (B.removedVolume_nonneg t ht)).mp hbound
