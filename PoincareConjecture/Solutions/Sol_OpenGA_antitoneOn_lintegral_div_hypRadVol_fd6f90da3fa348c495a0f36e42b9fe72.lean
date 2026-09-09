/-
Includes unchanged helper proofs from qinz1yang/differential-geometry,
Copyright 2026 The DifferentialGeometry contributors, Apache-2.0.
Source commit: 1b535dd102b94cc42b107cca27059687888f08b3.
The model-integral identity and final specialization are OpenGA results.
-/

import Theorems.Thm_OpenGA_antitoneOn_lintegral_Ioc_div
import Definitions.Def_DifferentialGeometry_ModelRadialVolume
import Definitions.Def_DifferentialGeometry_RadialCrossComparison

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
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

namespace OpenGA

/-- The model radial volume as an extended nonnegative Lebesgue integral. -/
theorem lintegral_hypDensity {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) :
    (∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (hypDensity q d t)) =
      ENNReal.ofReal (hypRadVol q d r) := by
  rw [hypRadVol, intervalIntegral.integral_of_le hr.le]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((hypDen_continuous q d).intervalIntegrable 0 r).1
    ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun t ht => (hypDensity_pos hq ht.1).le))).symm

end OpenGA

open OpenGA in
/-- Radial integral comparison normalized by the nonpositive-curvature model volume. -/
theorem solution {f : ℝ → ℝ≥0∞} {q R : ℝ} {d : ℕ}
    (hq : 0 ≤ q)
    (hf : AEMeasurable f (volume.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f (fun t => ENNReal.ofReal (hypDensity q d t))) :
    AntitoneOn (fun r => (∫⁻ t in Ioc (0 : ℝ) r, f t) /
      ENNReal.ofReal (hypRadVol q d r)) (Ioc (0 : ℝ) R) := by
  have hg : AEMeasurable (fun t => ENNReal.ofReal (hypDensity q d t))
      (volume.restrict (Ioc (0 : ℝ) R)) :=
    (ENNReal.continuous_ofReal.comp (hypDen_continuous q d)).aemeasurable
  have hpos : ∀ r ∈ Ioc (0 : ℝ) R,
      0 < ∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (hypDensity q d t) := by
    intro r hr
    rw [lintegral_hypDensity hq hr.1]
    exact ENNReal.ofReal_pos.mpr (hypRadVol_pos hq hr.1)
  have hfin : ∀ r ∈ Ioc (0 : ℝ) R,
      (∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (hypDensity q d t)) < ⊤ := by
    intro r hr
    rw [lintegral_hypDensity hq hr.1]
    exact ENNReal.ofReal_lt_top
  have h := antitoneOn_lintegral_Ioc_div hf hg hcross hpos hfin
  intro r hr s hs hrs
  simpa only [lintegral_hypDensity hq hr.1, lintegral_hypDensity hq hs.1]
    using h hr hs hrs
