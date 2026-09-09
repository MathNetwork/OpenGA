import OpenGALib.Analysis.IntegralComparison
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall

/-!
# Model-volume denominators for radial integral comparison

The DifferentialGeometry model has curvature `-q^2` for `q ≥ 0`, with
radial exponent `d = n - 1`. Its radial volume omits the constant angular
factor, which cancels in volume ratios. This file identifies the real model
integral with its nonnegative Lebesgue integral and specializes the abstract
integral comparison. Geometric density comparison remains a separate input.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

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

/-- Radial integral comparison normalized by the nonpositive-curvature model volume. -/
theorem antitoneOn_lintegral_div_hypRadVol {f : ℝ → ℝ≥0∞} {q R : ℝ} {d : ℕ}
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

end OpenGA
