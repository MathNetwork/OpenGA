import DifferentialGeometry.Geometry.Comparison.Volume.RatioIntegral

/-!
# Normalized integral comparison

The upstream cross-multiplied comparison of radial densities implies that the
ratio of their accumulated integrals is nonincreasing. The denominator is
explicitly positive and finite on each interval where the ratio is compared.

This is an analytic ingredient of Bishop-Gromov comparison. Interpreting the
integrals as ball volumes still requires the geometric polar integration and
curvature comparison results.

Source: DifferentialGeometry v0.1.2, commit
1b535dd102b94cc42b107cca27059687888f08b3,
Geometry/Comparison/Volume/RatioIntegral.lean, `lintegral_cross_le`.
The proof of that input is reused from its original namespace (Apache-2.0).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace OpenGA

/-- **Math.** Cross-comparison of nonnegative radial densities makes the ratio of
their accumulated integrals nonincreasing when the denominator is positive
and finite. No finiteness assumption on the numerator is needed. -/
theorem antitoneOn_lintegral_Ioc_div {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}
    (hf : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) R)))
    (hg : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f g)
    (hpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < ∫⁻ t in Ioc (0 : ℝ) r, g t ∂μ)
    (hfin : ∀ r ∈ Ioc (0 : ℝ) R, (∫⁻ t in Ioc (0 : ℝ) r, g t ∂μ) < ⊤) :
    AntitoneOn (fun r => (∫⁻ t in Ioc (0 : ℝ) r, f t ∂μ) /
      (∫⁻ t in Ioc (0 : ℝ) r, g t ∂μ)) (Ioc (0 : ℝ) R) := by
  intro r hr s hs hrs
  have hsub : Ioc (0 : ℝ) s ⊆ Ioc (0 : ℝ) R := Ioc_subset_Ioc le_rfl hs.2
  have hfs := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgs := hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hcrosss : CrossAnti s f g := by
    intro a b ha hab hbs
    exact hcross a b ha hab (hbs.trans hs.2)
  have hcomp := lintegral_cross_le hfs hgs hcrosss hr.1.le hrs
  dsimp only
  rw [ENNReal.div_le_iff (hpos s hs).ne' (hfin s hs).ne,
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl (hpos r hr).ne') (Or.inl (hfin r hr).ne)]
  exact hcomp

end OpenGA
