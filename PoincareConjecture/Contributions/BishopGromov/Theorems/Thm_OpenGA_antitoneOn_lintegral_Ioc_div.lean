import Definitions.Def_DifferentialGeometry_RadialCrossComparison



set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

theorem OpenGA.antitoneOn_lintegral_Ioc_div {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}
    (hf : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) R)))
    (hg : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f g)
    (hpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < ∫⁻ t in Ioc (0 : ℝ) r, g t ∂μ)
    (hfin : ∀ r ∈ Ioc (0 : ℝ) R, (∫⁻ t in Ioc (0 : ℝ) r, g t ∂μ) < ⊤) :
    AntitoneOn (fun r => (∫⁻ t in Ioc (0 : ℝ) r, f t ∂μ) /
      (∫⁻ t in Ioc (0 : ℝ) r, g t ∂μ)) (Ioc (0 : ℝ) R) := by sorry
