import Theorems.Thm_DifferentialGeometry_Geometry_Riemannian_VolumeComparison_lintegral_cross_le
import Definitions.Def_DifferentialGeometry_RadialCrossComparison



set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

theorem solution {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}
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
