import Definitions.Def_DifferentialGeometry_RadialCrossComparison
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint

open MeasureTheory Set
open scoped ENNReal





variable {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
set_option autoImplicit false

theorem DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_cross_le {s : ℝ}
    (hf : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) R)))
    (hg : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f g) (hs : 0 ≤ s) (hsR : s ≤ R) :
    (∫⁻ t in Ioc (0 : ℝ) R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * ∫⁻ t in Ioc (0 : ℝ) R, g t ∂μ := by sorry
