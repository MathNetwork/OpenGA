import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint

open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_Iic_cross {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [ClosedIicTopology α]
    {μ : Measure α} {f g : α → ℝ≥0∞} {s R : α}
    (hf : AEMeasurable f (μ.restrict (Iic R)))
    (hg : AEMeasurable g (μ.restrict (Iic R)))
    (hcross : ∀ ⦃a b : α⦄, a ≤ b → b ≤ R →
      f b * g a ≤ f a * g b)
    (hsR : s ≤ R) :
    (∫⁻ t in Iic R, f t ∂μ) * (∫⁻ t in Iic s, g t ∂μ)
      ≤ (∫⁻ t in Iic s, f t ∂μ) * ∫⁻ t in Iic R, g t ∂μ := by sorry
