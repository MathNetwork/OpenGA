/-
Copyright 2026 The DifferentialGeometry contributors.
Licensed under Apache-2.0. Adapted from qinz1yang/differential-geometry,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Only declaration placement and platform imports are changed.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint

open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem solution {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [ClosedIicTopology α]
    {μ : Measure α} {f g : α → ℝ≥0∞} {s R : α}
    (hf : AEMeasurable f (μ.restrict (Iic R)))
    (hg : AEMeasurable g (μ.restrict (Iic R)))
    (hcross : ∀ ⦃a b : α⦄, a ≤ b → b ≤ R →
      f b * g a ≤ f a * g b)
    (hsR : s ≤ R) :
    (∫⁻ t in Iic R, f t ∂μ) * (∫⁻ t in Iic s, g t ∂μ)
      ≤ (∫⁻ t in Iic s, f t ∂μ) * ∫⁻ t in Iic R, g t ∂μ := by
  have hAm : MeasurableSet (Iic s) := measurableSet_Iic
  have hBm : MeasurableSet (Ioc s R) := measurableSet_Ioc
  have hdisj : Disjoint (Iic s) (Ioc s R) := Iic_disjoint_Ioc le_rfl
  have hunion : Iic s ∪ Ioc s R = Iic R := Iic_union_Ioc_eq_Iic hsR
  have hAsub : Iic s ⊆ Iic R := Iic_subset_Iic.mpr hsR
  have hBsub : Ioc s R ⊆ Iic R := Ioc_subset_Iic_self
  have hfA : AEMeasurable f (μ.restrict (Iic s)) :=
    hf.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hfB : AEMeasurable f (μ.restrict (Ioc s R)) :=
    hf.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hgA : AEMeasurable g (μ.restrict (Iic s)) :=
    hg.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hgB : AEMeasurable g (μ.restrict (Ioc s R)) :=
    hg.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hf_split : ∫⁻ t in Iic R, f t ∂μ
      = (∫⁻ t in Iic s, f t ∂μ) + ∫⁻ t in Ioc s R, f t ∂μ := by
    rw [← hunion]
    exact lintegral_union hBm hdisj
  have hg_split : ∫⁻ t in Iic R, g t ∂μ
      = (∫⁻ t in Iic s, g t ∂μ) + ∫⁻ t in Ioc s R, g t ∂μ := by
    rw [← hunion]
    exact lintegral_union hBm hdisj
  have hstar : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Iic s, g t ∂μ)
      ≤ (∫⁻ t in Iic s, f t ∂μ) * ∫⁻ t in Ioc s R, g t ∂μ := by
    have e1 : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Iic s, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Iic s, f b * g a ∂μ ∂μ := by
      rw [← lintegral_mul_const'' _ hfB]
      exact lintegral_congr fun b => (lintegral_const_mul'' _ hgA).symm
    have e2 : (∫⁻ t in Iic s, f t ∂μ) * (∫⁻ t in Ioc s R, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Iic s, f a * g b ∂μ ∂μ := by
      rw [← lintegral_const_mul'' _ hgB]
      exact lintegral_congr fun b => (lintegral_mul_const'' _ hfA).symm
    rw [e1, e2]
    refine lintegral_mono_ae ((ae_restrict_mem hBm).mono fun b hb => ?_)
    exact lintegral_mono_ae ((ae_restrict_mem hAm).mono fun a ha =>
      hcross (ha.trans hb.1.le) hb.2)
  rw [hf_split, hg_split, add_mul, mul_add]
  exact add_le_add le_rfl hstar
