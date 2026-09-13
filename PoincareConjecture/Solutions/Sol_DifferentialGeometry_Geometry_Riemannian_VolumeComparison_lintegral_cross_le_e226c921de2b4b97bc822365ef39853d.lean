/-
Copyright 2026 The DifferentialGeometry contributors.
Licensed under Apache-2.0. Adapted from qinz1yang/differential-geometry,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Only declaration placement and platform imports are changed.
-/

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

theorem solution {s : ℝ}
    (hf : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) R)))
    (hg : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f g) (hs : 0 ≤ s) (hsR : s ≤ R) :
    (∫⁻ t in Ioc (0 : ℝ) R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * ∫⁻ t in Ioc (0 : ℝ) R, g t ∂μ := by
  have hAm : MeasurableSet (Ioc (0 : ℝ) s) := measurableSet_Ioc
  have hBm : MeasurableSet (Ioc s R) := measurableSet_Ioc
  have hdisj : Disjoint (Ioc (0 : ℝ) s) (Ioc s R) := Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Ioc (0 : ℝ) s ∪ Ioc s R = Ioc (0 : ℝ) R := Ioc_union_Ioc_eq_Ioc hs hsR
  have hAsub : Ioc (0 : ℝ) s ⊆ Ioc (0 : ℝ) R := Ioc_subset_Ioc le_rfl hsR
  have hBsub : Ioc s R ⊆ Ioc (0 : ℝ) R := Ioc_subset_Ioc hs le_rfl
  have hfA : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) s)) :=
    hf.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hfB : AEMeasurable f (μ.restrict (Ioc s R)) :=
    hf.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hgA : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) s)) :=
    hg.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hgB : AEMeasurable g (μ.restrict (Ioc s R)) :=
    hg.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hf_split : ∫⁻ t in Ioc (0 : ℝ) R, f t ∂μ
      = (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) + ∫⁻ t in Ioc s R, f t ∂μ := by
    rw [← hunion]; exact lintegral_union hBm hdisj
  have hg_split : ∫⁻ t in Ioc (0 : ℝ) R, g t ∂μ
      = (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ) + ∫⁻ t in Ioc s R, g t ∂μ := by
    rw [← hunion]; exact lintegral_union hBm hdisj
  have hstar : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * ∫⁻ t in Ioc s R, g t ∂μ := by
    have e1 : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Ioc (0 : ℝ) s, f b * g a ∂μ ∂μ := by
      rw [← lintegral_mul_const'' _ hfB]
      exact lintegral_congr fun b => (lintegral_const_mul'' _ hgA).symm
    have e2 : (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * (∫⁻ t in Ioc s R, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Ioc (0 : ℝ) s, f a * g b ∂μ ∂μ := by
      rw [← lintegral_const_mul'' _ hgB]
      exact lintegral_congr fun b => (lintegral_mul_const'' _ hfA).symm
    rw [e1, e2]
    refine lintegral_mono_ae ((ae_restrict_mem hBm).mono fun b hb => ?_)
    exact lintegral_mono_ae ((ae_restrict_mem hAm).mono fun a ha =>
      hcross a b ha.1 (ha.2.trans hb.1.le) hb.2)
  rw [hf_split, hg_split, add_mul, mul_add]
  exact add_le_add le_rfl hstar
