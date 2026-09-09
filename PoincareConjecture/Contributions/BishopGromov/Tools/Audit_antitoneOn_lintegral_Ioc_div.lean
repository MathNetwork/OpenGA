import Lean
import Theorems.Thm_OpenGA_antitoneOn_lintegral_Ioc_div
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
open Lean in
run_meta do
  let target ← Lean.getConstInfo `OpenGA.antitoneOn_lintegral_Ioc_div
  let solved ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq target.type solved.type do
    throwError "The solution type does not match its target"
  let axioms ← Lean.collectAxioms `solution
  for name in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "Unexpected proof axiom: {name}"
  Lean.logInfo m!"Exact target type matched after resolving the audited child proof; axioms: {axioms}"
