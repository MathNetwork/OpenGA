import Lean
import Theorems.Thm_OpenGA_antitoneOn_lintegral_div_hypRadVol
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

/-- **Math.** Cross-comparison of nonnegative radial densities makes the ratio of
their accumulated integrals nonincreasing when the denominator is positive
and finite. No finiteness assumption on the numerator is needed. -/
theorem OpenGA.antitoneOn_lintegral_Ioc_div {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}
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

open Lean in
run_meta do
  let target ← Lean.getConstInfo `OpenGA.antitoneOn_lintegral_div_hypRadVol
  let solved ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq target.type solved.type do
    throwError "Solution type mismatch"
  let axioms ← Lean.collectAxioms `solution
  for name in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "Unexpected axiom: {name}"
  Lean.logInfo m!"Exact target type and complete proof checked; axioms: {axioms}"
