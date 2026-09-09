/-
Includes unchanged model-positivity helper proofs from qinz1yang/differential-geometry,
Copyright 2026 The DifferentialGeometry contributors, Apache-2.0.
Source commit: 1b535dd102b94cc42b107cca27059687888f08b3.
The volume-loss and finite-trace arguments are OpenGA results.
-/

import Lean
import Definitions.Def_OpenGA_RadialSurgeryVolumeBudget
import Definitions.Def_OpenGA_SurgeryComparisonProcess
import Definitions.Def_OpenGA_WidthComparisonTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

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

section
variable {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}
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
end

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

namespace OpenGA
/-- **Math.** Model-volume monotonicity supplies a uniform positive lower
bound for the volume removed at each event. -/
theorem RadialSurgeryVolumeBudget.removedVolume_lower (B : RadialSurgeryVolumeBudget)
    {t : ℝ} (ht : t ∈ B.events) :
    B.anchor * hypRadVol B.modelParameter 2 B.removalRadius ≤ B.removedVolume t := by
  have hR : 0 < B.referenceRadius := B.removalRadius_pos.trans_le B.radius_le
  have hm := antitoneOn_lintegral_div_hypRadVol B.modelParameter_nonneg
    (B.density_measurable t ht) (B.density_comparison t ht)
    ⟨B.removalRadius_pos, B.radius_le⟩ ⟨hR, le_rfl⟩ B.radius_le
  have hle := (B.reference_lower t ht).trans hm
  have hmul := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr
      (hypRadVol_pos B.modelParameter_nonneg B.removalRadius_pos)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mp hle
  have hbound := hmul.trans (B.removal_contains t ht)
  rw [← ENNReal.ofReal_mul B.anchor_pos.le] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (B.removedVolume_nonneg t ht)).mp hbound
end OpenGA

namespace OpenGA
/-- **Math.** A finite budget and a uniform positive loss force finitely
many events. The lower loss is derived from radial model comparison. -/
theorem RadialSurgeryVolumeBudget.events_finite (B : RadialSurgeryVolumeBudget) :
    B.events.Finite := by
  classical
  by_contra hinfinite
  have heps : 0 < B.anchor * hypRadVol B.modelParameter 2 B.removalRadius :=
    mul_pos B.anchor_pos (hypRadVol_pos B.modelParameter_nonneg B.removalRadius_pos)
  obtain ⟨n, hn⟩ := exists_nat_gt (B.totalBudget /
    (B.anchor * hypRadVol B.modelParameter 2 B.removalRadius))
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite n
  have hsum : (s.card : ℝ) * (B.anchor * hypRadVol B.modelParameter 2 B.removalRadius) ≤
      ∑ t ∈ s, B.removedVolume t := by
    calc
      _ = ∑ _t ∈ s, B.anchor * hypRadVol B.modelParameter 2 B.removalRadius := by simp
      _ ≤ _ := Finset.sum_le_sum fun t ht => B.removedVolume_lower (hs ht)
  rw [hcard] at hsum
  have hbudget := B.volume_budget s hs
  have hgt := (div_lt_iff₀ heps).mp hn
  linarith
end OpenGA

namespace OpenGA
/-- **Math.** A finite set of interior event times gives a strictly ordered
partition whose open subintervals contain no event. -/
theorem exists_event_free_partition {events : Set ℝ} {T : ℝ}
    (hfinite : events.Finite) (hinside : events ⊆ Ioo 0 T) (hT : 0 < T) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : ℕ → ℝ,
      times 0 = 0 ∧ times n = T ∧
      (∀ i ≤ n, times i ∈ Icc 0 T) ∧
      (∀ i < n, times i < times (i + 1)) ∧
      (∀ i < n, Disjoint events (Ioo (times i) (times (i + 1)))) := by
  classical
  let cuts : Finset ℝ := insert 0 (insert T hfinite.toFinset)
  have hzero : 0 ∈ cuts := by simp [cuts]
  have hterminal : T ∈ cuts := by simp [cuts]
  have hcard : 1 < cuts.card := Finset.one_lt_card.mpr
    ⟨0, hzero, T, hterminal, hT.ne⟩
  have hmem (t : ℝ) (ht : t ∈ cuts) : t ∈ Icc 0 T := by
    simp only [cuts, Finset.mem_insert, Set.Finite.mem_toFinset] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨le_rfl, hT.le⟩
    · exact ⟨hT.le, le_rfl⟩
    · exact ⟨(hinside ht).1.le, (hinside ht).2.le⟩
  let e := cuts.orderIsoOfFin rfl
  let times : ℕ → ℝ := fun i => if h : i < cuts.card then (e ⟨i, h⟩).val else T
  have htimes (i : ℕ) (hi : i < cuts.card) : times i = (e ⟨i, hi⟩).val := by
    simp [times, hi]
  have he_mem (i : Fin cuts.card) : (e i).val ∈ Icc 0 T := hmem _ (e i).property
  have hfirst : times 0 = 0 := by
    rw [htimes 0 (by omega)]
    apply le_antisymm
    · have h : (e ⟨0, by omega⟩).val ≤ (e (e.symm ⟨0, hzero⟩)).val :=
        e.monotone (show (⟨0, by omega⟩ : Fin cuts.card) ≤ e.symm ⟨0, hzero⟩ from
          show 0 ≤ (e.symm ⟨0, hzero⟩).val from Nat.zero_le _)
      simpa only [OrderIso.apply_symm_apply] using h
    · exact (he_mem _).1
  have hlast : times (cuts.card - 1) = T := by
    rw [htimes _ (by omega)]
    apply le_antisymm (he_mem _).2
    have h : (e (e.symm ⟨T, hterminal⟩)).val ≤ (e ⟨cuts.card - 1, by omega⟩).val :=
      e.monotone (show e.symm ⟨T, hterminal⟩ ≤ (⟨cuts.card - 1, by omega⟩ : Fin cuts.card) by
      have := (e.symm ⟨T, hterminal⟩).isLt
      show (e.symm ⟨T, hterminal⟩).val ≤ cuts.card - 1
      omega)
    simpa only [OrderIso.apply_symm_apply] using h
  refine ⟨cuts.card - 1, by omega, times, hfirst, hlast, ?_, ?_, ?_⟩
  · intro i hi
    rw [htimes i (by omega)]
    exact he_mem _
  · intro i hi
    rw [htimes i (by omega), htimes (i + 1) (by omega)]
    exact e.strictMono (show (⟨i, by omega⟩ : Fin cuts.card) < ⟨i + 1, by omega⟩ by
      show i < i + 1
      omega)
  · intro i hi
    apply Set.disjoint_left.mpr
    intro t ht hinterval
    have htcut : t ∈ cuts := by simp [cuts, ht]
    let j : Fin cuts.card := e.symm ⟨t, htcut⟩
    have hej : (e j).val = t := by simp [j]
    rw [htimes i (by omega), htimes (i + 1) (by omega), ← hej] at hinterval
    have hlo : (⟨i, by omega⟩ : Fin cuts.card) < j := e.lt_iff_lt.mp hinterval.1
    have hhi : j < (⟨i + 1, by omega⟩ : Fin cuts.card) := e.lt_iff_lt.mp hinterval.2
    have hlo' : i < j.val := hlo
    have hhi' : j.val < i + 1 := hhi
    omega
end OpenGA

namespace OpenGA
/-- **Math.** Volume control removes the possibility of infinitely many
partition events, yielding the finite comparison trace used by the width
extinction reduction. -/
theorem nonempty_widthComparisonTrace_of_surgeryComparisonProcess {W T : ℝ}
    (P : SurgeryComparisonProcess W T) : Nonempty (WidthComparisonTrace W T) := by
  obtain ⟨n, hn, times, hfirst, hlast, hmem, hstrict, hfree⟩ :=
    exists_event_free_partition P.volumeControl.events_finite P.events_inside P.finalTime_pos
  have hgap (i : ℕ) (hi : i < n) :
      EventFreeInterval P.volumeControl.events T (times i) (times (i + 1)) :=
    ⟨(hmem i (by omega)).1, hstrict i hi, (hmem (i + 1) (by omega)).2, hfree i hi⟩
  refine ⟨{
    count := n
    count_pos := hn
    times := times
    first_time := hfirst
    last_time := hlast
    times_strict := hstrict
    scalar := fun i => P.scalar (times i)
    width := fun i => P.width (times i)
    scalar_cont := fun i hi => P.scalar_cont _ _ (hgap i hi)
    width_cont := fun i hi => P.width_cont _ _ (hgap i hi)
    scalar_initial := ?_
    width_initial := ?_
    width_nonneg := fun i hi => P.width_nonneg _ _ (hgap i hi)
    scalar_slope := fun i hi => P.scalar_slope _ _ (hgap i hi)
    comparison := fun i hi => P.comparison _ _ (hgap i hi)
    scalar_jump := fun i hi => P.scalar_jump _ _ _ (hgap i (by omega)) (hgap (i + 1) hi)
    width_jump := fun i hi => P.width_jump _ _ _ (hgap i (by omega)) (hgap (i + 1) hi)
  }⟩
  · simpa only [hfirst] using P.scalar_initial
  · simpa only [hfirst] using P.width_initial
end OpenGA

open Lean in
run_meta do
  for name in #[`OpenGA.RadialSurgeryVolumeBudget.removedVolume_lower, `OpenGA.RadialSurgeryVolumeBudget.events_finite, `OpenGA.exists_event_free_partition, `OpenGA.nonempty_widthComparisonTrace_of_surgeryComparisonProcess] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
    Lean.logInfo m!"{name}: {axioms}"
