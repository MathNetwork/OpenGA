import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import OpenGALib.Riemannian.Volume.Util.ChartLocalMeasure
import OpenGALib.Riemannian.Volume.Util.ChartOverlap

/-!
# Integral characterization of the chart-local Riemannian volume measure

For `chartLocalMeasure g α` defined as a pushforward + weighted Lebesgue,
this file establishes the lintegral identification that converts a
manifold-side set-integral into an `E`-side set-integral over the chart
image, ready for Mathlib's change-of-variables formula.

  * `measurableSet_extChartAt_target` — extended-chart target is
    Borel-measurable in `E`.
  * `aemeasurable_extChartAt_symm_restrict_target` — `(extChartAt I α).symm`
    is `AEMeasurable` against `(modelHaar.restrict target)`.
  * `chartSqrtGramDet_continuousOn_source` — chart Jacobian factor is
    continuous on the chart source (from `chartSqrtGramDet_contMDiffOn`).
  * `aemeasurable_chartSqrtGramDet_symm_pullback` — `AEMeasurable` for
    the pulled-back density.
  * `chartLocalMeasure_lintegral` — full pushforward identity:
    `∫⁻ x ∂(chartLocalMeasure g α) = ∫⁻ y in target, ofReal(√det) · F(symm y) ∂modelHaar`.
  * `chartLocalMeasure_lintegral_U_eq_setLIntegral_image` — restricted
    version: `∫⁻ x in U ∂(chartLocalMeasure g α) = ∫⁻ y in α '' U, ...`.

These feed the B3 chart-overlap invariance theorem.
-/

noncomputable section


open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace H := borel H
private local instance : BorelSpace H := ⟨rfl⟩

/-! ## Borel measurability of the chart target -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [MeasurableSpace M] in
/-- **Eng.** The extended-chart target `(extChartAt I α).target` is
Borel-measurable in `E`. Decomposes as
`I.symm ⁻¹' (chartAt H α).target ∩ range I`: preimage of an open set
under a continuous map intersected with the closed range of `I`. -/
lemma measurableSet_extChartAt_target (α : M) :
    MeasurableSet (extChartAt I α).target := by
  rw [extChartAt_target (I := I)]
  refine MeasurableSet.inter ?_ ?_
  · exact (I.continuous_symm.isOpen_preimage _
      (chartAt H α).open_target).measurableSet
  · exact I.isClosed_range.measurableSet

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
/-- **Eng.** `(extChartAt I α).symm` is `AEMeasurable` against
`modelHaar.restrict (extChartAt I α).target`. Used for pushforward
lintegral computations. -/
lemma aemeasurable_extChartAt_symm_restrict_target (α : M) :
    AEMeasurable ((extChartAt I α).symm)
      ((modelHaar (E := E)).restrict (extChartAt I α).target) :=
  (continuousOn_extChartAt_symm α).aemeasurable
    (measurableSet_extChartAt_target α)

/-! ## Continuity of `chartSqrtGramDet` on the chart source -/

omit [MeasurableSpace M] in
/-- **Eng.** `chartSqrtGramDet g α` is continuous on
`(chartAt H α).source = (trivializationAt α).baseSet`. Derived from
`chartSqrtGramDet_contMDiffOn` via `ContMDiffOn → ContinuousOn`. -/
lemma chartSqrtGramDet_continuousOn_source
    (g : RiemannianMetric I M) (α : M) :
    ContinuousOn (chartSqrtGramDet (I := I) g α) (chartAt H α).source :=
  -- `(trivializationAt α).baseSet = (chartAt H α).source` definitionally.
  (chartSqrtGramDet_contMDiffOn (I := I) g α).continuousOn

omit [MeasurableSpace M] in
/-- **Eng.** `y ↦ ENNReal.ofReal (chartSqrtGramDet g α ((extChartAt I α).symm y))`
is `AEMeasurable` on `modelHaar.restrict (extChartAt I α).target`.
Composition chain: `chartSqrtGramDet g α` continuous on chart source,
`(extChartAt I α).symm` continuous on target with image in source,
`ENNReal.ofReal` measurable. -/
lemma aemeasurable_chartSqrtGramDet_symm_pullback
    (g : RiemannianMetric I M) (α : M) :
    AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I α).target) := by
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target α
  have hcontOn :
      ContinuousOn (chartSqrtGramDet (I := I) g α ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
    refine (chartSqrtGramDet_continuousOn_source (I := I) g α).comp
      (continuousOn_extChartAt_symm α) ?_
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source] at hsource
    exact hsource
  have haem : AEMeasurable
      (fun y : E => chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict (extChartAt I α).target) :=
    hcontOn.aemeasurable htarget_meas
  exact ENNReal.measurable_ofReal.comp_aemeasurable haem

/-! ## Pushforward → setLIntegral on `E` -/

/-- **Math.** Pushforward identity for `chartLocalMeasure`: integrating
any measurable function against `chartLocalMeasure g α` reduces to a
weighted lintegral on the chart target in `E`. -/
theorem chartLocalMeasure_lintegral
    (g : RiemannianMetric I M) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) =
      ∫⁻ y in (extChartAt I α).target,
        ENNReal.ofReal (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)) *
          F ((extChartAt I α).symm y) ∂ (modelHaar (E := E)) := by
  unfold chartLocalMeasure
  have haem_base := aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) α
  have hw_aem := aemeasurable_chartSqrtGramDet_symm_pullback (I := I) g α
  have hwd_ac :
      (((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y))))
        ≪ (modelHaar (E := E)).restrict (extChartAt I α).target :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have haem : AEMeasurable (extChartAt I α).symm
      (((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity
        (fun y : E =>
          ENNReal.ofReal
            (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)))) :=
    haem_base.mono_ac hwd_ac
  rw [MeasureTheory.lintegral_map' hF.aemeasurable haem]
  have hcomp :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
      (μ := (modelHaar (E := E)).restrict (extChartAt I α).target) hw_aem
      (g := fun y : E => F ((extChartAt I α).symm y))
      (hF.aemeasurable.comp_aemeasurable haem_base)
  simp only [Pi.mul_apply] at hcomp
  rw [hcomp]

/-- **Eng.** Set-lintegral form for a measurable subset `A`. -/
theorem chartLocalMeasure_setLintegral_indicator
    (g : RiemannianMetric I M) (α : M)
    {A : Set M} (hAmeas : MeasurableSet A)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in A, F x ∂(chartLocalMeasure (I := I) g α) =
      ∫⁻ y in (extChartAt I α).target,
        ENNReal.ofReal (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)) *
          A.indicator F ((extChartAt I α).symm y) ∂ (modelHaar (E := E)) := by
  rw [← MeasureTheory.lintegral_indicator hAmeas]
  exact chartLocalMeasure_lintegral (I := I) g α (hF.indicator hAmeas)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [MeasurableSpace M] in
/-- **Eng.** Indicator trick: the `U.indicator`-style target lintegral
equals a set-lintegral over `(extChartAt I α) '' U`. -/
lemma setLIntegral_target_eq_setLIntegral_image
    (α : M) {U : Set M}
    (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H α).source) (h : E → ℝ≥0∞) :
    ∫⁻ y in (extChartAt I α).target,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)) * h y
            ∂(modelHaar (E := E)) =
      ∫⁻ y in (extChartAt I α) '' U, h y ∂(modelHaar (E := E)) := by
  have hUsub' : U ⊆ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hUsub
  have himg :
      (extChartAt I α) '' U =
        (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' U :=
    (extChartAt I α).image_eq_target_inter_inv_preimage hUsub'
  have hptwise : ∀ y ∈ (extChartAt I α).target,
      U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) * h y =
        ((extChartAt I α) '' U).indicator h y := by
    intro y hy
    by_cases hy' : (extChartAt I α).symm y ∈ U
    · have hy_img : y ∈ (extChartAt I α) '' U := by
        rw [himg]; exact ⟨hy, hy'⟩
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy_img, one_mul]
    · have hy_nimg : y ∉ (extChartAt I α) '' U := by
        rw [himg]; exact fun h => hy' h.2
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy_nimg, zero_mul]
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target α
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hptwise]
  have hV_meas : MeasurableSet ((extChartAt I α) '' U) :=
    extChartAt_image_measurableSet_of_open_subset_source α hUopen hUsub
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  rw [show ((extChartAt I α) '' U) ∩ (extChartAt I α).target =
        (extChartAt I α) '' U from by
    rw [himg]; ext y; constructor
    · rintro ⟨⟨hy_t, hy_u⟩, _⟩; exact ⟨hy_t, hy_u⟩
    · rintro ⟨hy_t, hy_u⟩; exact ⟨⟨hy_t, hy_u⟩, hy_t⟩]

/-- **Math.** Manifold-side set-lintegral equals chart-image set-lintegral. -/
theorem chartLocalMeasure_lintegral_U_eq_setLIntegral_image
    (g : RiemannianMetric I M) (α : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H α).source)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hUmeas : MeasurableSet U) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g α) =
      ∫⁻ y in (extChartAt I α) '' U,
        ENNReal.ofReal (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)) *
          F ((extChartAt I α).symm y) ∂ (modelHaar (E := E)) := by
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g α hUmeas hF]
  have hpt : ∀ y : E,
      ENNReal.ofReal
            (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)) *
          U.indicator F ((extChartAt I α).symm y) =
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)) *
          (ENNReal.ofReal
              (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)) *
            F ((extChartAt I α).symm y)) := by
    intro y
    by_cases hy : (extChartAt I α).symm y ∈ U
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
        mul_zero, zero_mul]
  conv_lhs => rw [MeasureTheory.setLIntegral_congr_fun
    (measurableSet_extChartAt_target α)
    (fun y _ => hpt y)]
  exact setLIntegral_target_eq_setLIntegral_image (I := I) α hUopen hUsub _

/-! ## Chart-overlap invariance (B3 main theorem) -/

omit [MeasurableSpace M] in
/-- **Math.** `chartSqrtGramDet` pullback in `tangentCoordChange` language:
`chartSqrtGramDet g α₁ x = |det(tangentCoordChange α₁ α₀ x)| · chartSqrtGramDet g α₀ x`.
Combines the abstract `chartSqrtGramDet_pullback` (via `transitionMatrix`)
with the analysis-side bridge `transitionMatrix_det_eq_tangentCoordChange_det`. -/
theorem chartSqrtGramDet_pullback_tangentCoordChange
    (g : RiemannianMetric I M) (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    chartSqrtGramDet (I := I) g α₁ x =
      |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det| *
        chartSqrtGramDet (I := I) g α₀ x := by
  rw [chartSqrtGramDet_pullback g α₀ α₁ hx₀ hx₁,
      transitionMatrix_det_eq_tangentCoordChange_det α₀ α₁ hx₀ hx₁]

/-- **Math.** **Chart-overlap invariance of `chartLocalMeasure`**: the two
chart-local measures at `α₀` and `α₁` give the same lintegral on any
measurable function over the chart-source overlap.

Proof sketch: convert both sides to chart-image set-lintegrals on `E`,
apply `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`
with the chart-transition map `extChartAt α₁ ∘ (extChartAt α₀).symm`,
then cancel the Jacobian factor using `chartSqrtGramDet_pullback_tangentCoordChange`
together with `ennreal_abs_det_tangentCoordChange_mul_abs_det_inv`.

Ground truth: do Carmo Ch.1 §2; Lee Ch.16 (smooth atlas + change-of-
variables formula gives chart-independent volume measure). -/
theorem chartLocalMeasure_lintegral_U_eq_of_overlap
    (g : RiemannianMetric I M) (α₀ α₁ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in (chartAt H α₀).source ∩ (chartAt H α₁).source, F x
        ∂(chartLocalMeasure (I := I) g α₀) =
      ∫⁻ x in (chartAt H α₀).source ∩ (chartAt H α₁).source, F x
        ∂(chartLocalMeasure (I := I) g α₁) := by
  set U : Set M := (chartAt H α₀).source ∩ (chartAt H α₁).source with hU_def
  have hUopen : IsOpen U :=
    (chartAt H α₀).open_source.inter (chartAt H α₁).open_source
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUsub0 : U ⊆ (chartAt H α₀).source := Set.inter_subset_left
  have hUsub1 : U ⊆ (chartAt H α₁).source := Set.inter_subset_right
  -- Convert both sides to chart-image set-lintegrals on `E`.
  rw [chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
        g α₀ hUopen hUsub0 hF hUmeas,
      chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
        g α₁ hUopen hUsub1 hF hUmeas]
  -- The chart-transition map `T = extChartAt α₁ ∘ (extChartAt α₀).symm`
  -- carries `α₀ '' U` to `α₁ '' U`, is injective there with derivative
  -- `tangentCoordChange α₀ α₁ ((extChartAt α₀).symm y)`.
  have hV0_meas : MeasurableSet ((extChartAt I α₀) '' U) :=
    extChartAt_image_measurableSet_of_open_subset_source α₀ hUopen hUsub0
  have hT_image :
      (extChartAt I α₁ ∘ (extChartAt I α₀).symm) '' ((extChartAt I α₀) '' U) =
        (extChartAt I α₁) '' U :=
    extChartAt_transition_image α₀ α₁ hUsub0
  have hT_injOn :
      Set.InjOn (extChartAt I α₁ ∘ (extChartAt I α₀).symm)
        ((extChartAt I α₀) '' U) :=
    extChartAt_transition_injOn_overlap_image α₀ α₁ hUsub0 hUsub1
  have hT_fderiv :
      ∀ y ∈ (extChartAt I α₀) '' U,
        HasFDerivWithinAt (extChartAt I α₁ ∘ (extChartAt I α₀).symm)
          (tangentCoordChange I α₀ α₁ ((extChartAt I α₀).symm y))
          ((extChartAt I α₀) '' U) y :=
    extChartAt_transition_hasFDerivWithinAt_on_overlap_image α₀ α₁ hUsub0 hUsub1
  rw [← hT_image,
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (μ := modelHaar (E := E)) hV0_meas hT_fderiv hT_injOn
        (g := fun z : E =>
          ENNReal.ofReal
              (chartSqrtGramDet (I := I) g α₁ ((extChartAt I α₁).symm z)) *
            F ((extChartAt I α₁).symm z))]
  -- Pointwise identify the integrands: cancel Jacobian factors using
  -- `chartSqrtGramDet_pullback_tangentCoordChange` + |det| · |det⁻¹| = 1.
  refine MeasureTheory.setLIntegral_congr_fun hV0_meas ?_
  intro y hy
  obtain ⟨x, hxU, hx_eq⟩ := hy
  have hx0 : x ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact hUsub0 hxU
  have hx1 : x ∈ (extChartAt I α₁).source := by
    rw [extChartAt_source]; exact hUsub1 hxU
  have hx_in_inter : x ∈ (extChartAt I α₀).source ∩ (extChartAt I α₁).source :=
    ⟨hx0, hx1⟩
  have hx_trivBase0 : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet := by
    show x ∈ (chartAt H α₀).source
    exact hUsub0 hxU
  have hx_trivBase1 : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet := by
    show x ∈ (chartAt H α₁).source
    exact hUsub1 hxU
  have hsymm0 : (extChartAt I α₀).symm y = x := by
    rw [← hx_eq]; exact (extChartAt I α₀).left_inv hx0
  have hTy :
      (extChartAt I α₁ ∘ (extChartAt I α₀).symm) y = extChartAt I α₁ x := by
    change extChartAt I α₁ ((extChartAt I α₀).symm y) = _
    rw [hsymm0]
  have hsymm1 :
      (extChartAt I α₁).symm ((extChartAt I α₁ ∘ (extChartAt I α₀).symm) y) = x := by
    rw [hTy]; exact (extChartAt I α₁).left_inv hx1
  have hdens_pb :
      chartSqrtGramDet (I := I) g α₁ x =
        |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det| *
          chartSqrtGramDet (I := I) g α₀ x :=
    chartSqrtGramDet_pullback_tangentCoordChange g α₀ α₁ hx_trivBase0 hx_trivBase1
  have hdet_mul :
      ENNReal.ofReal |(tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det| *
        ENNReal.ofReal |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det| = 1 :=
    ennreal_abs_det_tangentCoordChange_mul_abs_det_inv α₀ α₁ hx_in_inter
  simp only [hsymm0, hsymm1]
  rw [hdens_pb, ENNReal.ofReal_mul (abs_nonneg _)]
  rw [show
    ENNReal.ofReal |(tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det| *
        (ENNReal.ofReal |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det| *
          ENNReal.ofReal (chartSqrtGramDet (I := I) g α₀ x) * F x) =
      (ENNReal.ofReal |(tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det| *
        ENNReal.ofReal |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det|) *
        (ENNReal.ofReal (chartSqrtGramDet (I := I) g α₀ x) * F x) by ring]
  rw [hdet_mul, one_mul]

/-- **Math.** Restrict form: the two chart-local measures agree on the
chart-source overlap (as restricted measures). -/
theorem chartLocalMeasure_restrict_overlap_eq
    (g : RiemannianMetric I M) (α₀ α₁ : M) :
    (chartLocalMeasure (I := I) g α₀).restrict
        ((chartAt H α₀).source ∩ (chartAt H α₁).source) =
      (chartLocalMeasure (I := I) g α₁).restrict
        ((chartAt H α₀).source ∩ (chartAt H α₁).source) := by
  refine MeasureTheory.Measure.ext_of_lintegral _ (fun F hF => ?_)
  exact chartLocalMeasure_lintegral_U_eq_of_overlap (I := I) g α₀ α₁ hF

end Riemannian.Tensor
