import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.ChartLocalIbp
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.ENNReal.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [InnerProductSpace ℝ E] in
theorem integral_localDivergenceWithin_eq_of_interior_overlap_support [T2Space M]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source ∩ (chartAt H β).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    ∫ x, localDivergenceWithin (I := I) g α X x * φ x
        ∂(chartLocalMeasure (I := I) g α) =
      ∫ x, localDivergenceWithin (I := I) g β X x * φ x
        ∂(chartLocalMeasure (I := I) g β) := by
  have hsupp_α : tsupport φ ⊆ (chartAt H α).source := hφ_supp.trans Set.inter_subset_left
  have hsupp_β : tsupport φ ⊆ (chartAt H β).source := hφ_supp.trans Set.inter_subset_right
  have hibp_α := chart_local_ibp_within (I := I) g α X hφ hφ_compactSupp hsupp_α hφ_int
  have hibp_β := chart_local_ibp_within (I := I) g β X hφ hφ_compactSupp hsupp_β hφ_int
  rw [hibp_α, hibp_β]
  refine congrArg Neg.neg ?_
  set U : Set M := (chartAt H α).source ∩ (chartAt H β).source with hU_def
  have hU_open : IsOpen U := IsOpen.inter (chartAt H α).open_source (chartAt H β).open_source
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have htsa_supp : ∀ x ∉ U, tangentSectionAction (I := I) X φ x = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have hOpen_compl : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
    have hphi_zero_on_nhd : φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hOpen_compl.mem_nhds hxsupp] with z hz
      by_contra hne
      exact hz (subset_tsupport _ hne)
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) φ x = 0 := by
      have h_eq : mfderiv I 𝓘(ℝ) φ x = mfderiv I 𝓘(ℝ) (fun _ : M => (0 : ℝ)) x :=
        Filter.EventuallyEq.mfderiv_eq hphi_zero_on_nhd
      rw [h_eq, mfderiv_const]; rfl
    change mfderiv I 𝓘(ℝ) φ x (X x) = 0
    rw [hmfderiv_zero]; rfl
  have htsa_α : ∫ x, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g α) =
      ∫ x in U, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g α) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero htsa_supp]
  have htsa_β : ∫ x, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g β) =
      ∫ x in U, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g β) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero htsa_supp]
  rw [htsa_α, htsa_β]
  have h_meas_eq : (chartLocalMeasure (I := I) g α).restrict U =
      (chartLocalMeasure (I := I) g β).restrict U :=
    chartLocalMeasure_restrict_overlap_eq (I := I) g α β
  rw [show ∫ x in U, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X φ x
          ∂((chartLocalMeasure (I := I) g α).restrict U) from rfl]
  rw [show ∫ x in U, tangentSectionAction (I := I) X φ x
        ∂(chartLocalMeasure (I := I) g β) =
        ∫ x, tangentSectionAction (I := I) X φ x
          ∂((chartLocalMeasure (I := I) g β).restrict U) from rfl]
  rw [h_meas_eq]

omit [InnerProductSpace ℝ E] in
private lemma chartLocalMeasure_open_pos_of_interior_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {V : Set M} (hVopen : IsOpen V) {x₁ : M} (hx₁V : x₁ ∈ V)
    (hVsub : V ⊆ (chartAt H α).source)
    (hx₁_int : x₁ ∈ I.interior M) :
    0 < chartLocalMeasure (I := I) g α V := by
  classical
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hx₁_chart : x₁ ∈ (chartAt H α).source := hVsub hx₁V
  have hx₁_target_int : extChartAt I α x₁ ∈ interior (extChartAt I α).target :=
    extChartAt_mem_interior_target_of_isInteriorPoint
      (I := I) (M := M) α hx₁_chart hx₁_int
  have hx₁_range_int : extChartAt I α x₁ ∈ interior (Set.range I) := by
    have h_subset : interior (extChartAt I α).target ⊆ interior (Set.range I) := by
      change interior ((chartAt H α).extend I).target ⊆ _
      exact OpenPartialHomeomorph.interior_extend_target_subset_interior_range _
    exact h_subset hx₁_target_int
  have hind_meas : Measurable (V.indicator (fun _ : M => (1 : ℝ≥0∞))) :=
    (measurable_const).indicator hVmeas
  have hlint := chartLocalMeasure_lintegral (I := I) g α hind_meas
  have hVvol : chartLocalMeasure (I := I) g α V =
      ∫⁻ x, V.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ chartLocalMeasure (I := I) g α := by
    rw [lintegral_indicator hVmeas, setLIntegral_const, one_mul]
  rw [hVvol, hlint]
  set T : Set E := (extChartAt I α).target with hT_def
  have hT_meas : MeasurableSet T := measurableSet_extChartAt_target (I := I) α
  have hVsub' : V ⊆ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hVsub
  have hV_nhds : V ∈ 𝓝 x₁ := hVopen.mem_nhds hx₁V
  have hx₁src : x₁ ∈ (extChartAt I α).source := hVsub' hx₁V
  have hImgNhd : (extChartAt I α) '' V ∈ 𝓝 ((extChartAt I α) x₁) :=
    extChartAt_image_nhds_mem_nhds_of_mem_interior_range (I := I) (M := M)
      (x := α) (y := x₁) hx₁src hx₁_range_int hV_nhds
  rcases mem_nhds_iff.mp hImgNhd with ⟨W, hW_sub, hW_open, hW_mem⟩
  have hW_meas : MeasurableSet W := hW_open.measurableSet
  have hW_ne : W.Nonempty := ⟨(extChartAt I α) x₁, hW_mem⟩
  have hW_pos : 0 < (modelHaar (E := E)) W := hW_open.measure_pos _ hW_ne
  have hW_sub_T : W ⊆ T := by
    intro y hyW
    rcases hW_sub hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := hVsub' hxV
    have : (extChartAt I α) x ∈ T := (extChartAt I α).map_source hxsrc
    rwa [hxy] at this
  have hdensity_on_W : ∀ y ∈ W, 0 < chartDensity g α ((extChartAt I α).symm y) := by
    intro y hyW
    rcases hW_sub hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := hVsub' hxV
    have hleft : (extChartAt I α).symm y = x := by
      rw [← hxy]; exact (extChartAt I α).left_inv hxsrc
    rw [hleft]
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hVsub hxV
    exact chartDensity_pos (I := I) g α hxbase
  have hind_on_W : ∀ y ∈ W,
      V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) = 1 := by
    intro y hyW
    rcases hW_sub hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := hVsub' hxV
    have hleft : (extChartAt I α).symm y = x := by
      rw [← hxy]; exact (extChartAt I α).left_inv hxsrc
    rw [hleft, Set.indicator_of_mem hxV]
  have h_restrict_subset :
      ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
            V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
              ∂(modelHaar (E := E))
        ≤ ∫⁻ y in T, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
            V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
              ∂(modelHaar (E := E)) :=
    lintegral_mono_set hW_sub_T
  refine lt_of_lt_of_le ?_ h_restrict_subset
  by_contra h0
  have h0' : ¬ (0 < ∫⁻ y in W, ENNReal.ofReal
      (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) := h0
  have h0eq :
      ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
            ∂(modelHaar (E := E)) = 0 :=
    le_antisymm (not_lt.mp h0') (zero_le _)
  have haem_density_T : AEMeasurable
      (fun y : E => chartDensity g α ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict (extChartAt I α).target) := by
    have hcontOn : ContinuousOn
        (fun y : E => chartDensity g α ((extChartAt I α).symm y))
        (extChartAt I α).target := by
      refine (chartDensity_continuousOn (I := I) g α).comp
        (continuousOn_extChartAt_symm (I := I) α) ?_
      intro y hy
      have : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    exact hcontOn.aemeasurable hT_meas
  have haem_density_W : AEMeasurable
      (fun y : E => chartDensity g α ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict W) :=
    haem_density_T.mono_measure (Measure.restrict_mono hW_sub_T le_rfl)
  have h1 : AEMeasurable
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)))
      ((modelHaar (E := E)).restrict W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable haem_density_W
  have hsymm_aem_T : AEMeasurable (extChartAt I α).symm
      ((modelHaar (E := E)).restrict (extChartAt I α).target) :=
    (continuousOn_extChartAt_symm (I := I) α).aemeasurable hT_meas
  have hsymm_aem_W : AEMeasurable (extChartAt I α).symm
      ((modelHaar (E := E)).restrict W) :=
    hsymm_aem_T.mono_measure (Measure.restrict_mono hW_sub_T le_rfl)
  have h2 : AEMeasurable
      (fun y : E => V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict W) :=
    hind_meas.comp_aemeasurable hsymm_aem_W
  have haem_integrand : AEMeasurable
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y))
      ((modelHaar (E := E)).restrict W) := h1.mul h2
  have hae_zero := (MeasureTheory.lintegral_eq_zero_iff' haem_integrand).mp h0eq
  have hW_ae_zero :
      ∀ᵐ y ∂(modelHaar (E := E)), y ∈ W →
        ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) = 0 :=
    (MeasureTheory.ae_restrict_iff' hW_meas).mp hae_zero
  have hW_zero : (modelHaar (E := E)) W = 0 := by
    have hyNotW : ∀ᵐ y ∂(modelHaar (E := E)), y ∉ W := by
      filter_upwards [hW_ae_zero] with y hy
      intro hyW
      have hpos : 0 < ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) := by
        rw [hind_on_W y hyW, mul_one]
        exact ENNReal.ofReal_pos.mpr (hdensity_on_W y hyW)
      exact (ne_of_gt hpos) (hy hyW)
    exact measure_eq_zero_iff_ae_notMem.mpr hyNotW
  exact (ne_of_gt hW_pos) hW_zero

private lemma exists_open_nbhd_positive
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hfcont : ContinuousOn f U)
    {x : M} (hxU : x ∈ U) (hfx : 0 < f x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, f x / 2 < f y := by
  classical
  have hfx2 : 0 < f x / 2 := by positivity
  have hfcont_at : ContinuousAt f x :=
    (hfcont x hxU).continuousAt (hU.mem_nhds hxU)
  have hfx_lt : f x / 2 < f x := by linarith
  obtain ⟨V₀, hV₀_nhd, hV₀⟩ : ∃ V₀ ∈ 𝓝 x, ∀ y ∈ V₀, f x / 2 < f y := by
    have := hfcont_at.eventually (p := fun y => f x / 2 < y) ?_
    · exact ⟨_, this, fun y hy => hy⟩
    · exact eventually_nhds_iff.mpr ⟨Ioi (f x / 2), fun _ => id, isOpen_Ioi, hfx_lt⟩
  rcases mem_nhds_iff.mp hV₀_nhd with ⟨W, hW_sub, hW_open, hxW⟩
  refine ⟨W ∩ U, hW_open.inter hU, ⟨hxW, hxU⟩, Set.inter_subset_right, ?_⟩
  intro y hy
  exact hV₀ y (hW_sub hy.1)

omit [InnerProductSpace ℝ E] in
private lemma exists_smooth_bump_in_open [T2Space M]
    {V : Set M} (hVopen : IsOpen V) {x : M} (hxV : x ∈ V) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ V ∧ (∀ y, 0 ≤ φ y) ∧ 0 < φ x := by
  classical
  have hVnhd : V ∈ 𝓝 x := hVopen.mem_nhds hxV
  obtain ⟨f, _, hfsupp_subset⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hVnhd
  refine ⟨f, f.contMDiff, f.hasCompactSupport, hfsupp_subset, ?_, ?_⟩
  · intro y; exact f.nonneg
  · rw [f.eq_one]; exact one_pos

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞) (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

omit [InnerProductSpace ℝ E] in
private theorem localDivergenceWithin_chart_invariance_pos [T2Space M]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) (hx_β : x ∈ (chartAt H β).source)
    (hx_int : x ∈ I.interior M)
    (hΔpos : 0 < localDivergenceWithin (I := I) g α X x -
      localDivergenceWithin (I := I) g β X x) :
    False := by
  classical
  set U : Set M := (chartAt H α).source ∩ (chartAt H β).source ∩ I.interior M
    with hU_def
  have hUopen : IsOpen U := by
    refine IsOpen.inter ?_ isOpen_interior_M
    exact IsOpen.inter (chartAt H α).open_source (chartAt H β).open_source
  have hxU : x ∈ U := ⟨⟨hx_α, hx_β⟩, hx_int⟩
  set Δ : M → ℝ := fun y => localDivergenceWithin (I := I) g α X y -
      localDivergenceWithin (I := I) g β X y with hΔ_def
  have hα_contOn : ContinuousOn (localDivergenceWithin (I := I) g α X) U := by
    refine (localDivergenceWithin_continuousOn (I := I) g α X).mono ?_
    intro x' hx'; exact hx'.1.1
  have hβ_contOn : ContinuousOn (localDivergenceWithin (I := I) g β X) U := by
    refine (localDivergenceWithin_continuousOn (I := I) g β X).mono ?_
    intro x' hx'; exact hx'.1.2
  have hΔ_contOn : ContinuousOn Δ U := hα_contOn.sub hβ_contOn
  obtain ⟨V, hVopen, hxV, hVU, hΔ_pos⟩ :=
    exists_open_nbhd_positive (M := M) hUopen hΔ_contOn hxU hΔpos
  obtain ⟨φ, hφ_smooth, hφ_compactSupp, hφ_supp, hφ_nonneg, hφx_pos⟩ :=
    exists_smooth_bump_in_open (I := I) hVopen hxV
  have hsupp_overlap : tsupport φ ⊆
      (chartAt H α).source ∩ (chartAt H β).source := by
    intro y hy
    exact (hVU (hφ_supp hy)).1
  have hsupp_int : tsupport φ ⊆ I.interior M := by
    intro y hy
    exact (hVU (hφ_supp hy)).2
  have hint_eq := integral_localDivergenceWithin_eq_of_interior_overlap_support
    (I := I) g α β X hφ_smooth hφ_compactSupp hsupp_overlap hsupp_int
  have hrestrict_eq := chartLocalMeasure_restrict_overlap_eq (I := I) g α β
  set Uoverlap : Set M := (chartAt H α).source ∩ (chartAt H β).source
    with hUoverlap_def
  have hsupp_in_overlap : tsupport φ ⊆ Uoverlap := hsupp_overlap
  have hβ_int_via_restrict :
      ∫ y, localDivergenceWithin (I := I) g β X y * φ y
        ∂(chartLocalMeasure (I := I) g β) =
        ∫ y, localDivergenceWithin (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g α) := by
    have hzero_off : ∀ y ∉ Uoverlap, localDivergenceWithin (I := I) g β X y * φ y = 0 := by
      intro y hy
      have hy_supp : y ∉ tsupport φ := fun h => hy (hsupp_overlap h)
      have : φ y = 0 := by
        by_contra hne; exact hy_supp (subset_tsupport _ hne)
      rw [this, mul_zero]
    have hβ_to_U : ∫ y, localDivergenceWithin (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g β) =
        ∫ y in Uoverlap, localDivergenceWithin (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g β) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero_off).symm
    have hα_to_U : ∫ y, localDivergenceWithin (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ y in Uoverlap, localDivergenceWithin (I := I) g β X y * φ y
          ∂(chartLocalMeasure (I := I) g α) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero_off).symm
    rw [hβ_to_U, hα_to_U]
    change ∫ y, localDivergenceWithin (I := I) g β X y * φ y
          ∂((chartLocalMeasure (I := I) g β).restrict Uoverlap) =
        ∫ y, localDivergenceWithin (I := I) g β X y * φ y
          ∂((chartLocalMeasure (I := I) g α).restrict Uoverlap)
    rw [← hrestrict_eq]
  have hsupp_α_chart : tsupport φ ⊆ (chartAt H α).source :=
    hsupp_overlap.trans Set.inter_subset_left
  have hsupp_β_chart : tsupport φ ⊆ (chartAt H β).source :=
    hsupp_overlap.trans Set.inter_subset_right
  have h1_int : Integrable
      (fun y => localDivergenceWithin (I := I) g α X y * φ y)
      (chartLocalMeasure (I := I) g α) := by
    have h_cont_total : Continuous
        (fun y => localDivergenceWithin (I := I) g α X y * φ y) := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ (chartAt H α).source
      · have hα_at : ContinuousAt (localDivergenceWithin (I := I) g α X) y :=
          ((localDivergenceWithin_continuousOn (I := I) g α X) y hy).continuousAt
            ((chartAt H α).open_source.mem_nhds hy)
        exact hα_at.mul hφ_smooth.continuous.continuousAt
      · have hy_supp : y ∉ tsupport φ := fun h => hy (hsupp_α_chart h)
        have h_open : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
        have hphi_zero_nhd : φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy_supp] with z hz
          by_contra hne; exact hz (subset_tsupport _ hne)
        have hzero_nhd : (fun z => localDivergenceWithin (I := I) g α X z * φ z) =ᶠ[𝓝 y]
            (fun _ => (0 : ℝ)) := by
          filter_upwards [hphi_zero_nhd] with z hz
          rw [hz, mul_zero]
        exact (continuous_const.continuousAt.congr hzero_nhd.symm)
    have h_compact_supp : HasCompactSupport (fun y =>
        localDivergenceWithin (I := I) g α X y * φ y) :=
      hφ_compactSupp.mul_left
    have hsupp_α' : tsupport (fun y => localDivergenceWithin (I := I) g α X y * φ y) ⊆
        (chartAt H α).source := by
      refine subset_trans ?_ hsupp_α_chart
      refine closure_minimal ?_ (isClosed_tsupport φ)
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hne
      have : φ y = 0 := by
        by_contra hne'; exact hne (subset_tsupport _ hne')
      exact hy (by rw [this, mul_zero])
    have hμ_supp_bound : chartLocalMeasure (I := I) g α
          (tsupport (fun y => localDivergenceWithin (I := I) g α X y * φ y)) < ⊤ :=
      chartLocalMeasure_compact_lt_top (I := I) g α h_compact_supp hsupp_α'
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖localDivergenceWithin (I := I) g α X y * φ y‖ ≤ C :=
      h_compact_supp.exists_bound_of_continuous h_cont_total
    refine ⟨h_cont_total.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hbnd : ∀ᵐ y ∂(chartLocalMeasure (I := I) g α),
        ENNReal.ofReal (‖localDivergenceWithin (I := I) g α X y * φ y‖) ≤
        ENNReal.ofReal C *
          (tsupport (fun y => localDivergenceWithin (I := I) g α X y * φ y)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      by_cases hy : y ∈ tsupport (fun y => localDivergenceWithin (I := I) g α X y * φ y)
      · rw [Set.indicator_of_mem hy, mul_one]
        exact ENNReal.ofReal_le_ofReal (hC y)
      · rw [Set.indicator_of_notMem hy, mul_zero]
        have : localDivergenceWithin (I := I) g α X y * φ y = 0 := by
          by_contra hne; exact hy (subset_tsupport _ hne)
        rw [this]; simp
    calc ∫⁻ y, ENNReal.ofReal ‖localDivergenceWithin (I := I) g α X y * φ y‖
          ∂(chartLocalMeasure (I := I) g α)
        ≤ ∫⁻ y, ENNReal.ofReal C *
            (tsupport (fun y => localDivergenceWithin (I := I) g α X y * φ y)).indicator
              (fun _ => (1 : ℝ≥0∞)) y
          ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
      _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α
            (tsupport (fun y => localDivergenceWithin (I := I) g α X y * φ y)) := by
            rw [lintegral_const_mul _ ((measurable_const).indicator
              (isClosed_tsupport _).measurableSet)]
            rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
            rw [setLIntegral_const, one_mul]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp_bound
  have h2_int : Integrable
      (fun y => localDivergenceWithin (I := I) g β X y * φ y)
      (chartLocalMeasure (I := I) g α) := by
    have h_cont_total : Continuous
        (fun y => localDivergenceWithin (I := I) g β X y * φ y) := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ (chartAt H β).source
      · have hβ_at : ContinuousAt (localDivergenceWithin (I := I) g β X) y :=
          ((localDivergenceWithin_continuousOn (I := I) g β X) y hy).continuousAt
            ((chartAt H β).open_source.mem_nhds hy)
        exact hβ_at.mul hφ_smooth.continuous.continuousAt
      · have hy_supp : y ∉ tsupport φ := fun h => hy (hsupp_β_chart h)
        have h_open : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
        have hphi_zero_nhd : φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy_supp] with z hz
          by_contra hne; exact hz (subset_tsupport _ hne)
        have hzero_nhd : (fun z => localDivergenceWithin (I := I) g β X z * φ z) =ᶠ[𝓝 y]
            (fun _ => (0 : ℝ)) := by
          filter_upwards [hphi_zero_nhd] with z hz
          rw [hz, mul_zero]
        exact (continuous_const.continuousAt.congr hzero_nhd.symm)
    have h_compact_supp : HasCompactSupport
        (fun y => localDivergenceWithin (I := I) g β X y * φ y) := hφ_compactSupp.mul_left
    have hsupp_α' : tsupport (fun y => localDivergenceWithin (I := I) g β X y * φ y) ⊆
        (chartAt H α).source := by
      refine subset_trans ?_ hsupp_α_chart
      refine closure_minimal ?_ (isClosed_tsupport φ)
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hne
      have : φ y = 0 := by
        by_contra hne'; exact hne (subset_tsupport _ hne')
      exact hy (by rw [this, mul_zero])
    have hμ_supp_bound : chartLocalMeasure (I := I) g α
          (tsupport (fun y => localDivergenceWithin (I := I) g β X y * φ y)) < ⊤ :=
      chartLocalMeasure_compact_lt_top (I := I) g α h_compact_supp hsupp_α'
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖localDivergenceWithin (I := I) g β X y * φ y‖ ≤ C :=
      h_compact_supp.exists_bound_of_continuous h_cont_total
    refine ⟨h_cont_total.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hbnd : ∀ᵐ y ∂(chartLocalMeasure (I := I) g α),
        ENNReal.ofReal (‖localDivergenceWithin (I := I) g β X y * φ y‖) ≤
        ENNReal.ofReal C *
          (tsupport (fun y => localDivergenceWithin (I := I) g β X y * φ y)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      by_cases hy : y ∈ tsupport (fun y => localDivergenceWithin (I := I) g β X y * φ y)
      · rw [Set.indicator_of_mem hy, mul_one]
        exact ENNReal.ofReal_le_ofReal (hC y)
      · rw [Set.indicator_of_notMem hy, mul_zero]
        have : localDivergenceWithin (I := I) g β X y * φ y = 0 := by
          by_contra hne; exact hy (subset_tsupport _ hne)
        rw [this]; simp
    calc ∫⁻ y, ENNReal.ofReal ‖localDivergenceWithin (I := I) g β X y * φ y‖
          ∂(chartLocalMeasure (I := I) g α)
        ≤ ∫⁻ y, ENNReal.ofReal C *
            (tsupport (fun y => localDivergenceWithin (I := I) g β X y * φ y)).indicator
              (fun _ => (1 : ℝ≥0∞)) y
          ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
      _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α
            (tsupport (fun y => localDivergenceWithin (I := I) g β X y * φ y)) := by
            rw [lintegral_const_mul _ ((measurable_const).indicator
              (isClosed_tsupport _).measurableSet)]
            rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
            rw [setLIntegral_const, one_mul]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp_bound
  have hΔ_int_zero :
      ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) = 0 := by
    have hexpand : (fun y => Δ y * φ y) =
        fun y => localDivergenceWithin (I := I) g α X y * φ y -
          localDivergenceWithin (I := I) g β X y * φ y := by
      funext y; simp [Δ, sub_mul]
    rw [hexpand, integral_sub h1_int h2_int, hint_eq, ← hβ_int_via_restrict]
    ring
  have hΔ_int_pos :
      0 < ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := by
    have hV_sub_α : V ⊆ (chartAt H α).source := by
      intro y hy
      exact ((hVU hy).1).1
    have hφx_half_pos : 0 < φ x / 2 := by linarith
    obtain ⟨V₀, hV₀_open, hxV₀, hV₀_sub_V, hφ_pos_V₀⟩ :
        ∃ V₀ : Set M, IsOpen V₀ ∧ x ∈ V₀ ∧ V₀ ⊆ V ∧ ∀ y ∈ V₀, φ x / 2 < φ y :=
      exists_open_nbhd_positive (M := M) hVopen hφ_smooth.continuous.continuousOn
        hxV hφx_pos
    have hV₀_sub_α : V₀ ⊆ (chartAt H α).source := hV₀_sub_V.trans hV_sub_α
    have hV₀_int : x ∈ V₀ := hxV₀
    have hμ_V₀_pos : 0 < chartLocalMeasure (I := I) g α V₀ :=
      chartLocalMeasure_open_pos_of_interior_mem (I := I) g α hV₀_open hxV₀ hV₀_sub_α
        hx_int
    have hLC : LocallyCompactSpace M := by
      have _hE : ProperSpace E := FiniteDimensional.proper ℝ E
      have _hH : LocallyCompactSpace H := I.locallyCompactSpace
      exact ChartedSpace.locallyCompactSpace H M
    obtain ⟨K, hK_compact, hxK_int, hK_sub_V₀⟩ :=
      exists_compact_subset hV₀_open hxV₀
    set V₁ : Set M := interior K with hV₁_def
    have hV₁_open : IsOpen V₁ := isOpen_interior
    have hxV₁ : x ∈ V₁ := hxK_int
    have hV₁_sub_V₀ : V₁ ⊆ V₀ := interior_subset.trans hK_sub_V₀
    have hV₁_sub_K : V₁ ⊆ K := interior_subset
    have hV₁_sub_α : V₁ ⊆ (chartAt H α).source := hV₁_sub_V₀.trans hV₀_sub_α
    have hμ_V₁_pos : 0 < chartLocalMeasure (I := I) g α V₁ :=
      chartLocalMeasure_open_pos_of_interior_mem (I := I) g α hV₁_open hxV₁ hV₁_sub_α
        hx_int
    have hμ_V₁_lt_top : chartLocalMeasure (I := I) g α V₁ < ⊤ := by
      apply lt_of_le_of_lt (measure_mono hV₁_sub_K)
      have hK_chart_α : K ⊆ (chartAt H α).source := hK_sub_V₀.trans hV₀_sub_α
      exact chartLocalMeasure_compact_lt_top (I := I) g α hK_compact hK_chart_α
    have hΔ_int : Integrable (fun y => Δ y * φ y) (chartLocalMeasure (I := I) g α) := by
      have hexpand : (fun y => Δ y * φ y) =
          fun y => localDivergenceWithin (I := I) g α X y * φ y -
            localDivergenceWithin (I := I) g β X y * φ y := by
        funext y; simp [Δ, sub_mul]
      rw [hexpand]
      exact Integrable.sub h1_int h2_int
    set c : ℝ := Δ x / 2 * (φ x / 2) with hc_def
    have hc_pos : 0 < c := by
      have h1 : 0 < Δ x / 2 := by linarith
      exact mul_pos h1 hφx_half_pos
    have hbound_V₁ : ∀ y ∈ V₁, c ≤ Δ y * φ y := by
      intro y hy
      have hy_V₀ : y ∈ V₀ := hV₁_sub_V₀ hy
      have hy_V : y ∈ V := hV₀_sub_V hy_V₀
      have hΔy : Δ x / 2 < Δ y := hΔ_pos y hy_V
      have hφy : φ x / 2 < φ y := hφ_pos_V₀ y hy_V₀
      have hΔy_pos : 0 < Δ y := by linarith
      have hφy_pos : 0 < φ y := by linarith
      calc c = Δ x / 2 * (φ x / 2) := rfl
        _ ≤ Δ y * (φ x / 2) := by
            apply mul_le_mul_of_nonneg_right hΔy.le; linarith
        _ ≤ Δ y * φ y := by
            apply mul_le_mul_of_nonneg_left hφy.le; linarith
    have hΔphi_nonneg : ∀ y, 0 ≤ Δ y * φ y := by
      intro y
      by_cases hy : y ∈ V
      · have hΔy : Δ x / 2 < Δ y := hΔ_pos y hy
        have hΔy_pos : 0 < Δ y := by linarith
        exact mul_nonneg hΔy_pos.le (hφ_nonneg y)
      · have hy_supp : y ∉ tsupport φ := fun h => hy (hφ_supp h)
        have hφy : φ y = 0 := by
          by_contra hne; exact hy_supp (subset_tsupport _ hne)
        rw [hφy, mul_zero]
    have hV₁_meas : MeasurableSet V₁ := hV₁_open.measurableSet
    have hint_const : ∫ _ in V₁, c ∂(chartLocalMeasure (I := I) g α) =
        (chartLocalMeasure (I := I) g α V₁).toReal * c := by
      rw [setIntegral_const]
      change (chartLocalMeasure (I := I) g α).real V₁ * c = _
      rw [Measure.real]
    have hΔphi_int_on_V₁ : IntegrableOn (fun y => Δ y * φ y) V₁
        (chartLocalMeasure (I := I) g α) := hΔ_int.integrableOn
    have hc_int_on_V₁ : IntegrableOn (fun _ => c) V₁
        (chartLocalMeasure (I := I) g α) :=
      integrableOn_const (hs := hμ_V₁_lt_top.ne)
    have hLB_V₁ : ∫ _ in V₁, c ∂(chartLocalMeasure (I := I) g α) ≤
        ∫ y in V₁, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := by
      refine setIntegral_mono_on hc_int_on_V₁ hΔphi_int_on_V₁ hV₁_meas ?_
      intro y hy; exact hbound_V₁ y hy
    have hLB_total : ∫ y in V₁, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) ≤
        ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) :=
      MeasureTheory.setIntegral_le_integral hΔ_int
        (Filter.Eventually.of_forall hΔphi_nonneg)
    calc 0 < (chartLocalMeasure (I := I) g α V₁).toReal * c := by
            apply mul_pos
            · rw [ENNReal.toReal_pos_iff]
              exact ⟨hμ_V₁_pos, hμ_V₁_lt_top⟩
            · exact hc_pos
      _ = ∫ _ in V₁, c ∂(chartLocalMeasure (I := I) g α) := hint_const.symm
      _ ≤ ∫ y in V₁, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := hLB_V₁
      _ ≤ ∫ y, Δ y * φ y ∂(chartLocalMeasure (I := I) g α) := hLB_total
  linarith

omit [InnerProductSpace ℝ E] in
theorem localDivergenceWithin_chart_invariance [T2Space M]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M}
    (hx_α : x ∈ (chartAt H α).source)
    (hx_β : x ∈ (chartAt H β).source)
    (hx_int : x ∈ I.interior M) :
    localDivergenceWithin (I := I) g α X x = localDivergenceWithin (I := I) g β X x := by
  classical
  by_contra hne
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hΔneg | hΔpos
  · refine localDivergenceWithin_chart_invariance_pos
      (I := I) g β α X hx_β hx_α hx_int ?_
    linarith
  · exact localDivergenceWithin_chart_invariance_pos
      (I := I) g α β X hx_α hx_β hx_int hΔpos

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
