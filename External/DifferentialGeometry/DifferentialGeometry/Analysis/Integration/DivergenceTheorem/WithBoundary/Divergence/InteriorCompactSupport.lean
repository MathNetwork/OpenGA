import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.ChartLocalIbp
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.ChartInvariance
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Proper
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Compactness.LocallyCompact


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

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hev : (X : ∀ x, TangentSpace I x) =ᶠ[𝓝 x] (0 : ∀ x, TangentSpace I x)) :
    localDivergenceWithin (I := I) g α X x = 0 := by
  classical
  set y : E := extChartAt I α x with hy_def
  have hxs : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hy_target : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hxs
  have hsymm_y : (extChartAt I α).symm y = x := (extChartAt I α).left_inv hxs
  have hcont_symm_at : ContinuousAt (extChartAt I α).symm y :=
    continuousAt_extChartAt_symm'' (I := I) (x := α) hy_target
  have hev_pre : ∀ i : Fin (Module.finrank ℝ E),
      (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
        =ᶠ[𝓝[(extChartAt I α).target] y] (fun _ : E => (0 : ℝ)) := by
    intro i
    have hcwa : ContinuousWithinAt (extChartAt I α).symm (extChartAt I α).target y := by
      have h := (continuousOn_extChartAt_symm (I := I) α) y hy_target
      exact h
    have htendsto : Filter.Tendsto (extChartAt I α).symm
        (𝓝[(extChartAt I α).target] y) (𝓝 x) := by
      have h := hcwa.tendsto
      rw [hsymm_y] at h
      exact h
    have hpull : (fun z : E => (X : ∀ x, TangentSpace I x) ((extChartAt I α).symm z))
        =ᶠ[𝓝[(extChartAt I α).target] y]
        (fun z : E => (0 : ∀ x, TangentSpace I x) ((extChartAt I α).symm z)) :=
      htendsto.eventually hev
    have htarget_nhd : (extChartAt I α).target ∈ 𝓝[(extChartAt I α).target] y :=
      self_mem_nhdsWithin
    filter_upwards [hpull, htarget_nhd] with z hz htz
    have hXz : X ((extChartAt I α).symm z) = (0 : TangentSpace I _) := hz
    have hsymm_base : (extChartAt I α).symm z ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hsymm_src : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target htz
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymm_src
      exact hsymm_src
    have hcoeffZero : chartCoeffOnE (I := I) α X i z = 0 := by
      unfold chartCoeffOnE chartCoeff
      rw [hXz]
      have h0 : ((trivializationAt E (TangentSpace I) α)
          ⟨(extChartAt I α).symm z, (0 : TangentSpace I _)⟩).2 = 0 :=
        ((trivializationAt E (TangentSpace I) α).linear ℝ hsymm_base).map_zero
      rw [h0]
      simp
    rw [hcoeffZero, zero_mul]
  rw [localDivergenceWithin_def]
  have hsum_zero : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I α).target i
        (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y = 0 := by
    intro i
    unfold partialDerivWithin
    have hat_y : (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y
        = (fun _ : E => (0 : ℝ)) y :=
      Filter.EventuallyEq.eq_of_nhdsWithin (hev_pre i) hy_target
    have hfderiv_eq :
        fderivWithin ℝ
            (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
            (extChartAt I α).target y =
          fderivWithin ℝ (fun _ : E => (0 : ℝ)) (extChartAt I α).target y :=
      Filter.EventuallyEq.fderivWithin_eq (hev_pre i) hat_y
    rw [hfderiv_eq]
    rw [show (fun _ : E => (0 : ℝ)) = Function.const E 0 from rfl, fderivWithin_const]
    rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I α).target i
        (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
        (extChartAt I α x)) = 0 from by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [show (extChartAt I α x) = y from rfl]
    exact hsum_zero i]
  rw [zero_div]

omit [InnerProductSpace ℝ E] in
lemma divergence_g_with_boundary_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hev : (X : ∀ x, TangentSpace I x) =ᶠ[𝓝 x] (0 : ∀ x, TangentSpace I x)) :
    divergence_g_with_boundary (I := I) g X x = 0 := by
  rw [divergence_g_with_boundary_def]
  exact localDivergenceWithin_zero_of_eventuallyEq_zero (I := I) g x X
    (mem_chart_source H x) hev


omit [InnerProductSpace ℝ E] in
lemma support_divergence_g_with_boundary_subset_of_interior_support
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (_hX_int : tsupport X ⊆ I.interior M) :
    Function.support (divergence_g_with_boundary (I := I) g X) ⊆ tsupport X := by
  intro x hx
  by_contra hxnotin
  have h_open : IsOpen (tsupport X)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : (X : ∀ x, TangentSpace I x) =ᶠ[𝓝 x] (0 : ∀ x, TangentSpace I x) := by
    filter_upwards [h_open.mem_nhds hxnotin] with y hy
    change X y = (0 : TangentSpace I y)
    by_contra hne
    have hyS : y ∈ Function.support (X : ∀ x, TangentSpace I x) := hne
    exact hy (subset_tsupport _ hyS)
  exact hx (divergence_g_with_boundary_zero_of_eventuallyEq_zero (I := I) g X hev)

omit [InnerProductSpace ℝ E] in
lemma tsupport_divergence_g_with_boundary_subset_of_interior_support
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX_int : tsupport X ⊆ I.interior M) :
    tsupport (divergence_g_with_boundary (I := I) g X) ⊆ tsupport X :=
  closure_minimal
    (support_divergence_g_with_boundary_subset_of_interior_support
      (I := I) g X hX_int) (isClosed_tsupport _)

omit [InnerProductSpace ℝ E] in
lemma hasCompactSupport_divergence_g_with_boundary
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : HasCompactSupport X) (hX_int : tsupport X ⊆ I.interior M) :
    HasCompactSupport (divergence_g_with_boundary (I := I) g X) :=
  hX.mono'
    (support_divergence_g_with_boundary_subset_of_interior_support
      (I := I) g X hX_int)

omit [InnerProductSpace ℝ E] in
private lemma tangentSectionAction_continuous_of_interior_support
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Continuous (tangentSectionAction (I := I) X f) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_supp : x ∈ tsupport f
  · have hx_int : x ∈ I.interior M := hf_int hx_supp
    have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
    have hx_target_int : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_mem_interior_target_of_isInteriorPoint
        (I := I) (M := M) x hx_chart hx_int
    have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
        ((extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) :=
      tangentSectionAction_contMDiffOn (I := I) x X hf
    have hxsrc : x ∈ (extChartAt I x).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_chart
    have hxU : x ∈ (extChartAt I x).source ∩
        (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target :=
      ⟨hxsrc, hx_target_int⟩
    have hUopen : IsOpen ((extChartAt I x).source ∩
        (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) := by
      have hcontOn := continuousOn_extChartAt (I := I) x
      exact hcontOn.isOpen_inter_preimage (isOpen_extChartAt_source (I := I) x)
        isOpen_interior
    have hcont_at : ContinuousAt (tangentSectionAction (I := I) X f) x :=
      ((hsmooth x hxU).continuousWithinAt.continuousAt) (hUopen.mem_nhds hxU)
    exact hcont_at
  · have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
    have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_supp] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have hev_action : tangentSectionAction (I := I) X f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hev.eventually_nhds] with y hy
      have hmfderiv_zero : mfderiv I 𝓘(ℝ) f y = 0 := by
        rw [Filter.EventuallyEq.mfderiv_eq hy, mfderiv_const]
        rfl
      change mfderiv I 𝓘(ℝ) f y (X y) = 0
      rw [hmfderiv_zero]; rfl
    exact (continuous_const.continuousAt.congr hev_action.symm)

omit [InnerProductSpace ℝ E] in
private lemma exists_smooth_interior_cutoff
    [T2Space M] [SigmaCompactSpace M]
    {K : Set M} (hK_compact : IsCompact K) (hK_sub : K ⊆ I.interior M) :
    ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ I.interior M ∧
      (∀ᶠ y in 𝓝ˢ K, χ y = 1) ∧ (∀ y, χ y ∈ Icc (0 : ℝ) 1) := by
  classical
  haveI : LocallyCompactSpace M := locallyCompactSpace_of_chartedSpace E H I M
  haveI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  haveI : NormalSpace M := NormalSpace.of_regularSpace_lindelofSpace
  obtain ⟨L, hL_compact, hKL, hL_sub_int⟩ :=
    exists_compact_between hK_compact (isOpen_interior_M (I := I) (M := M)) hK_sub
  obtain ⟨f, hf_one, hf_zero, hf_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      hK_compact.isClosed hKL
  refine ⟨f, f.contMDiff.of_le (mod_cast le_top), ?_, ?_, hf_one, hf_range⟩
  · refine HasCompactSupport.of_support_subset_isCompact hL_compact ?_
    intro y hy
    by_contra hyL
    exact hy (hf_zero y hyL)
  · refine subset_trans ?_ hL_sub_int
    refine closure_minimal ?_ hL_compact.isClosed
    intro y hy
    by_contra hyL
    exact hy (hf_zero y hyL)

omit [InnerProductSpace ℝ E] in
private lemma integrable_cLM_of_cs_chartSource
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (chartLocalMeasure (I := I) g α) := by
  classical
  have hsupp_compact : IsCompact (tsupport f) := hf_cs
  have hμ_supp : chartLocalMeasure (I := I) g α (tsupport f) < ⊤ :=
    chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact hf_supp
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hCpt := hsupp_compact.image hf_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · exact (hCmem ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hf_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      simp [hf_zero]
  have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ‖f x‖ ≤
        ENNReal.ofReal C * (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, mul_one]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have hf_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      rw [hf_zero]; simp
  refine ⟨hf_cont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, ENNReal.ofReal C *
            (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
    _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α (tsupport f) := by
          rw [lintegral_const_mul _ ((measurable_const).indicator
            (isClosed_tsupport _).measurableSet)]
          rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
          rw [setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp

omit [InnerProductSpace ℝ E] in
private lemma withDensity_pou_restrict_zero_of_disjoint
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {α : M} {K : Set M} (hK_meas : MeasurableSet K)
    (hα_disj : tsupport ((chartAtlasPOU I M) α : M → ℝ) ∩ K = ∅) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x))).restrict K = 0 := by
  classical
  ext A hA
  rw [Measure.restrict_apply hA, Measure.coe_zero, Pi.zero_apply]
  rw [MeasureTheory.withDensity_apply _ (hA.inter hK_meas)]
  refine setLIntegral_eq_zero (hA.inter hK_meas) ?_
  intro x hx
  obtain ⟨_, hxK⟩ := hx
  have hx_notin : x ∉ tsupport ((chartAtlasPOU I M) α : M → ℝ) := by
    intro hx_in
    have : x ∈ tsupport ((chartAtlasPOU I M) α : M → ℝ) ∩ K := ⟨hx_in, hxK⟩
    rw [hα_disj] at this
    exact (Set.notMem_empty _) this
  have hρα_zero : ((chartAtlasPOU I M) α : M → ℝ) x = 0 := by
    by_contra hne
    exact hx_notin (subset_tsupport _ hne)
  change ENNReal.ofReal (((chartAtlasPOU I M) α : M → ℝ) x) = 0
  rw [hρα_zero]
  simp

omit [InnerProductSpace ℝ E] in
private lemma riemannianVolumeMeasure_restrict_finset_sum
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {K : Set M} (hK_compact : IsCompact K) :
    (riemannianVolumeMeasure (I := I) (M := M) g).restrict K =
      (∑ α ∈ (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset,
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x))).restrict K := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset
    with hS_def
  have hSmem : ∀ {α : M}, α ∈ S ↔
      (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty := fun {α} =>
    Set.Finite.mem_toFinset _
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set f : M → MeasureTheory.Measure M := fun α =>
    ((chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))).restrict K with hf_def
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def]
  rw [MeasureTheory.Measure.restrict_sum _ hK_meas]
  change MeasureTheory.Measure.sum f =
    (∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))).restrict K
  rw [show MeasureTheory.Measure.sum f
      = MeasureTheory.Measure.sum (fun i : (S : Set M) => f i)
        + MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) from
    (MeasureTheory.Measure.sum_add_sum_compl (S : Set M) f).symm]
  have hcompl_zero : MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) = 0 := by
    have hzero : ∀ i : ↥((S : Set M)ᶜ), f i = 0 := by
      intro i
      have hi : (i : M) ∉ S := i.2
      have hi_iff := hSmem (α := (i : M))
      rw [hi_iff] at hi
      rw [Set.not_nonempty_iff_eq_empty] at hi
      exact withDensity_pou_restrict_zero_of_disjoint (I := I) (M := M) g hK_meas hi
    ext B hB
    rw [MeasureTheory.Measure.sum_apply _ hB]
    simp [hzero]
  rw [hcompl_zero, add_zero]
  have hSF : MeasureTheory.Measure.sum (fun i : (S : Set M) => f i) = ∑ α ∈ S, f α :=
    MeasureTheory.Measure.sum_coe_finset S f
  rw [hSF]
  refine Finset.induction
    (motive := fun (T : Finset M) =>
      ∑ α ∈ T, f α = (∑ α ∈ T, (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))).restrict K)
    ?_ ?_ S
  · simp only [Finset.sum_empty, hf_def]
    exact (Measure.restrict_zero (s := K)).symm
  · intro α t hα ih
    simp only [Finset.sum_insert hα]
    rw [show f α = ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))).restrict K from rfl]
    rw [ih, ← Measure.restrict_add]

omit [InnerProductSpace ℝ E] in
private lemma integral_riemannianVolume_compactSupport_finset_sum
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {h : M → ℝ} (hh_cont : Continuous h) (hh_cs : HasCompactSupport h) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ (pouFinset_for_compactSet (I := I) (M := M) hh_cs).toFinset,
          ∫ x, h x * ((chartAtlasPOU I M) α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M
  set K : Set M := tsupport h with hK_def
  have hK_compact : IsCompact K := hh_cs
  have hK_closed : IsClosed K := isClosed_tsupport _
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset
  haveI : IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hLHS : ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∫ x in K, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := riemannianVolumeMeasure
        (I := I) (M := M) g) (s := K) (f := h) ?_).symm
    intro x hx
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [hLHS]
  rw [show (∫ x in K, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, h x ∂((riemannianVolumeMeasure (I := I) (M := M) g).restrict K) from rfl]
  rw [riemannianVolumeMeasure_restrict_finset_sum (I := I) (M := M) g hK_compact]
  rw [show ∫ x, h x ∂((∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
            (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))).restrict K)
      = ∫ x in K, h x ∂(∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
            (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))) from rfl]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ∑ α ∈ S,
        (chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)))
        (s := K) (f := h) (fun x hx => ?_)]
  swap
  · by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [show ∫ x, h x ∂(∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)))
      = ∑ α ∈ S, ∫ x, h x ∂((chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))) from ?_]
  swap
  · have hh_int : ∀ α ∈ S, Integrable h
        ((chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))) := by
      intro α _
      have hh_int_global : Integrable h (riemannianVolumeMeasure (I := I) (M := M) g) :=
        hh_cont.integrable_of_hasCompactSupport hh_cs
      exact hh_int_global.mono_measure
        (chartLocalMeasure_withDensity_le_riemannianMeasure (I := I) (M := M) g ρ α)
    exact integral_finset_sum_measure hh_int
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have hρ_aem : AEMeasurable (fun x : M => ENNReal.ofReal ((ρ α : M → ℝ) x))
      (chartLocalMeasure (I := I) g α) :=
    (ENNReal.measurable_ofReal.comp ((ρ α).contMDiff.continuous).measurable).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ((ρ α : M → ℝ) x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => by simp)
  rw [integral_withDensity_eq_integral_toReal_smul₀
        (μ := chartLocalMeasure (I := I) g α)
        (f := fun x : M => ENNReal.ofReal ((ρ α : M → ℝ) x)) hρ_aem hρ_lt_top
        (g := h)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change (ENNReal.ofReal ((ρ α : M → ℝ) x)).toReal • h x = h x * ((ρ α : M → ℝ) x)
  rw [ENNReal.toReal_ofReal (ρ.nonneg α x), smul_eq_mul, mul_comm]

omit [InnerProductSpace ℝ E] in
private lemma integral_riemannianVolume_eq_chartLocal_of_support_in_chart
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α₀ : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α₀).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x ∂(chartLocalMeasure (I := I) g α₀) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have h_step1 : ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α) := by
    have hKey :=
      chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
        (I := I) (M := M) (g_fam := fun _ : ℝ => g) (t := 0)
        (h := f) hf_cont
    simp only [riemannianMeasureFamily_def] at hKey
    exact hKey.symm
  rw [h_step1]
  have h_step2 : ∀ α ∈ S,
      ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀) := by
    intro α _
    refine chartLocalMeasure_integral_eq_of_support_in_overlap (I := I) g α α₀
      (fun x => f x * ρ α x) ?_
    intro x hx
    simp only
    by_cases hxα : x ∈ (chartAt H α).source
    · have hxα₀ : x ∉ (chartAt H α₀).source := fun hxα₀' => hx ⟨hxα, hxα₀'⟩
      have hxnotin : x ∉ tsupport f := fun h => hxα₀ (hf_supp h)
      have hfx_zero : f x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hfx_zero, zero_mul]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hρα_zero, mul_zero]
  rw [Finset.sum_congr rfl h_step2]
  have h_each_int : ∀ α ∈ S, Integrable (fun x : M => f x * ρ α x)
      (chartLocalMeasure (I := I) g α₀) := by
    intro α _
    have hcont : Continuous (fun x : M => f x * ρ α x) :=
      hf_cont.mul (ρ α).contMDiff.continuous
    have hsupp_sub : tsupport (fun x : M => f x * ρ α x) ⊆ tsupport f := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hfx : f x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by rw [hfx, zero_mul])
    have hcs_each : HasCompactSupport (fun x : M => f x * ρ α x) :=
      HasCompactSupport.of_compactSpace _
    exact integrable_cLM_of_cs_chartSource (I := I) g α₀
      hcont hcs_each (hsupp_sub.trans hf_supp)
  rw [show (∑ α ∈ S, ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀))
      = ∫ x, ∑ α ∈ S, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀) from
        (integral_finset_sum (μ := chartLocalMeasure (I := I) g α₀) S h_each_int).symm]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [← Finset.mul_sum]
  have hsum_one : ∑ α ∈ S, ρ α x = 1 := by
    have hfins : ρ.finsupport x ⊆ S := by
      intro α hα
      rw [chartAtlasPOU_finset_mem]
      rw [ρ.mem_finsupport, Function.mem_support] at hα
      exact ⟨x, hα⟩
    exact ρ.sum_finsupport' x (mem_univ x) hfins
  rw [hsum_one, mul_one]

omit [InnerProductSpace ℝ E] in
private lemma integral_riemannianVolume_eq_chartLocal_of_compactSupport_in_chart
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α₀ : M)
    {h : M → ℝ} (hh_cont : Continuous h) (hh_cs : HasCompactSupport h)
    (hh_supp : tsupport h ⊆ (chartAt H α₀).source) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x ∂(chartLocalMeasure (I := I) g α₀) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M
  set K : Set M := tsupport h
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) (hh_cs : IsCompact K)).toFinset
  have hSmem : ∀ {α : M}, α ∈ S ↔ (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty :=
    fun {α} => Set.Finite.mem_toFinset _
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  rw [integral_riemannianVolume_compactSupport_finset_sum (I := I) (M := M) g hh_cont hh_cs]
  have h_step_b : ∀ α ∈ S,
      ∫ x, h x * ((ρ α : M → ℝ)) x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, h x * ((ρ α : M → ℝ)) x ∂(chartLocalMeasure (I := I) g α₀) := by
    intro α _
    refine chartLocalMeasure_integral_eq_of_support_in_overlap (I := I) g α α₀
      (fun x => h x * (ρ α : M → ℝ) x) ?_
    intro x hx
    change h x * (ρ α : M → ℝ) x = 0
    by_cases hxα : x ∈ (chartAt H α).source
    · have hxα₀ : x ∉ (chartAt H α₀).source := fun h' => hx ⟨hxα, h'⟩
      have hxK : x ∉ K := fun h' => hxα₀ (hh_supp h')
      have hh_zero : h x = 0 := by
        by_contra hne
        exact hxK (subset_tsupport _ hne)
      rw [hh_zero, zero_mul]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h' => hxα (hρsub α h')
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hρα_zero, mul_zero]
  rw [Finset.sum_congr rfl h_step_b]
  have hint_each : ∀ α ∈ S, Integrable (fun x : M => h x * (ρ α : M → ℝ) x)
      (chartLocalMeasure (I := I) g α₀) := by
    intro α _
    have hcont : Continuous (fun x : M => h x * (ρ α : M → ℝ) x) :=
      hh_cont.mul (ρ α).contMDiff.continuous
    have hsupp_sub : tsupport (fun x : M => h x * (ρ α : M → ℝ) x) ⊆ tsupport h := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hh_zero : h x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by rw [hh_zero, zero_mul])
    have hcs_each : HasCompactSupport (fun x : M => h x * (ρ α : M → ℝ) x) :=
      hh_cs.mono' (subset_trans (subset_tsupport _) hsupp_sub)
    refine integrable_cLM_of_cs_chartSource (I := I) g α₀
      hcont hcs_each (hsupp_sub.trans hh_supp)
  rw [show (∑ α ∈ S, ∫ x, h x * (ρ α : M → ℝ) x ∂(chartLocalMeasure (I := I) g α₀))
      = ∫ x, ∑ α ∈ S, h x * (ρ α : M → ℝ) x ∂(chartLocalMeasure (I := I) g α₀) from
        (integral_finset_sum (μ := chartLocalMeasure (I := I) g α₀) S hint_each).symm]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change (∑ α ∈ S, h x * (ρ α : M → ℝ) x) = h x
  rw [← Finset.mul_sum]
  by_cases hxK : x ∈ K
  · have hsum_one : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 := by
      have hfins_S : ρ.finsupport x ⊆ S := by
        intro α hα
        rw [hSmem]
        rw [ρ.mem_finsupport] at hα
        exact ⟨x, subset_tsupport _ hα, hxK⟩
      exact ρ.sum_finsupport' x (Set.mem_univ x) hfins_S
    rw [hsum_one, mul_one]
  · have hh_zero : h x = 0 := by
      by_contra hne
      exact hxK (subset_tsupport _ hne)
    rw [hh_zero, zero_mul]

omit [InnerProductSpace ℝ E] in
theorem integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX_int : tsupport X ⊆ I.interior M) :
    ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have hX_compact : IsCompact (tsupport X) :=
    .of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
  have hdiv_supp : tsupport (divergence_g_with_boundary (I := I) g X) ⊆ tsupport X :=
    tsupport_divergence_g_with_boundary_subset_of_interior_support
      (I := I) g X hX_int
  have hdiv_supp_int : tsupport (divergence_g_with_boundary (I := I) g X) ⊆ I.interior M :=
    hdiv_supp.trans hX_int
  have hdiv_cont : Continuous (divergence_g_with_boundary (I := I) g X) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
    · have hx_int : x ∈ I.interior M := hdiv_supp_int hx_supp
      have hcont_int :
          ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
        divergence_g_with_boundary_continuousOn_interior (I := I) g X
      exact (hcont_int x hx_int).continuousAt (isOpen_interior_M.mem_nhds hx_int)
    · have h_open : IsOpen (tsupport (divergence_g_with_boundary (I := I) g X))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev_zero : (divergence_g_with_boundary (I := I) g X) =ᶠ[𝓝 x]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        by_contra hne
        exact hy (subset_tsupport _ hne)
      exact (continuous_const.continuousAt.congr hev_zero.symm)
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_supp_int, hχ_one_nhds, hχ_range⟩ :=
    exists_smooth_interior_cutoff (I := I) (M := M) hX_compact hX_int
  have h_step_a : ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, divergence_g_with_boundary (I := I) g X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    have hKey :=
      chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
        (I := I) (M := M) (g_fam := fun _ : ℝ => g) (t := 0)
        (h := divergence_g_with_boundary (I := I) g X) hdiv_cont
    simp only [riemannianMeasureFamily_def] at hKey
    exact hKey.symm
  rw [h_step_a]
  have hχ_one_K : ∀ x ∈ tsupport X, χ x = 1 := by
    intro x hxK
    rcases (Filter.eventually_iff_exists_mem.mp hχ_one_nhds) with ⟨U, hU_nhds, hU_eq⟩
    have hU_int : tsupport X ⊆ interior U := by
      rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
    exact hU_eq x (interior_subset (hU_int hxK))
  have hχ_one_supp : ∀ x ∈ tsupport (divergence_g_with_boundary (I := I) g X), χ x = 1 :=
    fun x hx => hχ_one_K x (hdiv_supp hx)
  have hdiv_mul_chi_eq : ∀ x : M,
      divergence_g_with_boundary (I := I) g X x * χ x =
        divergence_g_with_boundary (I := I) g X x := by
    intro x
    by_cases hxsupp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
    · rw [hχ_one_supp x hxsupp, mul_one]
    · have hdiv_zero : divergence_g_with_boundary (I := I) g X x = 0 := by
        by_contra hne
        exact hxsupp (subset_tsupport _ hne)
      rw [hdiv_zero, zero_mul]
  have h_step_b : ∀ α ∈ S,
      ∫ x, divergence_g_with_boundary (I := I) g X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, divergence_g_with_boundary (I := I) g X x *
            (χ x * ρ α x) ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hχx : divergence_g_with_boundary (I := I) g X x * χ x =
        divergence_g_with_boundary (I := I) g X x := hdiv_mul_chi_eq x
    calc divergence_g_with_boundary (I := I) g X x * ρ α x
        = (divergence_g_with_boundary (I := I) g X x * χ x) * ρ α x := by rw [hχx]
      _ = divergence_g_with_boundary (I := I) g X x * (χ x * ρ α x) := by ring
  rw [Finset.sum_congr rfl h_step_b]
  have h_step_c : ∀ α ∈ S,
      ∫ x, divergence_g_with_boundary (I := I) g X x * (χ x * ρ α x)
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergenceWithin (I := I) g α X x *
            (χ x * ρ α x) ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hxα : x ∈ (chartAt H α).source
    · by_cases hx_int : x ∈ I.interior M
      · simp only [voss_weyl_divergence_with_boundary_formula
            (I := I) g α X hxα hx_int]
      · have hxnotin : x ∉ tsupport χ := fun h => hx_int (hχ_supp_int h)
        have hχ_zero : χ x = 0 := by
          by_contra hne
          exact hxnotin (subset_tsupport _ hne)
        change divergence_g_with_boundary (I := I) g X x * (χ x * ρ α x) =
          localDivergenceWithin (I := I) g α X x * (χ x * ρ α x)
        rw [hχ_zero, zero_mul, mul_zero, mul_zero]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      change divergence_g_with_boundary (I := I) g X x * (χ x * ρ α x) =
        localDivergenceWithin (I := I) g α X x * (χ x * ρ α x)
      rw [hρα_zero, mul_zero, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl h_step_c]
  set φ : M → M → ℝ := fun α x => χ x * (ρ α : M → ℝ) x with hφ_def
  have hφ_smooth : ∀ α : M, ContMDiff I 𝓘(ℝ) ∞ (φ α) := fun α =>
    hχ_smooth.mul (ρ α).contMDiff
  have hφ_cs : ∀ α : M, HasCompactSupport (φ α) := fun α => hχ_cs.mul_right
  have hφ_supp_chart : ∀ α : M, tsupport (φ α) ⊆ (chartAt H α).source := fun α => by
    have h1 : tsupport (φ α) ⊆ tsupport (ρ α : M → ℝ) := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hρ_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by change χ x * (ρ α : M → ℝ) x = 0; rw [hρ_zero, mul_zero])
    exact h1.trans (hρsub α)
  have hφ_supp_int : ∀ α : M, tsupport (φ α) ⊆ I.interior M := fun α => by
    have h1 : tsupport (φ α) ⊆ tsupport χ := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hχ_zero : χ x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by change χ x * (ρ α : M → ℝ) x = 0; rw [hχ_zero, zero_mul])
    exact h1.trans hχ_supp_int
  have h_step_d : ∀ α ∈ S,
      ∫ x, localDivergenceWithin (I := I) g α X x * (φ α x)
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp_within (I := I) g α X (hφ_smooth α) (hφ_cs α)
      (hφ_supp_chart α) (hφ_supp_int α)
  rw [Finset.sum_congr rfl h_step_d]
  rw [show (∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α))
      = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α)) from by
    rw [← Finset.sum_neg_distrib]]
  have hAct_cont : ∀ α : M,
      Continuous (tangentSectionAction (I := I) X (φ α)) := fun α =>
    tangentSectionAction_continuous_of_interior_support (I := I) X (hφ_smooth α)
      (hφ_supp_int α)
  have hAct_supp : ∀ α : M,
      tsupport (tangentSectionAction (I := I) X (φ α)) ⊆ (chartAt H α).source := by
    intro α
    refine subset_trans ?_ (hφ_supp_chart α)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hne
    have h_open : IsOpen (tsupport (φ α))ᶜ := (isClosed_tsupport _).isOpen_compl
    have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hne] with y hy
      by_contra hne'
      exact hy (subset_tsupport _ hne')
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
      rfl
    have hAct_zero : tangentSectionAction (I := I) X (φ α) x = 0 := by
      change mfderiv I 𝓘(ℝ) (φ α) x (X x) = 0
      rw [hmfderiv_zero]; rfl
    exact hx hAct_zero
  have h_step_e : ∀ α ∈ S,
      ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    exact (integral_riemannianVolume_eq_chartLocal_of_support_in_chart
      (I := I) g α (hAct_cont α) (hAct_supp α)).symm
  rw [Finset.sum_congr rfl h_step_e]
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_each_int : ∀ α ∈ S, Integrable
      (fun x : M => tangentSectionAction (I := I) X (φ α) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖tangentSectionAction (I := I) X (φ α) x‖ ≤ C := by
      have hCpt := (isCompact_univ (X := M)).image (hAct_cont α).norm
      obtain ⟨C, hCmem⟩ := hCpt.bddAbove
      exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
    exact (integrable_const C).mono' (hAct_cont α).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  rw [show (∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
        (integral_finset_sum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S h_each_int).symm]
  have h_pt : ∀ x : M,
      ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x = 0 := by
    intro x
    by_cases hXx : X x = (0 : TangentSpace I x)
    · refine Finset.sum_eq_zero (fun α _ => ?_)
      exact tangentSectionAction_zero_of_X_zero (I := I) X (φ α) hXx
    · have hxsupp : x ∈ Function.support (X : ∀ x, TangentSpace I x) := hXx
      have hxK : x ∈ tsupport X := subset_tsupport _ hxsupp
      rcases (Filter.eventually_iff_exists_mem.mp hχ_one_nhds) with ⟨U, hU_nhds, hU_eq⟩
      have hU_int : tsupport X ⊆ interior U := by
        rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
      have hxU : x ∈ interior U := hU_int hxK
      have hU_x_nhd : U ∈ 𝓝 x :=
        mem_nhds_iff.mpr ⟨interior U, interior_subset, isOpen_interior, hxU⟩
      have hev_φα : ∀ α : M, (φ α) =ᶠ[𝓝 x] (fun y => (ρ α : M → ℝ) y) := by
        intro α
        filter_upwards [hU_x_nhd] with y hyU
        change χ y * (ρ α : M → ℝ) y = (ρ α : M → ℝ) y
        rw [hU_eq y hyU, one_mul]
      have hmfderiv_φα : ∀ α : M,
          mfderiv I 𝓘(ℝ) (φ α) x = mfderiv I 𝓘(ℝ) ((ρ α : M → ℝ)) x := by
        intro α
        exact Filter.EventuallyEq.mfderiv_eq (hev_φα α)
      have hact_eq : ∀ α : M,
          tangentSectionAction (I := I) X (φ α) x =
            tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x := by
        intro α
        unfold tangentSectionAction
        rw [hmfderiv_φα α]
        rfl
      rw [show (∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
          = ∑ α ∈ S, tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x from
            Finset.sum_congr rfl (fun α _ => hact_eq α)]
      have hMDiff_each : ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
        fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
      have hcomm := tangentSectionAction_finset_sum (I := I) X S
        (fun α => ((ρ α : M → ℝ))) x hMDiff_each
      rw [← hcomm]
      have h_finset_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
          (fun _ : M => (1 : ℝ)) := by
        filter_upwards [ρ.eventually_finsupport_subset x] with y hy
        have hyfins_sub_S : ρ.finsupport y ⊆ S := by
          intro α hα
          rw [chartAtlasPOU_finset_mem]
          rw [ρ.mem_finsupport, Function.mem_support] at hα
          exact ⟨y, hα⟩
        exact ρ.sum_finsupport' y (mem_univ y) hyfins_sub_S
      unfold tangentSectionAction
      have h_fun_eq : (∑ α ∈ S, (ρ α : M → ℝ)) = fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
        funext y
        rw [Finset.sum_apply]
      rw [h_fun_eq]
      rw [Filter.EventuallyEq.mfderiv_eq h_finset_eq_one, mfderiv_const]
      rfl
  rw [show (fun x : M => ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
      = (fun _ : M => (0 : ℝ)) from funext h_pt]
  rw [integral_zero, neg_zero]

omit [InnerProductSpace ℝ E] in
theorem integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) :
    ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M
  set K : Set M := tsupport X
  have hK_compact : IsCompact K := hX
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset
    with hS_def
  have hSmem : ∀ {α : M}, α ∈ S ↔ (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty :=
    fun {α} => Set.Finite.mem_toFinset _
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have hdiv_supp : tsupport (divergence_g_with_boundary (I := I) g X) ⊆ K :=
    tsupport_divergence_g_with_boundary_subset_of_interior_support
      (I := I) g X hX_int
  have hdiv_supp_int : tsupport (divergence_g_with_boundary (I := I) g X) ⊆ I.interior M :=
    hdiv_supp.trans hX_int
  have hdiv_cs : HasCompactSupport (divergence_g_with_boundary (I := I) g X) :=
    hasCompactSupport_divergence_g_with_boundary (I := I) g hX hX_int
  have hdiv_cont : Continuous (divergence_g_with_boundary (I := I) g X) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
    · have hx_int : x ∈ I.interior M := hdiv_supp_int hx_supp
      have hcont_int :
          ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
        divergence_g_with_boundary_continuousOn_interior (I := I) g X
      exact (hcont_int x hx_int).continuousAt (isOpen_interior_M.mem_nhds hx_int)
    · have h_open : IsOpen (tsupport (divergence_g_with_boundary (I := I) g X))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev_zero : (divergence_g_with_boundary (I := I) g X) =ᶠ[𝓝 x]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        by_contra hne
        exact hy (subset_tsupport _ hne)
      exact (continuous_const.continuousAt.congr hev_zero.symm)
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_supp_int, hχ_one_nhds, hχ_range⟩ :=
    exists_smooth_interior_cutoff (I := I) (M := M) hK_compact hX_int
  have h_step_a : ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x
          ∂(chartLocalMeasure (I := I) g α) := by
    have hSdiv : (pouFinset_for_compactSet (I := I) (M := M) hdiv_cs).toFinset ⊆ S := by
      intro α hα
      rw [Set.Finite.mem_toFinset _] at hα
      rw [hSmem]
      rcases hα with ⟨x, hxρα, hx⟩
      exact ⟨x, hxρα, hdiv_supp hx⟩
    rw [integral_riemannianVolume_compactSupport_finset_sum (I := I) (M := M) g
        hdiv_cont hdiv_cs]
    apply Finset.sum_subset hSdiv
    intro α _ hα_notin
    rw [Set.Finite.mem_toFinset _] at hα_notin
    simp only [Set.mem_setOf_eq] at hα_notin
    rw [Set.not_nonempty_iff_eq_empty] at hα_notin
    have h_zero : ∀ x : M,
        divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x = 0 := by
      intro x
      by_cases hxρ : x ∈ tsupport ((chartAtlasPOU I M) α : M → ℝ)
      · have hxnotin : x ∉ tsupport (divergence_g_with_boundary (I := I) g X) := by
          intro h
          have : x ∈ tsupport ((chartAtlasPOU I M) α : M → ℝ) ∩
              tsupport (divergence_g_with_boundary (I := I) g X) := ⟨hxρ, h⟩
          rw [hα_notin] at this
          exact (Set.notMem_empty _) this
        have hdiv_zero : divergence_g_with_boundary (I := I) g X x = 0 := by
          by_contra hne
          exact hxnotin (subset_tsupport _ hne)
        rw [hdiv_zero, zero_mul]
      · have hρα_zero : (ρ α : M → ℝ) x = 0 := by
          by_contra hne
          exact hxρ (subset_tsupport _ hne)
        rw [hρα_zero, mul_zero]
    rw [show (fun x : M => divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x) =
        (fun _ : M => (0 : ℝ)) from funext h_zero]
    exact integral_zero ..
  rw [h_step_a]
  have hχ_one_K : ∀ x ∈ K, χ x = 1 := by
    intro x hxK
    rcases (Filter.eventually_iff_exists_mem.mp hχ_one_nhds) with ⟨U, hU_nhds, hU_eq⟩
    have hU_int : K ⊆ interior U := by
      rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
    exact hU_eq x (interior_subset (hU_int hxK))
  have hχ_one_supp : ∀ x ∈ tsupport (divergence_g_with_boundary (I := I) g X), χ x = 1 :=
    fun x hx => hχ_one_K x (hdiv_supp hx)
  have hdiv_mul_chi_eq : ∀ x : M,
      divergence_g_with_boundary (I := I) g X x * χ x =
        divergence_g_with_boundary (I := I) g X x := by
    intro x
    by_cases hxsupp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
    · rw [hχ_one_supp x hxsupp, mul_one]
    · have hdiv_zero : divergence_g_with_boundary (I := I) g X x = 0 := by
        by_contra hne
        exact hxsupp (subset_tsupport _ hne)
      rw [hdiv_zero, zero_mul]
  have h_step_b : ∀ α ∈ S,
      ∫ x, divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, divergence_g_with_boundary (I := I) g X x *
            (χ x * (ρ α : M → ℝ) x) ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hχx : divergence_g_with_boundary (I := I) g X x * χ x =
        divergence_g_with_boundary (I := I) g X x := hdiv_mul_chi_eq x
    calc divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x
        = (divergence_g_with_boundary (I := I) g X x * χ x) * (ρ α : M → ℝ) x := by rw [hχx]
      _ = divergence_g_with_boundary (I := I) g X x * (χ x * (ρ α : M → ℝ) x) := by ring
  rw [Finset.sum_congr rfl h_step_b]
  have h_step_c : ∀ α ∈ S,
      ∫ x, divergence_g_with_boundary (I := I) g X x * (χ x * (ρ α : M → ℝ) x)
        ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergenceWithin (I := I) g α X x *
            (χ x * (ρ α : M → ℝ) x) ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hxα : x ∈ (chartAt H α).source
    · by_cases hx_int : x ∈ I.interior M
      · simp only [voss_weyl_divergence_with_boundary_formula
            (I := I) g α X hxα hx_int]
      · have hxnotin : x ∉ tsupport χ := fun h => hx_int (hχ_supp_int h)
        have hχ_zero : χ x = 0 := by
          by_contra hne
          exact hxnotin (subset_tsupport _ hne)
        change divergence_g_with_boundary (I := I) g X x * (χ x * (ρ α : M → ℝ) x) =
          localDivergenceWithin (I := I) g α X x * (χ x * (ρ α : M → ℝ) x)
        rw [hχ_zero, zero_mul, mul_zero, mul_zero]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      change divergence_g_with_boundary (I := I) g X x * (χ x * (ρ α : M → ℝ) x) =
        localDivergenceWithin (I := I) g α X x * (χ x * (ρ α : M → ℝ) x)
      rw [hρα_zero, mul_zero, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl h_step_c]
  set φ : M → M → ℝ := fun α x => χ x * (ρ α : M → ℝ) x with hφ_def
  have hφ_smooth : ∀ α : M, ContMDiff I 𝓘(ℝ) ∞ (φ α) := fun α =>
    hχ_smooth.mul (ρ α).contMDiff
  have hφ_cs : ∀ α : M, HasCompactSupport (φ α) := fun α => hχ_cs.mul_right
  have hφ_supp_chart : ∀ α : M, tsupport (φ α) ⊆ (chartAt H α).source := fun α => by
    have h1 : tsupport (φ α) ⊆ tsupport (ρ α : M → ℝ) := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hρ_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by change χ x * (ρ α : M → ℝ) x = 0; rw [hρ_zero, mul_zero])
    exact h1.trans (hρsub α)
  have hφ_supp_int : ∀ α : M, tsupport (φ α) ⊆ I.interior M := fun α => by
    have h1 : tsupport (φ α) ⊆ tsupport χ := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hχ_zero : χ x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by change χ x * (ρ α : M → ℝ) x = 0; rw [hχ_zero, zero_mul])
    exact h1.trans hχ_supp_int
  have h_step_d : ∀ α ∈ S,
      ∫ x, localDivergenceWithin (I := I) g α X x * (φ α x)
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp_within (I := I) g α X (hφ_smooth α) (hφ_cs α)
      (hφ_supp_chart α) (hφ_supp_int α)
  rw [Finset.sum_congr rfl h_step_d]
  rw [show (∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α))
      = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α)) from by
    rw [← Finset.sum_neg_distrib]]
  have hAct_cont : ∀ α : M,
      Continuous (tangentSectionAction (I := I) X (φ α)) := fun α =>
    tangentSectionAction_continuous_of_interior_support (I := I) X (hφ_smooth α)
      (hφ_supp_int α)
  have hAct_supp : ∀ α : M,
      tsupport (tangentSectionAction (I := I) X (φ α)) ⊆ (chartAt H α).source := by
    intro α
    refine subset_trans ?_ (hφ_supp_chart α)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hne
    have h_open : IsOpen (tsupport (φ α))ᶜ := (isClosed_tsupport _).isOpen_compl
    have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hne] with y hy
      by_contra hne'
      exact hy (subset_tsupport _ hne')
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
      rfl
    have hAct_zero : tangentSectionAction (I := I) X (φ α) x = 0 := by
      change mfderiv I 𝓘(ℝ) (φ α) x (X x) = 0
      rw [hmfderiv_zero]; rfl
    exact hx hAct_zero
  have hAct_cs : ∀ α : M, HasCompactSupport (tangentSectionAction (I := I) X (φ α)) := by
    intro α
    have h1 : Function.support (tangentSectionAction (I := I) X (φ α)) ⊆ tsupport (φ α) := by
      intro x hx
      by_contra hne
      have h_open : IsOpen (tsupport (φ α))ᶜ := (isClosed_tsupport _).isOpen_compl
      have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hne] with y hy
        by_contra hne'
        exact hy (subset_tsupport _ hne')
      have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
        rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
        rfl
      have hAct_zero : tangentSectionAction (I := I) X (φ α) x = 0 := by
        change mfderiv I 𝓘(ℝ) (φ α) x (X x) = 0
        rw [hmfderiv_zero]; rfl
      exact hx hAct_zero
    exact (hφ_cs α).mono' h1
  have h_step_e : ∀ α ∈ S,
      ∫ x, tangentSectionAction (I := I) X (φ α) x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    exact (integral_riemannianVolume_eq_chartLocal_of_compactSupport_in_chart
      (I := I) g α (hAct_cont α) (hAct_cs α) (hAct_supp α)).symm
  rw [Finset.sum_congr rfl h_step_e]
  haveI : IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hAct_int : ∀ α ∈ S, Integrable
      (fun x : M => tangentSectionAction (I := I) X (φ α) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := fun α _ =>
    (hAct_cont α).integrable_of_hasCompactSupport (hAct_cs α)
  rw [show (∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
        (integral_finset_sum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S hAct_int).symm]
  have h_pt : ∀ x : M,
      ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x = 0 := by
    intro x
    by_cases hXx : X x = (0 : TangentSpace I x)
    · refine Finset.sum_eq_zero (fun α _ => ?_)
      exact tangentSectionAction_zero_of_X_zero (I := I) X (φ α) hXx
    · have hxsupp : x ∈ Function.support (X : ∀ x, TangentSpace I x) := hXx
      have hxK : x ∈ K := subset_tsupport _ hxsupp
      rcases (Filter.eventually_iff_exists_mem.mp hχ_one_nhds) with ⟨U, hU_nhds, hU_eq⟩
      have hU_int : K ⊆ interior U := by
        rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
      have hxU : x ∈ interior U := hU_int hxK
      have hU_x_nhd : U ∈ 𝓝 x :=
        mem_nhds_iff.mpr ⟨interior U, interior_subset, isOpen_interior, hxU⟩
      have hev_φα : ∀ α : M, (φ α) =ᶠ[𝓝 x] (fun y => (ρ α : M → ℝ) y) := by
        intro α
        filter_upwards [hU_x_nhd] with y hyU
        change χ y * (ρ α : M → ℝ) y = (ρ α : M → ℝ) y
        rw [hU_eq y hyU, one_mul]
      have hmfderiv_φα : ∀ α : M,
          mfderiv I 𝓘(ℝ) (φ α) x = mfderiv I 𝓘(ℝ) ((ρ α : M → ℝ)) x := by
        intro α
        exact Filter.EventuallyEq.mfderiv_eq (hev_φα α)
      have hact_eq : ∀ α : M,
          tangentSectionAction (I := I) X (φ α) x =
            tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x := by
        intro α
        unfold tangentSectionAction
        rw [hmfderiv_φα α]
        rfl
      rw [show (∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
          = ∑ α ∈ S, tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x from
            Finset.sum_congr rfl (fun α _ => hact_eq α)]
      have hMDiff_each : ∀ α ∈ S,
          MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
        fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
      have hcomm := tangentSectionAction_finset_sum (I := I) X S
        (fun α => ((ρ α : M → ℝ))) x hMDiff_each
      rw [← hcomm]
      have h_finset_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
          (fun _ : M => (1 : ℝ)) := by
        filter_upwards [ρ.eventually_finsupport_subset x] with y hy
        have hfins_S : ρ.finsupport y ⊆ S := by
          intro α hα
          rw [hSmem]
          rw [ρ.mem_finsupport] at hα
          have hα_x : α ∈ ρ.fintsupport x := hy ((ρ.mem_finsupport y).mpr hα)
          have hx_tsupp : x ∈ tsupport (ρ α : M → ℝ) :=
            (ρ.mem_fintsupport_iff x α).mp hα_x
          exact ⟨x, hx_tsupp, hxK⟩
        exact ρ.sum_finsupport' y (Set.mem_univ y) hfins_S
      unfold tangentSectionAction
      have h_fun_eq : (∑ α ∈ S, (ρ α : M → ℝ)) = fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
        funext y
        rw [Finset.sum_apply]
      rw [h_fun_eq]
      rw [Filter.EventuallyEq.mfderiv_eq h_finset_eq_one, mfderiv_const]
      rfl
  rw [show (fun x : M => ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
      = (fun _ : M => (0 : ℝ)) from funext h_pt]
  rw [integral_zero, neg_zero]

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
