import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz























namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Metric
open scoped Manifold Topology ContDiff NNReal
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [ChartedSpace H M] in




private lemma lipschitzOnWith_of_tendsto_aux
    {β : Type*} [PseudoMetricSpace β] (g : ℝ → E → β) (g0 : E → β) (K : ℝ≥0)
    (S : Set E) (l : Filter ℝ) [l.NeBot]
    (hlip : ∀ᶠ t in l, LipschitzOnWith K (g t) S)
    (hconv : ∀ z ∈ S, Filter.Tendsto (fun t => g t z) l (nhds (g0 z))) :
    LipschitzOnWith K g0 S := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hdist_tendsto : Filter.Tendsto (fun t => dist (g t x) (g t y)) l
      (nhds (dist (g0 x) (g0 y))) :=
    (continuous_dist.tendsto (g0 x, g0 y)).comp ((hconv x hx).prodMk_nhds (hconv y hy))
  refine le_of_tendsto hdist_tendsto ?_
  filter_upwards [hlip] with t ht
  rw [lipschitzOnWith_iff_dist_le_mul] at ht
  exact ht x hx y hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] in





omit [FiniteDimensional ℝ E] in
private lemma differentiableAt_chartTrivRepr_of_contMDiff_section
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (t : ℝ)
    (hCM : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (TotalSpace.mk' E x (X t x) : TangentBundle I M)))
    (z : E) (hz_int : z ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ (fun y : E => chartTrivRepr (I := I) α (X t) y) z := by
  have hz : z ∈ (extChartAt I α).target := interior_subset hz_int
  have hpull : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α (X t) ∘ (extChartAt I α).symm)
      ((extChartAt I α) ''
        ((chartAt H α).source ∩ (trivializationAt E (TangentSpace I) α).baseSet) ∩
        (extChartAt I α).target) :=
    contDiffOn_chartE_pullback_of_contMDiff_section (I := I) α (X t) hCM
  set S := (extChartAt I α) ''
        ((chartAt H α).source ∩ (trivializationAt E (TangentSpace I) α).baseSet) ∩
        (extChartAt I α).target with hS
  have hsubset : interior ((extChartAt I α).target : Set E) ⊆ S := by
    intro w hw
    have hwt : w ∈ (extChartAt I α).target := interior_subset hw
    have hsrc : (extChartAt I α).symm w ∈ (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hwt
    exact ⟨⟨(extChartAt I α).symm w, ⟨hsrc, hsrc⟩, (extChartAt I α).right_inv hwt⟩, hwt⟩
  have hSnhds : S ∈ 𝓝 z :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hz_int) hsubset
  have hdw : DifferentiableWithinAt ℝ
      (chartE_section_repr (I := I) α (X t) ∘ (extChartAt I α).symm) S z :=
    (hpull z (hsubset hz_int)).differentiableWithinAt (by simp)
  exact hdw.differentiableAt hSnhds

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in




private lemma continuousOn_fderiv_chartTrivRepr
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hgrad : ContinuousOn (fun q : ℝ × M =>
        fderiv ℝ (fun z => chartTrivRepr (I := I) α (X q.1) z) (extChartAt I α q.2))
      (Set.univ : Set (ℝ × M))) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (fun z => chartTrivRepr (I := I) α (X p.1) z) p.2)
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I α).target) := by
  have hg : ContinuousOn (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I α).target) := by
    apply ContinuousOn.prodMk
    · exact continuousOn_fst
    · exact (continuousOn_extChartAt_symm α).comp continuousOn_snd (by intro p hp; exact hp.2)
  have hmaps : MapsTo (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
      ((Set.univ : Set ℝ) ×ˢ (extChartAt I α).target) (Set.univ : Set (ℝ × M)) := by
    intro p hp; exact Set.mem_univ _
  refine (hgrad.comp hg hmaps).congr ?_
  intro p hp
  simp only [Function.comp_apply]
  rw [(extChartAt I α).right_inv hp.2]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in




private lemma pointwise_tendsto_chartTrivRepr
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (L : ℝ)
    (hcont : ContinuousOn (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.univ : Set (ℝ × M)))
    (z : E) :
    Filter.Tendsto (fun t : ℝ => chartTrivRepr (I := I) α (X t) z)
      (nhdsWithin 0 (Set.Ioo (0:ℝ) L)) (nhds (chartTrivRepr (I := I) α (X 0) z)) := by
  set x₀ := (extChartAt I α).symm z with hx0
  have hrepr : (fun t : ℝ => chartTrivRepr (I := I) α (X t) z)
      = (fun t : ℝ => trivToE (I := I) α x₀ (X t x₀)) := by funext t; rfl
  rw [hrepr]
  have hgoalval : chartTrivRepr (I := I) α (X 0) z = trivToE (I := I) α x₀ (X 0 x₀) := rfl
  rw [hgoalval]
  have hXc : Continuous (fun t : ℝ => (X t x₀ : E)) := by
    have hcontU : Continuous (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2)) :=
      continuousOn_univ.mp hcont
    exact hcontU.comp (by continuity : Continuous (fun t : ℝ => ((t, x₀) : ℝ × M)))
  have hclm : Filter.Tendsto (fun t : ℝ => trivToE (I := I) α x₀ (X t x₀)) (nhds 0)
      (nhds (trivToE (I := I) α x₀ (X 0 x₀))) :=
    ((trivToE (I := I) α x₀).continuous.tendsto _).comp hXc.continuousAt
  exact hclm.mono_left nhdsWithin_le_nhds

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in




theorem corrected_chart_field_lipschitz_of_data
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) (T : ℝ) (hT : 0 < T)
    (hcont : ContinuousOn (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2)) (Set.univ : Set (ℝ × M)))
    (hgrad : ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartTrivRepr (I := I) α (X q.1) z) (extChartAt I α q.2)) (Set.univ : Set (ℝ × M)))
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        ContinuousOn (fun y : E => chartTrivRepr (I := I) α (X t) y) (Metric.closedBall (I ((chartAt H α) α)) r)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K) (fun y : E => chartTrivRepr (I := I) α (X t) y) (Metric.ball (I ((chartAt H α) α)) r)) ∧
      Metric.closedBall (I ((chartAt H α) α)) r ⊆ (extChartAt I α).target := by
  classical
  set center : E := extChartAt I α α with hcenter
  have hcenter_eq : center = I ((chartAt H α) α) := by rw [hcenter, extChartAt_coe]; rfl
  have hcenter_int : center ∈ interior ((extChartAt I α).target : Set E) :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp BoundarylessManifold.isInteriorPoint
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp isOpen_interior center hcenter_int
  set r := r₀ / 2 with hr
  have hr_pos : 0 < r := by positivity
  have hcball_sub : Metric.closedBall center r ⊆ interior ((extChartAt I α).target : Set E) := by
    intro z hz
    apply hr₀_sub
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz
    have : r < r₀ := by rw [hr]; linarith
    linarith
  set L := T / 2 with hL
  have hL_pos : 0 < L := by positivity
  have hL_lt : L < T := by rw [hL]; linarith
  have hjoint_full := continuousOn_fderiv_chartTrivRepr (I := I) X α hgrad
  have hbox_sub : (Set.Icc (0:ℝ) L) ×ˢ (Metric.closedBall center r) ⊆
      (Set.univ : Set ℝ) ×ˢ (extChartAt I α).target := fun p hp =>
    ⟨Set.mem_univ _, interior_subset (hcball_sub hp.2)⟩
  have hjoint : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fun z => chartTrivRepr (I := I) α (X p.1) z) p.2)
      ((Set.Icc (0:ℝ) L) ×ˢ (Metric.closedBall center r)) := hjoint_full.mono hbox_sub
  have hcompact : IsCompact ((Set.Icc (0:ℝ) L) ×ˢ (Metric.closedBall center r)) :=
    isCompact_Icc.prod (isCompact_closedBall center r)
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn hjoint
  set C := max C₀ 0 with hC
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) L, ∀ z ∈ Metric.closedBall center r,
      ‖fderiv ℝ (fun z => chartTrivRepr (I := I) α (X t) z) z‖ ≤ C := fun t ht z hz =>
    (hC₀ (t, z) ⟨ht, hz⟩).trans (le_max_left _ _)
  have hLipPos : ∀ t ∈ Set.Ioc (0:ℝ) L,
      LipschitzOnWith (Real.toNNReal C) (fun y : E => chartTrivRepr (I := I) α (X t) y) (Metric.closedBall center r) := by
    intro t ht
    have htT : t ∈ Set.Ioo (0:ℝ) T := ⟨ht.1, lt_of_le_of_lt ht.2 hL_lt⟩
    have htIcc : t ∈ Set.Icc (0:ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
    have hCM : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x : M => (TotalSpace.mk' E x (X t x) : TangentBundle I M)) := by
      have hslice : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
        (contMDiff_const (c := t)).prodMk contMDiff_id
      exact hint.comp_contMDiff hslice (fun x => ⟨htT, Set.mem_univ x⟩)
    refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) ?_ ?_ (convex_closedBall center r)
    · intro z hz
      exact differentiableAt_chartTrivRepr_of_contMDiff_section (I := I) X α t hCM z (hcball_sub hz)
    · intro z hz
      rw [Real.le_toNNReal_iff_coe_le hC_nonneg]
      exact hbound t htIcc z hz
  have hLipAll : ∀ t ∈ Set.Icc (0:ℝ) L,
      LipschitzOnWith (Real.toNNReal C) (fun y : E => chartTrivRepr (I := I) α (X t) y) (Metric.closedBall center r) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      haveI : (nhdsWithin (0:ℝ) (Set.Ioo (0:ℝ) L)).NeBot := left_nhdsWithin_Ioo_neBot hL_pos
      refine lipschitzOnWith_of_tendsto_aux
        (fun s => fun y : E => chartTrivRepr (I := I) α (X s) y)
        (fun y : E => chartTrivRepr (I := I) α (X 0) y) (Real.toNNReal C)
        (Metric.closedBall center r) (nhdsWithin 0 (Set.Ioo (0:ℝ) L)) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact hLipPos s ⟨hs.1, le_of_lt hs.2⟩
      · intro z hz
        exact pointwise_tendsto_chartTrivRepr (I := I) X α L hcont z
    · exact hLipPos t ⟨h0, ht.2⟩
  rw [hcenter_eq] at hLipAll
  refine ⟨L, C, r, hL_pos, hr_pos, hC_nonneg, ?_, ?_, ?_⟩
  · intro t ht
    exact (hLipAll t ht).continuousOn
  · intro t ht
    exact (hLipAll t ht).mono Metric.ball_subset_closedBall
  · rw [← hcenter_eq]
    exact hcball_sub.trans interior_subset

end DifferentialGeometry.PDE.RicciFlow.ODE
