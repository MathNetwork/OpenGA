import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowToTangentLift



noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

section MaximalGeodesicWitnessFromLift

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem exists_picardLift_witness_interval
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {g_v : ℝ → TangentBundle I M}
    (hg0 : g_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hg_int : IsMIntegralCurveAt g_v
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∃ (ε : ℝ), 0 < ε ∧
      IsMIntegralCurveOn g_v (geodesicVectorFieldChart (I := I) g p)
        (Metric.ball (0 : ℝ) ε) ∧
      IsGeodesicOnWithInitial (I := I) g
        (projectCurve (I := I) g_v) (Metric.ball (0 : ℝ) ε) p v ∧
      (∀ s ∈ Metric.ball (0 : ℝ) ε, (g_v s).proj ∈ (chartAt H p).source) := by
  classical
  have hg_int' := hg_int
  rw [isMIntegralCurveAt_iff'] at hg_int'
  obtain ⟨ε₀, hε₀, hg_on⟩ := hg_int'
  have hcont_g_v : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousAt (fun s => (g_v s).proj) 0 :=
    hπ_cont.continuousAt.comp hcont_g_v
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hg0_proj : (g_v 0).proj = p := by rw [hg0]
  have hpreim_nhds :
      (fun s => (g_v s).proj) ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) := by
    apply hcomp.preimage_mem_nhds
    rw [hg0_proj]; exact hp_open.mem_nhds hp_mem
  obtain ⟨ε₁, hε₁, hε₁_sub⟩ := Metric.mem_nhds_iff.mp hpreim_nhds
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_, ?_, ?_⟩
  · exact hg_on.mono (Metric.ball_subset_ball (min_le_left _ _))
  · exact ⟨g_v, fun _ => rfl, hg0,
      hg_on.mono (Metric.ball_subset_ball (min_le_left _ _))⟩
  · intro s hs
    have hs_ε₁ : s ∈ Metric.ball (0 : ℝ) ε₁ :=
      Metric.ball_subset_ball (min_le_right _ _) hs
    exact hε₁_sub hs_ε₁

end MaximalGeodesicWitnessFromLift

section ClopenPropagation

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isMIntegralCurveOn_eq_of_isPreconnected
    (g : SmoothRiemannianMetric I M) (p : M)
    {f₁ f₂ : ℝ → TangentBundle I M}
    {K : Set ℝ} (hK_open : IsOpen K) (hK_conn : IsPreconnected K)
    (h0_K : (0 : ℝ) ∈ K)
    (hf₁_on : IsMIntegralCurveOn f₁ (geodesicVectorFieldChart (I := I) g p) K)
    (hf₂_on : IsMIntegralCurveOn f₂ (geodesicVectorFieldChart (I := I) g p) K)
    (hf₁_src : ∀ s ∈ K, (f₁ s).proj ∈ (chartAt H p).source)
    (h0_eq : f₁ 0 = f₂ 0) :
    Set.EqOn f₁ f₂ K := by
  classical
  set A : Set ℝ := {s ∈ K | f₁ s = f₂ s} with hA_def
  have h0_A : (0 : ℝ) ∈ A := ⟨h0_K, h0_eq⟩
  have hf₁_cont : ContinuousOn f₁ K := hf₁_on.continuousOn
  have hf₂_cont : ContinuousOn f₂ K := hf₂_on.continuousOn
  have hclosed_in_K : IsClosed {s : ℝ | s ∈ K ∧ f₁ s = f₂ s} ∨ True := Or.inr trivial
  have hA_rel_open : ∀ s ∈ A, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ U ∩ K ⊆ A := by
    intro s hs_A
    obtain ⟨hs_K, hs_eq⟩ := hs_A
    have hK_nhds : K ∈ 𝓝 s := hK_open.mem_nhds hs_K
    have hf₁_at_s : IsMIntegralCurveAt f₁
        (geodesicVectorFieldChart (I := I) g p) s :=
      hf₁_on.isMIntegralCurveAt hK_nhds
    have hf₂_at_s : IsMIntegralCurveAt f₂
        (geodesicVectorFieldChart (I := I) g p) s :=
      hf₂_on.isMIntegralCurveAt hK_nhds
    have hsrc_s : (f₁ s).proj ∈ (chartAt H p).source := hf₁_src s hs_K
    have heq_ev :=
      isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
        (I := I) (g := g) (α := p) (t₀ := s)
        (f₁ := f₁) (f₂ := f₂) hsrc_s hf₁_at_s hf₂_at_s hs_eq
    rw [Filter.eventuallyEq_iff_exists_mem] at heq_ev
    obtain ⟨U₀, hU₀_nhds, hU₀_eq⟩ := heq_ev
    obtain ⟨U, hU_sub, hU_open, hs_U⟩ := _root_.mem_nhds_iff.mp hU₀_nhds
    refine ⟨U, hU_open, hs_U, ?_⟩
    intro s' hs'
    refine ⟨hs'.2, ?_⟩
    exact hU₀_eq (hU_sub hs'.1)
  have hKnA_rel_open : ∀ s ∈ K \ A, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ U ∩ K ⊆ K \ A := by
    intro s hs_KnA
    obtain ⟨hs_K, hs_nA⟩ := hs_KnA
    have hs_neq : f₁ s ≠ f₂ s := by
      intro h
      exact hs_nA ⟨hs_K, h⟩
    have hpair_cont : ContinuousAt (fun s : ℝ => (f₁ s, f₂ s)) s := by
      apply ContinuousAt.prodMk
      · exact (hf₁_cont.continuousWithinAt hs_K).continuousAt (hK_open.mem_nhds hs_K)
      · exact (hf₂_cont.continuousWithinAt hs_K).continuousAt (hK_open.mem_nhds hs_K)
    have hdiag_closed : IsClosed {q : TangentBundle I M × TangentBundle I M | q.1 = q.2} :=
      isClosed_diagonal
    have hndiag_open : IsOpen {q : TangentBundle I M × TangentBundle I M | q.1 ≠ q.2} :=
      hdiag_closed.isOpen_compl
    have hpreim : (fun s : ℝ => (f₁ s, f₂ s)) ⁻¹'
        {q : TangentBundle I M × TangentBundle I M | q.1 ≠ q.2} ∈ 𝓝 s :=
      hpair_cont.preimage_mem_nhds (hndiag_open.mem_nhds hs_neq)
    obtain ⟨U, hU_sub, hU_open, hs_U⟩ := _root_.mem_nhds_iff.mp hpreim
    refine ⟨U, hU_open, hs_U, ?_⟩
    intro s' hs'
    refine ⟨hs'.2, ?_⟩
    intro hs'_A
    obtain ⟨_, hs'_eq⟩ := hs'_A
    have : f₁ s' ≠ f₂ s' := hU_sub hs'.1
    exact this hs'_eq
  intro s hs_K
  by_contra h_neq
  have hs_KnA : s ∈ K \ A := ⟨hs_K, fun h => h_neq h.2⟩
  set U_A : Set ℝ := ⋃ (s : ℝ) (hsA : s ∈ A), Classical.choose (hA_rel_open s hsA) with hU_A_def
  have hU_A_open : IsOpen U_A := by
    apply isOpen_iUnion; intro s
    apply isOpen_iUnion; intro hsA
    exact (Classical.choose_spec (hA_rel_open s hsA)).1
  have hA_sub_U_A : A ⊆ U_A := by
    intro x hx
    simp only [hU_A_def, Set.mem_iUnion]
    refine ⟨x, hx, (Classical.choose_spec (hA_rel_open x hx)).2.1⟩
  have hU_A_inter_K_sub_A : U_A ∩ K ⊆ A := by
    intro x ⟨hx_U, hx_K⟩
    simp only [hU_A_def, Set.mem_iUnion] at hx_U
    obtain ⟨s', hs'_A, hx_s'⟩ := hx_U
    have hsub := (Classical.choose_spec (hA_rel_open s' hs'_A)).2.2
    exact hsub ⟨hx_s', hx_K⟩
  set U_KnA : Set ℝ := ⋃ (s : ℝ) (hsKnA : s ∈ K \ A),
    Classical.choose (hKnA_rel_open s hsKnA) with hU_KnA_def
  have hU_KnA_open : IsOpen U_KnA := by
    apply isOpen_iUnion; intro s
    apply isOpen_iUnion; intro hsKnA
    exact (Classical.choose_spec (hKnA_rel_open s hsKnA)).1
  have hKnA_sub_U_KnA : K \ A ⊆ U_KnA := by
    intro x hx
    simp only [hU_KnA_def, Set.mem_iUnion]
    refine ⟨x, hx, (Classical.choose_spec (hKnA_rel_open x hx)).2.1⟩
  have hU_KnA_inter_K_sub_KnA : U_KnA ∩ K ⊆ K \ A := by
    intro x ⟨hx_U, hx_K⟩
    simp only [hU_KnA_def, Set.mem_iUnion] at hx_U
    obtain ⟨s', hs'_KnA, hx_s'⟩ := hx_U
    have hsub := (Classical.choose_spec (hKnA_rel_open s' hs'_KnA)).2.2
    exact hsub ⟨hx_s', hx_K⟩
  have hK_cover : K ⊆ U_A ∪ U_KnA := by
    intro x hx_K
    by_cases hxA : x ∈ A
    · left; exact hA_sub_U_A hxA
    · right; exact hKnA_sub_U_KnA ⟨hx_K, hxA⟩
  have hcontra : (K ∩ (U_A ∩ U_KnA)).Nonempty :=
    hK_conn U_A U_KnA hU_A_open hU_KnA_open hK_cover
      ⟨0, h0_K, hA_sub_U_A h0_A⟩
      ⟨s, hs_K, hKnA_sub_U_KnA hs_KnA⟩
  obtain ⟨x, hx_K, hx_UA, hx_UKnA⟩ := hcontra
  have hxA : x ∈ A := hU_A_inter_K_sub_A ⟨hx_UA, hx_K⟩
  have hxKnA : x ∈ K \ A := hU_KnA_inter_K_sub_KnA ⟨hx_UKnA, hx_K⟩
  exact hxKnA.2 hxA

end ClopenPropagation

section PicardLiftProjEqMaximalGeodesic

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem picardLift_proj_eq_maximalGeodesic_on_ball
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {g_v : ℝ → TangentBundle I M}
    (hg0 : g_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hg_int : IsMIntegralCurveAt g_v
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∃ (ε : ℝ), 0 < ε ∧
      ∀ t ∈ Metric.ball (0 : ℝ) ε,
        maximalGeodesic (I := I) g p v t = (g_v t).proj := by
  classical
  obtain ⟨ε, hε, hg_on, hgeo, hg_src⟩ :=
    exists_picardLift_witness_interval (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  set J : Set ℝ := Metric.ball (0 : ℝ) ε with hJ_def
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have ht_witness : MaximalGeodesicWitness (I := I) g p v t :=
    ⟨projectCurve (I := I) g_v, J, Metric.isOpen_ball,
      (convex_ball (0 : ℝ) ε).isPreconnected, Metric.mem_ball_self hε, ht, hgeo⟩
  have ht_mem : t ∈ maximalGeodesicInterval (I := I) g p v := ht_witness
  rw [maximalGeodesic_of_mem (I := I) ht_mem]
  obtain ⟨J', hJ'_open, hJ'_conn, h0_J', ht_J', hgeo'⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v ht_mem
  obtain ⟨f', hproj', hf'_0, hf'_on⟩ := hgeo'
  set K : Set ℝ := J ∩ J' with hK_def
  have hK_open : IsOpen K := Metric.isOpen_ball.inter hJ'_open
  have hK_conn : IsPreconnected K := by
    have hJ_ord : OrdConnected J :=
      ((convex_ball (0 : ℝ) ε).isPreconnected).ordConnected
    have hJ'_ord : OrdConnected J' := hJ'_conn.ordConnected
    have hK_ord : OrdConnected K := hJ_ord.inter hJ'_ord
    exact hK_ord.isPreconnected
  have h0_K : (0 : ℝ) ∈ K := ⟨Metric.mem_ball_self hε, h0_J'⟩
  have ht_K : t ∈ K := ⟨ht, ht_J'⟩
  have hg_on_K : IsMIntegralCurveOn g_v
      (geodesicVectorFieldChart (I := I) g p) K :=
    hg_on.mono Set.inter_subset_left
  have hf'_on_K : IsMIntegralCurveOn f' (geodesicVectorFieldChart (I := I) g p) K :=
    hf'_on.mono Set.inter_subset_right
  have hg_src_K : ∀ s ∈ K, (g_v s).proj ∈ (chartAt H p).source := by
    intro s hs_K
    exact hg_src s hs_K.1
  have heqOn := isMIntegralCurveOn_eq_of_isPreconnected (I := I) (g := g) (p := p)
    (f₁ := g_v) (f₂ := f') hK_open hK_conn h0_K hg_on_K hf'_on_K hg_src_K
    (by rw [hg0, hf'_0])
  have hg_t_eq : g_v t = f' t := heqOn ht_K
  have : (g_v t).proj = (f' t).proj := by rw [hg_t_eq]
  rw [this]
  exact (hproj' t).symm

end PicardLiftProjEqMaximalGeodesic

section ChartFlowOrbitLiftProjEqMaximalGeodesic

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLift_proj_eq_maximalGeodesic_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {Φ : (E × E) × ℝ → E × E}
    (hF_0 : chartFlowOrbitLift (I := I) Φ p v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hF_int : IsMIntegralCurveAt (chartFlowOrbitLift (I := I) Φ p v)
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      (chartFlowOrbitLift (I := I) Φ p v s).proj =
        maximalGeodesic (I := I) g p v s := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  obtain ⟨ε, hε, h_max_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have hF_proj_0 : (chartFlowOrbitLift (I := I) Φ p v 0).proj = p := by
    rw [hF_0]
  have hp_src : (g_v 0).proj ∈ (chartAt H p).source := by
    rw [hg0]; exact mem_chart_source H p
  have h0_eq : g_v 0 = chartFlowOrbitLift (I := I) Φ p v 0 := by
    rw [hg0, hF_0]
  have hgF_ev :=
    isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := p) (t₀ := 0)
      (f₁ := g_v) (f₂ := chartFlowOrbitLift (I := I) Φ p v)
      hp_src hg_int hF_int h0_eq
  have h_ball_nhds : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
  filter_upwards [hgF_ev, h_ball_nhds] with s hs_eq hs_ball
  have h_max_s : maximalGeodesic (I := I) g p v s = (g_v s).proj :=
    h_max_eq s hs_ball
  rw [h_max_s, ← hs_eq]

end ChartFlowOrbitLiftProjEqMaximalGeodesic

section HeadlineRD2

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlowOrbitLift_proj_eq_maximalGeodesic_data
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) =
          ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        chartFlowOrbitLift (I := I) Φ p v 0 =
          (⟨p, v⟩ : TangentBundle I M)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveAt (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) 0) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        ∀ᶠ s in 𝓝 (0 : ℝ),
          (chartFlowOrbitLift (I := I) Φ p v s).proj =
            maximalGeodesic (I := I) g p v s) := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, hF_0,
    _hF_proj, _hF_chartPush, hF_int⟩ :=
    exists_chartFlowOrbitLift_data_uniform (I := I) (g := g) (p := p)
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, hF_0,
    hF_int, ?_⟩
  intro v hv
  exact chartFlowOrbitLift_proj_eq_maximalGeodesic_eventually
    (I := I) (g := g) (p := p) (v := v) (Φ := Φ) (hF_0 v hv) (hF_int v hv)

end HeadlineRD2

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
