import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChainedFlowContinuity
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact



noncomputable section

open Set Filter Topology Metric Bundle Manifold Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem intrinsicGeodesic_compactArc
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    IsCompact (intrinsicGeodesic (I := I) g hEnorm p v '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.image_of_continuousOn
    (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem intrinsicGeodesic_arc_lebesgue_mesh
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ q : M,
      ∀ s ∈ Metric.ball t δ,
        intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H q).source := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  set c : M → Set ℝ := fun q => γ ⁻¹' (chartAt H q).source with hc_def
  have hc_open : ∀ q : M, IsOpen (c q) := by
    intro q
    exact (chartAt H q).open_source.preimage hγ_cont
  have hc_cover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ q : M, c q := by
    intro t _ht
    refine Set.mem_iUnion.mpr ⟨γ t, ?_⟩
    simp only [hc_def, Set.mem_preimage]
    exact mem_chart_source H (γ t)
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.Icc (0 : ℝ) 1) (c := c)
      isCompact_Icc hc_open hc_cover
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht
  obtain ⟨q, hq⟩ := hδ t ht
  refine ⟨q, ?_⟩
  intro s hs
  have : s ∈ c q := hq hs
  simpa only [hc_def, Set.mem_preimage] using this

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem intrinsicGeodesic_arc_finite_chart_cover
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ∃ (δ : ℝ) (q : (Set.Icc (0 : ℝ) 1) → M) (s : Finset (Set.Icc (0 : ℝ) 1)),
      0 < δ ∧
      Set.Icc (0 : ℝ) 1 ⊆ ⋃ t ∈ s, Metric.ball (t : ℝ) δ ∧
      ∀ t : Set.Icc (0 : ℝ) 1, ∀ r ∈ Metric.ball (t : ℝ) δ,
        intrinsicGeodesic (I := I) g hEnorm p v r ∈ (chartAt H (q t)).source := by
  classical
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    intrinsicGeodesic_arc_lebesgue_mesh (I := I) g hEnorm p v
  have hq_choice : ∀ t : Set.Icc (0 : ℝ) 1, ∃ q : M,
      ∀ r ∈ Metric.ball (t : ℝ) δ,
        intrinsicGeodesic (I := I) g hEnorm p v r ∈ (chartAt H q).source := by
    intro t
    obtain ⟨q, hq⟩ := hδ (t : ℝ) t.2
    exact ⟨q, hq⟩
  choose q hq using hq_choice
  set U : (Set.Icc (0 : ℝ) 1) → Set ℝ := fun t => Metric.ball (t : ℝ) δ with hU_def
  have hU_open : ∀ t, IsOpen (U t) := fun t => Metric.isOpen_ball
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ t, U t := by
    intro r hr
    refine Set.mem_iUnion.mpr ⟨⟨r, hr⟩, ?_⟩
    simp only [hU_def]
    exact Metric.mem_ball_self hδ_pos
  obtain ⟨s, hs⟩ :=
    isCompact_Icc.elim_finite_subcover U hU_open hcover
  refine ⟨δ, q, s, hδ_pos, ?_, ?_⟩
  · intro r hr
    have := hs hr
    simpa only [hU_def] using this
  · intro t r hr
    exact hq t r hr

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [InnerProductSpace ℝ E] in
theorem intrinsicGeodesic_hasGeodesicEquationAt_to_lift
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (hγ_cont : Continuous γ) (t : ℝ) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t).proj = γ t ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t)) t ∧
      γ =ᶠ[𝓝 t] (fun s => (f₁ s).proj) := by
  classical
  set y : M := γ t with hy_def
  set v : E := deriv
    (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) y γ) t
    with hv_def
  obtain ⟨f₁, hf₁_init, hf₁⟩ := exists_chartCenteredLift_at (I := I) g y v t
  have hf₁_proj_t : (f₁ t).proj = y := by rw [hf₁_init]
  refine ⟨f₁, by rw [hf₁_proj_t], by rw [hy_def] at hf₁ ⊢; exact hf₁, ?_⟩
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) y γ with hw_def
  set c₁ : ℝ → E × E := fun s => (w s, deriv w s) with hc₁_def
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hγ_src_ev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H y).source := by
    apply hγ_cont.continuousAt.preimage_mem_nhds
    exact (chartAt H y).open_source.mem_nhds (by rw [hy_def]; exact hy_src)
  have hev_first : ∀ᶠ s in 𝓝 t, HasDerivAt w (deriv w s) s :=
    hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g y
      hγ_cont.continuousAt (by rw [hy_def]; exact hy_src) (hγ t)
  have hev_second : ∀ᶠ s in 𝓝 t,
      HasDerivAt (deriv w)
        (- chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s)) s := by
    filter_upwards [hγ_src_ev] with s hs
    exact hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
      hγ_cont.continuousAt hs (hγ s)
  have hc₁_phase : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₁ (chartPhaseVF (I := I) g y (c₁ s)) s ∧
        c₁ s ∈ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hev_first, hev_second, hγ_src_ev] with s hf hsd hsrc
    refine ⟨?_, ?_⟩
    · have hpair : HasDerivAt c₁
          ((deriv w s,
            - chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s))) s :=
        hf.prodMk hsd
      have hrhs : chartPhaseVF (I := I) g y (c₁ s) =
          (deriv w s,
            - chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s)) := by
        simp only [hc₁_def, chartPhaseVF_apply]
      rw [hrhs]; exact hpair
    · refine ⟨?_, Set.mem_univ _⟩
      have hp_ext_src : γ s ∈ (extChartAt I y).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
      have hp_target : extChartAt I y (γ s) ∈ (extChartAt I y).target :=
        (extChartAt I y).map_source hp_ext_src
      have : (c₁ s).1 = extChartAt I y (γ s) := by simp [hc₁_def, hw_def]
      rw [this]
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) y hp_target
  set c₂ : ℝ → E × E := chartPushLift (I := I) f₁ t with hc₂_def
  have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_contAt : ContinuousAt (fun s => (f₁ s).proj) t :=
    hπ_cont.continuousAt.comp hf₁.continuousAt
  have hf_src_ev : ∀ᶠ s in 𝓝 t, (f₁ s).proj ∈ (chartAt H y).source := by
    apply hproj_contAt.preimage_mem_nhds
    rw [hf₁_proj_t]; exact (chartAt H y).open_source.mem_nhds hy_src
  have hc₂_deriv : ∀ᶠ s in 𝓝 t, HasDerivAt (chartPushLift (I := I) f₁ t)
      (chartPushVF (I := I) g y f₁ t s) s := by
    have hf₁' : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g y) t := hf₁
    exact chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := y)
      (t₀ := t) (f := f₁) hf₁'
  have hc₂_phase : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₂ (chartPhaseVF (I := I) g y (c₂ s)) s ∧
        c₂ s ∈ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hc₂_deriv, hf_src_ev] with s hd hs
    refine ⟨?_, ?_⟩
    · have heq := chartPushVF_eq_chartPhaseVF_at (I := I) g y (f := f₁) (t₀ := t)
        hf₁_proj_t s hs
      rw [heq] at hd; exact hd
    · rw [hc₂_def, chartPushLift_eq_pair (I := I) t s (by rw [hf₁_proj_t]; exact hs)]
      refine ⟨?_, Set.mem_univ _⟩
      rw [hf₁_proj_t]
      have hp_ext_src : (f₁ s).proj ∈ (extChartAt I y).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs
      have hp_target : extChartAt I y (f₁ s).proj ∈ (extChartAt I y).target :=
        (extChartAt I y).map_source hp_ext_src
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) y hp_target
  have hc₁_t : c₁ t = (extChartAt I y y, v) := by
    have hwt : w t = extChartAt I y y := by simp [hw_def, hy_def]
    have hvt : deriv w t = v := by rw [hv_def, hw_def]
    simp only [hc₁_def, hwt, hvt]
  have hc₂_t : c₂ t = (extChartAt I y y, v) := by
    rw [hc₂_def, chartPushLift_self_pair (I := I) f₁ t, hf₁_proj_t]
    have hfib : chartFiberCoord (I := I) y (f₁ t) = v := by
      rw [show f₁ t = (⟨y, v⟩ : TangentBundle I M) from hf₁_init]
      exact chartFiberCoord_mk_self (I := I) y v
    rw [hfib]
  have hz₀_int : (extChartAt I y y, v) ∈
      (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hp_ext_src : y ∈ (extChartAt I y).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
    have hp_target : extChartAt I y y ∈ (extChartAt I y).target :=
      (extChartAt I y).map_source hp_ext_src
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) y hp_target
  have hceq : c₁ =ᶠ[𝓝 t] c₂ :=
    chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (q := y)
      hz₀_int hc₁_t hc₂_t hc₁_phase hc₂_phase
  have hfst : ∀ᶠ s in 𝓝 t, extChartAt I y (γ s) = extChartAt I y (f₁ s).proj := by
    filter_upwards [hceq, hf_src_ev] with s hs hsrc
    have h1 : (c₁ s).1 = extChartAt I y (γ s) := by simp [hc₁_def, hw_def]
    have h2 : (c₂ s).1 = extChartAt I y (f₁ s).proj := by
      rw [hc₂_def, chartPushLift_eq_pair (I := I) t s (by rw [hf₁_proj_t]; exact hsrc)]
      rw [hf₁_proj_t]
    rw [← h1, ← h2, hs]
  filter_upwards [hγ_src_ev, hf_src_ev, hfst] with s hγs hfs heq
  have hγ_es : γ s ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγs
  have hf_es : (f₁ s).proj ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hfs
  exact (extChartAt I y).injOn hγ_es hf_es heq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

private def flowProj (α : M) (Φ : (E × E) × ℝ → E × E) (z : E × E) (s : ℝ) : M :=
  (extChartAt I α).symm (Φ (z, s)).1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem flowProj_continuousOn
    [I.Boundaryless]
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {ρ T : ℝ}
    {N : Type*} [TopologicalSpace N] {z : N → E × E} {S : Set N}
    (hΦ : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T))
    (hz_cont : ContinuousOn z S)
    (hz_ball : ∀ n ∈ S, z n ∈ Metric.ball z₀ ρ)
    (htgt : ∀ n ∈ S, ∀ τ ∈ Set.Ioo (-T) T,
      (Φ (z n, τ)).1 ∈ (extChartAt I α).target) :
    ContinuousOn (fun nτ : N × ℝ => flowProj (I := I) α Φ (z nτ.1) nτ.2)
      (S ×ˢ Set.Ioo (-T) T) := by
  classical
  have hpair_cont : ContinuousOn (fun nτ : N × ℝ => (z nτ.1, nτ.2))
      (S ×ˢ Set.Ioo (-T) T) := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact hz_cont.comp continuousOn_fst (fun x hx => hx.1)
    · exact continuousOn_snd
  have hpair_maps : Set.MapsTo (fun nτ : N × ℝ => (z nτ.1, nτ.2))
      (S ×ˢ Set.Ioo (-T) T) ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T) := by
    intro nτ hnτ
    exact ⟨hz_ball nτ.1 hnτ.1, hnτ.2⟩
  have hΦcomp : ContinuousOn (fun nτ : N × ℝ => Φ (z nτ.1, nτ.2))
      (S ×ˢ Set.Ioo (-T) T) :=
    hΦ.comp hpair_cont hpair_maps
  have hfst : ContinuousOn (fun nτ : N × ℝ => (Φ (z nτ.1, nτ.2)).1)
      (S ×ˢ Set.Ioo (-T) T) :=
    (continuous_fst.comp_continuousOn hΦcomp)
  have hsymm : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (fun nτ : N × ℝ => (Φ (z nτ.1, nτ.2)).1)
      (S ×ˢ Set.Ioo (-T) T) (extChartAt I α).target := by
    intro nτ hnτ
    exact htgt nτ.1 hnτ.1 nτ.2 hnτ.2
  exact hsymm.comp hfst hmaps

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem perChart_jointContinuity_of_flowIdentifiedOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {z : TangentSpace I p → E × E}
    {tₖ ε r ρ T : ℝ}
    (hεT : ε ≤ T)
    (hΦ : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T))
    (hz_cont : ContinuousOn z (Metric.ball v₀ r))
    (hz_ball : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball z₀ ρ)
    (htgt : ∀ v ∈ Metric.ball v₀ r, ∀ τ ∈ Set.Ioo (-ε) ε,
      (Φ (z v, τ)).1 ∈ (extChartAt I α).target)
    (hident : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - ε) (tₖ + ε),
      intrinsicGeodesic (I := I) g hEnorm p v t =
        flowProj (I := I) α Φ (z v) (t - tₖ)) :
    ContinuousOn
      (fun vt : TangentSpace I p × ℝ =>
        intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) := by
  classical
  have hshift_cont : ContinuousOn (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) :=
    (continuousOn_fst).prodMk ((continuousOn_snd).sub continuousOn_const)
  have hshift_maps : Set.MapsTo (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (-ε) ε) := by
    intro vt hvt
    refine ⟨hvt.1, ?_, ?_⟩
    · exact lt_sub_iff_add_lt.mpr (by linarith [hvt.2.1])
    · exact sub_lt_iff_lt_add.mpr (by linarith [hvt.2.2])
  have hbase_cont : ContinuousOn
      (fun vτ : TangentSpace I p × ℝ => flowProj (I := I) α Φ (z vτ.1) vτ.2)
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (-ε) ε) := by
    have hΦ' : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-ε) ε) :=
      hΦ.mono (Set.prod_mono (le_refl _)
        (Set.Ioo_subset_Ioo (by linarith) hεT))
    exact flowProj_continuousOn (I := I) (α := α) (Φ := Φ) (z₀ := z₀)
      (ρ := ρ) (T := ε) (z := z) (S := Metric.ball v₀ r)
      hΦ' hz_cont hz_ball htgt
  have hcomp_cont : ContinuousOn
      (fun vt : TangentSpace I p × ℝ => flowProj (I := I) α Φ (z vt.1) (vt.2 - tₖ))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) :=
    hbase_cont.comp hshift_cont hshift_maps
  apply hcomp_cont.congr
  intro vt hvt
  exact hident vt.1 hvt.1 vt.2 hvt.2







private theorem dist_le_of_speed_bound_on_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : ℝ → F} {c' : ℝ → F} {z₀ : F} {R M T'' : ℝ}
    (hMpos : 0 < M) (hMT'' : M * T'' ≤ R) (hT''_pos : 0 < T'')
    (hc0 : c 0 = z₀)
    (hderiv : ∀ s ∈ Set.Icc (0:ℝ) T'', HasDerivWithinAt c (c' s) (Set.Icc 0 T'') s)
    (hbound : ∀ s ∈ Set.Icc (0:ℝ) T'', dist (c s) z₀ ≤ R → ‖c' s‖ ≤ M) :
    ∀ s ∈ Set.Icc (0:ℝ) T'', dist (c s) z₀ ≤ M * s := by
  classical
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) hMT''
  set G : Set ℝ := {t ∈ Set.Icc (0:ℝ) T'' | ∀ s ∈ Set.Icc (0:ℝ) t, dist (c s) z₀ ≤ R}
    with hG_def
  have hc_cont : ContinuousOn c (Set.Icc 0 T'') :=
    fun s hs => (hderiv s hs).continuousWithinAt

  have hbd_on_G : ∀ t ∈ G, ∀ s ∈ Set.Icc (0:ℝ) t, dist (c s) z₀ ≤ M * s := by
    intro t ht s hs
    obtain ⟨ht_Icc, ht_R⟩ := ht
    have hsT : s ∈ Set.Icc (0:ℝ) T'' := ⟨hs.1, le_trans hs.2 ht_Icc.2⟩
    have hsub : Set.Icc (0:ℝ) s ⊆ Set.Icc (0:ℝ) T'' := Set.Icc_subset_Icc le_rfl hsT.2
    have hderiv' : ∀ r ∈ Set.Icc (0:ℝ) s, HasDerivWithinAt c (c' r) (Set.Icc 0 s) r :=
      fun r hr => (hderiv r (hsub hr)).mono hsub
    have hbnd' : ∀ r ∈ Set.Icc (0:ℝ) s, ‖c' r‖ ≤ M := fun r hr =>
      hbound r (hsub hr) (ht_R r ⟨hr.1, le_trans hr.2 hs.2⟩)
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (f := c) (f' := c')
      (C := M) (a := (0:ℝ)) (b := s) hderiv'
      (fun r hr => hbnd' r ⟨hr.1, le_of_lt hr.2⟩) s (Set.right_mem_Icc.mpr hs.1)
    rw [dist_eq_norm]
    calc ‖c s - z₀‖ = ‖c s - c 0‖ := by rw [hc0]
      _ ≤ M * (s - 0) := hseg
      _ = M * s := by rw [sub_zero]
  have h0_G : (0:ℝ) ∈ G := by
    refine ⟨⟨le_refl _, le_of_lt hT''_pos⟩, fun s hs => ?_⟩
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    rw [hs0, hc0, dist_self]; exact le_of_lt hR_pos
  have hG_bdd : BddAbove G := ⟨T'', fun t ht => ht.1.2⟩
  have hG_ne : G.Nonempty := ⟨0, h0_G⟩
  set t0 : ℝ := sSup G with ht0_def
  have ht0_nonneg : 0 ≤ t0 := le_csSup hG_bdd h0_G
  have ht0_le : t0 ≤ T'' := csSup_le hG_ne (fun t ht => ht.1.2)
  have ht0_G : t0 ∈ G := by
    refine ⟨⟨ht0_nonneg, ht0_le⟩, fun s hs => ?_⟩
    rcases lt_or_eq_of_le hs.2 with hst | hst
    · obtain ⟨t, ht_G, hst'⟩ := exists_lt_of_lt_csSup hG_ne hst
      exact ht_G.2 s ⟨hs.1, le_of_lt hst'⟩
    ·
      rw [hst]
      rcases eq_or_lt_of_le ht0_nonneg with h0 | h0
      · rw [← h0, hc0, dist_self]; exact le_of_lt hR_pos
      · have hsub_cwa : ContinuousWithinAt (fun r => c r - z₀) (Set.Ico 0 t0) t0 :=
          (((hderiv t0 ⟨ht0_nonneg, ht0_le⟩).continuousWithinAt).mono
            (Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht0_le))).sub
            continuousWithinAt_const
        have hφ_within : ContinuousWithinAt (fun r => dist (c r) z₀) (Set.Ico 0 t0) t0 := by
          simpa only [dist_eq_norm] using hsub_cwa.norm
        haveI : (nhdsWithin t0 (Set.Ico (0:ℝ) t0)).NeBot := by
          rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (ne_of_lt h0)]
          exact ⟨ht0_nonneg, le_refl _⟩
        refine le_of_tendsto hφ_within.tendsto ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        obtain ⟨t, ht_G, hrt⟩ := exists_lt_of_lt_csSup hG_ne hr.2
        exact ht_G.2 r ⟨hr.1, le_of_lt hrt⟩

  have ht0_eq : t0 = T'' := by
    by_contra hne
    have ht0_lt : t0 < T'' := lt_of_le_of_ne ht0_le hne
    have hstrict : dist (c t0) z₀ ≤ M * t0 := hbd_on_G t0 ht0_G t0 ⟨ht0_nonneg, le_refl _⟩
    have hstrict' : dist (c t0) z₀ < R :=
      lt_of_le_of_lt hstrict (lt_of_lt_of_le (mul_lt_mul_of_pos_left ht0_lt hMpos) hMT'')
    have hball_nhds : {x : F | dist x z₀ < R} ∈ nhds (c t0) :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hstrict'
    have hpreim : c ⁻¹' {x : F | dist x z₀ < R} ∈ nhdsWithin t0 (Set.Icc 0 T'') :=
      (hderiv t0 ⟨ht0_nonneg, ht0_le⟩).continuousWithinAt.preimage_mem_nhdsWithin hball_nhds
    rw [Metric.mem_nhdsWithin_iff] at hpreim
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := hpreim
    set t1 : ℝ := min (t0 + δ / 2) T'' with ht1_def
    have ht1_gt : t0 < t1 := by
      rw [ht1_def]; exact lt_min (by linarith) ht0_lt
    have ht1_le : t1 ≤ T'' := min_le_right _ _
    have ht1_G : t1 ∈ G := by
      refine ⟨⟨le_trans ht0_nonneg (le_of_lt ht1_gt), ht1_le⟩, fun s hs => ?_⟩
      by_cases hsl : s ≤ t0
      · exact ht0_G.2 s ⟨hs.1, hsl⟩
      · push_neg at hsl
        have hs_time : s ∈ Metric.ball t0 δ ∩ Set.Icc (0:ℝ) T'' := by
          refine ⟨?_, ⟨hs.1, le_trans hs.2 ht1_le⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          refine ⟨by linarith, ?_⟩
          have h1 : t1 ≤ t0 + δ / 2 := min_le_left _ _
          linarith [hs.2]
        have hres := hδ_sub hs_time
        rw [Set.mem_preimage, Set.mem_setOf_eq] at hres
        exact le_of_lt hres
    exact absurd (le_csSup hG_bdd ht1_G) (not_le.mpr ht1_gt)

  intro s hs
  rw [← ht0_eq] at hs
  exact hbd_on_G t0 ht0_G s hs



omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [I.Boundaryless] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem chartPhaseVF_bddOn_closedBall
    (g : SmoothRiemannianMetric I M) (α : M) (z₀ : E × E) {R : ℝ} (hR : 0 ≤ R)
    (hsub : Metric.closedBall z₀ R ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ M : ℝ, 0 < M ∧
      ∀ x ∈ Metric.closedBall z₀ R, ‖chartPhaseVF (I := I) g α x‖ ≤ M := by
  obtain ⟨L, hL⟩ := chartPhaseVF_lipschitzOnWith_of_compact (I := I) g α
    (isCompact_closedBall z₀ R) hsub
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall z₀ R).exists_bound_of_continuousOn hL.continuousOn
  exact ⟨|C| + 1, by positivity, fun x hx => le_trans (hC x hx) (by linarith [le_abs_self C])⟩





omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem orbit_speed_confined_fwd
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : ℝ → E × E} {z₀ : E × E} {R ρ M T_f : ℝ}
    (hMpos : 0 < M) (hRρ : ρ < R) (hρ_nonneg : 0 ≤ ρ) (hT_f : 0 < T_f)
    (hz_c : dist (c 0) z₀ ≤ ρ)
    (hderiv : ∀ s ∈ Set.Icc (0:ℝ) (min T_f ((R - ρ) / M)),
      HasDerivWithinAt c (chartPhaseVF (I := I) g α (c s))
        (Set.Icc 0 (min T_f ((R - ρ) / M))) s)
    (hM : ∀ x ∈ Metric.closedBall z₀ R, ‖chartPhaseVF (I := I) g α x‖ ≤ M) :
    ∀ s ∈ Set.Icc (0:ℝ) (min T_f ((R - ρ) / M)), c s ∈ Metric.closedBall z₀ R := by
  set T' : ℝ := min T_f ((R - ρ) / M) with hT'_def
  have hT'_pos : 0 < T' := lt_min hT_f (div_pos (by linarith) hMpos)
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hMT' : M * T' ≤ R - ρ := by
    calc M * T' ≤ M * ((R - ρ) / M) := by
          apply mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hMpos)
      _ = R - ρ := by field_simp
  have hbound' : ∀ s ∈ Set.Icc (0:ℝ) T', dist (c s) (c 0) ≤ R - ρ →
      ‖chartPhaseVF (I := I) g α (c s)‖ ≤ M := by
    intro s _ hds
    refine hM (c s) ?_
    rw [Metric.mem_closedBall]
    calc dist (c s) z₀ ≤ dist (c s) (c 0) + dist (c 0) z₀ := dist_triangle _ _ _
      _ ≤ (R - ρ) + ρ := by linarith [hds, hz_c]
      _ = R := by ring
  have hkey := dist_le_of_speed_bound_on_Icc
    (c := c) (c' := fun s => chartPhaseVF (I := I) g α (c s))
    (z₀ := c 0) (R := R - ρ) (M := M) (T'' := T') hMpos hMT' hT'_pos rfl hderiv hbound'
  intro s hs
  rw [Metric.mem_closedBall]
  have hMs : M * s ≤ R - ρ := le_trans
    (by apply mul_le_mul_of_nonneg_left hs.2 (le_of_lt hMpos)) hMT'
  calc dist (c s) z₀ ≤ dist (c s) (c 0) + dist (c 0) z₀ := dist_triangle _ _ _
    _ ≤ (R - ρ) + ρ := by linarith [hkey s hs, hz_c]
    _ = R := by ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem flowOrbit_speed_confined_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {N : Type*} [TopologicalSpace N]
    {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {z : N → E × E} {S : Set N}
    {R ρ Mb T_f : ℝ}
    (hMpos : 0 < Mb) (hRρ : ρ < R) (hρ_nonneg : 0 ≤ ρ) (hT_f : 0 < T_f)
    (hRMT : R - ρ < Mb * T_f)
    (hz_ball : ∀ v ∈ S, dist (z v) z₀ ≤ ρ)
    (hΦinit : ∀ v ∈ S, Φ (z v, 0) = z v)
    (hΦ_phase : ∀ v ∈ S, ∀ s ∈ Set.Ioo (-T_f) T_f,
      HasDerivAt (fun τ => Φ (z v, τ)) (chartPhaseVF (I := I) g α (Φ (z v, s))) s)
    (hM : ∀ x ∈ Metric.closedBall z₀ R, ‖chartPhaseVF (I := I) g α x‖ ≤ Mb) :
    ∀ v ∈ S, ∀ s ∈ Set.Icc (0:ℝ) ((R - ρ) / Mb),
      Φ (z v, s) ∈ Metric.closedBall z₀ R := by
  intro v hv s hs
  have hdivlt : (R - ρ) / Mb < T_f := by rw [div_lt_iff₀ hMpos]; linarith [hRMT]
  have hmin : min T_f ((R - ρ) / Mb) = (R - ρ) / Mb := min_eq_right (le_of_lt hdivlt)
  have hconf := orbit_speed_confined_fwd g α (c := fun τ => Φ (z v, τ)) (z₀ := z₀)
    (R := R) (ρ := ρ) (T_f := T_f) hMpos hRρ hρ_nonneg hT_f
    (by show dist (Φ (z v, 0)) z₀ ≤ ρ; rw [hΦinit v hv]; exact hz_ball v hv)
    (fun s' hs' => by
      rw [hmin] at hs'
      have hs'_Ioo : s' ∈ Set.Ioo (-T_f) T_f :=
        ⟨by linarith [hs'.1], lt_of_le_of_lt hs'.2 hdivlt⟩
      exact (hΦ_phase v hv s' hs'_Ioo).hasDerivWithinAt)
    hM
  rw [hmin] at hconf
  exact hconf s hs

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem flowOrbit_cutoff_confined_explicit
    (g : SmoothRiemannianMetric I M) (α : M)
    {orbit : ℝ → E × E} {z₀ z_c : E × E} (b : ContDiffBump z₀) {ρ Mb εPL : ℝ}
    (hMpos : 0 < Mb) (hρ_nonneg : 0 ≤ ρ) (hρ_lt : ρ < b.rIn) (hεPL : 0 < εPL)
    (hzc : dist z_c z₀ ≤ ρ) (horbit0 : orbit 0 = z_c)
    (hderiv : ∀ s ∈ Set.Icc (0:ℝ) (min εPL ((b.rIn - ρ) / Mb)),
      HasDerivWithinAt orbit
        (chartPhaseVFTime (I := I) g α z₀ b s (orbit s))
        (Set.Icc 0 (min εPL ((b.rIn - ρ) / Mb))) s)
    (hM : ∀ x ∈ Metric.closedBall z₀ b.rIn, ‖chartPhaseVF (I := I) g α x‖ ≤ Mb) :
    ∀ s ∈ Set.Icc (0:ℝ) (min εPL ((b.rIn - ρ) / Mb)),
      orbit s ∈ Metric.closedBall z₀ b.rIn := by
  set T'' : ℝ := min εPL ((b.rIn - ρ) / Mb) with hT''_def
  have hT''_pos : 0 < T'' := lt_min hεPL (div_pos (by linarith) hMpos)
  have hMT'' : Mb * T'' ≤ b.rIn - ρ := by
    calc Mb * T'' ≤ Mb * ((b.rIn - ρ) / Mb) := by
          apply mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hMpos)
      _ = b.rIn - ρ := by field_simp
  have hbound : ∀ s ∈ Set.Icc (0:ℝ) T'', dist (orbit s) z_c ≤ b.rIn - ρ →
      ‖chartPhaseVFTime (I := I) g α z₀ b s (orbit s)‖ ≤ Mb := by
    intro s _ hds
    have hin : orbit s ∈ Metric.closedBall z₀ b.rIn := by
      rw [Metric.mem_closedBall]
      calc dist (orbit s) z₀ ≤ dist (orbit s) z_c + dist z_c z₀ := dist_triangle _ _ _
        _ ≤ (b.rIn - ρ) + ρ := by linarith [hds, hzc]
        _ = b.rIn := by ring
    have heq : chartPhaseVFTime (I := I) g α z₀ b s (orbit s) =
        chartPhaseVF (I := I) g α (orbit s) := by
      rw [chartPhaseVFTime_apply]
      exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α z₀ b hin
    rw [heq]; exact hM (orbit s) hin
  have hkey := dist_le_of_speed_bound_on_Icc
    (c := orbit) (c' := fun s => chartPhaseVFTime (I := I) g α z₀ b s (orbit s))
    (z₀ := z_c) (R := b.rIn - ρ) (M := Mb) (T'' := T'')
    hMpos hMT'' hT''_pos horbit0 hderiv hbound
  intro s hs
  rw [Metric.mem_closedBall]
  have hMs : Mb * s ≤ b.rIn - ρ :=
    le_trans (mul_le_mul_of_nonneg_left hs.2 (le_of_lt hMpos)) hMT''
  calc dist (orbit s) z₀ ≤ dist (orbit s) z_c + dist z_c z₀ := dist_triangle _ _ _
    _ ≤ (b.rIn - ρ) + ρ := by linarith [hkey s hs, hzc, hMs]
    _ = b.rIn := by ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem flowOrbit_cutoff_confined_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    {orbit : ℝ → E × E} {z₀ z_c : E × E} (b : ContDiffBump z₀) {ρ Mb εPL : ℝ}
    (hMpos : 0 < Mb) (hρ_nonneg : 0 ≤ ρ) (hρ_lt : ρ < b.rIn) (hεPL : 0 < εPL)
    (hRMT : b.rIn - ρ < Mb * εPL)
    (hzc : dist z_c z₀ ≤ ρ) (horbit0 : orbit 0 = z_c)
    (hderiv : ∀ s ∈ Set.Ioo (-εPL) εPL,
      HasDerivAt orbit (chartPhaseVFTime (I := I) g α z₀ b s (orbit s)) s)
    (hM : ∀ x ∈ Metric.closedBall z₀ b.rIn, ‖chartPhaseVF (I := I) g α x‖ ≤ Mb) :
    ∀ s ∈ Set.Ioo (-((b.rIn - ρ) / Mb)) ((b.rIn - ρ) / Mb),
      orbit s ∈ Metric.closedBall z₀ b.rIn := by
  have hdivlt : (b.rIn - ρ) / Mb < εPL := by rw [div_lt_iff₀ hMpos]; linarith [hRMT]
  have hmin : min εPL ((b.rIn - ρ) / Mb) = (b.rIn - ρ) / Mb :=
    min_eq_right (le_of_lt hdivlt)
  set T' : ℝ := (b.rIn - ρ) / Mb with hT'_def
  have hT'_pos : 0 < T' := div_pos (by linarith) hMpos
  have hMT' : Mb * T' ≤ b.rIn - ρ := le_of_eq (by rw [hT'_def]; field_simp)
  have hfwd : ∀ s ∈ Set.Icc (0:ℝ) T', orbit s ∈ Metric.closedBall z₀ b.rIn := by
    have h := flowOrbit_cutoff_confined_explicit g α b hMpos hρ_nonneg hρ_lt hεPL hzc
      horbit0
      (by
        rw [hmin]
        intro s hs
        exact (hderiv s ⟨by linarith [hs.1, hεPL], by linarith [hs.2, hdivlt]⟩).hasDerivWithinAt)
      hM
    rw [hmin] at h; exact h
  have hbwd : ∀ u ∈ Set.Icc (0:ℝ) T', orbit (-u) ∈ Metric.closedBall z₀ b.rIn := by
    have hkey := dist_le_of_speed_bound_on_Icc
      (c := fun u => orbit (-u))
      (c' := fun u => -(chartPhaseVFTime (I := I) g α z₀ b (-u) (orbit (-u))))
      (z₀ := z_c) (R := b.rIn - ρ) (M := Mb) (T'' := T') hMpos hMT' hT'_pos
      (by simp only [neg_zero]; exact horbit0)
      (fun u hu => by
        have hu_Ioo : -u ∈ Set.Ioo (-εPL) εPL :=
          ⟨by linarith [hu.2, hdivlt], by linarith [hu.1, hεPL]⟩
        simpa using ((hderiv (-u) hu_Ioo).scomp u ((hasDerivAt_id u).neg)).hasDerivWithinAt)
      (fun u _ hds => by
        have hin : orbit (-u) ∈ Metric.closedBall z₀ b.rIn := by
          rw [Metric.mem_closedBall]
          calc dist (orbit (-u)) z₀ ≤ dist (orbit (-u)) z_c + dist z_c z₀ :=
                dist_triangle _ _ _
            _ ≤ (b.rIn - ρ) + ρ := by linarith [hds, hzc]
            _ = b.rIn := by ring
        rw [norm_neg]
        have heq : chartPhaseVFTime (I := I) g α z₀ b (-u) (orbit (-u)) =
            chartPhaseVF (I := I) g α (orbit (-u)) := by
          rw [chartPhaseVFTime_apply]
          exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α z₀ b hin
        rw [heq]; exact hM (orbit (-u)) hin)
    intro u hu
    rw [Metric.mem_closedBall]
    have hMu : Mb * u ≤ b.rIn - ρ :=
      le_trans (mul_le_mul_of_nonneg_left hu.2 (le_of_lt hMpos)) hMT'
    calc dist (orbit (-u)) z₀ ≤ dist (orbit (-u)) z_c + dist z_c z₀ := dist_triangle _ _ _
      _ ≤ (b.rIn - ρ) + ρ := by linarith [hkey u hu, hzc, hMu]
      _ = b.rIn := by ring
  intro s hs
  by_cases hs0 : (0:ℝ) ≤ s
  · exact hfwd s ⟨hs0, le_of_lt hs.2⟩
  · push_neg at hs0
    have hneg := hbwd (-s) ⟨by linarith, by linarith [hs.1]⟩
    rwa [neg_neg] at hneg

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [NormedSpace ℝ E] [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem flowOrbit_uniform_confinement
    {N : Type*} [TopologicalSpace N]
    {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {ρ_f T_f : ℝ}
    {z : N → E × E} {v₀ : N} {W : Set (E × E)}
    (hρ_f : 0 < ρ_f) (hT_f : 0 < T_f)
    (hΦ : ContinuousOn Φ ((Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f))
    (hΦ0 : Φ (z₀, 0) = z₀)
    (hz_cont : ContinuousAt z v₀) (hz0 : z v₀ = z₀)
    (hW : W ∈ 𝓝 z₀) :
    ∃ (S : Set N) (T' : ℝ), IsOpen S ∧ v₀ ∈ S ∧ 0 < T' ∧ T' < T_f ∧
      (∀ v ∈ S, z v ∈ Metric.ball z₀ ρ_f) ∧
      (∀ v ∈ S, ∀ s ∈ Set.Ioo (-T') T', Φ (z v, s) ∈ W) := by
  classical
  have h_open : IsOpen ((Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hz₀0_mem : ((z₀, (0 : ℝ)) : (E × E) × ℝ) ∈
      (Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f :=
    ⟨Metric.mem_ball_self hρ_f, ⟨by linarith, hT_f⟩⟩
  have hΦ_contAt : ContinuousAt Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ) :=
    hΦ.continuousAt (h_open.mem_nhds hz₀0_mem)
  have hpair_contAt : ContinuousAt (fun ws : N × ℝ => ((z ws.1, ws.2) : (E × E) × ℝ))
      ((v₀, (0 : ℝ)) : N × ℝ) :=
    (hz_cont.comp continuousAt_fst).prodMk continuousAt_snd
  have hΨ_contAt : ContinuousAt (fun ws : N × ℝ => Φ ((z ws.1, ws.2) : (E × E) × ℝ))
      ((v₀, (0 : ℝ)) : N × ℝ) := by
    have hval : ((z v₀, (0 : ℝ)) : (E × E) × ℝ) = ((z₀, (0 : ℝ)) : (E × E) × ℝ) := by
      rw [hz0]
    refine ContinuousAt.comp ?_ hpair_contAt
    rw [hval]; exact hΦ_contAt
  have hW_nhds : W ∈ 𝓝 (Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ)) := by rw [hΦ0]; exact hW
  have h_orbit_preim : (fun ws : N × ℝ => Φ ((z ws.1, ws.2) : (E × E) × ℝ)) ⁻¹' W ∈
      𝓝 ((v₀, (0 : ℝ)) : N × ℝ) := by
    apply hΨ_contAt.preimage_mem_nhds
    have hval : Φ ((z v₀, (0 : ℝ)) : (E × E) × ℝ) = Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ) := by
      rw [hz0]
    rw [hval]; exact hW_nhds
  have hz_preim : z ⁻¹' (Metric.ball z₀ ρ_f) ∈ 𝓝 v₀ := by
    apply hz_cont.preimage_mem_nhds
    rw [hz0]; exact Metric.ball_mem_nhds _ hρ_f
  obtain ⟨S₁, V₁, hS₁_open, hS₁_mem, hV₁_open, hV₁_mem, h_sub⟩ :=
    mem_nhds_prod_iff'.mp h_orbit_preim
  obtain ⟨S₂, hS₂_sub, hS₂_open, hv₀_S₂⟩ := _root_.mem_nhds_iff.mp hz_preim
  set S : Set N := S₁ ∩ S₂ with hS_def
  have hS_open : IsOpen S := hS₁_open.inter hS₂_open
  have hv₀_S : v₀ ∈ S := ⟨hS₁_mem, hv₀_S₂⟩
  obtain ⟨T₀, hT₀_pos, hT₀_sub⟩ := Metric.isOpen_iff.mp hV₁_open (0 : ℝ) hV₁_mem
  set T' : ℝ := min T₀ T_f / 2 with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]; have : 0 < min T₀ T_f := lt_min hT₀_pos hT_f; linarith
  have hT'_lt_Tf : T' < T_f := by
    rw [hT'_def]; have h1 : min T₀ T_f ≤ T_f := min_le_right _ _; linarith
  have hT'_lt_T₀ : T' < T₀ := by
    rw [hT'_def]; have h1 : min T₀ T_f ≤ T₀ := min_le_left _ _; linarith
  have hIoo_sub_V₁ : Set.Ioo (-T') T' ⊆ V₁ := by
    intro s hs
    apply hT₀_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨S, T', hS_open, hv₀_S, hT'_pos, hT'_lt_Tf, ?_, ?_⟩
  · intro v hv
    exact hS₂_sub hv.2
  · intro v hv s hs
    have hv_S₁ : v ∈ S₁ := hv.1
    have hs_V₁ : s ∈ V₁ := hIoo_sub_V₁ hs
    have hpair : (v, s) ∈ S₁ ×ˢ V₁ := ⟨hv_S₁, hs_V₁⟩
    exact h_sub hpair

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem geodesic_chartPhaseVF_on_open
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (hγ_cont : Continuous γ)
    {U : Set ℝ} (hU_open : IsOpen U)
    (hγ_src : ∀ s ∈ U, γ s ∈ (chartAt H α).source) :
    ∀ s ∈ U,
      HasDerivAt
        (fun r : ℝ =>
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ r,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ) r) : E × E))
        (chartPhaseVF (I := I) g α
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ s,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ) s) : E × E)) s ∧
      (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ s)
        ∈ interior (extChartAt I α).target := by
  classical
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
    with hw_def
  intro s hs
  have hsU_nhds : U ∈ 𝓝 s := hU_open.mem_nhds hs
  have hs_src : γ s ∈ (chartAt H α).source := hγ_src s hs
  have hev_first : ∀ᶠ r in 𝓝 s, HasDerivAt w (deriv w r) r :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt
      (I := I) g α hγ_cont.continuousAt hs_src (hγ s)
  have hfirst : HasDerivAt w (deriv w s) s := hev_first.self_of_nhds
  have hsecond : HasDerivAt (deriv w)
      (- chartChristoffelContraction (I := I) g α (deriv w s) (deriv w s) (w s)) s :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity
      (I := I) g α hγ_cont.continuousAt hs_src (hγ s)
  refine ⟨?_, ?_⟩
  · have hpair : HasDerivAt
        (fun r : ℝ => (w r, deriv w r))
        ((deriv w s,
          - chartChristoffelContraction (I := I) g α (deriv w s) (deriv w s) (w s))) s :=
      hfirst.prodMk hsecond
    have hrhs : chartPhaseVF (I := I) g α (w s, deriv w s) =
        (deriv w s,
          - chartChristoffelContraction (I := I) g α (deriv w s) (deriv w s) (w s)) := by
      simp only [chartPhaseVF_apply]
    rw [hrhs]; exact hpair
  · have hp_ext_src : γ s ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs_src
    have hp_target : extChartAt I α (γ s) ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hp_ext_src
    have hval : w s = extChartAt I α (γ s) := by simp [hw_def]
    rw [hval]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hp_target

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem perJunction_flowIdentification
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E}
    {z : TangentSpace I p → E × E}
    {tₖ r R T' : ℝ}
    (hT'_pos : 0 < T')
    (hball : Metric.closedBall z₀ R ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s)
    (hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall z₀ R)
    (hgeo_src : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source)
    (hgeo_in : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
        ∈ Metric.closedBall z₀ R)
    (hinit : ∀ v ∈ Metric.ball v₀ r,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)
    (hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v) :
    ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      intrinsicGeodesic (I := I) g hEnorm p v t =
        flowProj (I := I) α Φ (z v) (t - tₖ) := by
  classical
  intro v hv t ht
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_geo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
    with hw_def
  set c₁ : ℝ → E × E := fun s => (w (tₖ + s), deriv w (tₖ + s)) with hc₁_def
  set c₂ : ℝ → E × E := fun s => Φ (z v, s) with hc₂_def
  set U : Set ℝ := Set.Ioo (tₖ - T') (tₖ + T') with hU_def
  have hU_open : IsOpen U := isOpen_Ioo
  have hsrc_U : ∀ s ∈ U, γ s ∈ (chartAt H α).source := by
    intro s hsU; exact hgeo_src v hv s hsU
  have hgeo_phase := geodesic_chartPhaseVF_on_open (I := I) (g := g) (α := α) (γ := γ)
    hγ_geo hγ_cont hU_open hsrc_U
  have hc₁_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s := by
    intro s hs
    have htks : tₖ + s ∈ U := by
      rw [hU_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    obtain ⟨hder, _⟩ := hgeo_phase (tₖ + s) htks
    have hshift : HasDerivAt (fun r : ℝ => tₖ + r) 1 s := by
      simpa using (hasDerivAt_id s).const_add tₖ
    have hcomp := hder.scomp s hshift
    simp only [one_smul] at hcomp
    have hfun : ((fun r : ℝ => ((w r, deriv w r) : E × E)) ∘ fun r : ℝ => tₖ + r) = c₁ := by
      funext r; simp only [Function.comp_apply, hc₁_def]
    rw [hfun] at hcomp
    have hrhs : c₁ s = ((w (tₖ + s), deriv w (tₖ + s)) : E × E) := by rw [hc₁_def]
    rw [hrhs]; exact hcomp
  have hc₂_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s := by
    intro s hs; exact hΦ_phase v hv s hs
  have hc₁_in : ∀ s ∈ Set.Ioo (-T') T', c₁ s ∈ Metric.closedBall z₀ R := by
    intro s hs
    have htks : tₖ + s ∈ U := by
      rw [hU_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := hgeo_in v hv (tₖ + s) htks
    rw [hc₁_def]; exact this
  have hc₂_in : ∀ s ∈ Set.Ioo (-T') T', c₂ s ∈ Metric.closedBall z₀ R := by
    intro s hs; exact hΦ_in v hv s hs
  have hc₁_zero : c₁ 0 = z v := by
    rw [hc₁_def]; simp only [add_zero]; exact hinit v hv
  have hc₂_zero : c₂ 0 = z v := by rw [hc₂_def]; exact hΦinit v hv
  have hmatch : c₁ 0 = c₂ 0 := by rw [hc₁_zero, hc₂_zero]
  have heq : ∀ s ∈ Set.Ioo (-T') T', c₁ s = c₂ s :=
    chartPhaseVF_orbit_uniqueness_uniform_Ioo_closedBall (I := I) g α
      hball hT'_pos hc₁_phase hc₂_phase hc₁_in hc₂_in hmatch
  have hs_mem : (t - tₖ) ∈ Set.Ioo (-T') T' := by
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · have := ht.1; rw [Set.mem_Ioo] at ht; linarith [ht.1]
    · rw [Set.mem_Ioo] at ht; linarith [ht.2]
  have hfst := congrArg Prod.fst (heq (t - tₖ) hs_mem)
  have hc₁_fst : (c₁ (t - tₖ)).1 = extChartAt I α (γ t) := by
    rw [hc₁_def]
    simp only []
    rw [show tₖ + (t - tₖ) = t by ring, hw_def]
    simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
  have hc₂_fst : (c₂ (t - tₖ)).1 = (Φ (z v, t - tₖ)).1 := by rw [hc₂_def]
  rw [hc₁_fst, hc₂_fst] at hfst
  have hγ_es : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hsrc_U t ht
  have hsymm : (extChartAt I α).symm (extChartAt I α (γ t)) = γ t :=
    (extChartAt I α).left_inv hγ_es
  rw [flowProj, ← hfst, hsymm]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem perJunction_phaseIdentification
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E}
    {z : TangentSpace I p → E × E}
    {tₖ r R T' : ℝ}
    (hT'_pos : 0 < T')
    (hball : Metric.closedBall z₀ R ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s)
    (hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall z₀ R)
    (hgeo_src : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source)
    (hgeo_in : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
        ∈ Metric.closedBall z₀ R)
    (hinit : ∀ v ∈ Metric.ball v₀ r,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)
    (hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v) :
    ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E) =
        Φ (z v, t - tₖ) := by
  classical
  intro v hv t ht
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_geo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
    with hw_def
  set c₁ : ℝ → E × E := fun s => (w (tₖ + s), deriv w (tₖ + s)) with hc₁_def
  set c₂ : ℝ → E × E := fun s => Φ (z v, s) with hc₂_def
  set U : Set ℝ := Set.Ioo (tₖ - T') (tₖ + T') with hU_def
  have hU_open : IsOpen U := isOpen_Ioo
  have hsrc_U : ∀ s ∈ U, γ s ∈ (chartAt H α).source := by
    intro s hsU; exact hgeo_src v hv s hsU
  have hgeo_phase := geodesic_chartPhaseVF_on_open (I := I) (g := g) (α := α) (γ := γ)
    hγ_geo hγ_cont hU_open hsrc_U
  have hc₁_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s := by
    intro s hs
    have htks : tₖ + s ∈ U := by
      rw [hU_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    obtain ⟨hder, _⟩ := hgeo_phase (tₖ + s) htks
    have hshift : HasDerivAt (fun r : ℝ => tₖ + r) 1 s := by
      simpa using (hasDerivAt_id s).const_add tₖ
    have hcomp := hder.scomp s hshift
    simp only [one_smul] at hcomp
    have hfun : ((fun r : ℝ => ((w r, deriv w r) : E × E)) ∘ fun r : ℝ => tₖ + r) = c₁ := by
      funext r; simp only [Function.comp_apply, hc₁_def]
    rw [hfun] at hcomp
    have hrhs : c₁ s = ((w (tₖ + s), deriv w (tₖ + s)) : E × E) := by rw [hc₁_def]
    rw [hrhs]; exact hcomp
  have hc₂_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s := by
    intro s hs; exact hΦ_phase v hv s hs
  have hc₁_in : ∀ s ∈ Set.Ioo (-T') T', c₁ s ∈ Metric.closedBall z₀ R := by
    intro s hs
    have htks : tₖ + s ∈ U := by
      rw [hU_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := hgeo_in v hv (tₖ + s) htks
    rw [hc₁_def]; exact this
  have hc₂_in : ∀ s ∈ Set.Ioo (-T') T', c₂ s ∈ Metric.closedBall z₀ R := by
    intro s hs; exact hΦ_in v hv s hs
  have hc₁_zero : c₁ 0 = z v := by
    rw [hc₁_def]; simp only [add_zero]; exact hinit v hv
  have hc₂_zero : c₂ 0 = z v := by rw [hc₂_def]; exact hΦinit v hv
  have hmatch : c₁ 0 = c₂ 0 := by rw [hc₁_zero, hc₂_zero]
  have heq : ∀ s ∈ Set.Ioo (-T') T', c₁ s = c₂ s :=
    chartPhaseVF_orbit_uniqueness_uniform_Ioo_closedBall (I := I) g α
      hball hT'_pos hc₁_phase hc₂_phase hc₁_in hc₂_in hmatch
  have hs_mem : (t - tₖ) ∈ Set.Ioo (-T') T' := by
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · have := ht.1; rw [Set.mem_Ioo] at ht; linarith [ht.1]
    · rw [Set.mem_Ioo] at ht; linarith [ht.2]
  have hpair := heq (t - tₖ) hs_mem
  have hc₁_eval : c₁ (t - tₖ) =
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ) t)
        : E × E) := by
    rw [hc₁_def]
    simp only []
    rw [show tₖ + (t - tₖ) = t by ring, hw_def]
  have hc₂_eval : c₂ (t - tₖ) = Φ (z v, t - tₖ) := by rw [hc₂_def]
  rw [hc₁_eval, hc₂_eval] at hpair
  exact hpair

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicGeodesic_window_of_junction_data
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    (α : M) {x₀ w₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target)
    {z : TangentSpace I p → E × E} {tₖ : ℝ} {rz : ℝ} (hrz : 0 < rz)
    (hz_cont : ContinuousOn z (Metric.ball v₀ rz)) (hz0 : z v₀ = (x₀, w₀))
    (hgeo : ∀ (b : ContDiffBump ((x₀, w₀) : E × E)),
      Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) →
      ∃ rgeo εgeo : ℝ, 0 < rgeo ∧ 0 < εgeo ∧ rgeo ≤ rz ∧
      (∀ v ∈ Metric.ball v₀ rgeo, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ t ∈ Set.Ioo (tₖ - εgeo) (tₖ + εgeo),
        intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ t ∈ Set.Ioo (tₖ - εgeo) (tₖ + εgeo),
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) t,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
          ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo,
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) := by
  classical
  obtain ⟨b, rPL, εPL, ρΦ, TΦ, Φ, hrPL, hεPL, hρΦ, hTΦ, hb_sub, hΦ_loc, hΦ_C1,
      hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined (I := I) (M := M)
      (g := g) (α := α) (x₀ := x₀) (v₀ := w₀) hx₀
  have hΦ_cont : ContinuousOn Φ
      ((Metric.ball ((x₀, w₀) : E × E) ρΦ) ×ˢ Set.Ioo (-TΦ) TΦ) :=
    hΦ_C1.continuousOn
  have hrPL_pos : (0 : ℝ) < (rPL : ℝ) := by exact_mod_cast hrPL
  set ρf : ℝ := min ρΦ (rPL : ℝ) with hρf_def
  have hρf_pos : 0 < ρf := lt_min hρΦ hrPL_pos
  have hρf_le_ρΦ : ρf ≤ ρΦ := min_le_left _ _
  have hρf_le_rPL : ρf ≤ (rPL : ℝ) := min_le_right _ _
  set Tcap : ℝ := min TΦ εPL with hTcap_def
  have hTcap_pos : 0 < Tcap := lt_min hTΦ hεPL
  have hTcap_le_TΦ : Tcap ≤ TΦ := min_le_left _ _
  have hTcap_le_εPL : Tcap ≤ εPL := min_le_right _ _
  have hΦ_cont' : ContinuousOn Φ
      ((Metric.ball ((x₀, w₀) : E × E) ρf) ×ˢ Set.Ioo (-Tcap) Tcap) :=
    hΦ_cont.mono (Set.prod_mono (Metric.ball_subset_ball hρf_le_ρΦ)
      (Set.Ioo_subset_Ioo (by linarith [hTcap_le_TΦ]) hTcap_le_TΦ))
  have hz_contAt : ContinuousAt z v₀ :=
    hz_cont.continuousAt (Metric.ball_mem_nhds _ hrz)
  have hW_nhds : Metric.ball ((x₀, w₀) : E × E) b.rIn ∈ 𝓝 ((x₀, w₀) : E × E) :=
    Metric.ball_mem_nhds _ b.rIn_pos
  obtain ⟨S, T', hS_open, hv₀_S, hT'_pos, hT'_lt_Tcap, hz_ball_S, horbit_in⟩ :=
    flowOrbit_uniform_confinement (Φ := Φ) (z₀ := (x₀, w₀)) (ρ_f := ρf) (T_f := Tcap)
      (z := z) (v₀ := v₀) (W := Metric.ball ((x₀, w₀) : E × E) b.rIn)
      hρf_pos hTcap_pos hΦ_cont' hΦ_init0 hz_contAt hz0 hW_nhds
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hS_open v₀ hv₀_S
  set r : ℝ := min r₀ rz with hr_def
  have hr_pos : 0 < r := lt_min hr₀_pos hrz
  have hr_le_r₀ : r ≤ r₀ := min_le_left _ _
  have hr_le_rz : r ≤ rz := min_le_right _ _
  have hr_sub : Metric.ball v₀ r ⊆ S :=
    subset_trans (Metric.ball_subset_ball hr_le_r₀) hr₀_sub
  have hrIn_le_rOut : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
  have hballIn_sub_target : Metric.closedBall ((x₀, w₀) : E × E) b.rIn ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
    subset_trans (Metric.closedBall_subset_closedBall hrIn_le_rOut) hb_sub
  have hz_ball_ρf : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball ((x₀, w₀) : E × E) ρf :=
    fun v hv => hz_ball_S v (hr_sub hv)
  have hz_ball_r : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball ((x₀, w₀) : E × E) ρΦ :=
    fun v hv => Metric.ball_subset_ball hρf_le_ρΦ (hz_ball_ρf v hv)
  have hz_PL : ∀ v ∈ Metric.ball v₀ r,
      z v ∈ Metric.closedBall ((x₀, w₀) : E × E) rPL := by
    intro v hv
    have := hz_ball_ρf v hv
    rw [Metric.mem_ball] at this
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le this hρf_le_rPL)
  have hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v := by
    intro v hv
    exact hΦ_loc.apply_initial (z v) (hz_PL v hv)
  have hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn := by
    intro v hv s hs
    exact Metric.ball_subset_closedBall (horbit_in v (hr_sub hv) s hs)
  have hz_ball_rIn : ∀ v ∈ Metric.ball v₀ r,
      z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn := by
    intro v hv
    have h0 : (0 : ℝ) ∈ Set.Ioo (-T') T' := ⟨by linarith, hT'_pos⟩
    have := horbit_in v (hr_sub hv) 0 h0
    rwa [hΦinit v hv] at this
  have hT'_le_εPL : T' ≤ εPL := le_of_lt (lt_of_lt_of_le hT'_lt_Tcap hTcap_le_εPL)
  have hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s := by
    intro v hv s hs
    have hs_Icc : s ∈ Set.Icc (-εPL) εPL := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [hs.1, hT'_le_εPL], by linarith [hs.2, hT'_le_εPL]⟩
    have hd := hΦ_loc.hasDerivWithinAt (z v) (hz_PL v hv) s hs_Icc
    have hIoo_nhds : Set.Ioo (-εPL) εPL ∈ 𝓝 s := by
      apply isOpen_Ioo.mem_nhds
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hs.1, hT'_le_εPL], by linarith [hs.2, hT'_le_εPL]⟩
    have hIcc_nhds : Set.Icc (-εPL) εPL ∈ 𝓝 s :=
      Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
    have hd' : HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVFTime (I := I) g α (x₀, w₀) b s (Φ (z v, s))) s :=
      hd.hasDerivAt hIcc_nhds
    have horbit_inner : Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
      hΦ_in v hv s hs
    have hcutoff_eq :
        chartPhaseVFTime (I := I) g α (x₀, w₀) b s (Φ (z v, s)) =
          chartPhaseVF (I := I) g α (Φ (z v, s)) := by
      rw [chartPhaseVFTime_apply]
      exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α (x₀, w₀) b horbit_inner
    rwa [hcutoff_eq] at hd'
  obtain ⟨rgeo, εgeo, hrgeo_pos, hεgeo_pos, _hrgeo_le, _hz_geo, hgeo_src0, hgeo_in0,
      hinit0⟩ := hgeo b hb_sub
  set rfin : ℝ := min r rgeo with hrfin_def
  have hrfin_pos : 0 < rfin := lt_min hr_pos hrgeo_pos
  have hrfin_le_r : rfin ≤ r := min_le_left _ _
  have hrfin_le_rgeo : rfin ≤ rgeo := min_le_right _ _
  set Tfin : ℝ := min T' εgeo with hTfin_def
  have hTfin_pos : 0 < Tfin := lt_min hT'_pos hεgeo_pos
  have hTfin_le_T' : Tfin ≤ T' := min_le_left _ _
  have hTfin_le_εgeo : Tfin ≤ εgeo := min_le_right _ _
  have hball_sub : Metric.ball v₀ rfin ⊆ Metric.ball v₀ r :=
    Metric.ball_subset_ball hrfin_le_r
  have hball_sub_geo : Metric.ball v₀ rfin ⊆ Metric.ball v₀ rgeo :=
    Metric.ball_subset_ball hrfin_le_rgeo
  have hIoo_sub : Set.Ioo (-Tfin) Tfin ⊆ Set.Ioo (-T') T' :=
    Set.Ioo_subset_Ioo (by linarith) hTfin_le_T'
  have hIoo_sub_geo : ∀ s, s ∈ Set.Ioo (tₖ - Tfin) (tₖ + Tfin) →
      s ∈ Set.Ioo (tₖ - εgeo) (tₖ + εgeo) := by
    intro s hs
    exact Set.Ioo_subset_Ioo (by linarith) (by linarith) hs
  have hΦ_phase' : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (-Tfin) Tfin,
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s :=
    fun v hv s hs => hΦ_phase v (hball_sub hv) s (hIoo_sub hs)
  have hΦ_in' : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (-Tfin) Tfin,
      Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
    fun v hv s hs => hΦ_in v (hball_sub hv) s (hIoo_sub hs)
  have hgeo_src : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (tₖ - Tfin) (tₖ + Tfin),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source :=
    fun v hv s hs => hgeo_src0 v (hball_sub_geo hv) s (hIoo_sub_geo s hs)
  have hgeo_in : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (tₖ - Tfin) (tₖ + Tfin),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) s,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E)
        ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
    fun v hv s hs => hgeo_in0 v (hball_sub_geo hv) s (hIoo_sub_geo s hs)
  have hinit : ∀ v ∈ Metric.ball v₀ rfin,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v :=
    fun v hv => hinit0 v (hball_sub_geo hv)
  have hΦinit' : ∀ v ∈ Metric.ball v₀ rfin, Φ (z v, 0) = z v :=
    fun v hv => hΦinit v (hball_sub hv)
  have hident := perJunction_flowIdentification (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := (x₀, w₀)) (z := z) (tₖ := tₖ) (r := rfin) (R := b.rIn)
    (T' := Tfin) hTfin_pos hballIn_sub_target hΦ_phase' hΦ_in' hgeo_src hgeo_in hinit
    hΦinit'
  refine ⟨rfin, Tfin, hrfin_pos, hTfin_pos, ?_⟩
  have htgt : ∀ v ∈ Metric.ball v₀ rfin, ∀ τ ∈ Set.Ioo (-Tfin) Tfin,
      (Φ (z v, τ)).1 ∈ (extChartAt I α).target := by
    intro v hv τ hτ
    have hin := hΦ_in' v hv τ hτ
    have := hballIn_sub_target hin
    exact interior_subset this.1
  have hz_cont_r : ContinuousOn z (Metric.ball v₀ rfin) :=
    hz_cont.mono (Metric.ball_subset_ball (le_trans hrfin_le_r hr_le_rz))
  have hz_ball_rfin : ∀ v ∈ Metric.ball v₀ rfin,
      z v ∈ Metric.ball ((x₀, w₀) : E × E) ρΦ :=
    fun v hv => hz_ball_r v (hball_sub hv)
  exact perChart_jointContinuity_of_flowIdentifiedOn (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := (x₀, w₀)) (z := z) (tₖ := tₖ) (ε := Tfin) (r := rfin)
    (ρ := ρΦ) (T := TΦ) (le_of_lt (lt_of_lt_of_le
      (lt_of_le_of_lt hTfin_le_T' hT'_lt_Tcap) hTcap_le_TΦ))
    hΦ_cont hz_cont_r hz_ball_rfin htgt hident

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

private def intrinsicVelocityLift
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (s : ℝ) : TangentBundle I M :=
  ⟨intrinsicGeodesic (I := I) g hEnorm p v s,
    (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) s : ℝ →L[ℝ] _) (1 : ℝ)⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicVelocityLift_proj
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (s : ℝ) :
    (intrinsicVelocityLift (I := I) g hEnorm p v s).proj =
      intrinsicGeodesic (I := I) g hEnorm p v s := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem chartFiberCoord_intrinsicVelocityLift
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (α : M) (s : ℝ)
    (hs : intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α (intrinsicVelocityLift (I := I) g hEnorm p v s) =
      deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
        (intrinsicGeodesic (I := I) g hEnorm p v)) s := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := by
    have hcm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ Set.univ :=
      intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v
    have hcmAt : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ s :=
      (hcm s (Set.mem_univ s)).contMDiffAt Filter.univ_mem
    exact hcmAt.mdifferentiableAt (by norm_num)
  have hfiber :
      chartFiberCoord (I := I) α (intrinsicVelocityLift (I := I) g hEnorm p v s) =
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
          ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) := by
    have hbase : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hs
    have hcoe :=
      (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem (R := ℝ) hbase
    rw [chartFiberCoord_def]
    change (trivializationAt E (TangentSpace I) α
      (intrinsicVelocityLift (I := I) g hEnorm p v s)).2 = _
    have hsnd : (trivializationAt E (TangentSpace I) α
        (intrinsicVelocityLift (I := I) g hEnorm p v s)).2 =
        (trivializationAt E (TangentSpace I) α).linearMapAt ℝ (γ s)
          ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) := by
      have := congrFun hcoe ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ))
      exact this.symm
    rw [hsnd]
    rfl
  rw [hfiber]
  rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    (I := I) (M := M) (γ := γ) hγ_mdiff α hs]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem phasePoint_eq_extChartAt_tangent_intrinsicVelocityLift
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (α : M) (s : ℝ)
    (hs : intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source) :
    ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
        (intrinsicGeodesic (I := I) g hEnorm p v) s,
      deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
        (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E) =
      extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (intrinsicVelocityLift (I := I) g hEnorm p v s) := by
  classical
  have hproj : (intrinsicVelocityLift (I := I) g hEnorm p v s).proj ∈
      (chartAt H α).source := hs
  rw [extChartAt_tangent_zero_apply (I := I) α hproj]
  refine Prod.ext ?_ ?_
  · simp only [intrinsicVelocityLift_proj,
      DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
  · have h := chartFiberCoord_intrinsicVelocityLift (I := I) g hEnorm p v α s hs
    rw [chartFiberCoord_def] at h
    rw [← h]
    have hsnd := extChartAt_tangent_apply_snd (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M))
      (p := intrinsicVelocityLift (I := I) g hEnorm p v s) hproj
    exact hsnd

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicVelocityLift_window_of_junction_data
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    (α : M) {x₀ w₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target)
    {z : TangentSpace I p → E × E} {tₖ : ℝ} {rz : ℝ} (hrz : 0 < rz)
    (hz_cont : ContinuousOn z (Metric.ball v₀ rz)) (hz0 : z v₀ = (x₀, w₀))
    (hgeo : ∀ (b : ContDiffBump ((x₀, w₀) : E × E)),
      Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) →
      ∃ rgeo εgeo : ℝ, 0 < rgeo ∧ 0 < εgeo ∧ rgeo ≤ rz ∧
      (∀ v ∈ Metric.ball v₀ rgeo, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ t ∈ Set.Ioo (tₖ - εgeo) (tₖ + εgeo),
        intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ t ∈ Set.Ioo (tₖ - εgeo) (tₖ + εgeo),
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) t,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
          ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo,
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicVelocityLift (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) := by
  classical
  obtain ⟨b, rPL, εPL, ρΦ, TΦ, Φ, hrPL, hεPL, hρΦ, hTΦ, hb_sub, hΦ_loc, hΦ_C1,
      hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined (I := I) (M := M)
      (g := g) (α := α) (x₀ := x₀) (v₀ := w₀) hx₀
  have hΦ_cont : ContinuousOn Φ
      ((Metric.ball ((x₀, w₀) : E × E) ρΦ) ×ˢ Set.Ioo (-TΦ) TΦ) :=
    hΦ_C1.continuousOn
  have hrPL_pos : (0 : ℝ) < (rPL : ℝ) := by exact_mod_cast hrPL
  set ρf : ℝ := min ρΦ (rPL : ℝ) with hρf_def
  have hρf_pos : 0 < ρf := lt_min hρΦ hrPL_pos
  have hρf_le_ρΦ : ρf ≤ ρΦ := min_le_left _ _
  have hρf_le_rPL : ρf ≤ (rPL : ℝ) := min_le_right _ _
  set Tcap : ℝ := min TΦ εPL with hTcap_def
  have hTcap_pos : 0 < Tcap := lt_min hTΦ hεPL
  have hTcap_le_TΦ : Tcap ≤ TΦ := min_le_left _ _
  have hTcap_le_εPL : Tcap ≤ εPL := min_le_right _ _
  have hΦ_cont' : ContinuousOn Φ
      ((Metric.ball ((x₀, w₀) : E × E) ρf) ×ˢ Set.Ioo (-Tcap) Tcap) :=
    hΦ_cont.mono (Set.prod_mono (Metric.ball_subset_ball hρf_le_ρΦ)
      (Set.Ioo_subset_Ioo (by linarith [hTcap_le_TΦ]) hTcap_le_TΦ))
  have hz_contAt : ContinuousAt z v₀ :=
    hz_cont.continuousAt (Metric.ball_mem_nhds _ hrz)
  have hW_nhds : Metric.ball ((x₀, w₀) : E × E) b.rIn ∈ 𝓝 ((x₀, w₀) : E × E) :=
    Metric.ball_mem_nhds _ b.rIn_pos
  obtain ⟨S, T', hS_open, hv₀_S, hT'_pos, hT'_lt_Tcap, hz_ball_S, horbit_in⟩ :=
    flowOrbit_uniform_confinement (Φ := Φ) (z₀ := (x₀, w₀)) (ρ_f := ρf) (T_f := Tcap)
      (z := z) (v₀ := v₀) (W := Metric.ball ((x₀, w₀) : E × E) b.rIn)
      hρf_pos hTcap_pos hΦ_cont' hΦ_init0 hz_contAt hz0 hW_nhds
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hS_open v₀ hv₀_S
  set r : ℝ := min r₀ rz with hr_def
  have hr_pos : 0 < r := lt_min hr₀_pos hrz
  have hr_le_r₀ : r ≤ r₀ := min_le_left _ _
  have hr_le_rz : r ≤ rz := min_le_right _ _
  have hr_sub : Metric.ball v₀ r ⊆ S :=
    subset_trans (Metric.ball_subset_ball hr_le_r₀) hr₀_sub
  have hrIn_le_rOut : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
  have hballIn_sub_target : Metric.closedBall ((x₀, w₀) : E × E) b.rIn ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
    subset_trans (Metric.closedBall_subset_closedBall hrIn_le_rOut) hb_sub
  have hz_ball_ρf : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball ((x₀, w₀) : E × E) ρf :=
    fun v hv => hz_ball_S v (hr_sub hv)
  have hz_ball_r : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball ((x₀, w₀) : E × E) ρΦ :=
    fun v hv => Metric.ball_subset_ball hρf_le_ρΦ (hz_ball_ρf v hv)
  have hz_PL : ∀ v ∈ Metric.ball v₀ r,
      z v ∈ Metric.closedBall ((x₀, w₀) : E × E) rPL := by
    intro v hv
    have := hz_ball_ρf v hv
    rw [Metric.mem_ball] at this
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le this hρf_le_rPL)
  have hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v := by
    intro v hv
    exact hΦ_loc.apply_initial (z v) (hz_PL v hv)
  have hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn := by
    intro v hv s hs
    exact Metric.ball_subset_closedBall (horbit_in v (hr_sub hv) s hs)
  have hz_ball_rIn : ∀ v ∈ Metric.ball v₀ r,
      z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn := by
    intro v hv
    have h0 : (0 : ℝ) ∈ Set.Ioo (-T') T' := ⟨by linarith, hT'_pos⟩
    have := horbit_in v (hr_sub hv) 0 h0
    rwa [hΦinit v hv] at this
  have hT'_le_εPL : T' ≤ εPL := le_of_lt (lt_of_lt_of_le hT'_lt_Tcap hTcap_le_εPL)
  have hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s := by
    intro v hv s hs
    have hs_Icc : s ∈ Set.Icc (-εPL) εPL := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [hs.1, hT'_le_εPL], by linarith [hs.2, hT'_le_εPL]⟩
    have hd := hΦ_loc.hasDerivWithinAt (z v) (hz_PL v hv) s hs_Icc
    have hIoo_nhds : Set.Ioo (-εPL) εPL ∈ 𝓝 s := by
      apply isOpen_Ioo.mem_nhds
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hs.1, hT'_le_εPL], by linarith [hs.2, hT'_le_εPL]⟩
    have hIcc_nhds : Set.Icc (-εPL) εPL ∈ 𝓝 s :=
      Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
    have hd' : HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVFTime (I := I) g α (x₀, w₀) b s (Φ (z v, s))) s :=
      hd.hasDerivAt hIcc_nhds
    have horbit_inner : Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
      hΦ_in v hv s hs
    have hcutoff_eq :
        chartPhaseVFTime (I := I) g α (x₀, w₀) b s (Φ (z v, s)) =
          chartPhaseVF (I := I) g α (Φ (z v, s)) := by
      rw [chartPhaseVFTime_apply]
      exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α (x₀, w₀) b horbit_inner
    rwa [hcutoff_eq] at hd'
  obtain ⟨rgeo, εgeo, hrgeo_pos, hεgeo_pos, _hrgeo_le, _hz_geo, hgeo_src0, hgeo_in0,
      hinit0⟩ := hgeo b hb_sub
  set rfin : ℝ := min r rgeo with hrfin_def
  have hrfin_pos : 0 < rfin := lt_min hr_pos hrgeo_pos
  have hrfin_le_r : rfin ≤ r := min_le_left _ _
  have hrfin_le_rgeo : rfin ≤ rgeo := min_le_right _ _
  set Tfin : ℝ := min T' εgeo with hTfin_def
  have hTfin_pos : 0 < Tfin := lt_min hT'_pos hεgeo_pos
  have hTfin_le_T' : Tfin ≤ T' := min_le_left _ _
  have hTfin_le_εgeo : Tfin ≤ εgeo := min_le_right _ _
  have hball_sub : Metric.ball v₀ rfin ⊆ Metric.ball v₀ r :=
    Metric.ball_subset_ball hrfin_le_r
  have hball_sub_geo : Metric.ball v₀ rfin ⊆ Metric.ball v₀ rgeo :=
    Metric.ball_subset_ball hrfin_le_rgeo
  have hIoo_sub : Set.Ioo (-Tfin) Tfin ⊆ Set.Ioo (-T') T' :=
    Set.Ioo_subset_Ioo (by linarith) hTfin_le_T'
  have hIoo_sub_geo : ∀ s, s ∈ Set.Ioo (tₖ - Tfin) (tₖ + Tfin) →
      s ∈ Set.Ioo (tₖ - εgeo) (tₖ + εgeo) := by
    intro s hs
    exact Set.Ioo_subset_Ioo (by linarith) (by linarith) hs
  have hΦ_phase' : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (-Tfin) Tfin,
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s :=
    fun v hv s hs => hΦ_phase v (hball_sub hv) s (hIoo_sub hs)
  have hΦ_in' : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (-Tfin) Tfin,
      Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
    fun v hv s hs => hΦ_in v (hball_sub hv) s (hIoo_sub hs)
  have hgeo_src : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (tₖ - Tfin) (tₖ + Tfin),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source :=
    fun v hv s hs => hgeo_src0 v (hball_sub_geo hv) s (hIoo_sub_geo s hs)
  have hgeo_in : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (tₖ - Tfin) (tₖ + Tfin),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) s,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E)
        ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
    fun v hv s hs => hgeo_in0 v (hball_sub_geo hv) s (hIoo_sub_geo s hs)
  have hinit : ∀ v ∈ Metric.ball v₀ rfin,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v :=
    fun v hv => hinit0 v (hball_sub_geo hv)
  have hΦinit' : ∀ v ∈ Metric.ball v₀ rfin, Φ (z v, 0) = z v :=
    fun v hv => hΦinit v (hball_sub hv)
  have hpair_ident := perJunction_phaseIdentification (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := (x₀, w₀)) (z := z) (tₖ := tₖ) (r := rfin) (R := b.rIn)
    (T' := Tfin) hTfin_pos hballIn_sub_target hΦ_phase' hΦ_in' hgeo_src hgeo_in hinit
    hΦinit'
  refine ⟨rfin, Tfin, hrfin_pos, hTfin_pos, ?_⟩
  have htgt : ∀ v ∈ Metric.ball v₀ rfin, ∀ τ ∈ Set.Ioo (-Tfin) Tfin,
      Φ (z v, τ) ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    intro v hv τ hτ
    exact hballIn_sub_target (hΦ_in' v hv τ hτ)
  have hz_cont_r : ContinuousOn z (Metric.ball v₀ rfin) :=
    hz_cont.mono (Metric.ball_subset_ball (le_trans hrfin_le_r hr_le_rz))
  have hshift_cont : ContinuousOn (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (tₖ - Tfin) (tₖ + Tfin)) :=
    (continuousOn_fst).prodMk ((continuousOn_snd).sub continuousOn_const)
  have hshift_maps : Set.MapsTo (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (tₖ - Tfin) (tₖ + Tfin))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-Tfin) Tfin) := by
    intro vt hvt
    refine ⟨hvt.1, ?_, ?_⟩
    · exact lt_sub_iff_add_lt.mpr (by linarith [hvt.2.1])
    · exact sub_lt_iff_lt_add.mpr (by linarith [hvt.2.2])
  have hTfin_lt_TΦ : Tfin < TΦ :=
    lt_of_le_of_lt hTfin_le_T' (lt_of_lt_of_le hT'_lt_Tcap hTcap_le_TΦ)
  have hΦorbit_cont : ContinuousOn
      (fun vτ : TangentSpace I p × ℝ => Φ (z vτ.1, vτ.2))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-Tfin) Tfin) := by
    have hpair_cont : ContinuousOn
        (fun vτ : TangentSpace I p × ℝ => ((z vτ.1, vτ.2) : (E × E) × ℝ))
        ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-Tfin) Tfin) := by
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      exact hz_cont_r.comp continuousOn_fst (fun x hx => hx.1)
    have hΦ_cont'' : ContinuousOn Φ
        ((Metric.ball ((x₀, w₀) : E × E) ρΦ) ×ˢ Set.Ioo (-Tfin) Tfin) :=
      hΦ_cont.mono (Set.prod_mono (le_refl _)
        (Set.Ioo_subset_Ioo (by linarith) (le_of_lt hTfin_lt_TΦ)))
    have hpair_maps : Set.MapsTo
        (fun vτ : TangentSpace I p × ℝ => ((z vτ.1, vτ.2) : (E × E) × ℝ))
        ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-Tfin) Tfin)
        ((Metric.ball ((x₀, w₀) : E × E) ρΦ) ×ˢ Set.Ioo (-Tfin) Tfin) := by
      intro vτ hvτ
      exact ⟨hz_ball_r vτ.1 (hball_sub hvτ.1), hvτ.2⟩
    exact hΦ_cont''.comp hpair_cont hpair_maps
  have hsymm_cont : ContinuousOn
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).target :=
    continuousOn_extChartAt_symm (I := I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)
  have horbit_maps : Set.MapsTo
      (fun vτ : TangentSpace I p × ℝ => Φ (z vτ.1, vτ.2))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-Tfin) Tfin)
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).target := by
    intro vτ hvτ
    exact mem_extChartAt_tangent_zero_target (I := I) α (htgt vτ.1 hvτ.1 vτ.2 hvτ.2)
  have hlift_orbit_cont : ContinuousOn
      (fun vτ : TangentSpace I p × ℝ =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (Φ (z vτ.1, vτ.2)))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-Tfin) Tfin) :=
    hsymm_cont.comp hΦorbit_cont horbit_maps
  have hcomp_cont : ContinuousOn
      (fun vt : TangentSpace I p × ℝ =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (Φ (z vt.1, vt.2 - tₖ)))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (tₖ - Tfin) (tₖ + Tfin)) :=
    hlift_orbit_cont.comp hshift_cont hshift_maps
  apply hcomp_cont.congr
  rintro ⟨v, s⟩ ⟨hv, hs⟩
  have hgeo_src_s : intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source :=
    hgeo_src v hv s hs
  have hphase :
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) s,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E) =
        Φ (z v, s - tₖ) := hpair_ident v hv s hs
  have hbridge := phasePoint_eq_extChartAt_tangent_intrinsicVelocityLift
    (I := I) g hEnorm p v α s hgeo_src_s
  have hread : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
      (intrinsicVelocityLift (I := I) g hEnorm p v s) = Φ (z v, s - tₖ) := by
    rw [← hbridge]; exact hphase
  have hlift_mem : intrinsicVelocityLift (I := I) g hEnorm p v s ∈
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M)
      (intrinsicVelocityLift (I := I) g hEnorm p v s)
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hgeo_src_s
  calc intrinsicVelocityLift (I := I) g hEnorm p v s
      = (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
            (intrinsicVelocityLift (I := I) g hEnorm p v s)) :=
        ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hlift_mem).symm
    _ = (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (Φ (z v, s - tₖ)) := by rw [hread]

private theorem continuousOn_ball_prod_Icc_of_local_windows
    {V : Type*} [PseudoMetricSpace V] {Y : Type*} [TopologicalSpace Y]
    (v₀ : V) (f : V × ℝ → Y)
    (H : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
        ContinuousOn f ((Metric.ball v₀ r) ×ˢ Set.Ioo (t - ε) (t + ε))) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn f ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  choose! r ε hr hε hcont using H
  set U : Set.Icc (0 : ℝ) 1 → Set ℝ := fun t => Metric.ball (t : ℝ) (ε t) with hU
  have hUopen : ∀ t, IsOpen (U t) := fun _ => Metric.isOpen_ball
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ t, U t := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simp only [hU]
    exact Metric.mem_ball_self (hε x hx)
  obtain ⟨S, hS⟩ := isCompact_Icc.elim_finite_subcover U hUopen hcover
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
    have hmem := hS h0
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨t, ht, _⟩ := hmem
    exact (Finset.notMem_empty t) ht
  set ρ : ℝ := S.inf' hSne (fun t => r (t : ℝ)) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, Finset.lt_inf'_iff]
    intro t _
    exact hr (t : ℝ) t.2
  have hρ_le : ∀ t ∈ S, ρ ≤ r (t : ℝ) := by
    intro t ht
    rw [hρ]; exact Finset.inf'_le _ ht
  refine ⟨ρ, hρpos, ?_⟩
  rintro ⟨v, x⟩ ⟨hv, hx⟩
  obtain ⟨t, ht_S, hW_eq⟩ := Set.mem_iUnion₂.mp (hS hx)
  simp only [hU] at hW_eq
  set Wt : Set (V × ℝ) :=
    (Metric.ball v₀ (r (t : ℝ))) ×ˢ Set.Ioo ((t : ℝ) - ε (t : ℝ)) ((t : ℝ) + ε (t : ℝ))
    with hWt
  have hcontWt : ContinuousOn f Wt := hcont (t : ℝ) t.2
  have hx_Ioo : x ∈ Set.Ioo ((t : ℝ) - ε (t : ℝ)) ((t : ℝ) + ε (t : ℝ)) := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hW_eq
    exact ⟨by linarith [hW_eq.1], by linarith [hW_eq.2]⟩
  have hv_Wt : v ∈ Metric.ball v₀ (r (t : ℝ)) :=
    Metric.ball_subset_ball (hρ_le t ht_S) hv
  have hcwa : ContinuousWithinAt f Wt (v, x) := hcontWt _ ⟨hv_Wt, hx_Ioo⟩
  set N : Set (V × ℝ) := (Metric.ball v₀ ρ) ×ˢ (Metric.ball (t : ℝ) (ε (t : ℝ))) with hN
  have hN_open : IsOpen N := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hpt_N : (v, x) ∈ N := ⟨hv, by
    rw [Metric.mem_ball, Real.dist_eq] at hW_eq ⊢; exact hW_eq⟩
  have hN_sub_Wt : N ⊆ Wt := by
    rintro ⟨w, y⟩ ⟨hw, hy⟩
    refine ⟨Metric.ball_subset_ball (hρ_le t ht_S) hw, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcwa_N : ContinuousWithinAt f N (v, x) := hcwa.mono hN_sub_Wt
  exact hcwa_N.mono_of_mem_nhdsWithin (nhdsWithin_le_nhds (hN_open.mem_nhds hpt_N))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicGeodesic_junctionData_of_lift_continuousOn
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) (t : ℝ)
    {α : M}
    (hα_src : intrinsicGeodesic (I := I) g hEnorm p v₀ t ∈ (chartAt H α).source)
    {z : TangentSpace I p → E × E}
    (hz : z = fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E))
    {x₀ w₀ : E} (_hx₀ : x₀ = (z v₀).1) (_hw₀ : w₀ = (z v₀).2)
    (_hx₀_int : x₀ ∈ interior (extChartAt I α).target) (hz0 : z v₀ = (x₀, w₀))
    {r₀ a c : ℝ} (hr₀ : 0 < r₀) (ht_mem : t ∈ Set.Ioo a c)
    (hlift_cont : ContinuousOn
      (fun vs : TangentSpace I p × ℝ =>
        intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
      ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c)) :
    ∃ rz : ℝ, 0 < rz ∧ ContinuousOn z (Metric.ball v₀ rz) ∧
    (∀ (b : ContDiffBump ((x₀, w₀) : E × E)),
      Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) →
      ∃ rgeo εgeo : ℝ, 0 < rgeo ∧ 0 < εgeo ∧ rgeo ≤ rz ∧
      (∀ v ∈ Metric.ball v₀ rgeo, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
        intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) s,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E)
          ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo,
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) t,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E) = z v)) := by
  classical
  set L : TangentSpace I p × ℝ → TangentBundle I M :=
    fun vs => intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2 with hL_def
  set W : Set (TangentSpace I p × ℝ) := (Metric.ball v₀ r₀) ×ˢ Set.Ioo a c with hW_def
  have hW_open : IsOpen W := Metric.isOpen_ball.prod isOpen_Ioo
  have hpt_W : ((v₀, t) : TangentSpace I p × ℝ) ∈ W := ⟨Metric.mem_ball_self hr₀, ht_mem⟩
  have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hfoot_cont : ContinuousOn
      (fun vs : TangentSpace I p × ℝ => (L vs).proj) W :=
    hπ_cont.comp_continuousOn hlift_cont
  have hfoot_v₀t : (L ((v₀, t) : TangentSpace I p × ℝ)).proj =
      intrinsicGeodesic (I := I) g hEnorm p v₀ t := rfl
  have hpreim_open : IsOpen
      (W ∩ (fun vs : TangentSpace I p × ℝ => (L vs).proj) ⁻¹' (chartAt H α).source) :=
    hfoot_cont.isOpen_inter_preimage hW_open (chartAt H α).open_source
  have hpt_preim : ((v₀, t) : TangentSpace I p × ℝ) ∈
      W ∩ (fun vs : TangentSpace I p × ℝ => (L vs).proj) ⁻¹' (chartAt H α).source := by
    refine ⟨hpt_W, ?_⟩
    rw [Set.mem_preimage, hfoot_v₀t]; exact hα_src
  obtain ⟨rsrc, εsrc, hrsrc_pos, hεsrc_pos, hsrc_sub⟩ :
      ∃ rsrc εsrc : ℝ, 0 < rsrc ∧ 0 < εsrc ∧
        (Metric.ball v₀ rsrc) ×ˢ Set.Ioo (t - εsrc) (t + εsrc) ⊆
          W ∩ (fun vs : TangentSpace I p × ℝ => (L vs).proj) ⁻¹' (chartAt H α).source := by
    rw [Metric.isOpen_iff] at hpreim_open
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := hpreim_open ((v₀, t) : TangentSpace I p × ℝ) hpt_preim
    refine ⟨δ / 2, δ / 2, by linarith, by linarith, ?_⟩
    rintro ⟨v, s⟩ ⟨hv, hs⟩
    apply hδ_sub
    rw [Metric.mem_ball, Prod.dist_eq]
    rw [Metric.mem_ball] at hv
    rw [Set.mem_Ioo] at hs
    have hsdist : dist s t < δ / 2 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
    calc max (dist v v₀) (dist s t) < δ / 2 := max_lt hv hsdist
      _ < δ := by linarith
  have hsrc_mem : ∀ v ∈ Metric.ball v₀ rsrc, ∀ s ∈ Set.Ioo (t - εsrc) (t + εsrc),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source := by
    intro v hv s hs
    have := hsrc_sub (Set.mk_mem_prod hv hs)
    exact this.2
  have hsubW : ∀ v ∈ Metric.ball v₀ rsrc, ∀ s ∈ Set.Ioo (t - εsrc) (t + εsrc),
      ((v, s) : TangentSpace I p × ℝ) ∈ W := by
    intro v hv s hs
    exact (hsrc_sub (Set.mk_mem_prod hv hs)).1
  set phaseRead : TangentSpace I p × ℝ → E × E :=
    fun vs => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (L vs)
    with hphaseRead_def
  set Wsub : Set (TangentSpace I p × ℝ) :=
    (Metric.ball v₀ rsrc) ×ˢ Set.Ioo (t - εsrc) (t + εsrc) with hWsub_def
  have hWsub_sub_W : Wsub ⊆ W := by
    rintro ⟨v, s⟩ ⟨hv, hs⟩; exact hsubW v hv s hs
  have hext_cont : ContinuousOn (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
    continuousOn_extChartAt (I := I.tangent) (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hL_mem_src : ∀ vs ∈ Wsub,
      L vs ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rintro ⟨v, s⟩ hvs
    rw [extChartAt_source]
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) (L (v, s))
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    obtain ⟨hv, hs⟩ := hvs
    exact hsrc_mem v hv s hs
  have hphaseRead_cont : ContinuousOn phaseRead Wsub := by
    refine hext_cont.comp (hlift_cont.mono hWsub_sub_W) ?_
    exact hL_mem_src
  have hphase_eq : ∀ v ∈ Metric.ball v₀ rsrc, ∀ s ∈ Set.Ioo (t - εsrc) (t + εsrc),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) s,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E) = phaseRead (v, s) := by
    intro v hv s hs
    exact phasePoint_eq_extChartAt_tangent_intrinsicVelocityLift (I := I) g hEnorm p v α s
      (hsrc_mem v hv s hs)
  have ht_mem_εsrc : t ∈ Set.Ioo (t - εsrc) (t + εsrc) := ⟨by linarith, by linarith⟩
  have hz_slice : ∀ v ∈ Metric.ball v₀ rsrc, z v = phaseRead (v, t) := by
    intro v hv
    rw [hz]; exact hphase_eq v hv t ht_mem_εsrc
  have hslice_cont : ContinuousOn (fun v : TangentSpace I p => ((v, t) : TangentSpace I p × ℝ))
      (Metric.ball v₀ rsrc) :=
    continuousOn_id.prodMk continuousOn_const
  have hslice_maps : Set.MapsTo (fun v : TangentSpace I p => ((v, t) : TangentSpace I p × ℝ))
      (Metric.ball v₀ rsrc) Wsub :=
    fun v hv => ⟨hv, ht_mem_εsrc⟩
  have hz_cont_rsrc : ContinuousOn z (Metric.ball v₀ rsrc) := by
    apply ContinuousOn.congr (hphaseRead_cont.comp hslice_cont hslice_maps)
    intro v hv; exact hz_slice v hv
  have hbase_read : phaseRead (v₀, t) = (x₀, w₀) := by
    rw [← hz_slice v₀ (Metric.mem_ball_self hrsrc_pos), hz0]
  refine ⟨rsrc, hrsrc_pos, hz_cont_rsrc, ?_⟩
  intro b _hb_sub
  have hphaseRead_contAt : ContinuousWithinAt phaseRead Wsub ((v₀, t) : TangentSpace I p × ℝ) :=
    hphaseRead_cont _ ⟨Metric.mem_ball_self hrsrc_pos, ht_mem_εsrc⟩
  have hWsub_open : IsOpen Wsub := Metric.isOpen_ball.prod isOpen_Ioo
  have hWsub_nhds : Wsub ∈ 𝓝 ((v₀, t) : TangentSpace I p × ℝ) :=
    hWsub_open.mem_nhds ⟨Metric.mem_ball_self hrsrc_pos, ht_mem_εsrc⟩
  have hphaseRead_contAt' : ContinuousAt phaseRead ((v₀, t) : TangentSpace I p × ℝ) :=
    hphaseRead_contAt.continuousAt hWsub_nhds
  have hpreim_nhds : phaseRead ⁻¹' (Metric.ball ((x₀, w₀) : E × E) b.rIn) ∈
      𝓝 ((v₀, t) : TangentSpace I p × ℝ) := by
    apply hphaseRead_contAt'.preimage_mem_nhds
    rw [hbase_read]; exact Metric.ball_mem_nhds _ b.rIn_pos
  have hinter_nhds : (phaseRead ⁻¹' (Metric.ball ((x₀, w₀) : E × E) b.rIn) ∩ Wsub) ∈
      𝓝 ((v₀, t) : TangentSpace I p × ℝ) :=
    Filter.inter_mem hpreim_nhds hWsub_nhds
  rw [_root_.mem_nhds_iff] at hinter_nhds
  obtain ⟨O, hO_sub, hO_open, hO_mem⟩ := hinter_nhds
  rw [Metric.isOpen_iff] at hO_open
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hO_open ((v₀, t) : TangentSpace I p × ℝ) hO_mem
  set rgeo : ℝ := min (δ / 2) rsrc with hrgeo_def
  set εgeo : ℝ := min (δ / 2) εsrc with hεgeo_def
  have hrgeo_pos : 0 < rgeo := lt_min (by linarith) hrsrc_pos
  have hεgeo_pos : 0 < εgeo := lt_min (by linarith) hεsrc_pos
  have hrgeo_le_rsrc : rgeo ≤ rsrc := min_le_right _ _
  have hεgeo_le_εsrc : εgeo ≤ εsrc := min_le_right _ _
  have hwindow_sub : ∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
      ((v, s) : TangentSpace I p × ℝ) ∈ O := by
    intro v hv s hs
    apply hδ_sub
    rw [Metric.mem_ball, Prod.dist_eq]
    rw [Metric.mem_ball] at hv
    have hv' : dist v v₀ < δ / 2 := lt_of_lt_of_le hv (min_le_left _ _)
    rw [Set.mem_Ioo] at hs
    have hsdist : dist s t < δ / 2 := by
      have : εgeo ≤ δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
    calc max (dist v v₀) (dist s t) < δ / 2 := max_lt hv' hsdist
      _ < δ := by linarith
  have hwindow_inner : ∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
      phaseRead (v, s) ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn := by
    intro v hv s hs
    exact (hO_sub (hwindow_sub v hv s hs)).1
  have hwindow_src : ∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source := by
    intro v hv s hs
    exact hsrc_mem v (Metric.ball_subset_ball hrgeo_le_rsrc hv) s
      (Set.Ioo_subset_Ioo (by linarith [hεgeo_le_εsrc]) (by linarith [hεgeo_le_εsrc]) hs)
  refine ⟨rgeo, εgeo, hrgeo_pos, hεgeo_pos, hrgeo_le_rsrc, ?_, hwindow_src, ?_, ?_⟩
  · intro v hv
    have ht_geo : t ∈ Set.Ioo (t - εgeo) (t + εgeo) := ⟨by linarith, by linarith⟩
    have hread := hwindow_inner v hv t ht_geo
    rwa [← hz_slice v (Metric.ball_subset_ball hrgeo_le_rsrc hv)] at hread
  · intro v hv s hs
    have hread := hwindow_inner v hv s hs
    rw [← hphase_eq v (Metric.ball_subset_ball hrgeo_le_rsrc hv) s
      (Set.Ioo_subset_Ioo (by linarith [hεgeo_le_εsrc]) (by linarith [hεgeo_le_εsrc]) hs)] at hread
    exact Metric.ball_subset_closedBall hread
  · intro v hv
    rw [hz]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicVelocityLift_continuousOn_step
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) (τ : ℝ)
    {r₀ a c : ℝ} (hr₀ : 0 < r₀) (hτ_mem : τ ∈ Set.Ioo a c)
    (hlift_cont : ContinuousOn
      (fun vs : TangentSpace I p × ℝ =>
        intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
      ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c)) :
    ∃ r' ε' : ℝ, 0 < r' ∧ 0 < ε' ∧
      ContinuousOn
        (fun vs : TangentSpace I p × ℝ =>
          intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
        ((Metric.ball v₀ r') ×ˢ Set.Ioo (τ - ε') (τ + ε')) := by
  classical
  set α : M := intrinsicGeodesic (I := I) g hEnorm p v₀ τ with hα_def
  set z : TangentSpace I p → E × E :=
    fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) τ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) τ) : E × E)
    with hz_def
  set x₀ : E := (z v₀).1 with hx₀_def
  set w₀ : E := (z v₀).2 with hw₀_def
  have hx₀_eq : x₀ = extChartAt I α α := by
    rw [hx₀_def, hz_def]
    simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    rw [hα_def]
  have hx₀ : x₀ ∈ interior (extChartAt I α).target := by
    rw [hx₀_eq]
    have hsrc : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
    have htgt : extChartAt I α α ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α htgt
  have hz0 : z v₀ = (x₀, w₀) := by rw [hx₀_def, hw₀_def]
  have hα_src : intrinsicGeodesic (I := I) g hEnorm p v₀ τ ∈ (chartAt H α).source := by
    rw [← hα_def]; exact mem_chart_source H α
  obtain ⟨rz, hrz, hz_cont, hgeo⟩ :=
    intrinsicGeodesic_junctionData_of_lift_continuousOn (I := I) g hEnorm p v₀ τ
      (α := α) hα_src (z := z) hz_def (x₀ := x₀) (w₀ := w₀) hx₀_def hw₀_def hx₀ hz0
      hr₀ hτ_mem hlift_cont
  exact intrinsicVelocityLift_window_of_junction_data (I := I) g hEnorm p v₀ α
    (x₀ := x₀) (w₀ := w₀) hx₀ (z := z) (tₖ := τ) (rz := rz) hrz hz_cont hz0 hgeo

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicGeodesic_phasePoint_continuous_zero
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    Continuous (fun v : TangentSpace I p =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
          (intrinsicGeodesic (I := I) g hEnorm p v) 0,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
          (intrinsicGeodesic (I := I) g hEnorm p v)) 0) : E × E)) := by
  classical
  set CLM : E →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p with hCLM
  have hfun : (fun v : TangentSpace I p =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
          (intrinsicGeodesic (I := I) g hEnorm p v) 0,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
          (intrinsicGeodesic (I := I) g hEnorm p v)) 0) : E × E))
      = (fun v : TangentSpace I p => ((extChartAt I p p, CLM v) : E × E)) := by
    funext v
    have h1 : DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
        (intrinsicGeodesic (I := I) g hEnorm p v) 0 = extChartAt I p p := by
      rw [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def,
        intrinsicGeodesic_zero (I := I) g hEnorm p v]
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm p v) 0 :=
      (((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).contMDiffAt
        Filter.univ_mem).mdifferentiableAt one_ne_zero)
    have h2 : deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
        (I := I) p (intrinsicGeodesic (I := I) g hEnorm p v)) 0 = CLM v := by
      rw [hCLM]
      exact chartCurve_deriv_zero_eq (I := I) p hmdiff
        (intrinsicGeodesic_zero (I := I) g hEnorm p v)
        (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v)
    rw [h1, h2]
  rw [hfun]
  exact continuous_const.prodMk CLM.continuous

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicGeodesic_window_of_flowData
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {z : TangentSpace I p → E × E}
    {tₖ r R T' ρ : ℝ}
    (hT'_pos : 0 < T')
    (hball : Metric.closedBall z₀ R ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hΦ_cont : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T') T'))
    (hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s)
    (hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall z₀ R)
    (hgeo_src : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source)
    (hgeo_in : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
        ∈ Metric.closedBall z₀ R)
    (hinit : ∀ v ∈ Metric.ball v₀ r,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)
    (hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v)
    (hz_cont : ContinuousOn z (Metric.ball v₀ r))
    (hz_ball : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball z₀ ρ) :
    ContinuousOn
      (fun vt : TangentSpace I p × ℝ =>
        intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - T') (tₖ + T')) := by
  have hident := perJunction_flowIdentification (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := z₀) (z := z) (tₖ := tₖ) (r := r) (R := R) (T' := T')
    hT'_pos hball hΦ_phase hΦ_in hgeo_src hgeo_in hinit hΦinit
  have htgt : ∀ v ∈ Metric.ball v₀ r, ∀ τ ∈ Set.Ioo (-T') T',
      (Φ (z v, τ)).1 ∈ (extChartAt I α).target := by
    intro v hv τ hτ
    exact interior_subset (hball (hΦ_in v hv τ hτ)).1
  exact perChart_jointContinuity_of_flowIdentifiedOn (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := z₀) (z := z) (tₖ := tₖ) (ε := T') (r := r) (ρ := ρ) (T := T')
    (le_refl T') hΦ_cont hz_cont hz_ball htgt hident

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem exists_chartFlowData_of_zContinuousAt
    {N : Type*} [TopologicalSpace N]
    (g : SmoothRiemannianMetric I M) (α : M)
    {z₀ : E × E} {z : N → E × E} {v₀ : N}
    (hx₀ : (z₀).1 ∈ interior (extChartAt I α).target)
    (hz_cont : ContinuousAt z v₀) (hz0 : z v₀ = z₀) :
    ∃ (Φ : (E × E) × ℝ → E × E) (S : Set N) (T' R ρ : ℝ),
      IsOpen S ∧ v₀ ∈ S ∧ 0 < T' ∧ 0 < R ∧ 0 < ρ ∧
      Metric.closedBall z₀ R ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T') T') ∧
      (∀ v ∈ S, ∀ s ∈ Set.Ioo (-T') T',
        HasDerivAt (fun τ => Φ (z v, τ))
          (chartPhaseVF (I := I) g α (Φ (z v, s))) s) ∧
      (∀ v ∈ S, ∀ s ∈ Set.Ioo (-T') T', Φ (z v, s) ∈ Metric.closedBall z₀ R) ∧
      (∀ v ∈ S, Φ (z v, 0) = z v) ∧
      (∀ v ∈ S, z v ∈ Metric.ball z₀ ρ) := by
  classical
  obtain ⟨b, rN, εN, ρ, T, Φ, hrN, hεN, hρ_pos, hT_pos, hb_sub, hflow, hΦ_C1, hΦ_init⟩ :=
    exists_chartPhase_contDiffOn_isLocalFlow_combined (I := I) g α
      (x₀ := (z₀).1) (v₀ := (z₀).2) hx₀


  set ρ_f : ℝ := min ρ (rN : ℝ) with hρf_def
  set T_f : ℝ := min T εN with hTf_def
  have hρf_pos : 0 < ρ_f := lt_min hρ_pos (by exact_mod_cast hrN)
  have hTf_pos : 0 < T_f := lt_min hT_pos hεN
  have hρf_le_rN : ρ_f ≤ (rN : ℝ) := min_le_right _ _
  have hΦ_cont_f : ContinuousOn Φ ((Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f) :=
    hΦ_C1.continuousOn.mono (Set.prod_mono (Metric.ball_subset_ball (min_le_left _ _))
      (Set.Ioo_subset_Ioo (by linarith [min_le_left T εN]) (min_le_left _ _)))
  have hΦ0 : Φ (z₀, 0) = z₀ := hΦ_init
  have hW_nhds : Metric.ball z₀ b.rIn ∈ nhds z₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self b.rIn_pos)
  obtain ⟨S, T'c, hS_open, hv₀_S, hT'c_pos, hT'c_lt, hzS_ball, horbit_in⟩ :=
    flowOrbit_uniform_confinement (N := N) (Φ := Φ) (z₀ := z₀)
      (ρ_f := ρ_f) (T_f := T_f) (z := z) (v₀ := v₀) (W := Metric.ball z₀ b.rIn)
      hρf_pos hTf_pos hΦ_cont_f hΦ0 hz_cont hz0 hW_nhds
  have hzv_rN : ∀ v ∈ S, z v ∈ Metric.closedBall z₀ (rN : ℝ) := fun v hv =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hρf_le_rN (hzS_ball v hv))
  have hT'c_le_εN : T'c ≤ εN := le_trans (le_of_lt hT'c_lt) (min_le_right _ _)
  refine ⟨Φ, S, T'c, b.rOut, ρ_f, hS_open, hv₀_S, hT'c_pos, b.rOut_pos, hρf_pos,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb_sub
  · exact hΦ_cont_f.mono (Set.prod_mono (le_refl _)
      (Set.Ioo_subset_Ioo (by linarith) (le_of_lt hT'c_lt)))
  · intro v hv s hs
    have hs_ioo_εN : s ∈ Set.Ioo (-(εN : ℝ)) εN :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd := hflow.hasDerivWithinAt (z v) (hzv_rN v hv) s
      (Set.Ioo_subset_Icc_self hs_ioo_εN)
    have hda := hd.hasDerivAt (Icc_mem_nhds hs_ioo_εN.1 hs_ioo_εN.2)
    have horbit_rin : Φ (z v, s) ∈
        Metric.closedBall (((z₀).1, (z₀).2) : E × E) b.rIn :=
      Metric.ball_subset_closedBall (horbit_in v hv s hs)
    have hVF : chartPhaseVFTime (I := I) g α ((z₀).1, (z₀).2) b s (Φ (z v, s))
        = chartPhaseVF (I := I) g α (Φ (z v, s)) := by
      show chartPhaseVFCutoff (I := I) g α ((z₀).1, (z₀).2) b (Φ (z v, s))
        = chartPhaseVF (I := I) g α (Φ (z v, s))
      exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α
        ((z₀).1, (z₀).2) b horbit_rin
    rw [hVF] at hda
    exact hda
  · intro v hv s hs
    have h_in := horbit_in v hv s hs
    exact Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut)
      (Metric.ball_subset_closedBall h_in)
  · intro v hv
    exact hflow.apply_initial (z v) (hzv_rN v hv)
  · exact hzS_ball

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem exists_chartFlow_confined
    (g : SmoothRiemannianMetric I M) (α : M)
    {z₀ : E × E}
    (hx₀ : (z₀).1 ∈ interior (extChartAt I α).target) :
    ∃ (Φ : (E × E) × ℝ → E × E) (b : ContDiffBump z₀) (T' ρ : ℝ),
      0 < T' ∧ 0 < ρ ∧
      Metric.closedBall z₀ b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T') T') ∧
      (∀ w ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T') T',
        HasDerivAt (fun τ => Φ (w, τ))
          (chartPhaseVF (I := I) g α (Φ (w, s))) s) ∧
      (∀ w ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T') T',
        Φ (w, s) ∈ Metric.closedBall z₀ b.rIn) ∧
      (∀ w ∈ Metric.ball z₀ ρ, Φ (w, 0) = w) := by
  classical
  obtain ⟨b, rN, εN, ρ, T, Φ, hrN, hεN, hρ_pos, hT_pos, hb_sub, hflow, hΦ_C1, hΦ_init⟩ :=
    exists_chartPhase_contDiffOn_isLocalFlow_combined (I := I) g α
      (x₀ := (z₀).1) (v₀ := (z₀).2) hx₀
  have hbcenter : ((z₀).1, (z₀).2) = z₀ := rfl
  set ρ_f : ℝ := min ρ (rN : ℝ) with hρf_def
  have hρf_pos : 0 < ρ_f := lt_min hρ_pos (by exact_mod_cast hrN)
  have hρf_le_rN : ρ_f ≤ (rN : ℝ) := min_le_right _ _

  have hballIn_sub : Metric.closedBall z₀ b.rIn ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
    subset_trans (Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut)) hb_sub
  obtain ⟨Mb, hMb_pos, hMb⟩ :=
    chartPhaseVF_bddOn_closedBall (I := I) g α z₀ (le_of_lt b.rIn_pos) hballIn_sub

  set ρ_z : ℝ := b.rIn - min b.rIn (Mb * εN) / 2 with hρz_def
  have hmin_pos : 0 < min b.rIn (Mb * εN) := lt_min b.rIn_pos (by positivity)
  have hρz_pos : 0 < ρ_z := by
    rw [hρz_def]
    have h1 : min b.rIn (Mb * εN) ≤ b.rIn := min_le_left _ _
    linarith
  have hρz_lt : ρ_z < b.rIn := by rw [hρz_def]; linarith
  have hRMT : b.rIn - ρ_z < Mb * εN := by
    rw [hρz_def]
    have h2 : min b.rIn (Mb * εN) ≤ Mb * εN := min_le_right _ _
    have : (0:ℝ) < Mb * εN := by positivity
    linarith
  set ρ_w : ℝ := min ρ_f ρ_z with hρw_def
  have hρw_pos : 0 < ρ_w := lt_min hρf_pos hρz_pos
  have hρw_le_ρf : ρ_w ≤ ρ_f := min_le_left _ _
  have hρw_le_ρz : ρ_w ≤ ρ_z := min_le_right _ _
  have hw_ball_rN : ∀ w ∈ Metric.ball z₀ ρ_w, w ∈ Metric.closedBall z₀ (rN : ℝ) := fun w hw =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball
      (le_trans hρw_le_ρf hρf_le_rN) hw)
  have hρf_le_ρ : ρ_f ≤ ρ := min_le_left _ _
  set Tconf : ℝ := (b.rIn - ρ_z) / Mb with hTconf_def
  have hTconf_pos : 0 < Tconf := div_pos (by linarith) hMb_pos
  have hTconf_lt_εN : Tconf < εN := by rw [hTconf_def, div_lt_iff₀ hMb_pos]; linarith [hRMT]
  set T' : ℝ := min Tconf T with hT'_def
  have hT'_pos : 0 < T' := lt_min hTconf_pos hT_pos
  have hT'_le_Tconf : T' ≤ Tconf := min_le_left _ _
  have hT'_le_T : T' ≤ T := min_le_right _ _
  have hT'_lt_εN : T' < εN := lt_of_le_of_lt hT'_le_Tconf hTconf_lt_εN

  have hΦ_in : ∀ w ∈ Metric.ball z₀ ρ_w, ∀ s ∈ Set.Ioo (-T') T',
      Φ (w, s) ∈ Metric.closedBall z₀ b.rIn := by
    intro w hw s hs
    have hderiv_v : ∀ r ∈ Set.Ioo (-(εN : ℝ)) εN,
        HasDerivAt (fun τ => Φ (w, τ))
          (chartPhaseVFTime (I := I) g α z₀ b r (Φ (w, r))) r := fun r hr =>
      (hflow.hasDerivWithinAt w (hw_ball_rN w hw) r
        (Set.Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have hzc : dist w z₀ ≤ ρ_z :=
      le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp hw) hρw_le_ρz)
    have hconf := flowOrbit_cutoff_confined_symm (I := I) g α b hMb_pos
      (le_of_lt hρz_pos) hρz_lt hεN hRMT hzc
      (hflow.apply_initial w (hw_ball_rN w hw)) hderiv_v hMb
    exact hconf s ⟨by linarith [hs.1, hT'_le_Tconf], by linarith [hs.2, hT'_le_Tconf]⟩
  refine ⟨Φ, b, T', ρ_w, hT'_pos, hρw_pos, hb_sub, ?_, ?_, hΦ_in, ?_⟩
  · exact hΦ_C1.continuousOn.mono (Set.prod_mono
      (Metric.ball_subset_ball (le_trans hρw_le_ρf hρf_le_ρ))
      (Set.Ioo_subset_Ioo (by linarith [hT'_le_T]) hT'_le_T))
  · intro w hw s hs
    have hsεN : s ∈ Set.Ioo (-(εN : ℝ)) εN :=
      ⟨by linarith [hs.1, hT'_lt_εN], by linarith [hs.2, hT'_lt_εN]⟩
    have hda := (hflow.hasDerivWithinAt w (hw_ball_rN w hw) s
      (Set.Ioo_subset_Icc_self hsεN)).hasDerivAt (Icc_mem_nhds hsεN.1 hsεN.2)
    have horbit_in : Φ (w, s) ∈ Metric.closedBall z₀ b.rIn := hΦ_in w hw s hs
    have hVF : chartPhaseVFTime (I := I) g α z₀ b s (Φ (w, s))
        = chartPhaseVF (I := I) g α (Φ (w, s)) := by
      rw [chartPhaseVFTime_apply]
      exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α z₀ b horbit_in
    rw [hVF] at hda
    exact hda
  · intro w hw
    exact hflow.apply_initial w (hw_ball_rN w hw)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicGeodesic_chart_confined_of_orbit
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {α : M} {φ : ℝ → E × E} {tₖ T' : ℝ}
    (hφ_tgt : ∀ s ∈ Set.Ioo (-T') T',
      (φ s).1 ∈ interior (extChartAt I α).target)
    (hφ_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt φ (chartPhaseVF (I := I) g α (φ s)) s)
    (hmatch0 : ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
        (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
      deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
        (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = φ 0)
    (hsrc0 : intrinsicGeodesic (I := I) g hEnorm p v tₖ ∈ (chartAt H α).source) :
    ∀ s ∈ Set.Ioo (-T') T',
      intrinsicGeodesic (I := I) g hEnorm p v (tₖ + s) ∈ (chartAt H α).source ∧
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) (tₖ + s),
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) (tₖ + s)) : E × E) = φ s := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_geo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v


  set K : Set ℝ := Set.Ioo (tₖ - T') (tₖ + T') with hK_def
  set cγ : ℝ → E × E := fun t =>
    ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ t,
      deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ) t)
      : E × E) with hcγ_def
  set phiS : ℝ → E × E := fun t => φ (t - tₖ) with hphiS_def

  have hphiS_phase : ∀ t ∈ K, HasDerivAt phiS (chartPhaseVF (I := I) g α (phiS t)) t := by
    intro t ht
    have hts : t - tₖ ∈ Set.Ioo (-T') T' := by
      rw [hK_def, Set.mem_Ioo] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hd := (hφ_phase (t - tₖ) hts).scomp t ((hasDerivAt_id t).sub_const tₖ)
    simpa [hphiS_def] using hd
  have hphiS_tgt : ∀ t ∈ K, (phiS t).1 ∈ interior (extChartAt I α).target := by
    intro t ht
    have hts : t - tₖ ∈ Set.Ioo (-T') T' := by
      rw [hK_def, Set.mem_Ioo] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hφ_tgt (t - tₖ) hts

  set psiS : ℝ → M := fun t => (extChartAt I α).symm (phiS t).1 with hpsiS_def
  have hpsiS_src : ∀ t ∈ K, psiS t ∈ (chartAt H α).source := by
    intro t ht
    have h1 : (phiS t).1 ∈ (extChartAt I α).target := interior_subset (hphiS_tgt t ht)
    have h2 := (extChartAt I α).map_target h1
    rwa [extChartAt_source (I := I) α] at h2
  have hphiS_cont : ContinuousOn phiS K :=
    fun t ht => (hphiS_phase t ht).continuousAt.continuousWithinAt
  have hpsiS_cont : ContinuousOn psiS K := by
    have h1 : ContinuousOn (fun t => (phiS t).1) K := hphiS_cont.fst
    have h2 : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
      continuousOn_extChartAt_symm (I := I) α
    exact h2.comp h1 (fun t ht => interior_subset (hphiS_tgt t ht))


  have hpos_of_phase : ∀ t ∈ K, γ t ∈ (chartAt H α).source → cγ t = phiS t →
      γ t = psiS t := by
    intro t ht hsrc hphase
    have h1 : extChartAt I α (γ t) = (phiS t).1 := by
      have h := congrArg Prod.fst hphase
      simpa [hcγ_def, DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
        using h
    rw [hpsiS_def]
    show γ t = (extChartAt I α).symm (phiS t).1
    rw [← h1]
    exact ((extChartAt I α).left_inv
      (by rw [extChartAt_source (I := I) α]; exact hsrc)).symm


  suffices hKagree : ∀ t ∈ K, γ t ∈ (chartAt H α).source ∧ cγ t = phiS t by
    intro s hs
    have ht : tₖ + s ∈ K := by
      rw [hK_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    obtain ⟨hsrc, hphase⟩ := hKagree (tₖ + s) ht
    refine ⟨hsrc, ?_⟩
    have hps : phiS (tₖ + s) = φ s := by simp only [hphiS_def, add_sub_cancel_left]
    exact hphase.trans hps


  set A : Set ℝ := {t ∈ K | γ t ∈ (chartAt H α).source ∧ cγ t = phiS t} with hA_def
  have hK_open : IsOpen K := isOpen_Ioo
  have hK_conn : IsPreconnected K := isPreconnected_Ioo


  have hA_rel_open : ∀ t ∈ A, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ U ∩ K ⊆ A := by
    intro t₀ ht₀A
    obtain ⟨ht₀K, ht₀src, ht₀phase⟩ := ht₀A
    have hVsrc_open : IsOpen (γ ⁻¹' (chartAt H α).source) :=
      (chartAt H α).open_source.preimage hγ_cont
    set W : Set ℝ := (γ ⁻¹' (chartAt H α).source) ∩ K with hW_def
    have hW_open : IsOpen W := hVsrc_open.inter hK_open
    have ht₀_W : t₀ ∈ W := ⟨ht₀src, ht₀K⟩
    have hgeo := geodesic_chartPhaseVF_on_open (I := I) hγ_geo hγ_cont hW_open
      (fun s hs => hs.1)

    set c₁ : ℝ → E × E := fun r => cγ (t₀ + r) with hc₁_def
    set c₂ : ℝ → E × E := fun r => phiS (t₀ + r) with hc₂_def
    set z₀ : E × E := cγ t₀ with hz₀_def
    have hz₀_mem : z₀ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      refine ⟨?_, Set.mem_univ _⟩
      simpa [hz₀_def, hcγ_def] using (hgeo t₀ ht₀_W).2
    have hc₁0 : c₁ 0 = z₀ := by simp [hc₁_def, hz₀_def]
    have hc₂0 : c₂ 0 = z₀ := by
      simp only [hc₂_def, add_zero, hz₀_def]; exact ht₀phase.symm
    have hshift_to : Filter.Tendsto (fun r : ℝ => t₀ + r) (nhds 0) (nhds t₀) := by
      have h : Filter.Tendsto (fun r : ℝ => t₀ + r) (nhds 0) (nhds (t₀ + 0)) :=
        (continuous_const.add continuous_id).continuousAt
      simpa using h
    have hd1 : ∀ᶠ r in nhds (0:ℝ),
        HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ r)) r ∧
          c₁ r ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      have hr_W : ∀ᶠ r in nhds (0:ℝ), t₀ + r ∈ W :=
        hshift_to.eventually (hW_open.mem_nhds ht₀_W)
      filter_upwards [hr_W] with r hr
      obtain ⟨hderiv, htgt⟩ := hgeo (t₀ + r) hr
      refine ⟨?_, ?_, Set.mem_univ _⟩
      · have hsd : HasDerivAt (fun r : ℝ => t₀ + r) 1 r := (hasDerivAt_id r).const_add t₀
        simpa [hc₁_def, hcγ_def, Function.comp, one_smul] using hderiv.scomp r hsd
      · simpa [hc₁_def, hcγ_def] using htgt
    have hd2 : ∀ᶠ r in nhds (0:ℝ),
        HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ r)) r ∧
          c₂ r ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      have hr_K : ∀ᶠ r in nhds (0:ℝ), t₀ + r ∈ K :=
        hshift_to.eventually (hK_open.mem_nhds ht₀K)
      filter_upwards [hr_K] with r hr
      refine ⟨?_, ?_, Set.mem_univ _⟩
      · have hsd : HasDerivAt (fun r : ℝ => t₀ + r) 1 r := (hasDerivAt_id r).const_add t₀
        simpa [hc₂_def, Function.comp, one_smul] using (hphiS_phase (t₀ + r) hr).scomp r hsd
      · simpa [hc₂_def] using hphiS_tgt (t₀ + r) hr
    have huniq : c₁ =ᶠ[nhds (0:ℝ)] c₂ :=
      chartPhaseVF_orbit_uniqueness (I := I) hz₀_mem hc₁0 hc₂0 hd1 hd2

    have heq_t₀ : ∀ᶠ t in nhds t₀, cγ t = phiS t := by
      have hshift_back : Filter.Tendsto (fun t : ℝ => t - t₀) (nhds t₀) (nhds (0:ℝ)) := by
        have h : Filter.Tendsto (fun t : ℝ => t - t₀) (nhds t₀) (nhds (t₀ - t₀)) :=
          (continuous_id.sub continuous_const).continuousAt
        simpa using h
      filter_upwards [hshift_back.eventually huniq] with t ht
      simp only [hc₁_def, hc₂_def] at ht
      rwa [show t₀ + (t - t₀) = t from by ring] at ht
    have hcomb : ∀ᶠ t in nhds t₀, γ t ∈ (chartAt H α).source ∧ cγ t = phiS t := by
      filter_upwards [hVsrc_open.mem_nhds ht₀src, heq_t₀] with t hs he using ⟨hs, he⟩
    obtain ⟨U, hU_sub, hU_open, ht₀U⟩ := _root_.mem_nhds_iff.mp hcomb
    exact ⟨U, hU_open, ht₀U, fun x hx => ⟨hx.2, (hU_sub hx.1).1, (hU_sub hx.1).2⟩⟩


  have hA_closed : closure A ∩ K ⊆ A := by
    rintro t₀ ⟨ht₀_cl, ht₀K⟩
    rw [mem_closure_iff_seq_limit] at ht₀_cl
    obtain ⟨u, hu_A, hu_lim⟩ := ht₀_cl
    have hu_K : ∀ n, u n ∈ K := fun n => (hu_A n).1
    have hu_within : Filter.Tendsto u Filter.atTop (nhdsWithin t₀ K) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu_lim, Filter.Eventually.of_forall hu_K⟩

    have hγψ : (fun n => γ (u n)) = (fun n => psiS (u n)) :=
      funext fun n => hpos_of_phase (u n) (hu_A n).1 (hu_A n).2.1 (hu_A n).2.2
    have hlim_γ : Filter.Tendsto (fun n => γ (u n)) Filter.atTop (nhds (γ t₀)) :=
      (hγ_cont.continuousAt.tendsto).comp hu_lim
    have hlim_ψ : Filter.Tendsto (fun n => psiS (u n)) Filter.atTop (nhds (psiS t₀)) :=
      (hpsiS_cont t₀ ht₀K).tendsto.comp hu_within
    have hγt₀ : γ t₀ = psiS t₀ := by
      rw [hγψ] at hlim_γ
      exact tendsto_nhds_unique hlim_γ hlim_ψ
    have ht₀src : γ t₀ ∈ (chartAt H α).source := by rw [hγt₀]; exact hpsiS_src t₀ ht₀K

    set W₀ : Set ℝ := (γ ⁻¹' (chartAt H α).source) ∩ K with hW₀_def
    have hW₀_open : IsOpen W₀ :=
      ((chartAt H α).open_source.preimage hγ_cont).inter hK_open
    have hgeo0 := geodesic_chartPhaseVF_on_open (I := I) hγ_geo hγ_cont hW₀_open
      (fun s hs => hs.1)
    have hcγ_cont : ContinuousAt cγ t₀ := (hgeo0 t₀ ⟨ht₀src, ht₀K⟩).1.continuousAt
    have hlim_cγ : Filter.Tendsto (fun n => cγ (u n)) Filter.atTop (nhds (cγ t₀)) :=
      hcγ_cont.tendsto.comp hu_lim
    have hlim_phiS : Filter.Tendsto (fun n => phiS (u n)) Filter.atTop (nhds (phiS t₀)) :=
      (hphiS_cont t₀ ht₀K).tendsto.comp hu_within
    have hcφ : (fun n => cγ (u n)) = (fun n => phiS (u n)) :=
      funext fun n => (hu_A n).2.2
    have hcγt₀ : cγ t₀ = phiS t₀ := by
      rw [hcφ] at hlim_cγ
      exact tendsto_nhds_unique hlim_cγ hlim_phiS
    exact ⟨ht₀K, ht₀src, hcγt₀⟩
  have hKnA_rel_open : ∀ t ∈ K \ A, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ U ∩ K ⊆ K \ A := by
    intro t₀ ht₀
    obtain ⟨ht₀K, ht₀nA⟩ := ht₀
    have ht₀_ncl : t₀ ∉ closure A := fun h => ht₀nA (hA_closed ⟨h, ht₀K⟩)
    refine ⟨(closure A)ᶜ, isClosed_closure.isOpen_compl, ht₀_ncl, ?_⟩
    rintro x ⟨hxU, hxK⟩
    exact ⟨hxK, fun hxA => hxU (subset_closure hxA)⟩
  intro t htK
  have hT'_pos : 0 < T' := by
    rw [hK_def, Set.mem_Ioo] at htK; linarith [htK.1, htK.2]
  have htₖ_K : tₖ ∈ K := by
    rw [hK_def, Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
  have hphase_tₖ : cγ tₖ = phiS tₖ := by
    have hp0 : phiS tₖ = φ 0 := by simp [hphiS_def]
    rw [hp0]; exact hmatch0
  have h0_A : tₖ ∈ A := ⟨htₖ_K, hsrc0, hphase_tₖ⟩
  by_contra h_neq
  have hs_KnA : t ∈ K \ A := ⟨htK, fun h => h_neq h.2⟩
  set U_A : Set ℝ := ⋃ (u : ℝ) (huA : u ∈ A),
    Classical.choose (hA_rel_open u huA) with hU_A_def
  have hU_A_open : IsOpen U_A := by
    apply isOpen_iUnion; intro u
    apply isOpen_iUnion; intro huA
    exact (Classical.choose_spec (hA_rel_open u huA)).1
  have hA_sub_U_A : A ⊆ U_A := by
    intro x hx
    simp only [hU_A_def, Set.mem_iUnion]
    exact ⟨x, hx, (Classical.choose_spec (hA_rel_open x hx)).2.1⟩
  have hU_A_inter_K_sub_A : U_A ∩ K ⊆ A := by
    intro x hx
    obtain ⟨hx_U, hx_K⟩ := hx
    simp only [hU_A_def, Set.mem_iUnion] at hx_U
    obtain ⟨u, huA, hx_u⟩ := hx_U
    exact (Classical.choose_spec (hA_rel_open u huA)).2.2 ⟨hx_u, hx_K⟩
  set U_KnA : Set ℝ := ⋃ (u : ℝ) (huKnA : u ∈ K \ A),
    Classical.choose (hKnA_rel_open u huKnA) with hU_KnA_def
  have hU_KnA_open : IsOpen U_KnA := by
    apply isOpen_iUnion; intro u
    apply isOpen_iUnion; intro huKnA
    exact (Classical.choose_spec (hKnA_rel_open u huKnA)).1
  have hKnA_sub_U_KnA : K \ A ⊆ U_KnA := by
    intro x hx
    simp only [hU_KnA_def, Set.mem_iUnion]
    exact ⟨x, hx, (Classical.choose_spec (hKnA_rel_open x hx)).2.1⟩
  have hU_KnA_inter_K_sub_KnA : U_KnA ∩ K ⊆ K \ A := by
    intro x hx
    obtain ⟨hx_U, hx_K⟩ := hx
    simp only [hU_KnA_def, Set.mem_iUnion] at hx_U
    obtain ⟨u, huKnA, hx_u⟩ := hx_U
    exact (Classical.choose_spec (hKnA_rel_open u huKnA)).2.2 ⟨hx_u, hx_K⟩
  have hK_cover : K ⊆ U_A ∪ U_KnA := by
    intro x hx_K
    by_cases hxA : x ∈ A
    · exact Or.inl (hA_sub_U_A hxA)
    · exact Or.inr (hKnA_sub_U_KnA ⟨hx_K, hxA⟩)
  have hcontra : (K ∩ (U_A ∩ U_KnA)).Nonempty :=
    hK_conn U_A U_KnA hU_A_open hU_KnA_open hK_cover
      ⟨tₖ, htₖ_K, hA_sub_U_A h0_A⟩
      ⟨t, htK, hKnA_sub_U_KnA hs_KnA⟩
  obtain ⟨x, hx_K, hx_UA, hx_UKnA⟩ := hcontra
  have hxA : x ∈ A := hU_A_inter_K_sub_A ⟨hx_UA, hx_K⟩
  have hxKnA : x ∈ K \ A := hU_KnA_inter_K_sub_KnA ⟨hx_UKnA, hx_K⟩
  exact hxKnA.2 hxA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicVelocityLift_window_of_flow
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    (α : M) {z₀ : E × E} {Φ : (E × E) × ℝ → E × E} {b : ContDiffBump z₀}
    {T' ρ : ℝ} (hT'_pos : 0 < T') (hρ_pos : 0 < ρ)
    (hballOut : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hΦ_cont : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T') T'))
    (hΦ_phase : ∀ w ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (w, τ)) (chartPhaseVF (I := I) g α (Φ (w, s))) s)
    (hΦ_in : ∀ w ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T') T',
      Φ (w, s) ∈ Metric.closedBall z₀ b.rIn)
    (hΦinit : ∀ w ∈ Metric.ball z₀ ρ, Φ (w, 0) = w)
    {z : TangentSpace I p → E × E} {tₖ : ℝ} {rz : ℝ} (hrz : 0 < rz)
    (hz_cont : ContinuousOn z (Metric.ball v₀ rz)) (hz0 : z v₀ ∈ Metric.ball z₀ ρ)
    (hzmatch : ∀ v ∈ Metric.ball v₀ rz,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)
    (hsrc : ∀ v ∈ Metric.ball v₀ rz,
      intrinsicGeodesic (I := I) g hEnorm p v tₖ ∈ (chartAt H α).source) :
    ∃ r : ℝ, 0 < r ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicVelocityLift (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - T') (tₖ + T')) := by
  classical

  have hz_pre : z ⁻¹' Metric.ball z₀ ρ ∈ nhds v₀ :=
    (hz_cont.continuousAt (Metric.ball_mem_nhds _ hrz)).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hz0)
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.mem_nhds_iff.mp hz_pre
  set rfin : ℝ := min r₀ rz with hrfin_def
  have hrfin_pos : 0 < rfin := lt_min hr₀_pos hrz
  have hrfin_le_r₀ : rfin ≤ r₀ := min_le_left _ _
  have hrfin_le_rz : rfin ≤ rz := min_le_right _ _
  have hz_ballρ : ∀ v ∈ Metric.ball v₀ rfin, z v ∈ Metric.ball z₀ ρ :=
    fun v hv => hr₀_sub (Metric.ball_subset_ball hrfin_le_r₀ hv)
  have hballIn_sub : Metric.closedBall z₀ b.rIn ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
    subset_trans (Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut)) hballOut

  have hB2 : ∀ v ∈ Metric.ball v₀ rfin, ∀ s ∈ Set.Ioo (-T') T',
      intrinsicGeodesic (I := I) g hEnorm p v (tₖ + s) ∈ (chartAt H α).source ∧
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) (tₖ + s),
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) (tₖ + s)) : E × E) = Φ (z v, s) := by
    intro v hv s hs
    have hvz : v ∈ Metric.ball v₀ rz := Metric.ball_subset_ball hrfin_le_rz hv
    exact intrinsicGeodesic_chart_confined_of_orbit (I := I) g hEnorm p v (α := α)
      (φ := fun s => Φ (z v, s)) (tₖ := tₖ) (T' := T')
      (fun s' hs' => (hballIn_sub (hΦ_in (z v) (hz_ballρ v hv) s' hs')).1)
      (fun s' hs' => hΦ_phase (z v) (hz_ballρ v hv) s' hs')
      ((hzmatch v hvz).trans (hΦinit (z v) (hz_ballρ v hv)).symm)
      (hsrc v hvz) s hs
  refine ⟨rfin, hrfin_pos, ?_⟩
  have htgt : ∀ v ∈ Metric.ball v₀ rfin, ∀ τ ∈ Set.Ioo (-T') T',
      Φ (z v, τ) ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    intro v hv τ hτ
    exact hballIn_sub (hΦ_in (z v) (hz_ballρ v hv) τ hτ)
  have hz_cont_r : ContinuousOn z (Metric.ball v₀ rfin) :=
    hz_cont.mono (Metric.ball_subset_ball hrfin_le_rz)
  have hshift_cont : ContinuousOn (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (tₖ - T') (tₖ + T')) :=
    (continuousOn_fst).prodMk ((continuousOn_snd).sub continuousOn_const)
  have hshift_maps : Set.MapsTo (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (tₖ - T') (tₖ + T'))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-T') T') := by
    intro vt hvt
    refine ⟨hvt.1, ?_, ?_⟩
    · exact lt_sub_iff_add_lt.mpr (by linarith [hvt.2.1])
    · exact sub_lt_iff_lt_add.mpr (by linarith [hvt.2.2])
  have hΦorbit_cont : ContinuousOn
      (fun vτ : TangentSpace I p × ℝ => Φ (z vτ.1, vτ.2))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-T') T') := by
    have hpair_cont : ContinuousOn
        (fun vτ : TangentSpace I p × ℝ => ((z vτ.1, vτ.2) : (E × E) × ℝ))
        ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-T') T') := by
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      exact hz_cont_r.comp continuousOn_fst (fun x hx => hx.1)
    have hpair_maps : Set.MapsTo
        (fun vτ : TangentSpace I p × ℝ => ((z vτ.1, vτ.2) : (E × E) × ℝ))
        ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-T') T')
        ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T') T') :=
      fun vτ hvτ => ⟨hz_ballρ vτ.1 hvτ.1, hvτ.2⟩
    exact hΦ_cont.comp hpair_cont hpair_maps
  have hsymm_cont : ContinuousOn
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).target :=
    continuousOn_extChartAt_symm (I := I.tangent) (⟨α, (0 : E)⟩ : TangentBundle I M)
  have horbit_maps : Set.MapsTo
      (fun vτ : TangentSpace I p × ℝ => Φ (z vτ.1, vτ.2))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-T') T')
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).target := by
    intro vτ hvτ
    exact mem_extChartAt_tangent_zero_target (I := I) α (htgt vτ.1 hvτ.1 vτ.2 hvτ.2)
  have hlift_orbit_cont : ContinuousOn
      (fun vτ : TangentSpace I p × ℝ =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (Φ (z vτ.1, vτ.2)))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (-T') T') :=
    hsymm_cont.comp hΦorbit_cont horbit_maps
  have hcomp_cont : ContinuousOn
      (fun vt : TangentSpace I p × ℝ =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (Φ (z vt.1, vt.2 - tₖ)))
      ((Metric.ball v₀ rfin) ×ˢ Set.Ioo (tₖ - T') (tₖ + T')) :=
    hlift_orbit_cont.comp hshift_cont hshift_maps
  apply hcomp_cont.congr
  rintro ⟨v, s⟩ ⟨hv, hs⟩
  have hs' : s - tₖ ∈ Set.Ioo (-T') T' := by
    rw [Set.mem_Ioo] at hs ⊢
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hB2vs := hB2 v hv (s - tₖ) hs'
  rw [show tₖ + (s - tₖ) = s from by ring] at hB2vs
  have hgeo_src_s : intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source :=
    hB2vs.1
  have hphase :
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) s,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E) =
        Φ (z v, s - tₖ) := hB2vs.2
  have hbridge := phasePoint_eq_extChartAt_tangent_intrinsicVelocityLift
    (I := I) g hEnorm p v α s hgeo_src_s
  have hread : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
      (intrinsicVelocityLift (I := I) g hEnorm p v s) = Φ (z v, s - tₖ) := by
    rw [← hbridge]; exact hphase
  have hlift_mem : intrinsicVelocityLift (I := I) g hEnorm p v s ∈
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M)
      (intrinsicVelocityLift (I := I) g hEnorm p v s)
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hgeo_src_s
  calc intrinsicVelocityLift (I := I) g hEnorm p v s
      = (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
            (intrinsicVelocityLift (I := I) g hEnorm p v s)) :=
        ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hlift_mem).symm
    _ = (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (Φ (z v, s - tₖ)) := by rw [hread]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicGeodesic_window_of_zContinuousOn
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) (tₖ : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hz_cont : ContinuousOn
      (fun v : TangentSpace I p =>
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p v₀ tₖ)
            (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p v₀ tₖ)
            (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E))
      (Metric.ball v₀ r₀))
    (hfootsrc : ∀ v ∈ Metric.ball v₀ r₀,
      intrinsicGeodesic (I := I) g hEnorm p v tₖ ∈
        (chartAt H (intrinsicGeodesic (I := I) g hEnorm p v₀ tₖ)).source) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) := by
  classical
  set α : M := intrinsicGeodesic (I := I) g hEnorm p v₀ tₖ with hα_def
  set z : TangentSpace I p → E × E :=
    fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E)
    with hz_def
  have hx₀_eq : (z v₀).1 = extChartAt I α α := by
    simp only [hz_def, DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    rw [hα_def]
  have hx₀ : (z v₀).1 ∈ interior (extChartAt I α).target := by
    rw [hx₀_eq]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α ((extChartAt I α).map_source (mem_extChartAt_source (I := I) α))
  have hzca : ContinuousAt z v₀ := hz_cont.continuousAt (Metric.ball_mem_nhds v₀ hr₀)
  obtain ⟨Φ, S, T', R, ρ, hS_open, hv₀_S, hT'_pos, hR_pos, hρ_pos,
      hball, hΦ_cont, hΦ_phase, hΦ_in, hΦinit, hz_ball⟩ :=
    exists_chartFlowData_of_zContinuousAt (I := I) g α hx₀ hzca rfl
  obtain ⟨rS, hrS_pos, hrS_sub⟩ := Metric.isOpen_iff.mp hS_open v₀ hv₀_S
  set r : ℝ := min rS r₀ with hr_def
  have hr_pos : 0 < r := lt_min hrS_pos hr₀
  have hr_S : Metric.ball v₀ r ⊆ S := fun x hx =>
    hrS_sub (Metric.ball_subset_ball (min_le_left _ _) hx)


  have hB2 : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      intrinsicGeodesic (I := I) g hEnorm p v (tₖ + s) ∈ (chartAt H α).source ∧
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) (tₖ + s),
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) (tₖ + s)) : E × E) = Φ (z v, s) := by
    intro v hv s hs
    exact intrinsicGeodesic_chart_confined_of_orbit (I := I) g hEnorm p v (α := α)
      (φ := fun s => Φ (z v, s)) (tₖ := tₖ) (T' := T')
      (fun s' hs' => (hball (hΦ_in v (hr_S hv) s' hs')).1)
      (fun s' hs' => hΦ_phase v (hr_S hv) s' hs')
      (hΦinit v (hr_S hv)).symm
      (hfootsrc v (Metric.ball_subset_ball (min_le_right _ _) hv)) s hs
  refine ⟨r, T', hr_pos, hT'_pos, ?_⟩
  exact intrinsicGeodesic_window_of_flowData (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := z v₀) (z := z) (tₖ := tₖ) (r := r) (R := R) (T' := T') (ρ := ρ)
    hT'_pos hball hΦ_cont
    (fun v hv s hs => hΦ_phase v (hr_S hv) s hs)
    (fun v hv s hs => hΦ_in v (hr_S hv) s hs)
    (fun v hv t ht => by
      have hs' : t - tₖ ∈ Set.Ioo (-T') T' := by
        rw [Set.mem_Ioo] at ht; rw [Set.mem_Ioo]; constructor <;> linarith [ht.1, ht.2]
      have h := (hB2 v hv (t - tₖ) hs').1
      rwa [show tₖ + (t - tₖ) = t from by ring] at h)
    (fun v hv t ht => by
      have hs' : t - tₖ ∈ Set.Ioo (-T') T' := by
        rw [Set.mem_Ioo] at ht; rw [Set.mem_Ioo]; constructor <;> linarith [ht.1, ht.2]
      have h := (hB2 v hv (t - tₖ) hs').2
      rw [show tₖ + (t - tₖ) = t from by ring] at h
      rw [h]; exact hΦ_in v (hr_S hv) (t - tₖ) hs')
    (fun v _ => rfl)
    (fun v hv => hΦinit v (hr_S hv))
    (hz_cont.mono (Metric.ball_subset_ball (min_le_right _ _)))
    (fun v hv => hz_ball v (hr_S hv))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicVelocityLift_window_base
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ContinuousOn (fun vs : TangentSpace I p × ℝ =>
        intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (-ε) ε) := by
  classical
  set z : TangentSpace I p → E × E :=
    fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
          (intrinsicGeodesic (I := I) g hEnorm p v) 0,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
          (intrinsicGeodesic (I := I) g hEnorm p v)) 0) : E × E)
    with hz_def
  set x₀ : E := (z v₀).1 with hx₀_def
  set w₀ : E := (z v₀).2 with hw₀_def
  have hx₀_eq : x₀ = extChartAt I p p := by
    rw [hx₀_def, hz_def]
    simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    rw [intrinsicGeodesic_zero (I := I) g hEnorm p v₀]
  have hx₀ : x₀ ∈ interior (extChartAt I p).target := by
    rw [hx₀_eq]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) p ((extChartAt I p).map_source (mem_extChartAt_source (I := I) p))
  have hz_cont_all : Continuous z :=
    intrinsicGeodesic_phasePoint_continuous_zero (I := I) g hEnorm p
  have hz0 : z v₀ = (x₀, w₀) := by rw [hx₀_def, hw₀_def]
  have hgeo : ∀ (b : ContDiffBump ((x₀, w₀) : E × E)),
      Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) →
      ∃ rgeo εgeo : ℝ, 0 < rgeo ∧ 0 < εgeo ∧ rgeo ≤ 1 ∧
      (∀ v ∈ Metric.ball v₀ rgeo, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ t ∈ Set.Ioo ((0:ℝ) - εgeo) (0 + εgeo),
        intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H p).source) ∧
      (∀ v ∈ Metric.ball v₀ rgeo, ∀ t ∈ Set.Ioo ((0:ℝ) - εgeo) (0 + εgeo),
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
            (intrinsicGeodesic (I := I) g hEnorm p v) t,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
            (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
          ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rgeo,
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
            (intrinsicGeodesic (I := I) g hEnorm p v) 0,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
            (intrinsicGeodesic (I := I) g hEnorm p v)) 0) : E × E) = z v) := by
    intro b hb_sub

    obtain ⟨Φ, S, T', R, ρ, hS_open, hv₀_S, hT'_pos, hR_pos, hρ_pos,
        hball, hΦ_cont, hΦ_phase, hΦ_in, hΦinit, hz_ball⟩ :=
      exists_chartFlowData_of_zContinuousAt (I := I) g p hx₀ hz_cont_all.continuousAt rfl
    obtain ⟨rS, hrS_pos, hrS_sub⟩ := Metric.isOpen_iff.mp hS_open v₀ hv₀_S

    have hB2 : ∀ v ∈ Metric.ball v₀ rS, ∀ s ∈ Set.Ioo (-T') T',
        intrinsicGeodesic (I := I) g hEnorm p v (0 + s) ∈ (chartAt H p).source ∧
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
            (intrinsicGeodesic (I := I) g hEnorm p v) (0 + s),
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) p
            (intrinsicGeodesic (I := I) g hEnorm p v)) (0 + s)) : E × E) = Φ (z v, s) := by
      intro v hv s hs
      exact intrinsicGeodesic_chart_confined_of_orbit (I := I) g hEnorm p v (α := p)
        (φ := fun s => Φ (z v, s)) (tₖ := 0) (T' := T')
        (fun s' hs' => (hball (hΦ_in v (hrS_sub hv) s' hs')).1)
        (fun s' hs' => hΦ_phase v (hrS_sub hv) s' hs')
        (hΦinit v (hrS_sub hv)).symm
        (by rw [intrinsicGeodesic_zero (I := I) g hEnorm p v]; exact mem_chart_source H p)
        s hs


    set W : Set (TangentSpace I p × ℝ) :=
      (Metric.ball v₀ rS) ×ˢ Set.Ioo (-T') T' with hW_def
    have hW_open : IsOpen W := Metric.isOpen_ball.prod isOpen_Ioo
    have hF_cont : ContinuousOn (fun vs : TangentSpace I p × ℝ => Φ (z vs.1, vs.2)) W := by
      have h1 : ContinuousOn (fun vs : TangentSpace I p × ℝ => (z vs.1, vs.2)) W :=
        (hz_cont_all.comp_continuousOn continuousOn_fst).prodMk continuousOn_snd
      have hmaps : Set.MapsTo (fun vs : TangentSpace I p × ℝ => (z vs.1, vs.2)) W
          ((Metric.ball (z v₀) ρ) ×ˢ Set.Ioo (-T') T') :=
        fun vs hvs => ⟨hz_ball vs.1 (hrS_sub hvs.1), hvs.2⟩
      exact hΦ_cont.comp h1 hmaps
    have hF_v₀0 : Φ (z v₀, 0) = ((x₀, w₀) : E × E) := by rw [hΦinit v₀ hv₀_S, hz0]
    have hpre_open : IsOpen (W ∩ (fun vs : TangentSpace I p × ℝ => Φ (z vs.1, vs.2)) ⁻¹'
        Metric.ball ((x₀, w₀) : E × E) b.rIn) :=
      hF_cont.isOpen_inter_preimage hW_open Metric.isOpen_ball
    have hpt_pre : ((v₀, 0) : TangentSpace I p × ℝ) ∈
        W ∩ (fun vs : TangentSpace I p × ℝ => Φ (z vs.1, vs.2)) ⁻¹'
          Metric.ball ((x₀, w₀) : E × E) b.rIn := by
      refine ⟨⟨Metric.mem_ball_self hrS_pos, ⟨by linarith, hT'_pos⟩⟩, ?_⟩
      rw [Set.mem_preimage, hF_v₀0]; exact Metric.mem_ball_self b.rIn_pos
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hpre_open _ hpt_pre

    have hz_pre : z ⁻¹' Metric.ball ((x₀, w₀) : E × E) b.rIn ∈ nhds v₀ :=
      (hz_cont_all.continuousAt).preimage_mem_nhds
        (by rw [hz0]; exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self b.rIn_pos))
    obtain ⟨δz, hδz_pos, hδz_sub⟩ := Metric.mem_nhds_iff.mp hz_pre
    refine ⟨min (min δ rS) (min δz 1), min δ T', lt_min (lt_min hδ_pos hrS_pos)
      (lt_min hδz_pos one_pos), lt_min hδ_pos hT'_pos, le_trans (min_le_right _ _)
      (min_le_right _ _), ?_, ?_, ?_, ?_⟩
    ·
      intro v hv
      exact hδz_sub (Metric.ball_subset_ball
        (le_trans (min_le_right _ _) (min_le_left _ _)) hv)
    ·
      intro v hv t ht
      have hvS : v ∈ Metric.ball v₀ rS := Metric.ball_subset_ball
        (le_trans (min_le_left _ _) (min_le_right _ _)) hv
      have htT' : t ∈ Set.Ioo (-T') T' := by
        rw [Set.mem_Ioo] at ht ⊢
        exact ⟨by linarith [ht.1, min_le_right δ T'], by linarith [ht.2, min_le_right δ T']⟩
      have h := (hB2 v hvS t htT').1
      rwa [zero_add] at h
    ·
      intro v hv t ht
      have hvS : v ∈ Metric.ball v₀ rS := Metric.ball_subset_ball
        (le_trans (min_le_left _ _) (min_le_right _ _)) hv
      have htT' : t ∈ Set.Ioo (-T') T' := by
        rw [Set.mem_Ioo] at ht ⊢
        exact ⟨by linarith [ht.1, min_le_right δ T'], by linarith [ht.2, min_le_right δ T']⟩
      have hmatch := (hB2 v hvS t htT').2
      rw [zero_add] at hmatch
      rw [hmatch]

      have hvt_δ : (v, t) ∈ Metric.ball ((v₀, 0) : TangentSpace I p × ℝ) δ := by
        rw [Metric.mem_ball, Prod.dist_eq]
        refine max_lt ?_ ?_
        · have : dist v v₀ < δ := by
            have := Metric.ball_subset_ball
              (le_trans (min_le_left _ _) (min_le_left _ _)) hv
            rwa [Metric.mem_ball] at this
          exact this
        · rw [Real.dist_eq, sub_zero, abs_lt]
          rw [Set.mem_Ioo] at ht
          exact ⟨by linarith [ht.1, min_le_left δ T'], by linarith [ht.2, min_le_left δ T']⟩
      exact Metric.ball_subset_closedBall (hδ_sub hvt_δ).2
    ·
      intro v _
      rfl
  obtain ⟨r, ε, hr, hε, hlift⟩ :=
    intrinsicVelocityLift_window_of_junction_data (I := I) g hEnorm p v₀ p
      (x₀ := x₀) (w₀ := w₀) hx₀ (z := z) (tₖ := 0) (rz := 1) one_pos
      hz_cont_all.continuousOn hz0 hgeo
  exact ⟨r, ε, hr, hε, by simpa only [zero_sub, zero_add] using hlift⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
private theorem intrinsicVelocityLift_step_uniformWidth
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) (α : M) (τ : ℝ)
    {z₀ : E × E} {Φ : (E × E) × ℝ → E × E} {b : ContDiffBump z₀}
    {T' ρ : ℝ} (hT'_pos : 0 < T') (hρ_pos : 0 < ρ)
    (hballOut : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hΦ_cont : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T') T'))
    (hΦ_phase : ∀ w ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ' => Φ (w, τ')) (chartPhaseVF (I := I) g α (Φ (w, s))) s)
    (hΦ_in : ∀ w ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T') T',
      Φ (w, s) ∈ Metric.closedBall z₀ b.rIn)
    (hΦinit : ∀ w ∈ Metric.ball z₀ ρ, Φ (w, 0) = w)
    (hα_src : intrinsicGeodesic (I := I) g hEnorm p v₀ τ ∈ (chartAt H α).source)
    (hphase_near :
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v₀) τ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v₀)) τ) : E × E) ∈ Metric.ball z₀ ρ)
    {r₀ a c : ℝ} (hr₀ : 0 < r₀) (hτ_mem : τ ∈ Set.Ioo a c)
    (hlift_cont : ContinuousOn
      (fun vs : TangentSpace I p × ℝ =>
        intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
      ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c)) :
    ∃ r : ℝ, 0 < r ∧
      ContinuousOn
        (fun vs : TangentSpace I p × ℝ =>
          intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (τ - T') (τ + T')) := by
  classical
  set z : TangentSpace I p → E × E :=
    fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) τ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) τ) : E × E)
    with hz_def
  set x₀ : E := (z v₀).1 with hx₀_def
  set w₀ : E := (z v₀).2 with hw₀_def
  have hx₀_eq : x₀ = extChartAt I α (intrinsicGeodesic (I := I) g hEnorm p v₀ τ) := by
    simp only [hx₀_def, hz_def,
      DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
  have hx₀ : x₀ ∈ interior (extChartAt I α).target := by
    rw [hx₀_eq]
    have hsrc' : intrinsicGeodesic (I := I) g hEnorm p v₀ τ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hα_src
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α ((extChartAt I α).map_source hsrc')
  have hz0 : z v₀ = (x₀, w₀) := by rw [hx₀_def, hw₀_def]

  obtain ⟨rz, hrz, hz_cont, _hgeo⟩ :=
    intrinsicGeodesic_junctionData_of_lift_continuousOn (I := I) g hEnorm p v₀ τ
      (α := α) hα_src (z := z) hz_def (x₀ := x₀) (w₀ := w₀) hx₀_def hw₀_def hx₀ hz0
      hr₀ hτ_mem hlift_cont

  set L : TangentSpace I p × ℝ → TangentBundle I M :=
    fun vs => intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2 with hL_def
  have hfoot_cont : ContinuousOn (fun vs : TangentSpace I p × ℝ => (L vs).proj)
      ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hlift_cont
  have hpreim_open : IsOpen
      (((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c) ∩
        (fun vs : TangentSpace I p × ℝ => (L vs).proj) ⁻¹' (chartAt H α).source) :=
    hfoot_cont.isOpen_inter_preimage (Metric.isOpen_ball.prod isOpen_Ioo)
      (chartAt H α).open_source
  have hpt_preim : ((v₀, τ) : TangentSpace I p × ℝ) ∈
      ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c) ∩
        (fun vs : TangentSpace I p × ℝ => (L vs).proj) ⁻¹' (chartAt H α).source := by
    refine ⟨⟨Metric.mem_ball_self hr₀, hτ_mem⟩, ?_⟩
    rw [Set.mem_preimage]; exact hα_src
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hpreim_open _ hpt_preim
  have hsrc : ∀ v ∈ Metric.ball v₀ δ,
      intrinsicGeodesic (I := I) g hEnorm p v τ ∈ (chartAt H α).source := by
    intro v hv
    have hvτ : ((v, τ) : TangentSpace I p × ℝ) ∈
        Metric.ball ((v₀, τ) : TangentSpace I p × ℝ) δ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp hv) (by rw [dist_self]; exact hδ_pos)
    exact (hδ_sub hvτ).2

  refine intrinsicVelocityLift_window_of_flow (I := I) g hEnorm p v₀ α
    (z₀ := z₀) (Φ := Φ) (b := b) (T' := T') (ρ := ρ) hT'_pos hρ_pos hballOut
    hΦ_cont hΦ_phase hΦ_in hΦinit
    (z := z) (tₖ := τ) (rz := min rz δ) (lt_min hrz hδ_pos)
    (hz_cont.mono (Metric.ball_subset_ball (min_le_left _ _)))
    ?_ ?_ ?_
  · show z v₀ ∈ Metric.ball z₀ ρ
    rw [hz_def]; exact hphase_near
  · intro v _; rw [hz_def]
  · intro v hv
    exact hsrc v (Metric.ball_subset_ball (min_le_right _ _) hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem intrinsicGeodesic_jointContinuity
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E


  have key : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ r₀ a c : ℝ, 0 < r₀ ∧ t ∈ Set.Ioo a c ∧
      ContinuousOn (fun vs : TangentSpace I p × ℝ =>
        intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
        ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c) := by
    set L : TangentSpace I p × ℝ → TangentBundle I M :=
      fun vs => intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2 with hL_def
    set Good : Set ℝ := {c : ℝ | 0 < c ∧ c ≤ 2 ∧ ∃ r a : ℝ, 0 < r ∧ a < 0 ∧
      ContinuousOn L ((Metric.ball v₀ r) ×ˢ Set.Ioo a c)} with hGood_def
    obtain ⟨rb, εb, hrb, hεb, hbase⟩ :=
      intrinsicVelocityLift_window_base (I := I) g hEnorm p v₀
    have hc0_Good : min εb 2 ∈ Good := by
      refine ⟨lt_min hεb (by norm_num), min_le_right _ _, rb, -εb, hrb, by linarith, ?_⟩
      exact hbase.mono (Set.prod_mono_right (Set.Ioo_subset_Ioo le_rfl (min_le_left _ _)))
    have hGood_ne : Good.Nonempty := ⟨min εb 2, hc0_Good⟩
    have hGood_bdd : BddAbove Good := ⟨2, fun c hc => hc.2.1⟩
    set S : ℝ := sSup Good with hS_def
    have hc0_le_S : min εb 2 ≤ S := le_csSup hGood_bdd hc0_Good
    have hS_pos : 0 < S := lt_of_lt_of_le (lt_min hεb (by norm_num)) hc0_le_S
    have hS_gt1 : 1 < S := by
      by_contra hle
      push_neg at hle


      set αS : M := intrinsicGeodesic (I := I) g hEnorm p v₀ S with hαS_def
      have hzc1_int :
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) S,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) S) : E × E).1 ∈
            interior (extChartAt I αS).target := by
        simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
        rw [← hαS_def]
        exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
          (I := I) αS ((extChartAt I αS).map_source (mem_extChartAt_source (I := I) αS))
      obtain ⟨Φ, b, T', ρ, hT'_pos, hρ_pos, hballOut, hΦ_cont, hΦ_phase, hΦ_in, hΦinit⟩ :=
        exists_chartFlow_confined (I := I) g αS
          (z₀ := ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) S,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) S) : E × E)) hzc1_int

      have hγcont : Continuous (intrinsicGeodesic (I := I) g hEnorm p v₀) :=
        intrinsicGeodesic_continuous (I := I) g hEnorm p v₀
      have hαS_src : intrinsicGeodesic (I := I) g hEnorm p v₀ S ∈ (chartAt H αS).source := by
        rw [← hαS_def]; exact mem_chart_source H αS
      have hUpre : (intrinsicGeodesic (I := I) g hEnorm p v₀) ⁻¹' (chartAt H αS).source ∈ 𝓝 S :=
        hγcont.continuousAt.preimage_mem_nhds ((chartAt H αS).open_source.mem_nhds hαS_src)
      obtain ⟨U, hU_sub, hU_open, hSU⟩ := _root_.mem_nhds_iff.mp hUpre
      have hζ_contAt : ContinuousAt
          (fun t : ℝ => ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) t,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) t) : E × E)) S :=
        (geodesic_chartPhaseVF_on_open (I := I) (g := g) (α := αS)
          (γ := intrinsicGeodesic (I := I) g hEnorm p v₀)
          (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v₀) hγcont hU_open
          (fun s hs => hU_sub hs) S hSU).1.continuousAt
      have hpre1 :
          (fun t : ℝ => ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) t,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) t) : E × E)) ⁻¹'
            Metric.ball ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) S,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) S) : E × E) ρ ∈ 𝓝 S :=
        hζ_contAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ_pos)
      obtain ⟨δS, hδS_pos, hδS_sub⟩ :=
        Metric.mem_nhds_iff.mp (Filter.inter_mem hpre1 hUpre)

      have hmin_pos : 0 < min δS T' := lt_min hδS_pos hT'_pos
      obtain ⟨c', hc'_Good, hc'_gt⟩ :=
        exists_lt_of_lt_csSup hGood_ne (show S - min δS T' / 2 < S from by linarith)
      have hc'_le_S : c' ≤ S := le_csSup hGood_bdd hc'_Good
      obtain ⟨hc'_pos, _hc'_le2, r', a', hr', ha', hcont'⟩ := hc'_Good
      have hca_pos : 0 < c' - a' := by linarith
      set m : ℝ := min (min δS T') (c' - a') with hm_def
      have hm_le1 : m ≤ min δS T' := min_le_left _ _
      have hm_le2 : m ≤ c' - a' := min_le_right _ _
      have hm_pos : 0 < m := lt_min hmin_pos hca_pos
      have hδST' : min δS T' ≤ δS := min_le_left _ _
      have hδST'2 : min δS T' ≤ T' := min_le_right _ _
      have hSc' : S - c' < min δS T' / 2 := by linarith
      set τ : ℝ := c' - m / 4 with hτ_def
      have hτ_lt_c' : τ < c' := by rw [hτ_def]; linarith
      have hτ_gt_a' : a' < τ := by rw [hτ_def]; linarith
      have hτ_mem : τ ∈ Set.Ioo a' c' := ⟨hτ_gt_a', hτ_lt_c'⟩
      have hτ_ball : τ ∈ Metric.ball S δS := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        refine ⟨?_, ?_⟩
        · rw [hτ_def]; linarith
        · rw [hτ_def]; linarith
      have hτ_inter := hδS_sub hτ_ball
      have hα_src_τ : intrinsicGeodesic (I := I) g hEnorm p v₀ τ ∈ (chartAt H αS).source :=
        hτ_inter.2
      have hphase_near :
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) τ,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) τ) : E × E) ∈
            Metric.ball ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) S,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) S) : E × E) ρ :=
        hτ_inter.1
      obtain ⟨r'', hr'', hstep⟩ :=
        intrinsicVelocityLift_step_uniformWidth (I := I) g hEnorm p v₀ αS τ
          (z₀ := ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀) S,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) αS
              (intrinsicGeodesic (I := I) g hEnorm p v₀)) S) : E × E))
          (Φ := Φ) (b := b) (T' := T') (ρ := ρ) hT'_pos hρ_pos hballOut
          hΦ_cont hΦ_phase hΦ_in hΦinit hα_src_τ hphase_near
          (r₀ := r') (a := a') (c := c') hr' hτ_mem hcont'


      set rg : ℝ := min r' r'' with hrg_def
      set cg : ℝ := max c' (τ + T') with hcg_def
      have hglue : ContinuousOn L ((Metric.ball v₀ rg) ×ˢ Set.Ioo a' cg) := by
        rintro ⟨v, s⟩ ⟨hv, hs⟩
        rw [Set.mem_Ioo] at hs
        by_cases hsc : s < c'
        · have hmem1 : ((v, s) : TangentSpace I p × ℝ) ∈
              (Metric.ball v₀ r') ×ˢ Set.Ioo a' c' :=
            ⟨Metric.ball_subset_ball (min_le_left _ _) hv, ⟨hs.1, hsc⟩⟩
          exact ((hcont' _ hmem1).continuousAt
            ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hmem1)).continuousWithinAt
        · push_neg at hsc
          have hs_lt : s < τ + T' := (lt_max_iff.mp hs.2).resolve_left (not_lt.mpr hsc)
          have hmem2 : ((v, s) : TangentSpace I p × ℝ) ∈
              (Metric.ball v₀ r'') ×ˢ Set.Ioo (τ - T') (τ + T') :=
            ⟨Metric.ball_subset_ball (min_le_right _ _) hv,
              ⟨by rw [hτ_def]; linarith, hs_lt⟩⟩
          exact ((hstep _ hmem2).continuousAt
            ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hmem2)).continuousWithinAt
      have hcg_gt_c' : c' ≤ cg := le_max_left _ _
      have hnew_Good : min cg 2 ∈ Good := by
        refine ⟨lt_of_lt_of_le hc'_pos (le_min hcg_gt_c' ?_), min_le_right _ _,
          rg, a', lt_min hr' hr'', ha', ?_⟩
        · linarith
        · exact hglue.mono (Set.prod_mono_right
            (Set.Ioo_subset_Ioo le_rfl (min_le_left _ _)))
      have hnew_gt : S < min cg 2 := by
        have hcg_gt_S : S < cg := by
          have hτT' : S < τ + T' := by rw [hτ_def]; linarith
          exact lt_of_lt_of_le hτT' (le_max_right _ _)
        exact lt_min hcg_gt_S (by linarith)
      exact absurd (le_csSup hGood_bdd hnew_Good) (not_le.mpr hnew_gt)
    obtain ⟨c, hc_Good, hc_gt1⟩ := exists_lt_of_lt_csSup hGood_ne hS_gt1
    obtain ⟨_hc_pos, _hc_le2, r, a, hr, ha, hcont⟩ := hc_Good
    intro t ht
    exact ⟨r, a, c, hr, ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hc_gt1⟩, hcont⟩
  refine continuousOn_ball_prod_Icc_of_local_windows (V := TangentSpace I p) v₀
    (fun vt => intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2) ?_
  intro t ht
  set α : M := intrinsicGeodesic (I := I) g hEnorm p v₀ t with hα_def
  set z : TangentSpace I p → E × E :=
    fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
    with hz_def
  set x₀ : E := (z v₀).1 with hx₀_def
  set w₀ : E := (z v₀).2 with hw₀_def
  have hα_foot : intrinsicGeodesic (I := I) g hEnorm p v₀ t = α := rfl
  have hx₀_eq : x₀ = extChartAt I α α := by
    rw [hx₀_def, hz_def]
    simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    rw [hα_foot]
  have hx₀ : x₀ ∈ interior (extChartAt I α).target := by
    rw [hx₀_eq]
    have hsrc : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
    have htgt : extChartAt I α α ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α htgt
  have hz0 : z v₀ = (x₀, w₀) := by rw [hx₀_def, hw₀_def]
  obtain ⟨rz, hrz, hz_cont, hgeo⟩ :
      ∃ rz : ℝ, 0 < rz ∧ ContinuousOn z (Metric.ball v₀ rz) ∧
      (∀ (b : ContDiffBump ((x₀, w₀) : E × E)),
        Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
          (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) →
        ∃ rgeo εgeo : ℝ, 0 < rgeo ∧ 0 < εgeo ∧ rgeo ≤ rz ∧
        (∀ v ∈ Metric.ball v₀ rgeo, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) ∧
        (∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
          intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source) ∧
        (∀ v ∈ Metric.ball v₀ rgeo, ∀ s ∈ Set.Ioo (t - εgeo) (t + εgeo),
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v) s,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E)
            ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
        (∀ v ∈ Metric.ball v₀ rgeo,
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v) t,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E) = z v)) := by


    obtain ⟨r₀, a, c, hr₀, ht_mem, hlift⟩ :
        ∃ r₀ a c : ℝ, 0 < r₀ ∧ t ∈ Set.Ioo a c ∧
          ContinuousOn (fun vs : TangentSpace I p × ℝ =>
            intrinsicVelocityLift (I := I) g hEnorm p vs.1 vs.2)
            ((Metric.ball v₀ r₀) ×ˢ Set.Ioo a c) := key t ht
    have hα_src : intrinsicGeodesic (I := I) g hEnorm p v₀ t ∈ (chartAt H α).source := by
      rw [hα_foot]; exact mem_chart_source H α
    exact intrinsicGeodesic_junctionData_of_lift_continuousOn (I := I) g hEnorm p v₀ t
      (α := α) hα_src (z := z) hz_def (x₀ := x₀) (w₀ := w₀) hx₀_def hw₀_def hx₀ hz0
      hr₀ ht_mem hlift
  exact intrinsicGeodesic_window_of_junction_data (I := I) g hEnorm p v₀ α
    (x₀ := x₀) (w₀ := w₀) hx₀ (z := z) (tₖ := t) (rz := rz) hrz hz_cont hz0 hgeo


attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem expMapIntrinsic_continuous_of_jointContinuity
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M)
    (hjoint : ∀ v₀ : TangentSpace I p, ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    Continuous (fun v : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p v) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨ρ, hρ, hcont⟩ := hjoint v₀
  set F : TangentSpace I p × ℝ → M :=
    fun vt => intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2 with hF_def
  set sl : TangentSpace I p → TangentSpace I p × ℝ := fun v => (v, 1) with hsl_def
  have hcomp_eq :
      (fun v : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p v) = F ∘ sl := by
    funext v
    simp only [Function.comp_apply, hF_def, hsl_def, expMapIntrinsic]
  rw [hcomp_eq]
  have hsl_cont : Continuous sl := by
    rw [hsl_def]; exact continuous_id.prodMk continuous_const
  have hsl_maps : Set.MapsTo sl (Metric.ball v₀ ρ)
      ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro v hv
    exact ⟨hv, ⟨zero_le_one, le_refl 1⟩⟩
  have hball_nhds : Metric.ball v₀ ρ ∈ 𝓝 v₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hcw : ContinuousWithinAt (F ∘ sl) (Metric.ball v₀ ρ) v₀ := by
    apply ContinuousOn.continuousWithinAt _ (Metric.mem_ball_self hρ)
    exact hcont.comp hsl_cont.continuousOn hsl_maps
  exact hcw.continuousAt hball_nhds

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [Module.Finite ℝ E] in
omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem expMapIntrinsic_continuous
    [Module.Finite ℝ E]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    Continuous (fun v : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p v) :=
  expMapIntrinsic_continuous_of_jointContinuity (I := I) g hEnorm p
    (fun v₀ => intrinsicGeodesic_jointContinuity (I := I) g hEnorm p v₀)

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
