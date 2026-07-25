import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformUniqueness
import DifferentialGeometry.Geometry.Geodesic.GeodesicEquationFromIntegralCurve
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow



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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic

section UniformConfinement

variable [I.Boundaryless] [CompleteSpace E]


omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E] in
lemma exists_uniform_orbit_in_inner_ball
    (p : M)
    {x₀ : E} (_hx₀_def : x₀ = extChartAt I p p)
    {b : ContDiffBump ((x₀, (0 : E)) : E × E)}
    {ρ_V4 T_V4 : ℝ} (hρ_V4_pos : 0 < ρ_V4) (hT_V4_pos : 0 < T_V4)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_cd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V4) ×ˢ Set.Ioo (-T_V4) T_V4))
    (hΦ_init0 : Φ (((x₀, (0 : E)) : E × E), 0) = (x₀, (0 : E))) :
    ∃ (ρ T : ℝ), 0 < ρ ∧ 0 < T ∧ ρ ≤ ρ_V4 ∧ T < T_V4 ∧
      ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((x₀, v) : E × E), s) ∈ Metric.ball ((x₀, (0 : E)) : E × E) b.rIn := by
  classical
  have h_open : IsOpen
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ_V4) ×ˢ Set.Ioo (-T_V4) T_V4) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hz₀_mem : (((x₀, (0 : E)) : E × E), (0 : ℝ)) ∈
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ_V4) ×ˢ Set.Ioo (-T_V4) T_V4 :=
    ⟨Metric.mem_ball_self hρ_V4_pos, ⟨by linarith, hT_V4_pos⟩⟩
  have hΦ_cont : ContinuousAt Φ (((x₀, (0 : E)) : E × E), (0 : ℝ)) := by
    have hcdf : ContDiffOn ℝ 1 Φ _ := hΦ_cd
    have := hcdf.continuousOn
    exact this.continuousAt (h_open.mem_nhds hz₀_mem)
  have hΨ_cont : ContinuousAt (fun w : E × ℝ => Φ (((x₀, w.1) : E × E), w.2))
      ((0 : E), (0 : ℝ)) := by
    have h1 : Continuous (fun w : E × ℝ => (((x₀, w.1) : E × E), w.2)) := by
      apply Continuous.prodMk
      · exact (continuous_const.prodMk continuous_fst)
      · exact continuous_snd
    have h1_at_explicit : ContinuousAt
        (fun w : E × ℝ => (((x₀, w.1) : E × E), w.2))
        ((0 : E), (0 : ℝ)) := h1.continuousAt
    have h1_val : (fun w : E × ℝ => (((x₀, w.1) : E × E), w.2))
        ((0 : E), (0 : ℝ)) = (((x₀, (0 : E)) : E × E), (0 : ℝ)) := rfl
    have := ContinuousAt.comp (f := fun w : E × ℝ => (((x₀, w.1) : E × E), w.2))
      (g := Φ) (x := ((0 : E), (0 : ℝ))) ?_ h1_at_explicit
    · exact this
    · rw [h1_val]; exact hΦ_cont
  have h_inner_nhds : Metric.ball ((x₀, (0 : E)) : E × E) b.rIn ∈
      𝓝 ((x₀, (0 : E)) : E × E) :=
    Metric.ball_mem_nhds _ b.rIn_pos
  have h_preim : (fun w : E × ℝ => Φ (((x₀, w.1) : E × E), w.2)) ⁻¹'
      (Metric.ball ((x₀, (0 : E)) : E × E) b.rIn) ∈ 𝓝 ((0 : E), (0 : ℝ)) := by
    apply hΨ_cont.preimage_mem_nhds
    simp only [hΦ_init0]
    exact Metric.ball_mem_nhds _ b.rIn_pos
  obtain ⟨U, V, hU_open, hU_mem, hV_open, hV_mem, h_subset⟩ :=
    mem_nhds_prod_iff'.mp h_preim
  obtain ⟨ρ₀, hρ₀_pos, hρ₀_sub⟩ :=
    Metric.isOpen_iff.mp hU_open (0 : E) hU_mem
  obtain ⟨T₀, hT₀_pos, hT₀_sub⟩ :=
    Metric.isOpen_iff.mp hV_open (0 : ℝ) hV_mem
  have hT₀_Ioo : Set.Ioo (-T₀) T₀ ⊆ V := by
    intro s hs
    apply hT₀_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hs
  set ρ : ℝ := min ρ₀ ρ_V4 / 2 with hρ_def
  have hρ_pos : 0 < ρ := by
    apply div_pos
    · exact lt_min hρ₀_pos hρ_V4_pos
    · norm_num
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := by
    rw [hρ_def]
    have h1 : min ρ₀ ρ_V4 ≤ ρ₀ := min_le_left _ _
    linarith
  have hρ_le_ρ_V4 : ρ ≤ ρ_V4 := by
    rw [hρ_def]
    have h1 : min ρ₀ ρ_V4 ≤ ρ_V4 := min_le_right _ _
    linarith
  set T : ℝ := min T₀ (T_V4 / 2) / 2 with hT_def
  have hTmin_pos : 0 < min T₀ (T_V4 / 2) :=
    lt_min hT₀_pos (by linarith)
  have hT_pos : 0 < T := by
    rw [hT_def]; positivity
  have hT_le_T₀ : T < T₀ := by
    rw [hT_def]
    have h1 : min T₀ (T_V4 / 2) ≤ T₀ := min_le_left _ _
    linarith
  have hT_lt_T_V4 : T < T_V4 := by
    rw [hT_def]
    have h1 : min T₀ (T_V4 / 2) ≤ T_V4 / 2 := min_le_right _ _
    linarith
  refine ⟨ρ, T, hρ_pos, hT_pos, hρ_le_ρ_V4, hT_lt_T_V4, ?_⟩
  intro v hv s hs
  have hv_in_U : v ∈ U := by
    apply hρ₀_sub
    rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    have : ‖v‖ < ρ := hv
    have : ‖v‖ < ρ₀ := lt_of_lt_of_le this hρ_le_ρ₀
    exact this
  have hs_in_V : s ∈ V := by
    apply hT₀_Ioo
    refine ⟨?_, ?_⟩
    · linarith [hs.1]
    · linarith [hs.2]
  have h_pair : (v, s) ∈ U ×ˢ V := ⟨hv_in_U, hs_in_V⟩
  exact h_subset h_pair

end UniformConfinement

section UniformChartCoordExistence

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlow_uniform_orbit
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (b : ContDiffBump (((extChartAt I p p, (0 : E)) : E × E)))
      (r : ℝ≥0) (ε : ℝ) (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧
      Metric.closedBall (((extChartAt I p p, (0 : E)) : E × E)) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g p ((extChartAt I p p, (0 : E)) : E × E) b)
        (0 : ℝ) ((extChartAt I p p, (0 : E)) : E × E) r (-ε) ε Φ ∧
      Φ ((((extChartAt I p p, (0 : E)) : E × E)), 0) =
        ((extChartAt I p p, (0 : E)) : E × E) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          Metric.ball (((extChartAt I p p, (0 : E)) : E × E)) b.rIn) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨b, r, ε, ρ_V4, T_V4, Φ, hr, hε, hρ_V4_pos, hT_V4_pos, hb_sub, hΦ_ILF,
    hΦ_cd, hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined
      (I := I) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  obtain ⟨ρ, T, hρ_pos, hT_pos, _hρ_le_V4, _hT_lt_V4, h_orbit_in⟩ :=
    exists_uniform_orbit_in_inner_ball (I := I) (p := p)
      (x₀ := x₀) hx₀_def
      (b := b) (ρ_V4 := ρ_V4) (T_V4 := T_V4) hρ_V4_pos hT_V4_pos
      (Φ := Φ) hΦ_cd hΦ_init0
  exact ⟨b, r, ε, ρ, T, Φ, hr, hε, hρ_pos, hT_pos, hb_sub, hΦ_ILF, hΦ_init0,
    h_orbit_in⟩

end UniformChartCoordExistence

section UniformChartPhaseODE

variable [I.Boundaryless] [CompleteSpace E]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
lemma orbit_hasDerivAt_chartPhaseVF_uniform
    (g : SmoothRiemannianMetric I M) (p : M)
    {x₀ : E} (_hx₀_def : x₀ = extChartAt I p p)
    {b : ContDiffBump ((x₀, (0 : E)) : E × E)}
    {r : ℝ≥0} {ε : ℝ} (_hr_pos : 0 < r) (_hε_pos : 0 < ε)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_ILF : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b)
        (0 : ℝ) ((x₀, (0 : E)) : E × E) r (-ε) ε Φ)
    (_hb_sub : Metric.closedBall ((x₀, (0 : E)) : E × E) b.rOut ⊆
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    {ρ T : ℝ} (_hρ_pos : 0 < ρ) (_hT_pos : 0 < T) (hT_lt_ε : T < ε)
    (hρ_le_r : ρ ≤ (r : ℝ))
    (h_orbit_in : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        Metric.ball (((x₀, (0 : E)) : E × E)) b.rIn) :
    ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
  intro v hv s hs
  classical
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have hv_in : ((x₀, v) : E × E) ∈
      Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
    rw [Metric.mem_closedBall, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hv_r : ‖v‖ ≤ (r : ℝ) := le_of_lt (lt_of_lt_of_le hv hρ_le_r)
    exact max_le hr_nn hv_r
  have hs_Icc_ε : s ∈ Set.Icc (-ε) ε := by
    refine ⟨?_, ?_⟩
    · linarith [hs.1]
    · linarith [hs.2]
  have hs_Ioo_ε : s ∈ Set.Ioo (-ε) ε := by
    refine ⟨?_, ?_⟩
    · linarith [hs.1]
    · linarith [hs.2]
  have hs_Icc_T : s ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self hs
  have hd_within := hΦ_ILF.hasDerivWithinAt ((x₀, v) : E × E) hv_in s hs_Icc_ε
  have hVFTime_apply :
      chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b s
        (Φ (((x₀, v) : E × E), s)) =
      chartPhaseVFCutoff (I := I) g p ((x₀, (0 : E)) : E × E) b
        (Φ (((x₀, v) : E × E), s)) := rfl
  rw [hVFTime_apply] at hd_within
  have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs_Ioo_ε
  have hIcc_nhds : Set.Icc (-ε) ε ∈ 𝓝 s :=
    Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
  have hd_cutoff :
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVFCutoff (I := I) g p ((x₀, (0 : E)) : E × E) b
          (Φ (((x₀, v) : E × E), s))) s := hd_within.hasDerivAt hIcc_nhds
  have h_in : Φ (((x₀, v) : E × E), s) ∈
      Metric.ball ((x₀, (0 : E)) : E × E) b.rIn := h_orbit_in v hv s hs_Icc_T
  have h_in_closed : Φ (((x₀, v) : E × E), s) ∈
      Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
    Metric.ball_subset_closedBall h_in
  have h_eq :
      chartPhaseVFCutoff (I := I) g p ((x₀, (0 : E)) : E × E) b
        (Φ (((x₀, v) : E × E), s)) =
      chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s)) :=
    chartPhaseVFCutoff_eq_of_mem_closedBall (I := I)
      (g := g) (α := p) (z₀ := ((x₀, (0 : E)) : E × E)) (b := b) h_in_closed
  rw [h_eq] at hd_cutoff
  exact hd_cutoff

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_orbit_hasDerivAt_chartPhaseVF
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (b : ContDiffBump (((extChartAt I p p, (0 : E)) : E × E)))
      (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      Metric.closedBall (((extChartAt I p p, (0 : E)) : E × E)) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) =
          ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          Metric.ball ((extChartAt I p p, (0 : E)) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) := by
  classical
  obtain ⟨b, r, ε, ρ₀, T₀, Φ, hr, hε, hρ₀_pos, hT₀_pos, hb_sub, hΦ_ILF,
    _hΦ_init, h_orbit_in⟩ :=
    exists_chartFlow_uniform_orbit (I := I) (g := g) (p := p)
  set ρ : ℝ := min ρ₀ ((r : ℝ) / 2) with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min hρ₀_pos
    have : (0 : ℝ) < (r : ℝ) := hr
    linarith
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ_le_r : ρ ≤ (r : ℝ) := by
    rw [hρ_def]
    have h1 : min ρ₀ ((r : ℝ) / 2) ≤ (r : ℝ) / 2 := min_le_right _ _
    have h2 : (r : ℝ) / 2 ≤ (r : ℝ) := by
      have hrnn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
      linarith
    linarith
  set T : ℝ := min T₀ (ε / 2) with hT_def
  have hT_pos : 0 < T :=
    lt_min hT₀_pos (by linarith)
  have hT_le_T₀ : T ≤ T₀ := min_le_left _ _
  have hT_lt_ε : T < ε := by
    have h1 : min T₀ (ε / 2) ≤ ε / 2 := min_le_right _ _
    have : T = min T₀ (ε / 2) := hT_def
    rw [this]; linarith
  refine ⟨b, ρ, T, Φ, hρ_pos, hT_pos, hb_sub, ?_, ?_, ?_⟩
  · intro v hv
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
    have hv_in : ((extChartAt I p p, v) : E × E) ∈
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) (r : ℝ) := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      rw [Metric.mem_ball, dist_zero_right] at hv
      have hv_r : ‖v‖ ≤ (r : ℝ) := le_of_lt (lt_of_lt_of_le hv hρ_le_r)
      exact max_le hr_nn hv_r
    exact hΦ_ILF.apply_initial ((extChartAt I p p, v) : E × E) hv_in
  · intro v hv s hs
    have hv_ρ₀ : v ∈ Metric.ball (0 : E) ρ₀ := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      have : ‖v‖ < ρ := hv
      exact lt_of_lt_of_le this hρ_le_ρ₀
    have hs_T₀ : s ∈ Set.Icc (-T₀) T₀ := by
      refine ⟨?_, ?_⟩
      · linarith [hs.1]
      · linarith [hs.2]
    exact h_orbit_in v hv_ρ₀ s hs_T₀
  · intro v hv s hs
    have hv_ρ₀ : v ∈ Metric.ball (0 : E) ρ₀ := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      have : ‖v‖ < ρ := hv
      exact lt_of_lt_of_le this hρ_le_ρ₀
    have h_inner_T : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          Metric.ball (((extChartAt I p p, (0 : E)) : E × E)) b.rIn := by
      intro v' hv' s' hs'
      have hv'_ρ₀ : v' ∈ Metric.ball (0 : E) ρ₀ := by
        rw [Metric.mem_ball, dist_zero_right] at hv' ⊢
        have : ‖v'‖ < ρ := hv'
        exact lt_of_lt_of_le this hρ_le_ρ₀
      have hs'_T₀ : s' ∈ Set.Icc (-T₀) T₀ := by
        refine ⟨?_, ?_⟩
        · linarith [hs'.1]
        · linarith [hs'.2]
      exact h_orbit_in v' hv'_ρ₀ s' hs'_T₀
    exact orbit_hasDerivAt_chartPhaseVF_uniform
      (I := I) (g := g) (p := p) (x₀ := extChartAt I p p) rfl
      (b := b) (r := r) (ε := ε) hr hε
      (Φ := Φ) hΦ_ILF hb_sub
      (ρ := ρ) (T := T) hρ_pos hT_pos hT_lt_ε hρ_le_r h_inner_T
      v hv s hs

end UniformChartPhaseODE

section ManifoldIdentification

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
lemma per_v_orbit_proj_eq_lift_proj_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {x₀ : E} (hx₀_def : x₀ = extChartAt I p p)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init_v : Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E))
    (hΦ_chart_phase : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s ∧
      Φ (((x₀, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (f : ℝ → TangentBundle I M),
      f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℝ),
        (f s).proj = (extChartAt I p).symm (Φ (((x₀, v) : E × E), s)).1 := by
  classical
  obtain ⟨f, hf0, hf_int⟩ :=
    Geodesic.exists_isMIntegralCurveAt_geodesicVectorFieldChart
      (I := I) (g := g) (p := p) (v := v)
  refine ⟨f, hf0, hf_int, ?_⟩
  have hf0_proj : (f 0).proj = p := by rw [hf0]
  have hd_lift :=
    chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
      (I := I) (g := g) (α := p) (f := f) hf0_proj hf_int
  have hc0 : chartPushLift (I := I) f 0 0 = ((x₀, v) : E × E) := by
    have h := chartPushLift_self_pair (I := I) f 0
    rw [h]
    have hproj0 : (f 0).proj = p := hf0_proj
    have hfiber0 : chartFiberCoord (I := I) p (f 0) = v := by
      rw [hf0]
      have hp_src : p ∈ (chartAt H p).source := mem_chart_source H p
      have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hp_src
      have hp_extsrc : p ∈ (extChartAt I p).source := by
        rw [extChartAt_source]; exact hp_src
      change (trivializationAt E (TangentSpace I) p
          (⟨p, v⟩ : TangentBundle I M)).2 = v
      have hcore :
          (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p =
          (tangentBundleCore I M).coordChange (achart H p) (achart H p) p :=
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
          (b₀ := p) (b := p) hp_src
      have hself : ∀ w : E, tangentCoordChange I p p p w = w :=
        fun w => tangentCoordChange_self (I := I) (x := p) (z := p) (v := w) hp_extsrc
      have hcore_at :
          ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v = v := by
        rw [hcore]; exact hself v
      have happly :
          ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v =
          (trivializationAt E (TangentSpace I) p
            (⟨p, v⟩ : TangentBundle I M)).2 := by
        change ((trivializationAt E (TangentSpace I) p).linearMapAt ℝ p) v = _
        have hcoe :=
          (trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
            (R := ℝ) hbase
        exact congrFun hcoe v
      rw [← happly, hcore_at]
    rw [hproj0, hfiber0, hx₀_def]
  have hΦorbit_zero :
      (fun s' : ℝ => Φ (((x₀, v) : E × E), s')) 0 = ((x₀, v) : E × E) := hΦ_init_v
  have hbase_interior : ((x₀, v) : E × E) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hp_extsrc : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact mem_chart_source H p
    have h_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hp_extsrc
    refine ⟨?_, Set.mem_univ _⟩
    rw [hx₀_def]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
  have hcd_eq := chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
    (c₁ := chartPushLift (I := I) f 0)
    (c₂ := fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
    (z₀ := ((x₀, v) : E × E))
    hbase_interior hc0 hΦorbit_zero hd_lift hΦ_chart_phase
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f 0 := hf_int.continuousAt
  have hcomp0 : ContinuousAt (fun s => (f s).proj) 0 :=
    hπ_cont.continuousAt.comp hf_cont0
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
  have hsrc_nhds : (fun s : ℝ => (f s).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp0.preimage_mem_nhds
    rw [hf0_proj]; exact hp_nhds
  filter_upwards [hcd_eq, hsrc_nhds] with s hs_eq hs_src
  have h_fst_eq :
      extChartAt I p (f s).proj = (Φ (((x₀, v) : E × E), s)).1 := by
    have hpair := chartPushLift_fst (I := I) (f := f) 0 s (by
      rw [hf0_proj]; exact hs_src)
    rw [hf0_proj] at hpair
    have := congrArg Prod.fst hs_eq
    rw [hpair] at this
    exact this
  have hf_extsrc : (f s).proj ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact hs_src
  have h_inv :
      (extChartAt I p).symm (extChartAt I p (f s).proj) = (f s).proj :=
    (extChartAt I p).left_inv hf_extsrc
  have h_target := congrArg (extChartAt I p).symm h_fst_eq
  rw [h_inv] at h_target
  exact h_target

end ManifoldIdentification

section HeadlineUniformExistence

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_existence_interval
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
        ∃ (f : ℝ → TangentBundle I M),
          f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
          IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 ∧
          ∀ᶠ s in 𝓝 (0 : ℝ),
            (f s).proj =
              (extChartAt I p).symm
                (Φ (((extChartAt I p p, v) : E × E), s)).1) := by
  classical
  obtain ⟨b, ρ, T, Φ, hρ_pos, hT_pos, hb_sub, hΦ_init, h_orbit_in, h_orbit_phase⟩ :=
    exists_uniform_orbit_hasDerivAt_chartPhaseVF (I := I) (g := g) (p := p)
  have h_orbit_target : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    intro v hv s hs
    have h_in_ball : Φ (((extChartAt I p p, v) : E × E), s) ∈
        Metric.ball ((extChartAt I p p, (0 : E)) : E × E) b.rIn :=
      h_orbit_in v hv s hs
    have h_in_closed : Φ (((extChartAt I p p, v) : E × E), s) ∈
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall h_in_ball
    have h_inner_le_outer : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
    have h_in_outer : Φ (((extChartAt I p p, v) : E × E), s) ∈
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rOut :=
      Metric.closedBall_subset_closedBall h_inner_le_outer h_in_closed
    exact hb_sub h_in_outer
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, ?_, ?_, ?_, ?_⟩
  · exact hΦ_init
  · intro v hv s hs; exact h_orbit_target v hv s hs
  · exact h_orbit_phase
  · intro v hv
    have hΦ_init_v : Φ (((extChartAt I p p, v) : E × E), 0) =
        ((extChartAt I p p, v) : E × E) := hΦ_init v hv
    have hΦ_chart_phase : ∀ᶠ s in 𝓝 (0 : ℝ),
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      have hIoo_nhds : Set.Ioo (-T) T ∈ 𝓝 (0 : ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, hT_pos⟩
      filter_upwards [hIoo_nhds] with s hs
      refine ⟨h_orbit_phase v hv s hs, ?_⟩
      exact h_orbit_target v hv s (Set.Ioo_subset_Icc_self hs)
    exact per_v_orbit_proj_eq_lift_proj_eventually (I := I) (g := g) (p := p)
      (v := v) (x₀ := extChartAt I p p) rfl
      (Φ := Φ) hΦ_init_v hΦ_chart_phase

end HeadlineUniformExistence

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
