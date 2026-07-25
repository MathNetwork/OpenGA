import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowToTangentLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.InverseManifoldChain
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Exponential.Smoothness.MatchDataReduction
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
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

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section UnifiedPackaging

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_unified_chartFlow_data
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        ((extChartAt I p p, (0 : E)) : E × E) ∧
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
      (∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
          ((extChartAt I p p, (0 : E)) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨b, r, ε, ρ_V4, T_V4, Φ, hr, hε, hρ_V4_pos, hT_V4_pos, hb_sub, hΦ_ILF,
    hΦ_cd_V4, hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined
      (I := I) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  obtain ⟨ρ₀, T₀, hρ₀_pos, hT₀_pos, hρ₀_le_V4, hT₀_lt_V4, h_orbit_in⟩ :=
    exists_uniform_orbit_in_inner_ball (I := I) (p := p)
      (x₀ := x₀) hx₀_def
      (b := b) (ρ_V4 := ρ_V4) (T_V4 := T_V4) hρ_V4_pos hT_V4_pos
      (Φ := Φ) hΦ_cd_V4 hΦ_init0
  set ρ : ℝ := min ρ₀ ((r : ℝ) / 2) with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min hρ₀_pos
    have : (0 : ℝ) < (r : ℝ) := hr
    linarith
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ_le_ρ_V4 : ρ ≤ ρ_V4 := le_trans hρ_le_ρ₀ hρ₀_le_V4
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
  have hT_lt_T_V4 : T < T_V4 := lt_of_le_of_lt hT_le_T₀ hT₀_lt_V4
  have hΦ_cd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) := by
    apply hΦ_cd_V4.mono
    intro w hw
    refine ⟨?_, ?_⟩
    · exact (Metric.ball_subset_ball hρ_le_ρ_V4) hw.1
    · refine ⟨?_, ?_⟩
      · linarith [hw.2.1]
      · linarith [hw.2.2]
  have hΦ_init_v : ∀ v ∈ Metric.ball (0 : E) ρ,
      Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) := by
    intro v hv
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
    have hv_in : ((x₀, v) : E × E) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) (r : ℝ) := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      rw [Metric.mem_ball, dist_zero_right] at hv
      have hv_r : ‖v‖ ≤ (r : ℝ) := le_of_lt (lt_of_lt_of_le hv hρ_le_r)
      exact max_le hr_nn hv_r
    exact hΦ_ILF.apply_initial ((x₀, v) : E × E) hv_in
  have h_inner_T : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        Metric.ball (((x₀, (0 : E)) : E × E)) b.rIn := by
    intro v hv s hs
    have hv_ρ₀ : v ∈ Metric.ball (0 : E) ρ₀ := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      have : ‖v‖ < ρ := hv
      exact lt_of_lt_of_le this hρ_le_ρ₀
    have hs_T₀ : s ∈ Set.Icc (-T₀) T₀ := by
      refine ⟨?_, ?_⟩
      · linarith [hs.1]
      · linarith [hs.2]
    exact h_orbit_in v hv_ρ₀ s hs_T₀
  have hΦ_target : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ (((x₀, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    intro v hv s hs
    have h_in_ball := h_inner_T v hv s hs
    have h_in_closed : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall h_in_ball
    have h_inner_le_outer : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
    have h_in_outer : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rOut :=
      Metric.closedBall_subset_closedBall h_inner_le_outer h_in_closed
    exact hb_sub h_in_outer
  have hΦ_phase : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
    intro v hv s hs
    exact orbit_hasDerivAt_chartPhaseVF_uniform
      (I := I) (g := g) (p := p) (x₀ := x₀) hx₀_def
      (b := b) (r := r) (ε := ε) hr hε
      (Φ := Φ) hΦ_ILF hb_sub
      (ρ := ρ) (T := T) hρ_pos hT_pos hT_lt_ε hρ_le_r h_inner_T v hv s hs
  have hconst_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    change ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
        ((extChartAt I p p, (0 : E)) : E × E)
    exact chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
      (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ_ILF hb_sub hr hε
  rcases Filter.eventually_iff_exists_mem.mp hconst_ev with ⟨U, hU_nhds, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem_zero⟩
  rcases (Metric.isOpen_iff.mp hV_open) (0 : ℝ) hV_mem_zero with
    ⟨δ_match, hδ_match_pos, hδ_sub⟩
  set T_match : ℝ := min δ_match T with hT_match_def
  have hT_match_pos : 0 < T_match := lt_min hδ_match_pos hT_pos
  have hT_match_le_T : T_match ≤ T := min_le_right _ _
  have hT_match_le_δ : T_match ≤ δ_match := min_le_left _ _
  have hΦ_const_zero_section :
      ∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    intro s hs
    have hs_in_V : s ∈ V := by
      apply hδ_sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      refine ⟨?_, ?_⟩
      · have h1 : -T_match < s := hs.1
        linarith
      · have h2 : s < T_match := hs.2
        linarith
    exact hU _ (hVU hs_in_V)
  have hF_int : ∀ v ∈ Metric.ball (0 : E) ρ,
      IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
        (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T) := by
    intro v hv
    exact chartFlowOrbitLift_isMIntegralCurveOn_Ioo (I := I) g p v
      (hΦ_target v hv) (hΦ_phase v hv)
  refine ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)
    exact hΦ_cd
  · change Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      ((extChartAt I p p, (0 : E)) : E × E)
    exact hΦ_init0
  · intro v hv
    change Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E)
    exact hΦ_init_v v hv
  · intro v hv s hs
    change Φ (((extChartAt I p p, v) : E × E), s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)
    exact hΦ_target v hv s hs
  · intro v hv s hs
    change HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
      (chartPhaseVF (I := I) g p
        (Φ (((extChartAt I p p, v) : E × E), s))) s
    exact hΦ_phase v hv s hs
  · intro s hs
    change Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
      ((extChartAt I p p, (0 : E)) : E × E)
    exact hΦ_const_zero_section s hs
  · intro v hv
    exact hF_int v hv

end UnifiedPackaging

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
