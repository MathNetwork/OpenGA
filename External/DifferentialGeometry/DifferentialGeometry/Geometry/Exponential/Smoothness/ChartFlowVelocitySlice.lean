import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.Defs
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

section ChartCoordSlice

variable [I.Boundaryless] [CompleteSpace E]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma contDiffAt_chartFlow_slice_zero
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1 (fun v : E => Φ (((x₀, v) : E × E), t')) (0 : E) := by
  have hpair_cd : ContDiff ℝ 1 (fun v : E => (((x₀, v) : E × E), t')) := by
    have h_const_x₀ : ContDiff ℝ 1 (fun _ : E => x₀) := contDiff_const
    have h_id : ContDiff ℝ 1 (fun v : E => v) := contDiff_id
    have h_pair_E2 : ContDiff ℝ 1 (fun v : E => ((x₀, v) : E × E)) :=
      h_const_x₀.prodMk h_id
    have h_const_t : ContDiff ℝ 1 (fun _ : E => t') := contDiff_const
    exact h_pair_E2.prodMk h_const_t
  have hΦ_cda : ContDiffAt ℝ 1 Φ (((x₀, (0 : E)) : E × E), t') := by
    apply hcd.contDiffAt
    have hopen : IsOpen ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
      Metric.isOpen_ball.prod isOpen_Ioo
    refine hopen.mem_nhds ?_
    exact ⟨Metric.mem_ball_self hρ, ht'⟩
  exact hΦ_cda.comp (0 : E) hpair_cd.contDiffAt

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma contDiffAt_chartFlow_slice_fst_zero
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) := by
  have hslice := contDiffAt_chartFlow_slice_zero (Φ := Φ) (x₀ := x₀)
    (ρ := ρ) (T := T) (t' := t') hρ ht' hcd
  have hfst : ContDiff ℝ 1 (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp (0 : E) hslice

end ChartCoordSlice

section ManifoldCandidate

variable [I.Boundaryless]

def chartFlowCandidate (Φ : (E × E) × ℝ → E × E) (p : M) (t' : ℝ) :
    E → M :=
  fun v => (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t')).1

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] in
@[simp] lemma chartFlowCandidate_apply
    (Φ : (E × E) × ℝ → E × E) (p : M) (t' : ℝ) (v : E) :
    chartFlowCandidate (I := I) Φ p t' v =
      (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t')).1 := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] in
lemma chartFlowCandidate_zero_at_initial
    {Φ : (E × E) × ℝ → E × E} {p : M}
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E))) :
    chartFlowCandidate (I := I) Φ p 0 (0 : E) = p := by
  unfold chartFlowCandidate
  rw [hinit]
  exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)

end ManifoldCandidate

section CandidateChartCoord

variable [I.Boundaryless] [CompleteSpace E]

omit [IsManifold I ∞ M] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma extChartAt_symm_comp_chartFlowCandidate_at_zero
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ∀ᶠ v in 𝓝 (0 : E),
      extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v) =
        (Φ (((extChartAt I p p, v) : E × E), 0)).1 := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT⟩
  have hcd_slice_fst :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := 0) hρ ht0 hcd
  have hcont0 : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    hcd_slice_fst.continuousAt
  have hval0 : (Φ (((x₀, (0 : E)) : E × E), (0 : ℝ))).1 = x₀ := by
    rw [hinit]
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_target_open : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  have htarget_nhds : (extChartAt I p).target ∈ 𝓝 x₀ :=
    mem_nhds_iff.mpr ⟨interior (extChartAt I p).target, interior_subset,
      isOpen_interior, hx₀_target_open⟩
  have htarget_preimage : ∀ᶠ v in 𝓝 (0 : E),
      (Φ (((x₀, v) : E × E), (0 : ℝ))).1 ∈ (extChartAt I p).target := by
    apply hcont0.preimage_mem_nhds
    rw [hval0]; exact htarget_nhds
  filter_upwards [htarget_preimage] with v hv
  simp only [chartFlowCandidate_apply]
  exact (extChartAt I p).right_inv hv

omit [IsManifold I ∞ M] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma chartFlowCandidate_chart_contDiffAt_zero_at_origin
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1
      (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v))
      (0 : E) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT⟩
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := 0) hρ ht0 hcd
  have hev := extChartAt_symm_comp_chartFlowCandidate_at_zero
    (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ hT hinit hcd
  exact hslice.congr_of_eventuallyEq hev

end CandidateChartCoord

section Headline

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlow_slice_contDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        (extChartAt I p p, (0 : E)) ∧
      (∀ (t' : ℝ), t' ∈ Set.Ioo (-T) T →
        ContDiffAt ℝ 1
          (fun v : E => (Φ (((extChartAt I p p, v) : E × E), t')).1)
          (0 : E)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨_b, ρ, T, Φ, hρ_pos, hT_pos, _hb_sub, hcd, hinit⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_chartPhase_contDiffOn_isLocalFlow
      (I := I) (M := M) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, ?_⟩
  intro t' ht'
  exact contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
    (ρ := ρ) (T := T) (t' := t') hρ_pos ht' hcd

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlowCandidate_chart_contDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      ContDiffAt ℝ 1
        (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v))
        (0 : E) ∧
      chartFlowCandidate (I := I) Φ p 0 (0 : E) = p := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, _⟩ :=
    exists_chartFlow_slice_contDiffAt_zero (I := I) (g := g) (p := p)
  refine ⟨Φ, ?_, ?_⟩
  · exact chartFlowCandidate_chart_contDiffAt_zero_at_origin
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ_pos hT_pos hinit hcd
  · exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

omit [IsManifold I ∞ M] [I.Boundaryless] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma chartFlowCandidate_continuousAt_zero_at_origin
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ContinuousAt (chartFlowCandidate (I := I) Φ p 0) (0 : E) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT⟩
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := 0) hρ ht0 hcd
  have hcont_slice : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    hslice.continuousAt
  have hval0 : (Φ (((x₀, (0 : E)) : E × E), (0 : ℝ))).1 = x₀ := by
    rw [hinit]
  have hsymm_cont : ContinuousAt (extChartAt I p).symm x₀ :=
    continuousAt_extChartAt_symm (I := I) p
  have hcont_slice' : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) := hcont_slice
  have hsymm_at_x₀ : ContinuousAt (fun y : E => (extChartAt I p).symm y) x₀ := hsymm_cont
  have hcomp_step : ContinuousAt
      (fun v : E => (extChartAt I p).symm
        ((fun v' : E => (Φ (((x₀, v') : E × E), (0 : ℝ))).1) v))
      (0 : E) := by
    refine ContinuousAt.comp ?_ hcont_slice'
    show ContinuousAt (extChartAt I p).symm (Φ (((x₀, (0 : E)) : E × E), (0 : ℝ))).1
    rw [hval0]
    exact hsymm_at_x₀
  exact hcomp_step

omit [IsManifold I ∞ M] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma chartFlowCandidate_contMDiffAt_zero_at_origin
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ContMDiffAt 𝓘(ℝ, E) I 1 (chartFlowCandidate (I := I) Φ p 0) (0 : E) := by
  classical
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · exact chartFlowCandidate_continuousAt_zero_at_origin
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ hT hinit hcd
  · have hval : chartFlowCandidate (I := I) Φ p 0 (0 : E) = p :=
      chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit
    rw [hval]
    have hchart_cd :
        ContDiffAt ℝ 1
          (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v))
          (0 : E) :=
      chartFlowCandidate_chart_contDiffAt_zero_at_origin
        (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ hT hinit hcd
    have hsimp_range : (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    have hsimp_base : (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)) (0 : E) =
        (0 : E) := by simp
    rw [hsimp_base, hsimp_range]
    have hsymm_id : ∀ v : E, (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm v = v := by
      intro v; simp
    change ContDiffWithinAt ℝ 1
        (extChartAt I p ∘ chartFlowCandidate (I := I) Φ p 0 ∘
          (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm)
        Set.univ (0 : E)
    have hgoal_eq :
        (extChartAt I p ∘ chartFlowCandidate (I := I) Φ p 0 ∘
          (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm) =
        (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v)) := by
      ext v; simp [Function.comp]
    rw [hgoal_eq]
    exact hchart_cd.contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlowCandidate_contMDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      ContMDiffAt 𝓘(ℝ, E) I 1 (chartFlowCandidate (I := I) Φ p 0) (0 : E) ∧
      chartFlowCandidate (I := I) Φ p 0 (0 : E) = p := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, _⟩ :=
    exists_chartFlow_slice_contDiffAt_zero (I := I) (g := g) (p := p)
  refine ⟨Φ, ?_, ?_⟩
  · exact chartFlowCandidate_contMDiffAt_zero_at_origin
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ_pos hT_pos hinit hcd
  · exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
