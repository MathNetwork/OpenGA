import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ChartFlowVelocitySlice
import DifferentialGeometry.Geometry.Exponential.Smoothness.UniformChartFlowBridge
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

section RescaledOrbit

variable [I.Boundaryless]

def chartFlowOrbitRescaled (Φ : (E × E) × ℝ → E × E) (x₀ : E) (v : E) (t' : ℝ) :
    ℝ → E × E :=
  fun s => rescaleChartOrbit (E := E) t' (Φ (((x₀, v) : E × E), t' * s))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartFlowOrbitRescaled_apply
    (Φ : (E × E) × ℝ → E × E) (x₀ v : E) (t' s : ℝ) :
    chartFlowOrbitRescaled (E := E) Φ x₀ v t' s =
      rescaleChartOrbit (E := E) t' (Φ (((x₀, v) : E × E), t' * s)) := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartFlowOrbitRescaled_zero
    {Φ : (E × E) × ℝ → E × E} {x₀ v : E} {t' : ℝ}
    (hinit : Φ (((x₀, v) : E × E), 0) = (x₀, v)) :
    chartFlowOrbitRescaled (E := E) Φ x₀ v t' 0 = (x₀, t' • v) := by
  unfold chartFlowOrbitRescaled
  rw [mul_zero, hinit]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartFlowOrbitRescaled_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {p : M}
    {Φ : (E × E) × ℝ → E × E} {x₀ v : E} {t' s₀ : ℝ}
    (hd : HasDerivAt (fun s : ℝ => Φ (((x₀, v) : E × E), s))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), t' * s₀))) (t' * s₀)) :
    HasDerivAt (chartFlowOrbitRescaled (E := E) Φ x₀ v t')
      (chartPhaseVF (I := I) g p
        (chartFlowOrbitRescaled (E := E) Φ x₀ v t' s₀)) s₀ := by
  classical
  set c : ℝ → E × E := fun s => Φ (((x₀, v) : E × E), s) with hc_def
  exact hasDerivAt_rescaled_orbit (I := I) (g := g) (α := p)
    (c := c) (s₀ := s₀) (a := t') hd

end RescaledOrbit

section ZeroSectionOrbit

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPhaseVF_zero_section
    (g : SmoothRiemannianMetric I M) (p : M) :
    chartPhaseVF (I := I) g p
      ((extChartAt I p p, (0 : E)) : E × E) = (0, 0) := by
  classical
  have hΓ : chartChristoffelContraction (I := I) g p (0 : E) (0 : E)
      (extChartAt I p p) = 0 :=
    chartChristoffelContraction_zero_left (I := I) g p (0 : E)
      (extChartAt I p p)
  change ((0 : E), -chartChristoffelContraction (I := I) g p (0 : E) (0 : E)
      (extChartAt I p p)) = (0, 0)
  rw [hΓ, neg_zero]

end ZeroSectionOrbit

section FlowZeroSectionConstancy

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartFlow_zero_section_eventually_const
    {g : SmoothRiemannianMetric I M} {p : M}
    {Φ : (E × E) × ℝ → E × E} {b : ContDiffBump
      ((extChartAt I p p, (0 : E)) : E × E)} {r : ℝ≥0} {ε : ℝ}
    (hΦ : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g p (extChartAt I p p, (0 : E)) b)
        (0 : ℝ) ((extChartAt I p p, (0 : E)) : E × E) r (-ε) ε Φ)
    (hb_sub : Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
        ((extChartAt I p p, (0 : E)) : E × E) := by
  classical
  set c₁ : ℝ → E × E := fun s => Φ (((extChartAt I p p, (0 : E)) : E × E), s)
    with hc₁_def
  set c₂ : ℝ → E × E := fun _ => ((extChartAt I p p, (0 : E)) : E × E)
    with hc₂_def
  have hz₀_interior :
      ((extChartAt I p p, (0 : E)) : E × E) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hx₀_src : p ∈ (extChartAt I p).source :=
      mem_extChartAt_source (I := I) p
    have hx₀_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hx₀_src
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  have hc₁_zero : c₁ 0 = ((extChartAt I p p, (0 : E)) : E × E) := by
    have hinit : Φ ((((extChartAt I p p, (0 : E)) : E × E)), 0) =
        ((extChartAt I p p, (0 : E)) : E × E) :=
      hΦ.apply_initial ((extChartAt I p p, (0 : E)) : E × E)
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr)))
    rw [hc₁_def]; exact hinit
  have hc₂_zero : c₂ 0 = ((extChartAt I p p, (0 : E)) : E × E) := rfl
  have hc₁_cont0 : ContinuousAt c₁ 0 := by
    have hcont_on : ContinuousOn c₁ (Set.Icc (-ε) ε) := by
      exact hΦ.orbit_continuousOn ((extChartAt I p p, (0 : E)) : E × E)
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr)))
    have hIcc_nhds : Set.Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := by
      have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
      exact Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
    exact (hcont_on.continuousAt hIcc_nhds)
  have hc₁_inner_eventually : ∀ᶠ s in 𝓝 (0 : ℝ),
      c₁ s ∈ Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn := by
    have hinner_nhds :
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn ∈
        𝓝 ((extChartAt I p p, (0 : E)) : E × E) :=
      Metric.closedBall_mem_nhds _ b.rIn_pos
    exact hc₁_cont0.preimage_mem_nhds (by rw [hc₁_zero]; exact hinner_nhds)
  have hc₁_deriv : ∀ s ∈ Set.Ioo (-ε) ε,
      HasDerivAt c₁
        (chartPhaseVFCutoff (I := I) g p ((extChartAt I p p, (0 : E)) : E × E) b
          (c₁ s)) s := by
    intro s hs
    exact chartFlowOrbit_hasDerivAt_chartPhaseVF_of_isLocalFlow
      (I := I) (g := g) (α := p)
      (z₀ := ((extChartAt I p p, (0 : E)) : E × E)) (b := b) (r := r) (ε := ε)
      (Φ := Φ) hΦ
      (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr))) s hs
  have hc₁_deriv_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g p (c₁ s)) s ∧
      c₁ s ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
    have hball_sub_chart :
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      refine Set.Subset.trans ?_ hb_sub
      exact Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut)
    filter_upwards [hc₁_inner_eventually, hIoo_nhds] with s hsInner hsIoo
    refine ⟨?_, hball_sub_chart hsInner⟩
    have hcutoff_eq :
        chartPhaseVFCutoff (I := I) g p
          ((extChartAt I p p, (0 : E)) : E × E) b (c₁ s) =
        chartPhaseVF (I := I) g p (c₁ s) :=
      chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g p
        ((extChartAt I p p, (0 : E)) : E × E) b hsInner
    have hd := hc₁_deriv s hsIoo
    rw [hcutoff_eq] at hd
    exact hd
  have hVF_zero : chartPhaseVF (I := I) g p
      ((extChartAt I p p, (0 : E)) : E × E) = (0, 0) :=
    chartPhaseVF_zero_section (I := I) g p
  have hc₂_deriv_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g p (c₂ s)) s ∧
      c₂ s ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    refine ⟨?_, hz₀_interior⟩
    have h0 : HasDerivAt c₂ (0 : E × E) s :=
      hasDerivAt_const s ((extChartAt I p p, (0 : E)) : E × E)
    rw [show c₂ s = ((extChartAt I p p, (0 : E)) : E × E) from rfl, hVF_zero]
    exact h0
  have heq : c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ :=
    chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
      (c₁ := c₁) (c₂ := c₂)
      (z₀ := ((extChartAt I p p, (0 : E)) : E × E))
      hz₀_interior hc₁_zero hc₂_zero hc₁_deriv_ev hc₂_deriv_ev
  filter_upwards [heq] with s hs
  exact hs

end FlowZeroSectionConstancy

section FlowAtZeroEval

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartFlow_zero_section_apply_eventually_eq_origin
    {g : SmoothRiemannianMetric I M} {p : M}
    {Φ : (E × E) × ℝ → E × E} {b : ContDiffBump
      ((extChartAt I p p, (0 : E)) : E × E)} {r : ℝ≥0} {ε : ℝ}
    (hΦ : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g p (extChartAt I p p, (0 : E)) b)
        (0 : ℝ) ((extChartAt I p p, (0 : E)) : E × E) r (-ε) ε Φ)
    (hb_sub : Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ t' in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
        ((extChartAt I p p, (0 : E)) : E × E) :=
  chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
    (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ hb_sub hr hε

end FlowAtZeroEval

section CandidateSliceSmoothness

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma extChartAt_symm_comp_chartFlowCandidate_at_zero_general
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target) :
    ∀ᶠ v in 𝓝 (0 : E),
      extChartAt I p (chartFlowCandidate (I := I) Φ p t' v) =
        (Φ (((extChartAt I p p, v) : E × E), t')).1 := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hcd_slice_fst :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') hρ ht' hcd
  have hcont0 : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    hcd_slice_fst.continuousAt
  have htarget_nhds : (extChartAt I p).target ∈
      𝓝 ((Φ (((x₀, (0 : E)) : E × E), t')).1) :=
    (isOpen_extChartAt_target (I := I) p).mem_nhds hval
  have htarget_preimage : ∀ᶠ v in 𝓝 (0 : E),
      (Φ (((x₀, v) : E × E), t')).1 ∈ (extChartAt I p).target := by
    apply hcont0.preimage_mem_nhds
    exact htarget_nhds
  filter_upwards [htarget_preimage] with v hv
  simp only [chartFlowCandidate_apply]
  exact (extChartAt I p).right_inv hv

omit [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma chartFlowCandidate_chart_contDiffAt_zero_at_general_time
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target) :
    ContDiffAt ℝ 1
      (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p t' v))
      (0 : E) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') hρ ht' hcd
  have hev := extChartAt_symm_comp_chartFlowCandidate_at_zero_general
    (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) (t' := t') hρ ht' hcd hval
  exact hslice.congr_of_eventuallyEq hev

end CandidateSliceSmoothness

section ManifoldGap

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

def ChartFlowGeodesicMatchAt
    (g : SmoothRiemannianMetric I M) (p : M)
    (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ) : Prop :=
  ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
    (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
      chartFlowCandidate (I := I) Φ p t' v

end ManifoldGap

section ConditionalDischarge

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem uniformChartFlowBridge_of_match
    (g : SmoothRiemannianMetric I M) (p : M)
    {Φ : (E × E) × ℝ → E × E} {ρ T t' ρ' : ℝ}
    (hρ : 0 < ρ) (_hT : 0 < T) (ht'_pos : 0 < t') (ht'_in : t' ∈ Set.Ioo (-T) T)
    (hρ'_pos : 0 < ρ')
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target)
    (hval_p : (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p)
    (hmatch : ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ') :
    UniformChartFlowBridge (I := I) g p := by
  classical
  refine ⟨Φ, t', ρ', ht'_pos, hρ'_pos, ?_, hmatch⟩
  set x₀ : E := extChartAt I p p with hx₀_def
  have hchart_cd :
      ContDiffAt ℝ 1
        (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p t' v))
        (0 : E) :=
    chartFlowCandidate_chart_contDiffAt_zero_at_general_time
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) (t' := t')
      hρ ht'_in hcd hval
  have hcand_zero : chartFlowCandidate (I := I) Φ p t' (0 : E) = p := by
    change (extChartAt I p).symm (Φ (((x₀, (0 : E)) : E × E), t')).1 = p
    exact hval_p
  have hcd_slice_fst :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') hρ ht'_in hcd
  have hcont_slice0 : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    hcd_slice_fst.continuousAt
  have hsymm_cont : ContinuousAt (extChartAt I p).symm
      (Φ (((x₀, (0 : E)) : E × E), t')).1 :=
    continuousAt_extChartAt_symm'' (I := I) (x := p)
      (y := (Φ (((x₀, (0 : E)) : E × E), t')).1) hval
  have hcont_cand : ContinuousAt
      (chartFlowCandidate (I := I) Φ p t') (0 : E) := by
    have hinner : ContinuousAt
        (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) := hcont_slice0
    have hinner_eval : (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) =
        (Φ (((x₀, (0 : E)) : E × E), t')).1 := rfl
    have hcomp : ContinuousAt
        ((extChartAt I p).symm ∘
          (fun v : E => (Φ (((x₀, v) : E × E), t')).1)) (0 : E) :=
      hsymm_cont.comp_of_eq hinner hinner_eval.symm
    exact hcomp
  rw [contMDiffAt_iff]
  refine ⟨hcont_cand, ?_⟩
  have hsimp_range : (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  have hsimp_base : (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)) (0 : E) =
      (0 : E) := by simp
  rw [hsimp_base, hsimp_range, hcand_zero]
  have hgoal_eq :
      (extChartAt I p ∘ chartFlowCandidate (I := I) Φ p t' ∘
        (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm) =
      (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p t' v)) := by
    ext v; simp [Function.comp]
  rw [hgoal_eq]
  exact hchart_cd.contDiffWithinAt

end ConditionalDischarge

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem expMap_contMDiffAt_zero_of_chartFlowGeodesicMatch
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : ∃ (Φ : (E × E) × ℝ → E × E) (ρ T t' ρ' : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < t' ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < ρ' ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
        (extChartAt I p).target ∧
      (extChartAt I p).symm
        (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p ∧
      ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ') :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) := by
  obtain ⟨Φ, ρ, T, t', ρ', hρ, hT, ht'_pos, ht'_in, hρ'_pos,
    hcd, hval, hval_p, hmatch⟩ := h
  exact expMap_contMDiffAt_zero_of_uniformChartFlowBridge (I := I) (g := g) (p := p)
    (uniformChartFlowBridge_of_match (I := I) (g := g) (p := p)
      (Φ := Φ) (ρ := ρ) (T := T) (t' := t') (ρ' := ρ')
      hρ hT ht'_pos ht'_in hρ'_pos hcd hval hval_p hmatch)

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
