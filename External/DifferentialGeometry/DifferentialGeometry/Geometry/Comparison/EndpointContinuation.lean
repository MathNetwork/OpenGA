import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import DifferentialGeometry.Geometry.Comparison.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Comparison.ChartVelocityConvergence
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicSeed



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_extends_past_finite_endpoint
    (g : SmoothRiemannianMetric I M) {γ η : ℝ → M} {T δ : ℝ} (hδ : 0 < δ)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    ∃ γ' : ℝ → M,
      IsGeodesicOn (I := I) g γ' (Set.Iio (T + δ)) ∧
      (∀ t < T, γ' t = γ t) := by
  refine ⟨fun t => if t < T then γ t else η (t - T),
    Geodesic.isGeodesicOn_glue_at_limit (I := I) g hδ hγ hη hmatch, ?_⟩
  intro t ht
  simp only [if_pos ht]

def HasEndpointContinuation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (b : ℝ) : Prop :=
  ∃ (η : ℝ → M) (δ : ℝ), 0 < δ ∧
    IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ) ∧
    (∀ t ∈ Set.Ioo (-δ) δ, MDifferentiableAt 𝓘(ℝ, ℝ) I η t) ∧
    γ =ᶠ[nhdsWithin b (Set.Iio b)] (fun t => η (t - b))

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_orbit_uniqueness_Icc_left
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)} (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {a b : ℝ}
    {c₁ c₂ : ℝ → E × E}
    (hc₁_cont : ContinuousOn c₁ (Set.Icc a b))
    (hc₂_cont : ContinuousOn c₂ (Set.Icc a b))
    (hc₁_deriv : ∀ s ∈ Set.Ioc a b,
      HasDerivWithinAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) (Set.Iic s) s)
    (hc₂_deriv : ∀ s ∈ Set.Ioc a b,
      HasDerivWithinAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) (Set.Iic s) s)
    (hc₁_in_K : ∀ s ∈ Set.Ioc a b, c₁ s ∈ K)
    (hc₂_in_K : ∀ s ∈ Set.Ioc a b, c₂ s ∈ K)
    (h_eq_at_b : c₁ b = c₂ b) :
    Set.EqOn c₁ c₂ (Set.Icc a b) := by
  obtain ⟨L, hLip⟩ :=
    chartPhaseVF_lipschitzOnWith_of_compact (I := I) g α hK_compact hK_subset
  exact ODE_solution_unique_of_mem_Icc_left
    (v := fun _ z => chartPhaseVF (I := I) g α z) (s := fun _ => K) (K := L)
    (fun t _ => hLip) hc₁_cont hc₁_deriv hc₁_in_K hc₂_cont hc₂_deriv hc₂_in_K h_eq_at_b

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem hasEndpointContinuation_of_complete
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {aL b c : ℝ}
    (haLb : aL < b)
    (hc_nonneg : 0 ≤ c)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo aL b))
    (hSpeedBound : ∀ τ ∈ Set.Ioo aL b,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c)
    (hSpeedSq : ∀ s ∈ Set.Ioo aL b,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2)
    (_hγ : IsGeodesicOn (I := I) g γ (Set.Ioo aL b)) :
    HasEndpointContinuation (I := I) g γ b := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ_mdiff_on : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Ioo aL b) :=
    hγ_smooth.mdifferentiableOn (by norm_num)
  obtain ⟨y, hy_metric⟩ :=
    curve_exists_limit_of_bounded_speed (I := I) (γ := γ) (a := aL) (b := b) (c := c)
      haLb hc_nonneg hγ_smooth hSpeedBound
  have hy_mfld : Tendsto γ (𝓝[<] b) (𝓝 y) :=
    tendsto_nhds_of_tendsto_metric_nhds (I := I) (l := 𝓝[<] b) (f := γ) (p := y)
      hy_metric
  set u : ℝ → E := chartCurve (I := I) y γ with hu_def
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hy_ext_src : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
  have hy_target : extChartAt I y y ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source hy_ext_src
  have hy_interior : extChartAt I y y ∈ interior (extChartAt I y).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) y hy_target
  have hu_lim : Tendsto u (𝓝[<] b) (𝓝 (extChartAt I y y)) := by
    have hcont_at : ContinuousAt (extChartAt I y) y := continuousAt_extChartAt (I := I) y
    have := hcont_at.tendsto.comp hy_mfld
    simpa [hu_def, chartCurve] using this
  have hsrc_ev : ∀ᶠ s in 𝓝[<] b, γ s ∈ (chartAt H y).source :=
    hy_mfld ((chartAt H y).open_source.mem_nhds hy_src)
  obtain ⟨ε, K₁, S, hε, hS_compact, hS_sub, hbound⟩ :=
    chartVelocity_bound_near_limit (I := I) g y (γ := γ) (a := aL) (b := b) (c := c)
      haLb hc_nonneg hγ_mdiff_on hy_mfld hSpeedSq
  obtain ⟨a₀, ha₀_lt, ha₀_src⟩ :
      ∃ a₀ < b, ∀ s ∈ Set.Ioo a₀ b, γ s ∈ (chartAt H y).source := by
    obtain ⟨U, hU_nhds, hU_sub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsrc_ev
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
    refine ⟨b - ρ, by linarith, fun s hs => ?_⟩
    have hs_ball : s ∈ Metric.ball b ρ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hU_sub ⟨hρ_sub hs_ball, hs.2⟩
  set a : ℝ := max (max (b - ε) a₀) aL with ha_def
  have ha_lt_b : a < b := max_lt (max_lt (by linarith) ha₀_lt) haLb
  have ha_ge_ε : b - ε ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have ha_ge_a₀ : a₀ ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
  have ha_ge_aL : aL ≤ a := le_max_right _ _
  have hsub_aL : Set.Ioo a b ⊆ Set.Ioo aL b :=
    fun s hs => ⟨lt_of_le_of_lt ha_ge_aL hs.1, hs.2⟩
  have hsrc_on : ∀ s ∈ Set.Ioo a b, γ s ∈ (chartAt H y).source :=
    fun s hs => ha₀_src s ⟨lt_of_le_of_lt ha_ge_a₀ hs.1, hs.2⟩
  have hbound_on : ∀ s ∈ Set.Ioo a b,
      ‖deriv u s‖ ≤ K₁ ∧ u s ∈ S := by
    intro s hs
    have : s ∈ Set.Ioo (b - ε) b := ⟨lt_of_le_of_lt ha_ge_ε hs.1, hs.2⟩
    simpa [hu_def] using hbound s this
  have hγ_contAt : ∀ s ∈ Set.Ioo a b, ContinuousAt γ s := by
    intro s hs
    have hs_Ioo : s ∈ Set.Ioo aL b := hsub_aL hs
    exact ((hγ_smooth.continuousOn).continuousAt (isOpen_Ioo.mem_nhds hs_Ioo))
  have hγ_mdiffAt : ∀ s ∈ Set.Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := by
    intro s hs
    have hs_Ioo : s ∈ Set.Ioo aL b := hsub_aL hs
    exact (hγ_mdiff_on s hs_Ioo).mdifferentiableAt (isOpen_Ioo.mem_nhds hs_Ioo)
  have hODE_γ : ∀ s ∈ Set.Ioo a b,
      HasDerivAt (deriv u)
        (- chartChristoffelContraction (I := I) g y (deriv u s) (deriv u s) (u s)) s := by
    intro s hs
    have hgeq : HasGeodesicEquationAt (I := I) g γ s := _hγ s (hsub_aL hs)
    simpa [hu_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
        (γ := γ) (t := s) (hγ_contAt s hs) (hsrc_on s hs) hgeq
  have hDeriv_γ : ∀ s ∈ Set.Ioo a b, HasDerivAt u (deriv u s) s := by
    intro s hs
    have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I y) (γ s) :=
      mdifferentiableAt_extChartAt (I := I) (x := y) (hsrc_on s hs)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I y) ∘ γ) s :=
      hφ_mdiff.comp s (hγ_mdiffAt s hs)
    have hdiff : DifferentiableAt ℝ ((extChartAt I y) ∘ γ) s :=
      hcomp.differentiableAt
    simpa [hu_def, chartCurve] using hdiff.hasDerivAt
  obtain ⟨wγ, hwγ⟩ :=
    chartVelocity_converges_at_finite_endpoint_Ioo (I := I) g y
      (u := u) (u' := deriv u) (a := a) (b := b) (K₁ := K₁) (S := S)
      ha_lt_b hS_compact hS_sub
      (fun s hs => by simpa [hu_def] using hDeriv_γ s hs)
      (fun s hs => by simpa [hu_def] using hODE_γ s hs)
      (fun s hs => (hbound_on s hs).1)
      (fun s hs => (hbound_on s hs).2)
  set w : TangentSpace I y :=
    (trivializationAt E (TangentSpace I) y).symmL ℝ y wγ with hw_def
  obtain ⟨η, δ, hδ, hη0, hηcont, hη_mfd, hη_mdiffOn, hη_srcOn, hη_geo⟩ :=
    exists_isGeodesicOn_Ioo_at_velocity (I := I) g y w
  refine ⟨η, δ, hδ, hη_geo, hη_mdiffOn, ?_⟩
  have hδ_mem0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hη_chartVel0 : deriv (chartCurve (I := I) y η) 0 = wγ := by
    have hη0_src : η 0 ∈ (chartAt H y).source := by rw [hη0]; exact hy_src
    have hη_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I η 0 := hη_mdiffOn 0 hδ_mem0
    have hCC := chartCoord_mfderiv_eq_fderiv_at (I := I) (γ := η) (α := y)
      (s := 0) hη_mdiff0 hη0_src
    have hbase : (η 0) ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hη0_src
    have hround :
        ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ (η 0))
            ((mfderiv 𝓘(ℝ, ℝ) I η 0 : ℝ →L[ℝ] _) (1 : ℝ)) = wγ := by
      rw [hη_mfd, hw_def, hη0]
      exact (trivializationAt E (TangentSpace I) y).continuousLinearMapAt_symmL
        (R := ℝ) (by rw [TangentBundle.trivializationAt_baseSet]; exact hy_src) wγ
    have hderiv_eq : deriv (chartCurve (I := I) y η) 0 =
        (fderiv ℝ ((extChartAt I y) ∘ η) 0 : ℝ →L[ℝ] E) (1 : ℝ) := by
      rw [deriv]; rfl
    rw [hderiv_eq, ← hCC, hround]
  set uη : ℝ → E := chartCurve (I := I) y η with huη_def
  have hη_contOn : ∀ t ∈ Set.Ioo (-δ) δ, ContinuousAt η t :=
    fun t ht => (hη_mdiffOn t ht).continuousAt
  have hDeriv_η : ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt uη (deriv uη t) t := by
    intro t ht
    have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I y) (η t) :=
      mdifferentiableAt_extChartAt (I := I) (x := y) (hη_srcOn t ht)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I y) ∘ η) t :=
      hφ_mdiff.comp t (hη_mdiffOn t ht)
    have hdiff : DifferentiableAt ℝ ((extChartAt I y) ∘ η) t :=
      hcomp.differentiableAt
    simpa [huη_def, chartCurve] using hdiff.hasDerivAt
  have hODE_η : ∀ t ∈ Set.Ioo (-δ) δ,
      HasDerivAt (deriv uη)
        (- chartChristoffelContraction (I := I) g y (deriv uη t) (deriv uη t) (uη t)) t := by
    intro t ht
    simpa [huη_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
        (γ := η) (t := t) (hη_contOn t ht) (hη_srcOn t ht) (hη_geo t ht)
  have huη0 : uη 0 = extChartAt I y y := by rw [huη_def, chartCurve_def, hη0]
  have hS_closed : IsClosed S := hS_compact.isClosed
  have hφy_in_S : extChartAt I y y ∈ S := by
    refine hS_closed.mem_of_tendsto hu_lim ?_
    filter_upwards [Ioo_mem_nhdsLT ha_lt_b] with s hs using (hbound_on s hs).2
  have hwγ_norm : ‖wγ‖ ≤ K₁ := by
    refine le_of_tendsto (Tendsto.norm hwγ) ?_
    filter_upwards [Ioo_mem_nhdsLT ha_lt_b] with s hs using (hbound_on s hs).1
  set cγ : ℝ → E × E := fun s => if s < b then (u s, deriv u s)
    else (extChartAt I y y, wγ) with hcγ_def
  set cη : ℝ → E × E := fun s => (uη (s - b), deriv uη (s - b)) with hcη_def
  have hcγ_lt : ∀ s, s < b → cγ s = (u s, deriv u s) := fun s hs => by
    simp only [hcγ_def, if_pos hs]
  have hcγ_b : cγ b = (extChartAt I y y, wγ) := by
    simp only [hcγ_def, if_neg (lt_irrefl b)]
  have hcγ_deriv_open : ∀ s ∈ Set.Ioo a b,
      HasDerivAt cγ (chartPhaseVF (I := I) g y (cγ s)) s := by
    intro s hs
    have heq : cγ =ᶠ[𝓝 s] (fun r => (u r, deriv u r)) := by
      filter_upwards [isOpen_Iio.mem_nhds hs.2] with r hr using hcγ_lt r hr
    have hpair : HasDerivAt (fun r => (u r, deriv u r))
        (deriv u s,
          - chartChristoffelContraction (I := I) g y (deriv u s) (deriv u s) (u s)) s :=
      (hDeriv_γ s hs).prodMk (hODE_γ s hs)
    rw [hcγ_lt s hs.2, chartPhaseVF_mk]
    exact hpair.congr_of_eventuallyEq heq
  set Uγ : ℝ → E := fun s => (cγ s).1 with hUγ_def
  set Vγ : ℝ → E := fun s => (cγ s).2 with hVγ_def
  have hUγ_eq : ∀ s, s < b → Uγ s = u s := fun s hs => by
    simp only [hUγ_def, hcγ_lt s hs]
  have hVγ_eq : ∀ s, s < b → Vγ s = deriv u s := fun s hs => by
    simp only [hVγ_def, hcγ_lt s hs]
  have hUγ_b : Uγ b = extChartAt I y y := by simp only [hUγ_def, hcγ_b]
  have hVγ_b : Vγ b = wγ := by simp only [hVγ_def, hcγ_b]
  have hAccel_lim : Tendsto
      (fun s => - chartChristoffelContraction (I := I) g y (deriv u s) (deriv u s) (u s))
      (𝓝[<] b)
      (𝓝 (- chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))) := by
    have hΓcont := chartChristoffelContraction_continuousOn_prod (I := I) g y
    have hcontAt : ContinuousAt
        (fun p : E × E => chartChristoffelContraction (I := I) g y p.1 p.1 p.2)
        (wγ, extChartAt I y y) :=
      (hΓcont.continuousAt (((isOpen_univ.prod isOpen_interior)).mem_nhds
        ⟨Set.mem_univ _, hy_interior⟩))
    have hpair_lim : Tendsto (fun s => ((deriv u s, u s) : E × E)) (𝓝[<] b)
        (𝓝 (wγ, extChartAt I y y)) := hwγ.prodMk_nhds hu_lim
    exact (hcontAt.tendsto.comp hpair_lim).neg
  have hIoo_nhdsLT : Set.Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT ha_lt_b
  have hUγ_diffOn : DifferentiableOn ℝ Uγ (Set.Ioo a b) := by
    intro s hs
    refine ((hDeriv_γ s hs).differentiableAt.differentiableWithinAt).congr
      (fun r hr => (hUγ_eq r hr.2)) (hUγ_eq s hs.2)
  have hVγ_diffOn : DifferentiableOn ℝ Vγ (Set.Ioo a b) := by
    intro s hs
    refine ((hODE_γ s hs).differentiableAt.differentiableWithinAt).congr
      (fun r hr => (hVγ_eq r hr.2)) (hVγ_eq s hs.2)
  have hUγ_contAt : ContinuousWithinAt Uγ (Set.Ioo a b) b := by
    have ht : Tendsto Uγ (𝓝[<] b) (𝓝 (extChartAt I y y)) :=
      hu_lim.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (hUγ_eq s hs).symm)
    have : Tendsto Uγ (𝓝[Set.Ioo a b] b) (𝓝 (Uγ b)) := by
      rw [hUγ_b]; exact ht.mono_left (nhdsWithin_mono b (fun s hs => hs.2))
    exact this
  have hVγ_contAt : ContinuousWithinAt Vγ (Set.Ioo a b) b := by
    have ht : Tendsto Vγ (𝓝[<] b) (𝓝 wγ) :=
      hwγ.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (hVγ_eq s hs).symm)
    have : Tendsto Vγ (𝓝[Set.Ioo a b] b) (𝓝 (Vγ b)) := by
      rw [hVγ_b]; exact ht.mono_left (nhdsWithin_mono b (fun s hs => hs.2))
    exact this
  have hderiv_Uγ_lim : Tendsto (fun s => deriv Uγ s) (𝓝[<] b) (𝓝 wγ) := by
    refine hwγ.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have heq : Uγ =ᶠ[𝓝 s] u := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with r hr using hUγ_eq r hr
    exact (heq.deriv_eq).symm
  have hderiv_Vγ_lim : Tendsto (fun s => deriv Vγ s) (𝓝[<] b)
      (𝓝 (- chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))) := by
    refine hAccel_lim.congr' ?_
    filter_upwards [hIoo_nhdsLT] with s hsa
    have heqV : Vγ =ᶠ[𝓝 s] deriv u := by
      filter_upwards [isOpen_Iio.mem_nhds hsa.2] with r hr using hVγ_eq r hr
    rw [heqV.deriv_eq, (hODE_γ s hsa).deriv]
  have hUγ_bderiv : HasDerivWithinAt Uγ wγ (Set.Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv hUγ_diffOn hUγ_contAt hIoo_nhdsLT hderiv_Uγ_lim
  have hVγ_bderiv : HasDerivWithinAt Vγ
      (- chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))
      (Set.Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv hVγ_diffOn hVγ_contAt hIoo_nhdsLT hderiv_Vγ_lim
  have hcγ_bderiv : HasDerivWithinAt cγ (chartPhaseVF (I := I) g y (cγ b))
      (Set.Iic b) b := by
    have hprod : HasDerivWithinAt cγ
        (wγ, - chartChristoffelContraction (I := I) g y wγ wγ (extChartAt I y y))
        (Set.Iic b) b := hUγ_bderiv.prodMk hVγ_bderiv
    rw [hcγ_b, chartPhaseVF_mk]
    exact hprod
  obtain ⟨R, hR_pos, hR_sub⟩ :=
    Metric.isOpen_iff.mp isOpen_interior _ hy_interior
  set Kset : Set (E × E) :=
    Metric.closedBall (extChartAt I y y) (R / 2) ×ˢ Metric.closedBall (0 : E) (K₁ + 1)
    with hKset_def
  have hKset_compact : IsCompact Kset :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKset_sub : Kset ⊆ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    intro p hp
    refine ⟨hR_sub ?_, Set.mem_univ _⟩
    rw [Metric.mem_ball]
    have := hp.1; rw [Metric.mem_closedBall] at this
    linarith
  have hpair_in_Kset : ((extChartAt I y y, wγ) : E × E) ∈ Kset := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_self]; linarith
    · rw [Metric.mem_closedBall, dist_zero_right]; linarith
  have hKset_nhds : Kset ∈ 𝓝 ((extChartAt I y y, wγ) : E × E) := by
    rw [hKset_def, nhds_prod_eq]
    refine Filter.prod_mem_prod (Metric.closedBall_mem_nhds _ (by linarith))
      (Metric.closedBall_mem_nhds_of_mem ?_)
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hcγ_lim : Tendsto cγ (𝓝[<] b) (𝓝 ((extChartAt I y y, wγ) : E × E)) := by
    refine (hu_lim.prodMk_nhds hwγ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using (hcγ_lt s hs).symm
  have huη_contAt0 : ContinuousAt uη 0 := (hDeriv_η 0 hδ_mem0).continuousAt
  have hduη_contAt0 : ContinuousAt (deriv uη) 0 := (hODE_η 0 hδ_mem0).continuousAt
  have hshift0 : Tendsto (fun s : ℝ => s - b) (𝓝[<] b) (𝓝 (0 : ℝ)) := by
    have : Tendsto (fun s : ℝ => s - b) (𝓝 b) (𝓝 (0 : ℝ)) := by
      have hc := (continuous_sub_right b).tendsto b
      simpa using hc
    exact this.mono_left nhdsWithin_le_nhds
  have hcη_lim : Tendsto cη (𝓝[<] b) (𝓝 ((extChartAt I y y, wγ) : E × E)) := by
    have hu0 : Tendsto (fun s => uη (s - b)) (𝓝[<] b) (𝓝 (extChartAt I y y)) := by
      have := huη_contAt0.tendsto.comp hshift0
      rwa [huη0] at this
    have hdu0 : Tendsto (fun s => deriv uη (s - b)) (𝓝[<] b) (𝓝 wγ) := by
      have := hduη_contAt0.tendsto.comp hshift0
      rwa [hη_chartVel0] at this
    exact hu0.prodMk_nhds hdu0
  have hev_all : ∀ᶠ s in 𝓝[<] b,
      cγ s ∈ Kset ∧ cη s ∈ Kset ∧ (s - b) ∈ Set.Ioo (-δ) δ := by
    have h1 : ∀ᶠ s in 𝓝[<] b, cγ s ∈ Kset := hcγ_lim hKset_nhds
    have h2 : ∀ᶠ s in 𝓝[<] b, cη s ∈ Kset := hcη_lim hKset_nhds
    have h3 : ∀ᶠ s in 𝓝[<] b, (s - b) ∈ Set.Ioo (-δ) δ :=
      hshift0 (isOpen_Ioo.mem_nhds hδ_mem0)
    filter_upwards [h1, h2, h3] with s hs1 hs2 hs3 using ⟨hs1, hs2, hs3⟩
  obtain ⟨a', ha'_lt, ha'_all⟩ :
      ∃ a' < b, ∀ s ∈ Set.Ioo a' b,
        cγ s ∈ Kset ∧ cη s ∈ Kset ∧ (s - b) ∈ Set.Ioo (-δ) δ := by
    obtain ⟨U, hU_nhds, hU_sub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev_all
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
    refine ⟨b - ρ, by linarith, fun s hs => ?_⟩
    have hs_ball : s ∈ Metric.ball b ρ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hU_sub ⟨hρ_sub hs_ball, hs.2⟩
  set a₁ : ℝ := max a a' with ha₁_def
  have ha₁_lt : a₁ < b := max_lt ha_lt_b ha'_lt
  set a'' : ℝ := (a₁ + b) / 2 with ha''_def
  have ha''_gt_a₁ : a₁ < a'' := by rw [ha''_def]; linarith
  have ha''_lt : a'' < b := by rw [ha''_def]; linarith
  have ha''_gt_a : a < a'' := lt_of_le_of_lt (le_max_left _ _) ha''_gt_a₁
  have ha''_gt_a' : a' < a'' := lt_of_le_of_lt (le_max_right _ _) ha''_gt_a₁
  have hsub_a'' : Set.Ioo a'' b ⊆ Set.Ioo a b :=
    fun s hs => ⟨lt_of_lt_of_le ha''_gt_a hs.1.le, hs.2⟩
  have hsub_a''' : Set.Ioo a'' b ⊆ Set.Ioo a' b :=
    fun s hs => ⟨lt_of_lt_of_le ha''_gt_a' hs.1.le, hs.2⟩
  have hIcc_lt_sub : ∀ s ∈ Set.Icc a'' b, s < b → s ∈ Set.Ioo a b :=
    fun s hs hlt => ⟨lt_of_lt_of_le ha''_gt_a hs.1, hlt⟩
  have hIcc_lt_sub' : ∀ s ∈ Set.Icc a'' b, s < b → s ∈ Set.Ioo a' b :=
    fun s hs hlt => ⟨lt_of_lt_of_le ha''_gt_a' hs.1, hlt⟩
  have hcη_deriv_at : ∀ s : ℝ, (s - b) ∈ Set.Ioo (-δ) δ →
      HasDerivAt cη (chartPhaseVF (I := I) g y (cη s)) s := by
    intro s hsh
    have h1 : HasDerivAt (fun r => uη (r - b)) (deriv uη (s - b)) s :=
      (hDeriv_η (s - b) hsh).comp_sub_const s b
    have h2 : HasDerivAt (fun r => deriv uη (r - b))
        (- chartChristoffelContraction (I := I) g y (deriv uη (s - b)) (deriv uη (s - b))
          (uη (s - b))) s :=
      (hODE_η (s - b) hsh).comp_sub_const s b
    have := h1.prodMk h2
    rw [hcη_def, chartPhaseVF_mk]
    exact this
  have hcη_deriv_open : ∀ s ∈ Set.Ioo a'' b,
      HasDerivAt cη (chartPhaseVF (I := I) g y (cη s)) s :=
    fun s hs => hcη_deriv_at s (ha'_all s (hsub_a''' hs)).2.2
  have hcη_b : cη b = (extChartAt I y y, wγ) := by
    simp only [hcη_def, sub_self, huη0, hη_chartVel0]
  have h_eq_at_b : cγ b = cη b := by rw [hcγ_b, hcη_b]
  have hcγ_deriv_Ioc : ∀ s ∈ Set.Ioc a'' b,
      HasDerivWithinAt cγ (chartPhaseVF (I := I) g y (cγ s)) (Set.Iic s) s := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (hcγ_deriv_open s (hsub_a'' ⟨hs.1, hlt⟩)).hasDerivWithinAt
    · rw [heq]; exact hcγ_bderiv
  have hcη_deriv_Ioc : ∀ s ∈ Set.Ioc a'' b,
      HasDerivWithinAt cη (chartPhaseVF (I := I) g y (cη s)) (Set.Iic s) s := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (hcη_deriv_open s ⟨hs.1, hlt⟩).hasDerivWithinAt
    · rw [heq]
      exact (hcη_deriv_at b (by rw [sub_self]; exact hδ_mem0)).hasDerivWithinAt
  have hContAt_b : ∀ (cf : ℝ → E × E) (L : E × E), cf b = L →
      Tendsto cf (𝓝[<] b) (𝓝 L) → ContinuousWithinAt cf (Set.Icc a'' b) b := by
    intro cf L hval hlim
    have hIic : Tendsto cf (𝓝[Set.Iic b] b) (𝓝 L) := by
      rw [show Set.Iic b = Set.Iio b ∪ {b} from (Set.Iio_union_right).symm,
        nhdsWithin_union, Filter.tendsto_sup]
      refine ⟨hlim, ?_⟩
      rw [nhdsWithin_singleton, Filter.tendsto_pure_left]
      intro s hs; rw [hval]; exact mem_of_mem_nhds hs
    have hmono : Tendsto cf (𝓝[Set.Icc a'' b] b) (𝓝 L) :=
      hIic.mono_left (nhdsWithin_mono b (fun s hs => hs.2))
    change Tendsto cf (𝓝[Set.Icc a'' b] b) (𝓝 (cf b))
    rw [hval]; exact hmono
  have hcγ_contOn : ContinuousOn cγ (Set.Icc a'' b) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact ((hcγ_deriv_open s (hIcc_lt_sub s hs hlt)).continuousAt).continuousWithinAt
    · rw [show s = b from heq]
      exact hContAt_b cγ (extChartAt I y y, wγ) hcγ_b hcγ_lim
  have hcη_contOn : ContinuousOn cη (Set.Icc a'' b) := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact ((hcη_deriv_at s (ha'_all s (hIcc_lt_sub' s hs hlt)).2.2).continuousAt).continuousWithinAt
    · rw [show s = b from heq]
      exact hContAt_b cη (extChartAt I y y, wγ) hcη_b hcη_lim
  have hcγ_in_K : ∀ s ∈ Set.Ioc a'' b, cγ s ∈ Kset := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (ha'_all s (hsub_a''' ⟨hs.1, hlt⟩)).1
    · subst heq; rw [hcγ_b]; exact hpair_in_Kset
  have hcη_in_K : ∀ s ∈ Set.Ioc a'' b, cη s ∈ Kset := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact (ha'_all s (hsub_a''' ⟨hs.1, hlt⟩)).2.1
    · subst heq; rw [hcη_b]; exact hpair_in_Kset
  have hEqOn : Set.EqOn cγ cη (Set.Icc a'' b) :=
    chartPhaseVF_orbit_uniqueness_Icc_left (I := I) g y hKset_compact hKset_sub
      hcγ_contOn hcη_contOn hcγ_deriv_Ioc hcη_deriv_Ioc hcγ_in_K hcη_in_K h_eq_at_b
  refine Filter.eventually_of_mem (U := Set.Ioo a'' b) (Ioo_mem_nhdsLT ha''_lt) ?_
  intro s hs
  have hs_Icc : s ∈ Set.Icc a'' b := ⟨hs.1.le, hs.2.le⟩
  have hpair_eq : cγ s = cη s := hEqOn hs_Icc
  have hfst : u s = uη (s - b) := by
    have : (cγ s).1 = (cη s).1 := by rw [hpair_eq]
    rwa [hcγ_lt s hs.2, hcη_def] at this
  have hγ_src_s : γ s ∈ (chartAt H y).source := hsrc_on s (hsub_a'' hs)
  have hη_src_s : η (s - b) ∈ (chartAt H y).source :=
    hη_srcOn (s - b) (ha'_all s (hsub_a''' hs)).2.2
  have hγ_ext_src : γ s ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγ_src_s
  have hη_ext_src : η (s - b) ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hη_src_s
  have hround_γ : (extChartAt I y).symm (extChartAt I y (γ s)) = γ s :=
    (extChartAt I y).left_inv hγ_ext_src
  have hround_η : (extChartAt I y).symm (extChartAt I y (η (s - b))) = η (s - b) :=
    (extChartAt I y).left_inv hη_ext_src
  have hu_s : u s = extChartAt I y (γ s) := by rw [hu_def, chartCurve_def]
  have huη_s : uη (s - b) = extChartAt I y (η (s - b)) := by rw [huη_def, chartCurve_def]
  calc γ s = (extChartAt I y).symm (extChartAt I y (γ s)) := hround_γ.symm
    _ = (extChartAt I y).symm (u s) := by rw [hu_s]
    _ = (extChartAt I y).symm (uη (s - b)) := by rw [hfst]
    _ = (extChartAt I y).symm (extChartAt I y (η (s - b))) := by rw [huη_s]
    _ = η (s - b) := hround_η

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
