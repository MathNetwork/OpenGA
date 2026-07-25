import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.MfderivZero
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Exponential.ChartFlow.SmallVelocityRescaling
import DifferentialGeometry.Geometry.Exponential.ChartFlow.RescaledLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import Mathlib.Geometry.Manifold.Riemannian.PathELength



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section GaussLemma

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]



theorem radial_maximalGeodesic_hasGeodesicEquationAt_of_small
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
          DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicEquationAt
            (I := I) g (fun s : ℝ => maximalGeodesic (I := I) g p v s) t := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    Exponential.exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv t ht
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  obtain ⟨vb, hvb_def⟩ : ∃ vb : E, vb = (1 / t') • w := ⟨_, rfl⟩
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul]
    rw [div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  set J : Set ℝ := Set.Ioo (-T / t') (T / t') with hJ_def
  have hJ_open : IsOpen J := isOpen_Ioo
  have hJ_eq : J = Set.Ioo (-2 : ℝ) 2 := by rw [hJ_def, neg_div, hT_div]
  have hIcc_sub_J : Set.Ioo (-1 : ℝ) 2 ⊆ J := by
    rw [hJ_eq]; intro x hx; obtain ⟨hx0, hx1⟩ := hx; exact ⟨by linarith, by linarith⟩
  have ht_J : t ∈ J := hIcc_sub_J ht
  have h0_J : (0 : ℝ) ∈ J := hIcc_sub_J ⟨by norm_num, by norm_num⟩
  set F : ℝ → TangentBundle I M :=
    Exponential.chartFlowOrbitLiftRescaled (I := I) Φ p t' vb with hF_def
  have hF0 : F 0 = (⟨p, t' • vb⟩ : TangentBundle I M) :=
    Exponential.chartFlowOrbitLiftRescaled_zero (I := I) p vb t' (hΦ_init vb hvb_ball)
  have hF_int :
      IsMIntegralCurveOn F
        (Geodesic.geodesicVectorFieldChart (I := I) g p) J :=
    Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo (I := I) g p vb
      ht'_pos (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
  have hF_proj : ∀ s ∈ J,
      (F s).proj = maximalGeodesic (I := I) g p v s := by
    intro s hs
    have h := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := p) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := s) hs
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
    exact h
  have hgeo_init :
      Geodesic.IsGeodesicOnWithInitial (I := I) g
        (fun s : ℝ => (F s).proj) J p v := by
    refine ⟨F, fun _ => rfl, ?_, hF_int⟩
    rw [hF0, show (t' • vb : TangentSpace I p) = v from hvb_resc]
  obtain ⟨ρ_src, hρ_src_pos, hsrc⟩ :=
    Exponential.foot_in_source_throughout (I := I) (g := g) (p := p)
  have hF_src : (F t).proj ∈ (chartAt H p).source := by
    have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
      obtain ⟨ht0, ht1⟩ := ht
      refine ⟨?_, ?_⟩
      · nlinarith [ht'_pos.le, hT_pos.le, ht'_lt_T.le]
      · nlinarith [ht'_lt_T.le, ht'_pos.le]
    have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
    have hsrc' :=
      Exponential.chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p vb t' t
        hΦ_target_tt
    rw [hF_def]; exact hsrc'
  have hgeoAt :
      Geodesic.IsGeodesicAt (I := I) g (fun s : ℝ => (F s).proj) t :=
    hgeo_init.isGeodesicAt (hJ_open.mem_nhds ht_J) hF_src
  have hgeoEqF :
      Geodesic.HasGeodesicEquationAt (I := I) g (fun s : ℝ => (F s).proj) t :=
    hgeoAt.hasGeodesicEquationAt g
  have hEvEq : (fun s : ℝ => maximalGeodesic (I := I) g p v s)
      =ᶠ[nhds t] (fun s : ℝ => (F s).proj) := by
    filter_upwards [hJ_open.mem_nhds ht_J] with s hs
    exact (hF_proj s hs).symm
  exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (γ := fun s : ℝ => maximalGeodesic (I := I) g p v s)
    (γ' := fun s : ℝ => (F s).proj) (t₀ := t)
    (hF_proj t ht_J).symm hEvEq hgeoEqF

omit [NeZero (Module.finrank ℝ E)] in
theorem radial_maximalGeodesic_cont_and_foot_in_source_of_small
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ContinuousOn (fun s => maximalGeodesic (I := I) g p v s) (Set.Ioo (-1 : ℝ) 2) ∧
        ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
          maximalGeodesic (I := I) g p v t ∈ (chartAt H p).source := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    Exponential.exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  obtain ⟨vb, hvb_def⟩ : ∃ vb : E, vb = (1 / t') • w := ⟨_, rfl⟩
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul]
    rw [div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  have h12_sub_J : Set.Ioo (-1 : ℝ) 2 ⊆ Set.Ioo (-T / t') (T / t') := by
    rw [neg_div, hT_div]; intro x hx; obtain ⟨hx0, hx1⟩ := hx; exact ⟨by linarith, by linarith⟩
  have hF_int := Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo
    (I := I) g p vb ht'_pos (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
  have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousOn
      (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ p t' vb r).proj)
      (Set.Ioo (-T / t') (T / t')) :=
    hπ_cont.comp_continuousOn hF_int.continuousOn
  have hEqOn : Set.EqOn (fun r => maximalGeodesic (I := I) g p v r)
      (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ p t' vb r).proj)
      (Set.Ioo (-T / t') (T / t')) := by
    intro r hr
    have h := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := p) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := r) hr
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · exact ((hproj_cont.congr hEqOn).mono h12_sub_J)
  · intro t ht
    have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
      obtain ⟨ht0, ht1⟩ := ht
      refine ⟨?_, ?_⟩
      · nlinarith [ht'_pos.le, hT_pos.le, ht'_lt_T.le]
      · nlinarith [ht'_lt_T.le, ht'_pos.le]
    have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
    have hsrc' :=
      Exponential.chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p vb t' t
        hΦ_target_tt
    have ht_J : t ∈ Set.Ioo (-T / t') (T / t') := h12_sub_J ht
    have hEq := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := p) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := t) ht_J
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at hEq
    rw [← hEq]; exact hsrc'


def expMapC2Radius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  min (Classical.choose (Exponential.expMap_contMDiffAt_infty_of_norm_lt (I := I) g p))
    (min
      (Classical.choose
        (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p))
      (min
        (Classical.choose
          (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p))
        (Classical.choose
          (exists_metric_ball_subset_expMapDiffeo_source (I := I) g p))))

lemma expMapC2Radius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < expMapC2Radius (I := I) g p := by
  rw [expMapC2Radius, lt_min_iff, lt_min_iff, lt_min_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec
      (Exponential.expMap_contMDiffAt_infty_of_norm_lt (I := I) g p)).1
  · exact (Classical.choose_spec
      (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p)).1
  · exact (Classical.choose_spec
      (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p)).1
  · exact (Classical.choose_spec
      (exists_metric_ball_subset_expMapDiffeo_source (I := I) g p)).1

theorem expMap_contMDiffAt_infty_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {w : E}
    (hw : ‖w‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) w :=
  (Classical.choose_spec
    (Exponential.expMap_contMDiffAt_infty_of_norm_lt (I := I) g p)).2 w
    (lt_of_lt_of_le hw (min_le_left _ _))

lemma expMap_contMDiffAt2_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {w : E}
    (hw : ‖w‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 2
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) w :=
  (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p hw).of_le
    (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))

lemma radial_hasGeodesicEquationAt_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : ‖(v : E)‖ < expMapC2Radius (I := I) g p) (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    Geodesic.HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => maximalGeodesic (I := I) g p v s) t :=
  (Classical.choose_spec
    (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p)).2
    (lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))) t ht

lemma maximalGeodesic_rescale_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : ‖(v : E)‖ < expMapC2Radius (I := I) g p) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    maximalGeodesic (I := I) g p (t • v) 1 = maximalGeodesic (I := I) g p v t :=
  (Classical.choose_spec
    (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p)).2
    (lt_of_lt_of_le hv
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) t ht

lemma ball_subset_normalChartAt_target
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    x ∈ (NormalCoordinates.normalChartAt (I := I) g p).target := by
  rw [NormalCoordinates.normalChartAt_target_eq]
  refine (Classical.choose_spec
    (exists_metric_ball_subset_expMapDiffeo_source (I := I) g p)).2 ?_
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_lt_of_le hx
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))

lemma mem_expMapDiffeo_source_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source := by
  have := ball_subset_normalChartAt_target (I := I) g p hx
  rwa [NormalCoordinates.normalChartAt_target_eq] at this

lemma mem_expDomain_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    (show TangentSpace I p from x) ∈ expDomain (I := I) g p := by
  classical
  have hsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p hx
  by_cases hx0 : x = 0
  · subst hx0; exact zero_mem_expDomain (I := I) g p
  · by_contra hcon
    have hjunk : expMap (I := I) g p (show TangentSpace I p from x) = p :=
      expMap_of_not_mem_expDomain (I := I) hcon
    have hΦx : NormalCoordinates.expMapDiffeo (I := I) g p x = p := by
      rw [NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hsrc]; exact hjunk
    have hΦ0 : NormalCoordinates.expMapDiffeo (I := I) g p (0 : E) = p :=
      NormalCoordinates.expMapDiffeo_zero (I := I) g p
    have h0src : (0 : E) ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) g p
    have hinj : Set.InjOn (NormalCoordinates.expMapDiffeo (I := I) g p)
        (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      (NormalCoordinates.expMapDiffeo (I := I) g p).toPartialEquiv.injOn
    exact hx0 (hinj hsrc h0src (by rw [hΦx, hΦ0]))


omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma gp_coercive (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ c : ℝ, 0 < c ∧
      (∀ x : E, c * ‖x‖ ^ 2 ≤ g.inner p x x) ∧
      ∀ {d : ℝ}, (∀ x : E, d * ‖x‖ ^ 2 ≤ g.inner p x x) → d ≤ c := by
  classical
  have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  haveI : ProperSpace E := FiniteDimensional.proper_rclike (K := ℝ) (E := E)
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  set Q : E → ℝ := fun x => B x x with hQ
  have hQcont : Continuous Q := by
    have : Continuous (fun x : E => B x x) :=
      (B.continuous₂).comp (continuous_id.prodMk continuous_id)
    simpa [hQ] using this
  have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hsphere_ne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hQpos : ∀ x ∈ Metric.sphere (0 : E) 1, (0 : ℝ) < Q x := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h; rw [h] at hx
      simp only [mem_sphere_zero_iff_norm, norm_zero] at hx
      exact (zero_ne_one hx)
    exact g.pos p x hxne
  obtain ⟨u₀, hu₀_sphere, hu₀_min⟩ :=
    hsphere.exists_isMinOn hsphere_ne hQcont.continuousOn
  set c : ℝ := Q u₀ with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact hQpos u₀ hu₀_sphere
  refine ⟨c, hc_pos, ?_, ?_⟩
  · intro x
    change c * ‖x‖ ^ 2 ≤ B x x
    rcases eq_or_ne x 0 with hx0 | hx0
    · subst hx0
      rw [ContinuousLinearMap.map_zero₂, norm_zero]
      simp
    · have hnx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      set u : E := ‖x‖⁻¹ • x with hu_def
      have hu_sphere : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, hu_def, norm_smul]
        simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hnx_pos]
        exact inv_mul_cancel₀ (ne_of_gt hnx_pos)
      have hcuQ : Q u₀ ≤ Q u := hu₀_min hu_sphere
      have hcu : c ≤ B u u := by
        simpa only [hc_def, hQ] using hcuQ
      have hx_eq : x = ‖x‖ • u := by
        rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hnx_pos), one_smul]
      have hQscale : B x x = ‖x‖ ^ 2 * B u u := by
        nth_rewrite 1 [hx_eq]
        nth_rewrite 2 [hx_eq]
        rw [ContinuousLinearMap.map_smul₂, ContinuousLinearMap.map_smul, smul_eq_mul,
          smul_eq_mul]
        ring
      rw [hQscale]
      have hsq_nn : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
      calc c * ‖x‖ ^ 2 = ‖x‖ ^ 2 * c := by ring
        _ ≤ ‖x‖ ^ 2 * B u u := mul_le_mul_of_nonneg_left hcu hsq_nn
  · intro d hd
    have hu₀_norm : ‖u₀‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using hu₀_sphere
    have hdu₀ : d ≤ B u₀ u₀ := by
      simpa only [hu₀_norm, one_pow, mul_one] using hd u₀
    simpa only [hc_def, hQ] using hdu₀

def gpCoerciveConst (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  Classical.choose (gp_coercive (I := I) g p)

omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
lemma gpCoerciveConst_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < gpCoerciveConst (I := I) g p :=
  (Classical.choose_spec (gp_coercive (I := I) g p)).1

omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
lemma gpCoerciveConst_le (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
  (Classical.choose_spec (gp_coercive (I := I) g p)).2.1 x

omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
lemma le_gpCoerciveConst (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ}
    (hc : ∀ x : E, c * ‖x‖ ^ 2 ≤ g.inner p x x) :
    c ≤ gpCoerciveConst (I := I) g p :=
  (Classical.choose_spec (gp_coercive (I := I) g p)).2.2 hc

def expRadiusGp (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  Real.sqrt (gpCoerciveConst (I := I) g p) * expMapC2Radius (I := I) g p

lemma expRadiusGp_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < expRadiusGp (I := I) g p := by
  rw [expRadiusGp]
  exact mul_pos (Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p))
    (expMapC2Radius_pos (I := I) g p)

abbrev metricCoerciveConst (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  gpCoerciveConst (I := I) g p

omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
lemma metricCoerciveConst_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < metricCoerciveConst (I := I) g p :=
  gpCoerciveConst_pos (I := I) g p

omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
lemma metricCoerciveConst_le (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    metricCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
  gpCoerciveConst_le (I := I) g p x

abbrev metricCoerciveExpRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  expRadiusGp (I := I) g p

lemma norm_lt_expMapC2Radius_of_sqrt_inner_lt
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : Real.sqrt (g.inner p x x) < expRadiusGp (I := I) g p) :
    ‖x‖ < expMapC2Radius (I := I) g p := by
  have hc_pos : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  have hsq : g.inner p x x < (expRadiusGp (I := I) g p) ^ 2 :=
    Real.lt_sq_of_sqrt_lt hx
  have hR : (expRadiusGp (I := I) g p) ^ 2
      = gpCoerciveConst (I := I) g p * (expMapC2Radius (I := I) g p) ^ 2 := by
    rw [expRadiusGp, mul_pow, Real.sq_sqrt hc_pos.le]
  rw [hR] at hsq
  have hcoerc : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
    gpCoerciveConst_le (I := I) g p x
  have hlt : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2
      < gpCoerciveConst (I := I) g p * (expMapC2Radius (I := I) g p) ^ 2 :=
    lt_of_le_of_lt hcoerc hsq
  have hsq_lt : ‖x‖ ^ 2 < (expMapC2Radius (I := I) g p) ^ 2 :=
    lt_of_mul_lt_mul_left hlt hc_pos.le
  have hRpos : 0 < expMapC2Radius (I := I) g p := expMapC2Radius_pos (I := I) g p
  nlinarith [norm_nonneg x, hsq_lt, hRpos]


section GaussVariation

open Bundle Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [ChartedSpace H M] [CompleteSpace E] in
lemma gauss_t2Space_base (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space (TangentBundle I M)] : T2Space M := by
  have hproj : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hzero : Continuous (Bundle.zeroSection E (TangentSpace I)) :=
    (contMDiff_zeroSection (IB := I) ℝ (F := E) (E := (TangentSpace I : M → Type _))
      (n := ∞)).continuous
  have hinv : Function.LeftInverse (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (Bundle.zeroSection E (TangentSpace I)) := fun _ => rfl
  exact (IsEmbedding.of_leftInverse hinv hproj hzero).t2Space

private def gaussVariation (g : SmoothRiemannianMetric I M) (p : M) (v w : E) :
    ℝ → ℝ → M :=
  fun s t => expMap (I := I) g p (show TangentSpace I p from (t • (v + s • w)))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma velocityChartRep_differentiableAt_of_contMDiffAt2
    (γ : ℝ → M) (t₀ : ℝ) (hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)) t₀) t₀ := by
  set α : M := γ t₀ with hα
  have hchart_c2 : ContDiffAt ℝ 2 (fun u : ℝ => extChartAt I α (γ u)) t₀ :=
    contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt (I := I) (x := α)).comp t₀ hγC2)
  set sec : ℝ → E := fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (γ w)) u (1 : ℝ)
    with hsec
  have hsec_c1 : ContDiffAt ℝ 1 sec t₀ :=
    (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀
      (hchart_c2.fderiv_right (by norm_num))
  have hev_c2 : ∀ᶠ u in nhds t₀, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ u :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hγC2
  have hsrcmem : {u : ℝ | γ u ∈ (chartAt H α).source} ∈ nhds t₀ :=
    hγC2.continuousAt.preimage_mem_nhds
      ((chartAt H α).open_source.mem_nhds (mem_chart_source H (γ t₀)))
  have heq : (chartRepAt (I := I) γ (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)) t₀)
      =ᶠ[nhds t₀] sec := by
    filter_upwards [hsrcmem, hev_c2] with u hu hu_c2
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := γ) (hu_c2.mdifferentiableAt (by decide)) α (t := u) hu
    change (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ u)
        (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)) = sec u
    rw [hsec, show (γ t₀) = α from rfl]
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_c1.differentiableAt (by norm_num))

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma speedSq_hasDerivAt_zero_of_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t₀ : ℝ)
    (hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀)
    (hgeo : HasGeodesicEquationAt (I := I) g γ t₀) :
    HasDerivAt (fun t : ℝ => g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) 0 t₀ := by
  set V : ∀ u, TangentSpace I (γ u) := fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ) with hV
  have hVdiff := velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t₀ hγC2
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀ := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
      (contMDiffAt_extChartAt (I := I) (x := γ t₀) (n := 2)).comp t₀ hγC2
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hmc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g γ V V t₀
    hγC2.continuousAt hchartDeriv hVdiff hVdiff
  have hzero : covDerivAlong (I := I) g γ V t₀ = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t₀ hγC2 hgeo
  have hval : g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (V t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ V t₀) = 0 := by
    rw [hzero]; simp
  rw [← hval]; exact hmc

lemma radialCurve_contMDiffAt2
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t₀ : ℝ)
    (ht₀ : ‖t₀ • a‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ := by
  have hbase : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 (fun u : ℝ => u • a) t₀ :=
    (contMDiff_id.smul contMDiff_const).contMDiffAt
  have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) t₀) :=
    expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p ht₀
  exact hexp.comp t₀ hbase

private lemma radialCurve_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasGeodesicEquationAt (I := I) g
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ := by
  have htmem : t₀ ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hgeo : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => maximalGeodesic (I := I) g p a s) t₀ :=
    radial_hasGeodesicEquationAt_of_norm_lt_radius (I := I) g p ha t₀ htmem
  have hEvEq : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      =ᶠ[nhds t₀] (fun s : ℝ => maximalGeodesic (I := I) g p a s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with u hu
    have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    change (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)
        = maximalGeodesic (I := I) g p a u
    rw [expMap]
    exact maximalGeodesic_rescale_of_norm_lt_radius (I := I) g p ha u hu01
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hEvEq.eq_of_nhds hEvEq hgeo

lemma radialCurve_launch_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ)
      = (show TangentSpace I p from a) := by
  have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) 0) := by
    have h0 : ‖((fun u : ℝ => u • a) 0)‖ < expMapC2Radius (I := I) g p := by
      simp only; rw [zero_smul, norm_zero]; exact expMapC2Radius_pos (I := I) g p
    exact (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p h0).mdifferentiableAt (by decide)
  have hsmul_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) 0 := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun u : ℝ => u • a) := contMDiff_id.smul contMDiff_const
    exact hs.contMDiffAt.mdifferentiableAt (by decide)
  have hcomp : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘
        (fun u : ℝ => u • a) := rfl
  rw [hcomp, mfderiv_comp 0 hexp_mdiff hsmul_mdiff]
  simp only [ContinuousLinearMap.comp_apply]
  have hlaunch : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) 0 (1 : ℝ) = a := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun u : ℝ => u • a)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) 0 := by
      simpa using (hasFDerivAt_id (0 : ℝ)).smul_const a
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) (1 : ℝ) = a
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  rw [hlaunch, zero_smul, mfderiv_expMap_at_zero (I := I) g p]
  rfl

private def radialSpeedSq (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t : ℝ) : ℝ :=
  g.inner
    (expMap (I := I) g p (show TangentSpace I p from (t • a)))
    (mfderiv 𝓘(ℝ, ℝ) I
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) I
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t (1 : ℝ))

private lemma radialSpeedSq_hasDerivAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (radialSpeedSq (I := I) g p a) 0 t₀ := by
  have hnorm : ‖t₀ • a‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht₀
    have habs : |t₀| < 1 := by rw [abs_of_pos h0]; exact h1
    calc |t₀| * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right habs.le (norm_nonneg _)
      _ = ‖a‖ := one_mul _
      _ < _ := ha
  exact speedSq_hasDerivAt_zero_of_geodesic (I := I) g
    (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀
    (radialCurve_contMDiffAt2 (I := I) g p a t₀ hnorm)
    (radialCurve_hasGeodesicEquationAt (I := I) g p a ha t₀ ht₀)

lemma radialSpeedSq_eq_inner
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    radialSpeedSq (I := I) g p a t₀ = g.inner p a a := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  have hval0 : radialSpeedSq (I := I) g p a 0 = g.inner p a a := by
    have hv0 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ)
        = (show TangentSpace I p from a) := radialCurve_launch_velocity (I := I) g p a
    change g.inner
        (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • a)))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ))
      = g.inner p a a
    rw [hv0]
    have hb0 : (0 : ℝ) • a = (0 : E) := zero_smul ℝ a
    rw [show (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • a)) : M) = p by
      rw [hb0]; exact expMap_zero (I := I) g p]
  have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      radialSpeedSq (I := I) g p a x = radialSpeedSq (I := I) g p a y := by
    intro x hx y hy
    have hconv : Convex ℝ (Set.Ioo (0 : ℝ) 1) := convex_Ioo 0 1
    have hdiffOn : DifferentiableOn ℝ (radialSpeedSq (I := I) g p a) (Set.Ioo (0 : ℝ) 1) :=
      fun z hz =>
        ((radialSpeedSq_hasDerivAt_zero (I := I) g p a ha z hz).differentiableAt).differentiableWithinAt
    apply Convex.is_const_of_fderivWithin_eq_zero hconv hdiffOn _ hx hy
    intro z hz
    have hfd : HasFDerivWithinAt (radialSpeedSq (I := I) g p a) (0 : ℝ →L[ℝ] ℝ)
        (Set.Ioo (0 : ℝ) 1) z := by
      have h := ((radialSpeedSq_hasDerivAt_zero (I := I) g p a ha z hz).hasFDerivAt).hasFDerivWithinAt
        (s := Set.Ioo (0 : ℝ) 1)
      rwa [show (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)) = (0 : ℝ →L[ℝ] ℝ) from by
        ext; simp] at h
    rw [hfd.fderivWithin (uniqueDiffWithinAt_Ioo hz)]
  have hcont0 : ContinuousWithinAt (radialSpeedSq (I := I) g p a) (Set.Icc (0 : ℝ) 1) 0 := by
    set γ : ℝ → M :=
      fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M) with hγ
    set V : ∀ u, TangentSpace I (γ u) := fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ) with hV
    have hC2on : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t := by
      intro t ht
      have hnorm : ‖t • a‖ < expMapC2Radius (I := I) g p := by
        rw [norm_smul, Real.norm_eq_abs]
        obtain ⟨h0, h1⟩ := ht
        have habs : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
        calc |t| * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
          _ = ‖a‖ := one_mul _
          _ < _ := ha
      exact radialCurve_contMDiffAt2 (I := I) g p a t hnorm
    have hsec : ContinuousOn
        (fun t : ℝ => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) (Set.Icc (0 : ℝ) 1) :=
      sectionAlongCurve_continuousOn_totalSpace (I := I) γ V
        (fun t ht => (hC2on t ht).continuousAt.continuousWithinAt)
        (fun t ht => velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t (hC2on t ht))
    have hinner : ContinuousOn (fun t : ℝ => g.inner (γ t) (V t) (V t)) (Set.Icc (0 : ℝ) 1) :=
      Variation.continuousOn_g_inner_along_curve (I := I) g hsec hsec
    exact (hinner 0 ⟨le_refl 0, by norm_num⟩)
  have h0val : radialSpeedSq (I := I) g p a 0 = radialSpeedSq (I := I) g p a t₀ := by
    have h1 : Filter.Tendsto (radialSpeedSq (I := I) g p a)
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (radialSpeedSq (I := I) g p a 0)) :=
      hcont0.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
    have h2 : Filter.Tendsto (radialSpeedSq (I := I) g p a)
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (radialSpeedSq (I := I) g p a t₀)) := by
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with x hx using (hconst x hx t₀ ht₀).symm
    have hne : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)]
      exact nhdsGT_neBot 0
    exact tendsto_nhds_unique h1 h2
  rw [← h0val, hval0]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma variationFieldChartRep_differentiableAt_of_contDiffAt2
    (f : ℝ → ℝ → M) (t₀ : ℝ)
    (hF2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (f 0 t₀) (f q.1 q.2)) (0, t₀))
    (hcentral_cont : ContinuousAt (fun v : ℝ => f 0 v) t₀)
    (hslice_v : ∀ᶠ v in nhds t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀) t₀ := by
  set α : M := f 0 t₀ with hα
  have hjoint : ContDiffAt ℝ 2
      (Function.uncurry (fun v u : ℝ => extChartAt I α (f u v))) (t₀, (0 : ℝ)) := by
    have hswap : ContDiffAt ℝ 2
        ((fun q : ℝ × ℝ => extChartAt I α (f q.1 q.2)) ∘ (fun q : ℝ × ℝ => (q.2, q.1)))
        (t₀, (0 : ℝ)) :=
      hF2.comp (t₀, (0 : ℝ)) ((contDiffAt_snd).prodMk (contDiffAt_fst))
    exact hswap
  have hg0 : ContDiffAt ℝ 1 (fun _ : ℝ => (0 : ℝ)) t₀ := contDiffAt_const
  have hpartial : ContDiffAt ℝ 1
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v))
        ((fun _ : ℝ => (0 : ℝ)) v)) t₀ :=
    ContDiffAt.fderiv (𝕜 := ℝ) (f := fun v u : ℝ => extChartAt I α (f u v))
      (g := fun _ : ℝ => (0 : ℝ)) hjoint hg0 (by norm_num)
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    with hsec
  have hsec_c1 : ContDiffAt ℝ 1 sec t₀ :=
    (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hpartial
  have hsrc_nhds : {v : ℝ | f 0 v ∈ (chartAt H α).source} ∈ nhds t₀ := by
    refine hcentral_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t₀))
  have heq : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
      (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀) =ᶠ[nhds t₀] sec := by
    filter_upwards [hsrc_nhds, hslice_v] with v hv hslice_v_v
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u v) hslice_v_v α (t := 0) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f 0 v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_c1.differentiableAt (by norm_num))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma longitVelChartRep_differentiableAt_of_contDiffAt2
    (f : ℝ → ℝ → M) (t₀ : ℝ)
    (hF2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (f 0 t₀) (f q.1 q.2)) (0, t₀))
    (htransverse_cont : ContinuousAt (fun s : ℝ => f s t₀) 0)
    (hslice_u : ∀ᶠ s in nhds (0 : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => f s t₀)
        (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀ (1 : ℝ)) 0) 0 := by
  set α : M := f 0 t₀ with hα
  have hjoint : ContDiffAt ℝ 2
      (Function.uncurry (fun s u : ℝ => extChartAt I α (f s u))) (0, t₀) := hF2
  have hg0 : ContDiffAt ℝ 1 (fun _ : ℝ => t₀) 0 := contDiffAt_const
  have hpartial : ContDiffAt ℝ 1
      (fun s : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f s u))
        ((fun _ : ℝ => t₀) s)) 0 :=
    ContDiffAt.fderiv (𝕜 := ℝ) (f := fun s u : ℝ => extChartAt I α (f s u))
      (g := fun _ : ℝ => t₀) hjoint hg0 (by norm_num)
  set sec : ℝ → E := fun s : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f s u)) t₀ (1 : ℝ)
    with hsec
  have hsec_c1 : ContDiffAt ℝ 1 sec 0 :=
    (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp 0 hpartial
  have hsrc_nhds : {s : ℝ | f s t₀ ∈ (chartAt H α).source} ∈ nhds (0 : ℝ) := by
    refine htransverse_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t₀))
  have heq : (chartRepAt (I := I) (fun s : ℝ => f s t₀)
      (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀ (1 : ℝ)) 0) =ᶠ[nhds 0] sec := by
    filter_upwards [hsrc_nhds, hslice_u] with s hs hslice_u_s
    have hsrc : (fun u : ℝ => f s u) t₀ ∈ (chartAt H α).source := hs
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f s u) hslice_u_s α (t := t₀) hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t₀) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t₀) s) (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀ (1 : ℝ)) = sec s
    rw [hsec, show (fun s : ℝ => f s t₀) 0 = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun u : ℝ => extChartAt I α (f s u)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_c1.differentiableAt (by norm_num))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma launchSpeedSq_s_hasDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) :
    HasDerivAt (fun s : ℝ => g.inner p (v + s • w) (v + s • w))
      (2 * g.inner p v w) 0 := by
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB
  have hexpand : (fun s : ℝ => g.inner p (v + s • w) (v + s • w))
      = (fun s : ℝ => B v v + s * (B v w + B w v) + s ^ 2 * (B w w)) := by
    funext s
    change B (v + s • w) (v + s • w) = _
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  have hd1 : HasDerivAt (fun _ : ℝ => B v v) (0 : ℝ) 0 := hasDerivAt_const _ _
  have hd2 : HasDerivAt (fun s : ℝ => s * (B v w + B w v)) (B v w + B w v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (B v w + B w v)
  have hd3 : HasDerivAt (fun s : ℝ => s ^ 2 * (B w w)) (0 : ℝ) 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (B w w))
  have hd : HasDerivAt (fun s : ℝ => B v v + s * (B v w + B w v) + s ^ 2 * (B w w))
      (B v w + B w v) 0 := by simpa using (hd1.add hd2).add hd3
  have hsymm : B w v = B v w := g.symm p w v
  have hval : (2 : ℝ) * B v w = B v w + B w v := by rw [hsymm]; ring
  exact hval ▸ hd


private noncomputable def gaussClamp (δ : ℝ) : ℝ → ℝ :=
  fun s => δ * Real.arctan (s / δ)

private lemma gaussClamp_zero (δ : ℝ) : gaussClamp δ 0 = 0 := by
  simp [gaussClamp]

private lemma gaussClamp_hasDerivAt_one (δ : ℝ) (hδ : 0 < δ) :
    HasDerivAt (gaussClamp δ) 1 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s / δ) (1 / δ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const δ
  have h2 : HasDerivAt Real.arctan (1 / (1 + (0 / δ) ^ 2)) (0 / δ) := by
    simpa using Real.hasDerivAt_arctan (0 / δ)
  have h3 := (h2.comp 0 h1).const_mul δ
  have hcoef : δ * (1 / (1 + (0 / δ) ^ 2) * (1 / δ)) = 1 := by field_simp; ring
  rw [show gaussClamp δ = (fun s : ℝ => δ * Real.arctan (s / δ)) from rfl,
    show (1 : ℝ) = δ * (1 / (1 + (0 / δ) ^ 2) * (1 / δ)) from hcoef.symm]
  exact h3

private lemma gaussClamp_abs_lt (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    |gaussClamp δ s| < δ * (Real.pi / 2) := by
  change |δ * Real.arctan (s / δ)| < δ * (Real.pi / 2)
  rw [abs_mul, abs_of_pos hδ]
  apply mul_lt_mul_of_pos_left _ hδ
  rw [abs_lt]
  exact ⟨by linarith [Real.neg_pi_div_two_lt_arctan (s / δ)],
    by linarith [Real.arctan_lt_pi_div_two (s / δ)]⟩

private lemma gaussClamp_contMDiff (δ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (gaussClamp δ) := by
  change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => δ * Real.arctan (s / δ))
  rw [contMDiff_iff_contDiff]
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const δ))


private lemma gauss_phi_hasDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ‖v‖ < expMapC2Radius (I := I) g p)
    (hδsmall : ‖v‖ + δ * (Real.pi / 2) * ‖w‖ < expMapC2Radius (I := I) g p)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun t : ℝ => g.inner
        (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)))
      (g.inner p v w) t₀ := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  classical
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ s) • w))) : M)
    with hF
  have hclampMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (gaussClamp δ) := gaussClamp_contMDiff δ
  have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) := by
    refine ContMDiff.smul contMDiff_snd ?_
    refine contMDiff_const.add ?_
    exact (hclampMD.comp contMDiff_fst).smul contMDiff_const
  have hball : ∀ s : ℝ, ‖v + (gaussClamp δ s) • w‖ < expMapC2Radius (I := I) g p := by
    intro s
    calc ‖v + (gaussClamp δ s) • w‖ ≤ ‖v‖ + ‖(gaussClamp δ s) • w‖ := norm_add_le _ _
      _ = ‖v‖ + |gaussClamp δ s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v‖ + δ * (Real.pi / 2) * ‖w‖ := by
          nlinarith [norm_nonneg w, (gaussClamp_abs_lt δ hδ s).le]
      _ < _ := hδsmall
  have hball_t : ∀ s : ℝ, ‖t₀ • (v + (gaussClamp δ s) • w)‖ < expMapC2Radius (I := I) g p := by
    intro s
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht₀
    have habs : |t₀| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
    calc |t₀| * ‖v + (gaussClamp δ s) • w‖
        ≤ 1 * ‖v + (gaussClamp δ s) • w‖ :=
          mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖v + (gaussClamp δ s) • w‖ := one_mul _
      _ < _ := hball s
  have hslice_u_all : ∀ s : ℝ, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => F s u) t₀ := by
    intro s
    exact radialCurve_contMDiffAt2 (I := I) g p (v + (gaussClamp δ s) • w) t₀ (hball_t s)
  have hclamp0 : gaussClamp δ 0 = 0 := gaussClamp_zero δ
  have hcentral_eq : (fun t : ℝ => F 0 t)
      = (fun t : ℝ => (expMap (I := I) g p (show TangentSpace I p from (t • v)) : M)) := by
    funext t; rw [hF]; simp only; rw [hclamp0, zero_smul, add_zero]
  have hv_ball : ‖v‖ < expMapC2Radius (I := I) g p := hsmall
  have hFjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 2
      (fun q : ℝ × ℝ => F q.1 q.2) (0, t₀) := by
    have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
        (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t₀) :=
      hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
    have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          ((fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t₀)) := by
      have hval : (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t₀)
          = t₀ • (v + (gaussClamp δ 0) • w) := rfl
      rw [hval]
      exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p (hball_t 0)
    exact hexp.comp (0, t₀) hbase
  have hF2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (F 0 t₀) (F q.1 q.2)) (0, t₀) := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I (F 0 t₀)) (F 0 t₀) :=
      contMDiffAt_extChartAt (I := I) (x := F 0 t₀)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
        (fun q : ℝ × ℝ => extChartAt I (F 0 t₀) (F q.1 q.2)) (0, t₀) :=
      hext.comp (0, t₀) hFjoint
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  have htransverse_cont : ContinuousAt (fun s : ℝ => F s t₀) 0 := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2 (fun s : ℝ => (s, t₀)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact (hFjoint.comp 0 hincl).continuousAt
  have hcentral_cont : ContinuousAt (fun u : ℝ => F 0 u) t₀ := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2 (fun u : ℝ => ((0 : ℝ), u)) t₀ :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact (hFjoint.comp t₀ hincl).continuousAt
  have hslice_u_ev : ∀ᶠ s in nhds (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => F s u) t₀ :=
    Filter.Eventually.of_forall hslice_u_all
  have hslice_v_ev : ∀ᶠ v' in nhds t₀, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => F u v') 0 := by
    have hcont_norm : ContinuousAt (fun v' : ℝ => ‖v' • v‖) t₀ :=
      (continuous_norm.comp (continuous_id.smul continuous_const)).continuousAt
    have ht₀_ball : ‖t₀ • v‖ < expMapC2Radius (I := I) g p := by
      have := hball_t 0
      rwa [hclamp0, zero_smul, add_zero] at this
    have hnhds : {v' : ℝ | ‖v' • v‖ < expMapC2Radius (I := I) g p} ∈ nhds t₀ :=
      hcont_norm (isOpen_Iio.mem_nhds ht₀_ball)
    filter_upwards [hnhds] with v' hv'
    have hbase : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
        (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 := by
      have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) :=
        ContMDiff.smul contMDiff_const
          (contMDiff_const.add (hclampMD.smul contMDiff_const))
      exact hMD.contMDiffAt.of_le ENat.LEInfty.out
    have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          ((fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0) := by
      have hval : (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 = v' • v := by
        simp only; rw [hclamp0, zero_smul, add_zero]
      rw [hval]
      exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hv'
    exact hexp.comp 0 hbase
  have hcommute :
      covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
          (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ (1 : ℝ)) 0
        = covDerivAlong (I := I) g (fun u : ℝ => F 0 u)
          (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s u) 0 (1 : ℝ)) t₀ :=
    covDerivAlong_commute_transverse_longitudinal_of_variation (I := I) g F t₀ hF2 hslice_u_ev hslice_v_ev
      htransverse_cont hcentral_cont
  set γ : ℝ → M := fun t : ℝ => F 0 t with hγ
  set V : ∀ t, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F 0 u) t (1 : ℝ) with hVdef
  set W : ∀ t, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u t) 0 (1 : ℝ) with hWdef
  have hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀ := hslice_u_all 0
  have hγgeo : HasGeodesicEquationAt (I := I) g γ t₀ := by
    rw [show γ = (fun t : ℝ => (expMap (I := I) g p
      (show TangentSpace I p from (t • v)) : M)) from hcentral_eq]
    exact radialCurve_hasGeodesicEquationAt (I := I) g p v hv_ball t₀ ht₀
  have hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀ :=
    velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t₀ hγC2
  have hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀ := by
    have hslice_v_md : ∀ᶠ v' in nhds t₀,
        MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 := by
      filter_upwards [hslice_v_ev] with v' hv' using hv'.mdifferentiableAt (by decide)
    exact variationFieldChartRep_differentiableAt_of_contDiffAt2 (I := I) F t₀ hF2
      hcentral_cont hslice_v_md
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀ := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
      (contMDiffAt_extChartAt (I := I) (x := γ t₀) (n := 2)).comp t₀ hγC2
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hφ_mc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g γ V W t₀
    hγC2.continuousAt hchartDeriv hVdiff hWdiff
  have hV_vel : V = fun t : ℝ => (mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) := rfl
  have hVcov0 : covDerivAlong (I := I) g γ V t₀ = 0 := by
    rw [hV_vel]
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t₀ hγC2 hγgeo
  have hWcov_eq : covDerivAlong (I := I) g γ W t₀
      = covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
          (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ (1 : ℝ)) 0 := by
    rw [hγ, hWdef]; exact hcommute.symm
  set σ : ℝ → M := fun s : ℝ => F s t₀ with hσ
  set U : ∀ s, TangentSpace I (σ s) :=
    fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ (1 : ℝ) with hUdef
  have hU0_eq_Vt₀ : U 0 = V t₀ := rfl
  have hspeed_eq : (fun s : ℝ => g.inner (σ s) (U s) (U s))
      =ᶠ[nhds (0 : ℝ)] (fun s : ℝ => g.inner p (v + (gaussClamp δ s) • w)
        (v + (gaussClamp δ s) • w)) := by
    filter_upwards with s
    have hball_s := hball s
    have := radialSpeedSq_eq_inner (I := I) g p (v + (gaussClamp δ s) • w) hball_s t₀ ht₀
    rw [radialSpeedSq] at this
    exact this
  have hclamp_deriv : HasDerivAt (gaussClamp δ) 1 0 := gaussClamp_hasDerivAt_one δ hδ
  have hlaunch_sq_deriv :
      HasDerivAt (fun s : ℝ => g.inner p (v + (gaussClamp δ s) • w)
        (v + (gaussClamp δ s) • w)) (2 * g.inner p v w) 0 := by
    have hcomp : (fun s : ℝ => g.inner p (v + (gaussClamp δ s) • w)
        (v + (gaussClamp δ s) • w))
        = (fun r : ℝ => g.inner p (v + r • w) (v + r • w)) ∘ (gaussClamp δ) := rfl
    rw [hcomp]
    have hbase : HasDerivAt (fun r : ℝ => g.inner p (v + r • w) (v + r • w))
        (2 * g.inner p v w) (gaussClamp δ 0) := by
      rw [gaussClamp_zero δ]; exact launchSpeedSq_s_hasDerivAt (I := I) g p v w
    have hchain := hbase.scomp 0 hclamp_deriv
    simpa using hchain
  have hσC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 σ 0 := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2 (fun s : ℝ => (s, t₀)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact hFjoint.comp 0 hincl
  have hσchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (σ 0) σ) 0 := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (σ 0)) ∘ σ) 0 :=
      (contMDiffAt_extChartAt (I := I) (x := σ 0) (n := 2)).comp 0 hσC2
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hslice_u_md : ∀ᶠ s in nhds (0 : ℝ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ := by
    filter_upwards [hslice_u_ev] with s hs using hs.mdifferentiableAt (by decide)
  have hUdiff : DifferentiableAt ℝ (chartRepAt (I := I) σ U 0) 0 :=
    longitVelChartRep_differentiableAt_of_contDiffAt2 (I := I) F t₀ hF2
      htransverse_cont hslice_u_md
  have hσ_mc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g σ U U 0
    hσC2.continuousAt hσchartDeriv hUdiff hUdiff
  have hspeed_hasDerivAt :
      HasDerivAt (fun s : ℝ => g.inner (σ s) (U s) (U s)) (2 * g.inner p v w) 0 :=
    hlaunch_sq_deriv.congr_of_eventuallyEq hspeed_eq
  have hcov_val :
      g.inner (σ 0) (covDerivAlong (I := I) g σ U 0) (U 0)
        + g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
      = 2 * g.inner p v w :=
    hσ_mc.unique hspeed_hasDerivAt
  have hσ0 : σ 0 = γ t₀ := rfl
  have hcov_symm :
      g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
        = g.inner (σ 0) (covDerivAlong (I := I) g σ U 0) (U 0) :=
    g.symm (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
  have hcov_single :
      g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0) = g.inner p v w := by
    have h2 : 2 * g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
        = 2 * g.inner p v w := by
      rw [two_mul]
      nth_rewrite 1 [hcov_symm]
      exact hcov_val
    linarith [h2]
  have hsecond_term :
      g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀) = g.inner p v w := by
    rw [hWcov_eq]
    rw [show V t₀ = U 0 from hU0_eq_Vt₀.symm, ← hσ0]
    exact hcov_single
  have hfirst_term :
      g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀) = 0 := by
    rw [hVcov0]; simp
  have hφ_value :
      g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)
      = g.inner p v w := by
    rw [hfirst_term, hsecond_term, zero_add]
  have hφ_fun : (fun t : ℝ => g.inner (γ t) (V t) (W t))
      = (fun t : ℝ => g.inner
          (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ))) :=
    rfl
  rw [← hφ_fun, ← hφ_value]
  exact hφ_mc

end GaussVariation

section GaussAssembly

open Bundle Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic

theorem mfderiv_exp_radial
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t₀ : ℝ)
    (ht : ‖t₀ • a‖ < expMapC2Radius (I := I) g p) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ (1 : ℝ)
      = mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) (t₀ • a)
          (show TangentSpace I p from a) := by
  have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) t₀) :=
    (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p ht).mdifferentiableAt (by decide)
  have hsmul_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) t₀ := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun u : ℝ => u • a) :=
      contMDiff_id.smul contMDiff_const
    exact hs.contMDiffAt.mdifferentiableAt (by decide)
  have hcomp : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘
        (fun u : ℝ => u • a) := rfl
  rw [hcomp, mfderiv_comp t₀ hexp_mdiff hsmul_mdiff]
  simp only [ContinuousLinearMap.comp_apply]
  have hlaunch : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) t₀ (1 : ℝ) = a := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun u : ℝ => u • a)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) t₀ := by
      simpa using (hasFDerivAt_id (t₀ : ℝ)).smul_const a
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) (1 : ℝ) = a
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  rw [hlaunch]

private lemma gauss_phi_continuousOn
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) (δ : ℝ)
    (hsmall : ‖v‖ < expMapC2Radius (I := I) g p) :
    ContinuousOn (fun t : ℝ => g.inner
        (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)))
      (Set.Icc (0 : ℝ) 1) := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  classical
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ s) • w))) : M)
    with hF
  have hclamp0 : gaussClamp δ 0 = 0 := gaussClamp_zero δ
  set γ : ℝ → M := fun t : ℝ => F 0 t with hγ
  set V : ∀ t, TangentSpace I (γ t) := fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) with hVdef
  set W : ∀ t, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u t) 0 (1 : ℝ) with hWdef
  have hnorm_t : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖t • v‖ < expMapC2Radius (I := I) g p := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    calc |t| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ < _ := hsmall
  have hγC2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t := by
    intro t ht
    have heq : γ = fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • v)) : M) := by
      funext u; rw [hγ, hF]; simp only; rw [hclamp0, zero_smul, add_zero]
    rw [heq]
    exact radialCurve_contMDiffAt2 (I := I) g p v t (hnorm_t t ht)
  have hF2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (F 0 t) (F q.1 q.2)) (0, t) := by
    intro t ht
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) := by
      refine ContMDiff.smul contMDiff_snd ?_
      exact contMDiff_const.add (((gaussClamp_contMDiff δ).comp contMDiff_fst).smul contMDiff_const)
    have hFjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 2
        (fun q : ℝ × ℝ => F q.1 q.2) (0, t) := by
      have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
          (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t) :=
        hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
      have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
            ((fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t)) := by
        have hval : (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t) = t • v := by
          simp only; rw [hclamp0, zero_smul, add_zero]
        rw [hval]
        exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p (hnorm_t t ht)
      exact hexp.comp (0, t) hbase
    have hext : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I (F 0 t)) (F 0 t) :=
      contMDiffAt_extChartAt (I := I) (x := F 0 t)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
        (fun q : ℝ × ℝ => extChartAt I (F 0 t) (F q.1 q.2)) (0, t) :=
      hext.comp (0, t) hFjoint
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  have hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t :=
    fun t ht => velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t (hγC2 t ht)
  have hWdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t := by
    intro t ht
    have hslice_v_md : ∀ᶠ v' in nhds t,
        MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 := by
      have hcont_norm : ContinuousAt (fun v' : ℝ => ‖v' • v‖) t :=
        (continuous_norm.comp (continuous_id.smul continuous_const)).continuousAt
      have hnhds : {v' : ℝ | ‖v' • v‖ < expMapC2Radius (I := I) g p} ∈ nhds t :=
        hcont_norm (isOpen_Iio.mem_nhds (hnorm_t t ht))
      filter_upwards [hnhds] with v' hv'
      have hbase : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
          (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 := by
        have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) :=
          ContMDiff.smul contMDiff_const
            (contMDiff_const.add ((gaussClamp_contMDiff δ).smul contMDiff_const))
        exact hMD.contMDiffAt.of_le ENat.LEInfty.out
      have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
            ((fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0) := by
        have hval : (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 = v' • v := by
          simp only; rw [hclamp0, zero_smul, add_zero]
        rw [hval]
        exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hv'
      exact (hexp.comp 0 hbase).mdifferentiableAt (by decide)
    exact variationFieldChartRep_differentiableAt_of_contDiffAt2 (I := I) F t (hF2 t ht)
      (hγC2 t ht).continuousAt hslice_v_md
  have hsecV : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) (Set.Icc (0 : ℝ) 1) :=
    sectionAlongCurve_continuousOn_totalSpace (I := I) γ V
      (fun t ht => (hγC2 t ht).continuousAt.continuousWithinAt) hVdiff
  have hsecW : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E (γ t) (W t) : TangentBundle I M)) (Set.Icc (0 : ℝ) 1) :=
    sectionAlongCurve_continuousOn_totalSpace (I := I) γ W
      (fun t ht => (hγC2 t ht).continuousAt.continuousWithinAt) hWdiff
  exact Variation.continuousOn_g_inner_along_curve (I := I) g hsecV hsecW

set_option linter.unusedVariables false in
theorem gauss_lemma_pullback
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hsmall : ‖(v : E)‖ < expMapC2Radius (I := I) g p) :
    g.inner (expMap (I := I) g p (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v)) =
      g.inner p v v ∧
    ∀ {w : E}, g.inner p v w = (0 : ℝ) →
      g.inner (expMap (I := I) g p (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from w)) =
        (0 : ℝ) := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  have key : ∀ w : E,
      g.inner (expMap (I := I) g p (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from w)) = g.inner p v w := by
    intro w
    set R : ℝ := expMapC2Radius (I := I) g p with hR
    have hRpos : 0 < R - ‖v‖ := sub_pos.mpr hsmall
    set δ : ℝ := (R - ‖v‖) / (2 * ((Real.pi / 2) * ‖w‖ + 1)) with hδdef
    have hden_pos : 0 < 2 * ((Real.pi / 2) * ‖w‖ + 1) := by positivity
    have hδ : 0 < δ := by rw [hδdef]; exact div_pos hRpos hden_pos
    have hδsmall : ‖v‖ + δ * (Real.pi / 2) * ‖w‖ < R := by
      have hstep : δ * ((Real.pi / 2) * ‖w‖ + 1) = (R - ‖v‖) / 2 := by
        rw [hδdef]; field_simp
      have hle : δ * (Real.pi / 2) * ‖w‖ ≤ δ * ((Real.pi / 2) * ‖w‖ + 1) := by
        have heq : δ * (Real.pi / 2) * ‖w‖ = δ * ((Real.pi / 2) * ‖w‖) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) hδ.le
      have hbnd : δ * (Real.pi / 2) * ‖w‖ ≤ (R - ‖v‖) / 2 := by rw [← hstep]; exact hle
      linarith [hbnd, hRpos]
    set F : ℝ → ℝ → M := fun s t =>
      (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ s) • w))) : M)
      with hF
    set φ : ℝ → ℝ := fun t : ℝ => g.inner
        (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ))
      with hφdef
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (g.inner p v w) t := by
      intro t ht
      rw [hφdef]
      exact gauss_phi_hasDerivAt (I := I) g p v w δ hδ
        (by rw [← hR]; exact hsmall) (by rw [← hR]; exact hδsmall) t ht
    have hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
      rw [hφdef]
      exact gauss_phi_continuousOn (I := I) g p v w δ (by rw [← hR]; exact hsmall)
    have hint : IntervalIntegrable (fun _ : ℝ => g.inner p v w) MeasureTheory.volume 0 1 :=
      intervalIntegrable_const
    have hFTC : ∫ _t in (0 : ℝ)..1, (g.inner p v w) = φ 1 - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
    have hconstint : ∫ _t in (0 : ℝ)..1, (g.inner p v w) = g.inner p v w := by
      rw [intervalIntegral.integral_const]; simp
    have hφdiff : φ 1 - φ 0 = g.inner p v w := by rw [← hFTC, hconstint]
    have hsvar0 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)
        = 0 := by
      have hconstmap : (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ u) • w))) : M))
          = fun _ : ℝ => p := by
        funext u; simp only; rw [zero_smul]; exact expMap_zero (I := I) g p
      rw [hconstmap, mfderiv_const]; rfl
    have hφ0 : φ 0 = 0 := by
      have hφ0eval : φ 0 = g.inner
          (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ 0) • w))))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0
              (1 : ℝ)) := rfl
      rw [hφ0eval, hsvar0, ContinuousLinearMap.map_zero]
    have hφ1 : φ 1 = g.inner p v w := by rw [← hφdiff, hφ0, sub_zero]
    have hbase1 : (expMap (I := I) g p
        (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ 0) • w))))
        = (expMap (I := I) g p (show TangentSpace I p from v) : M) := by
      rw [gaussClamp_zero δ, zero_smul, add_zero, one_smul]
    have htvel1 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 1 (1 : ℝ)
        = mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from v) := by
      have hav : v + (gaussClamp δ 0) • w = v := by rw [gaussClamp_zero δ, zero_smul, add_zero]
      rw [hav]
      have hnorm1 : ‖(1 : ℝ) • v‖ < expMapC2Radius (I := I) g p := by
        rw [one_smul]; exact hsmall
      rw [mfderiv_exp_radial (I := I) g p v 1 hnorm1, one_smul]
    have hsvar1 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)
        = mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from w) := by
      set Hs : ℝ → E := fun u : ℝ => (1 : ℝ) • (v + (gaussClamp δ u) • w) with hHs
      have hHs0 : Hs 0 = v := by
        rw [hHs]; simp only; rw [gaussClamp_zero δ, zero_smul, add_zero, one_smul]
      have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) (Hs 0) := by
        rw [hHs0]
        exact (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hsmall).mdifferentiableAt
          (by decide)
      have hHs_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Hs 0 := by
        have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Hs := by
          rw [hHs]
          exact ContMDiff.smul contMDiff_const
            (contMDiff_const.add ((gaussClamp_contMDiff δ).smul contMDiff_const))
        exact hMD.contMDiffAt.mdifferentiableAt (by decide)
      have hcomp : (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M))
          = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘ Hs := rfl
      rw [hcomp, mfderiv_comp 0 hexp_mdiff hHs_mdiff]
      simp only [ContinuousLinearMap.comp_apply]
      have hHsderiv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Hs 0 (1 : ℝ) = w := by
        rw [mfderiv_eq_fderiv]
        have hclamp : HasDerivAt (gaussClamp δ) 1 0 := gaussClamp_hasDerivAt_one δ hδ
        have hHd : HasDerivAt Hs w 0 := by
          have h1 : HasDerivAt (fun u : ℝ => (gaussClamp δ u) • w) ((1 : ℝ) • w) 0 :=
            hclamp.smul_const w
          have h2 : HasDerivAt (fun u : ℝ => v + (gaussClamp δ u) • w)
              ((0 : E) + (1 : ℝ) • w) 0 := (hasDerivAt_const (0 : ℝ) v).add h1
          rw [zero_add, one_smul] at h2
          have h3 : Hs = fun u : ℝ => v + (gaussClamp δ u) • w := by
            rw [hHs]; funext u; rw [one_smul]
          rw [h3]; exact h2
        rw [hHd.hasFDerivAt.fderiv]
        change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) (1 : ℝ) = w
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
      rw [hHsderiv, hHs0]
    have hφ1eval : φ 1 = g.inner
        (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 1 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0
            (1 : ℝ)) := rfl
    have hcollapse : g.inner
          (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ 0) • w))))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 1 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0
              (1 : ℝ))
        = g.inner (expMap (I := I) g p (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
            (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
            (show TangentSpace I p from w)) := by
      rw [htvel1, hsvar1, hbase1]
    rw [hφ1eval, hcollapse] at hφ1
    exact hφ1
  refine ⟨?_, ?_⟩
  · exact key v
  · intro w hw
    rw [key w]; exact hw

end GaussAssembly

section RadialLengthEngine


open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

omit [NeZero (Module.finrank ℝ E)] in
theorem expMap_normalChartAt (g : SmoothRiemannianMetric I M) (p : M) {x : M}
    (hx : x ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    (expMap (I := I) g p
      (show TangentSpace I p from (NormalCoordinates.normalChartAt (I := I) g p x))) = x := by
  have hmem := (NormalCoordinates.normalChartAt (I := I) g p).map_source hx
  have h2 := NormalCoordinates.normalChartAt_symm_apply (I := I) g p
    (v := NormalCoordinates.normalChartAt (I := I) g p x) hmem
  have h1 := NormalCoordinates.normalChartAt_left_inv (I := I) g p hx
  rw [← h2, h1]

private theorem gauss_radial_lower_bound
    (g : SmoothRiemannianMetric I M) (p : M) {u : E}
    (hu : (show TangentSpace I p from u) ∈ expDomain (I := I) g p)
    (hsmall : ‖(u : E)‖ < expMapC2Radius (I := I) g p)
    (hune : u ≠ 0) (ζ : E) :
    (g.inner p u ζ)^2 / g.inner p u u ≤
      g.inner (expMap (I := I) g p (show TangentSpace I p from u))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ)) := by
  classical
  obtain ⟨hdiag, hcross⟩ := gauss_lemma_pullback (I := I) g p hu hsmall
  set q := expMap (I := I) g p (show TangentSpace I p from u) with hq
  set D : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
    with hD
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB
  set Bq : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hBq
  have hupos : 0 < B u u := g.pos p u hune
  have hune' : B u u ≠ 0 := ne_of_gt hupos
  set α : ℝ := B u ζ / B u u with hα
  set β : E := ζ - α • u with hβ
  have hdecomp : ζ = β + α • u := by rw [hβ]; abel
  have hβ_orth : B u β = 0 := by
    have key : B u β + α * B u u = B u ζ := by
      calc B u β + α * B u u = B u (β + α • u) := by rw [map_add, map_smul, smul_eq_mul]
        _ = B u ζ := by rw [← hdecomp]
    have hb : B u β = B u ζ - α * B u u := by linarith [key]
    rw [hb, hα]; field_simp; ring
  have hDζ : D ζ = D β + α • D u := by
    rw [show ζ = β + α • u from hdecomp, map_add, map_smul]
  change B u ζ ^ 2 / B u u ≤ Bq (D ζ) (D ζ)
  rw [hDζ]
  have hexpand : Bq (D β + α • D u) (D β + α • D u)
      = Bq (D β) (D β) + 2 * α * Bq (D u) (D β) + α^2 * Bq (D u) (D u) := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsym : Bq (D β) (D u) = Bq (D u) (D β) := g.symm q (D β) (D u)
    rw [hsym]; ring
  rw [hexpand]
  have hdiag' : Bq (D u) (D u) = B u u := hdiag
  have hcross' : Bq (D u) (D β) = 0 := hcross hβ_orth
  rw [hdiag', hcross']
  have hββ_nn : 0 ≤ Bq (D β) (D β) := by
    rcases eq_or_ne (D β) 0 with h | h
    · rw [h]; simp
    · exact (g.pos q (D β) h).le
  have hlhs : B u ζ ^ 2 / B u u = α^2 * B u u := by rw [hα]; field_simp
  rw [hlhs]
  nlinarith [hββ_nn, mul_nonneg (sq_nonneg α) hupos.le]

theorem gauss_radial_lower_bound_eq_iff
    (g : SmoothRiemannianMetric I M) (p : M) {u : E}
    (hu : (show TangentSpace I p from u) ∈ expDomain (I := I) g p)
    (hsmall : ‖(u : E)‖ < expMapC2Radius (I := I) g p)
    (hune : u ≠ 0) (ζ : E) :
    (g.inner p u ζ)^2 / g.inner p u u =
      g.inner (expMap (I := I) g p (show TangentSpace I p from u))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ))
    ↔ mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from
            (ζ - (g.inner p u ζ / g.inner p u u) • u)) = 0 := by
  classical
  obtain ⟨hdiag, hcross⟩ := gauss_lemma_pullback (I := I) g p hu hsmall
  set q := expMap (I := I) g p (show TangentSpace I p from u) with hq
  set D : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
    with hD
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB
  set Bq : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hBq
  have hupos : 0 < B u u := g.pos p u hune
  have hune' : B u u ≠ 0 := ne_of_gt hupos
  set α : ℝ := B u ζ / B u u with hα
  set β : E := ζ - α • u with hβ
  have hdecomp : ζ = β + α • u := by rw [hβ]; abel
  have hβ_orth : B u β = 0 := by
    have key : B u β + α * B u u = B u ζ := by
      calc B u β + α * B u u = B u (β + α • u) := by rw [map_add, map_smul, smul_eq_mul]
        _ = B u ζ := by rw [← hdecomp]
    have hb : B u β = B u ζ - α * B u u := by linarith [key]
    rw [hb, hα]; field_simp; ring
  have hDζ : D ζ = D β + α • D u := by
    rw [show ζ = β + α • u from hdecomp, map_add, map_smul]
  have hexpand : Bq (D ζ) (D ζ)
      = Bq (D β) (D β) + α^2 * B u u := by
    rw [hDζ]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsym : Bq (D β) (D u) = Bq (D u) (D β) := g.symm q (D β) (D u)
    have hdiag' : Bq (D u) (D u) = B u u := hdiag
    have hcross' : Bq (D u) (D β) = 0 := hcross hβ_orth
    rw [hsym, hdiag', hcross']; ring
  have hlhs : B u ζ ^ 2 / B u u = α^2 * B u u := by rw [hα]; field_simp
  have hiff_seminorm :
      (B u ζ ^ 2 / B u u = Bq (D ζ) (D ζ)) ↔ Bq (D β) (D β) = 0 := by
    rw [hlhs, hexpand]
    constructor
    · intro h; linarith
    · intro h; rw [h]; ring
  have hiff_zero : Bq (D β) (D β) = 0 ↔ D β = 0 := by
    constructor
    · intro h
      by_contra hne
      exact absurd h (ne_of_gt (g.pos q (D β) hne))
    · intro h; rw [h]; simp
  change ((B u ζ) ^ 2 / B u u = Bq (D ζ) (D ζ)) ↔ D β = 0
  rw [hiff_seminorm, hiff_zero]

theorem radial_chain_mfderiv
    (g : SmoothRiemannianMetric I M) (p : M) {γ : ℝ → M} {t : ℝ}
    (hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hsrc : γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hball : ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
      expMapC2Radius (I := I) g p)
    (hev : ∀ᶠ s in nhds t, γ s ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
    = mfderiv 𝓘(ℝ, E) I (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M))
        (NormalCoordinates.normalChartAt (I := I) g p (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ)) := by
  classical
  set c := NormalCoordinates.normalChartAt (I := I) g p with hc
  set ψ : ℝ → E := fun s => c (γ s) with hψ
  have hγeq : γ =ᶠ[nhds t] (fun s => expMap (I := I) g p (show TangentSpace I p from ψ s)) := by
    filter_upwards [hev] with s hs
    exact (expMap_normalChartAt (I := I) g p hs).symm
  rw [hγeq.mfderiv_eq]
  have hexp_diff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ t) :=
    (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hball).mdifferentiableAt (by decide)
  have hψ_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ψ t := by
    have hc_diff : MDifferentiableAt I 𝓘(ℝ, E) c (γ t) :=
      ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn one_ne_zero
        (γ t) hsrc).mdifferentiableAt
        ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds hsrc)
    exact hc_diff.comp t hγdiff
  rw [show (fun s => expMap (I := I) g p (show TangentSpace I p from ψ s))
      = (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) ∘ ψ from rfl,
    mfderiv_comp t hexp_diff hψ_diff]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem radialDist_hasDerivAt
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hBsym : ∀ a b : E, B a b = B b a)
    (ψ : ℝ → E) (ψ' : E) {t : ℝ}
    (hψ : HasDerivAt ψ ψ' t) (hpos : 0 < B (ψ t) (ψ t)) :
    HasDerivAt (fun s => Real.sqrt (B (ψ s) (ψ s)))
      (B (ψ t) ψ' / Real.sqrt (B (ψ t) (ψ t))) t := by
  have hf : HasDerivAt (fun s => B (ψ s) (ψ s)) (B ψ' (ψ t) + B (ψ t) ψ') t :=
    (B.hasFDerivAt.comp_hasDerivAt t hψ).clm_apply hψ
  have hsqrt := hf.sqrt (ne_of_gt hpos)
  have hcoef : (B ψ' (ψ t) + B (ψ t) ψ') / (2 * Real.sqrt (B (ψ t) (ψ t)))
      = B (ψ t) ψ' / Real.sqrt (B (ψ t) (ψ t)) := by
    rw [hBsym ψ' (ψ t), show B (ψ t) ψ' + B (ψ t) ψ' = 2 * B (ψ t) ψ' by ring,
      mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
  rwa [hcoef] at hsqrt

theorem gauss_pointwise_speed_lower_bound
    (g : SmoothRiemannianMetric I M) (p : M) {γ : ℝ → M} {t : ℝ}
    (hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hsrc : γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hdom : (show TangentSpace I p from (NormalCoordinates.normalChartAt (I := I) g p (γ t)))
      ∈ expDomain (I := I) g p)
    (hball : ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
      expMapC2Radius (I := I) g p)
    (hune : NormalCoordinates.normalChartAt (I := I) g p (γ t) ≠ 0)
    (hev : ∀ᶠ s in nhds t, γ s ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ)))^2
      / g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
          (NormalCoordinates.normalChartAt (I := I) g p (γ t))
    ≤ g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
  have hchain := radial_chain_mfderiv (I := I) g p hγdiff hsrc hball hev
  have hbase : γ t = expMap (I := I) g p
      (show TangentSpace I p from (NormalCoordinates.normalChartAt (I := I) g p (γ t))) :=
    (expMap_normalChartAt (I := I) g p hsrc).symm
  have hkernel := gauss_radial_lower_bound (I := I) g p hdom hball hune
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ))
  rw [← hbase] at hkernel
  rw [hchain]
  exact hkernel

end RadialLengthEngine

end GaussLemma

end Riemannian
end Geometry
end DifferentialGeometry
