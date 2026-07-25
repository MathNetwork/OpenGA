import DifferentialGeometry.Geometry.Exponential.ChartFlow.RescaledLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.MaximalRescaling



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

section UniformSmallRescaling

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem maximalGeodesic_rescaled_eq_orbit_proj
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t')
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_target : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s)
    {s : ℝ} (hs : s ∈ Set.Ioo (-T / t') (T / t')) :
    maximalGeodesic (I := I) g p (t' • v) s =
      (extChartAt I p).symm
        (Φ (((extChartAt I p p, v) : E × E), t' * s)).1 := by
  have h_proj_eq :=
    chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo (I := I)
      (g := g) (p := p) (v := v) (T := T) (t' := t') ht'_pos
      (Φ := Φ) hΦ_init hΦ_target hΦ_phase hs
  have hts_Ioo : t' * s ∈ Set.Ioo (-T) T :=
    mul_mem_Ioo_of_pos_of_lt ht'_pos hs
  have hΦ_target_ts := hΦ_target (t' * s) (Set.Ioo_subset_Icc_self hts_Ioo)
  have h_proj :=
    chartFlowOrbitLiftRescaled_proj (I := I) p v t' (Φ := Φ) s hΦ_target_ts
  rw [← h_proj_eq, h_proj]

omit [NeZero (Module.finrank ℝ E)] in
theorem foot_in_source_throughout
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          maximalGeodesic (I := I) g p v t ∈ (chartAt H p).source := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
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
  have hT_div : T / t' = 2 := by
    rw [ht'_def]; field_simp
  have ht_Ioo : t ∈ Set.Ioo (-T / t') (T / t') := by
    rw [neg_div, hT_div]
    obtain ⟨ht0, ht1⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have hmem_v : (v : E) = t' • vb := hvb_resc.symm
  have h_eq :
      maximalGeodesic (I := I) g p v t =
        (extChartAt I p).symm
          (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1 := by
    have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
      (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
      (s := t) ht_Ioo
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
    exact h
  rw [h_eq]
  have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
    obtain ⟨ht0, ht1⟩ := ht
    refine ⟨?_, ?_⟩
    · nlinarith [ht'_pos.le, hT_pos.le]
    · nlinarith [ht'_lt_T.le, ht'_pos.le]
  have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
  have hsrc :=
    chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p vb t' t
      hΦ_target_tt
  rw [chartFlowOrbitLiftRescaled_proj (I := I) p vb t' t hΦ_target_tt] at hsrc
  exact hsrc

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_rescale_at_one_of_small
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          maximalGeodesic (I := I) g p (t • v) 1 =
            maximalGeodesic (I := I) g p v t := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv t ht
  obtain ⟨ht0, ht1⟩ := ht
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
  rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
  · subst ht_zero
    rw [zero_smul, maximalGeodesic_zero (I := I) g p v]
    have h1 : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p
        (0 : TangentSpace I p) :=
      maximalGeodesicWitness_zero_all_times (I := I) g p 1
    rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p)
      (v := (0 : TangentSpace I p)) h1]
    obtain ⟨J, hJ_open, hJ_conn, h0J, h1J, hγ⟩ :=
      maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p) h1
    exact maximalGeodesicWitness_zero_curve_eq_p (I := I)
      hJ_open hJ_conn h0J hγ 1 h1J
  · have ht_Ioo : t ∈ Set.Ioo (-T / t') (T / t') := by
      rw [neg_div, hT_div]; exact ⟨by linarith, by linarith⟩
    have h_rhs :
        maximalGeodesic (I := I) g p v t =
          (extChartAt I p).symm
            (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1 := by
      have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
        (v := vb) (T := T) (t' := t') ht'_pos
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
        (s := t) ht_Ioo
      rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
      exact h
    set t'' : ℝ := t * t' with ht''_def
    have ht''_pos : 0 < t'' := by rw [ht''_def]; exact mul_pos ht_pos ht'_pos
    have ht''_lt_T : t'' < T := by
      rw [ht''_def]; nlinarith [ht'_pos.le, ht'_lt_T]
    have htvb : (t'' • vb : E) = t • w := by
      rw [ht''_def, ← smul_smul, hvb_resc, hw_def]
    have h_tv : (t • v : TangentSpace I p) = t'' • vb := htvb.symm
    have hone_Ioo : (1 : ℝ) ∈ Set.Ioo (-T / t'') (T / t'') := by
      have hlt : 1 < T / t'' := (one_lt_div ht''_pos).mpr ht''_lt_T
      have hneg : -T / t'' < 0 := by
        rw [neg_div]; exact neg_lt_zero.mpr (div_pos hT_pos ht''_pos)
      exact ⟨by linarith, hlt⟩
    have h_lhs :
        maximalGeodesic (I := I) g p (t • v) 1 =
          (extChartAt I p).symm
            (Φ (((extChartAt I p p, vb) : E × E), t'' * 1)).1 := by
      have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
        (v := vb) (T := T) (t' := t'') ht''_pos
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
        (s := (1 : ℝ)) hone_Ioo
      rw [show (t'' • vb : TangentSpace I p) = t • v from h_tv.symm] at h
      exact h
    rw [h_lhs, h_rhs]
    congr 2
    rw [ht''_def, mul_one, mul_comm]
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_continuousOn_Icc_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v₀ : TangentSpace I p}, ‖(v₀ : E)‖ < ρ →
        ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v₀ hv₀
  set w : E := (v₀ : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  set vb : E := (1 / t') • w with hvb_def
  have hvb_resc : t' • vb = (v₀ : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv₀
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp

  have h_eqOn : Set.EqOn (maximalGeodesic (I := I) g p v₀)
      (fun t => (extChartAt I p).symm
        (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have ht_Ioo : t ∈ Set.Ioo (-T / t') (T / t') := by
      rw [neg_div, hT_div]
      obtain ⟨ht0, ht1⟩ := ht
      exact ⟨by linarith, by linarith⟩
    have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
      (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
      (s := t) ht_Ioo
    rw [show (t' • vb : TangentSpace I p) = v₀ from hvb_resc] at h
    exact h

  have hφ_contOn : ContinuousOn
      (fun s : ℝ => Φ (((extChartAt I p p, vb) : E × E), s)) (Set.Ioo (-T) T) := by
    intro s hs
    exact ((hΦ_phase vb hvb_ball s hs).differentiableAt).continuousAt.continuousWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => t' * t) (Set.Icc (0 : ℝ) 1) (Set.Ioo (-T) T) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h_nonneg : 0 ≤ t' * t := mul_nonneg ht'_pos.le ht0
    have h_le : t' * t ≤ t' := by
      calc t' * t ≤ t' * 1 := mul_le_mul_of_nonneg_left ht1 ht'_pos.le
        _ = t' := mul_one t'
    exact ⟨by linarith, by linarith [ht'_lt_T]⟩
  have h_orbit_cont : ContinuousOn
      (fun t : ℝ => Φ (((extChartAt I p p, vb) : E × E), t' * t)) (Set.Icc (0 : ℝ) 1) :=
    hφ_contOn.comp ((continuous_const.mul continuous_id).continuousOn) hmap
  have h_fst : ContinuousOn
      (fun t : ℝ => (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) :=
    continuous_fst.comp_continuousOn h_orbit_cont
  have hmaps_target : Set.MapsTo
      (fun t : ℝ => (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) (extChartAt I p).target := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h_nonneg : 0 ≤ t' * t := mul_nonneg ht'_pos.le ht0
    have h_le : t' * t ≤ t' := by
      calc t' * t ≤ t' * 1 := mul_le_mul_of_nonneg_left ht1 ht'_pos.le
        _ = t' := mul_one t'
    have hts : t' * t ∈ Set.Icc (-T) T := ⟨by linarith, by linarith [ht'_lt_T.le]⟩
    exact interior_subset (hΦ_target vb hvb_ball (t' * t) hts).1
  have hF_cont : ContinuousOn
      (fun t => (extChartAt I p).symm
        (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_extChartAt_symm (I := I) p).comp h_fst hmaps_target
  exact hF_cont.congr h_eqOn


end UniformSmallRescaling

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
