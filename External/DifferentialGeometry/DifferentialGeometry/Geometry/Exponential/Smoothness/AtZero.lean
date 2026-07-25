import DifferentialGeometry.Geometry.Exponential.ChartFlow.RescaledLift
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Exponential.Smoothness.MatchDataReduction
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowData



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

section UnconditionalDischarge

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
theorem hasChartFlowGeodesicMatchData_unconditional
    (g : SmoothRiemannianMetric I M) (p : M) :
    HasChartFlowGeodesicMatchData (I := I) g p := by
  classical
  obtain ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T,
    hΦ_cd, hΦ_init0, hΦ_init_v, hΦ_target, hΦ_phase, hΦ_const_zero, _hF_int⟩ :=
    exists_unified_chartFlow_data (I := I) g p
  set t' : ℝ := T_match / 2 with ht'_def
  have ht'_pos : 0 < t' := by
    have : (0 : ℝ) < T_match / 2 := half_pos hT_match_pos
    rw [ht'_def]; exact this
  have ht'_lt_T_match : t' < T_match := by
    rw [ht'_def]
    exact half_lt_self hT_match_pos
  have ht'_lt_T : t' < T := lt_of_lt_of_le ht'_lt_T_match hT_match_le_T
  have ht'_in_Ioo : t' ∈ Set.Ioo (-T) T := by
    refine ⟨?_, ht'_lt_T⟩
    linarith
  have ht'_mul_one : t' * 1 = t' := mul_one t'
  have hmatch : ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ := by
    intro v hv_ball
    have hΦ_init_v_at : Φ (((extChartAt I p p, v) : E × E), 0) =
        ((extChartAt I p p, v) : E × E) := hΦ_init_v v hv_ball
    have hΦ_target_v : ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      intro s hs
      exact hΦ_target v hv_ball s hs
    have hΦ_phase_v : ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s := by
      intro s hs
      exact hΦ_phase v hv_ball s hs
    have hproj1 :=
      chartFlowOrbitLiftRescaled_proj_at_one (I := I) (g := g) (p := p) (v := v)
        (T := T) (t' := t') ht'_pos ht'_lt_T (Φ := Φ)
        hΦ_init_v_at hΦ_target_v hΦ_phase_v
    have hΦ_target_t' : Φ (((extChartAt I p p, v) : E × E), t' * 1) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      rw [ht'_mul_one]
      exact hΦ_target_v t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    have hproj_def :=
      chartFlowOrbitLiftRescaled_proj (I := I) (p := p) (v := v) (t' := t')
        (Φ := Φ) (s := 1) hΦ_target_t'
    have hcand_unfold : chartFlowCandidate (I := I) Φ p t' v =
        (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t')).1 := rfl
    have hproj_def' :
        (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
          (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t')).1 := by
      rw [hproj_def, ht'_mul_one]
    rw [← hproj1, hproj_def', ← hcand_unfold]
  have ht'_in_match : t' ∈ Set.Ioo (-T_match) T_match := by
    refine ⟨?_, ht'_lt_T_match⟩
    linarith
  have hΦ_t'_zero : Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
      ((extChartAt I p p, (0 : E)) : E × E) := hΦ_const_zero t' ht'_in_match
  have hΦ_t'_zero_fst : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 =
      extChartAt I p p := by
    rw [hΦ_t'_zero]
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hval_target : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target := by
    rw [hΦ_t'_zero_fst]; exact hx₀_target
  have hval_symm : (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p := by
    rw [hΦ_t'_zero_fst]
    exact (extChartAt I p).left_inv hx₀_src
  exact ⟨Φ, ρ, T, t', ρ, hρ_pos, hT_pos, ht'_pos, ht'_in_Ioo, hρ_pos,
    hΦ_cd, hval_target, hval_symm, hmatch⟩

end UnconditionalDischarge

section TrulyUnconditional

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
theorem expMap_contMDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
  expMap_contMDiffAt_zero_of_chartFlowGeodesicMatchData (I := I) g p
    (hasChartFlowGeodesicMatchData_unconditional (I := I) g p)

end TrulyUnconditional

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
