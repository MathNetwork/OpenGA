import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.VariationalMapContDiffOnK
import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.ContDiffOnK
import DifferentialGeometry.Analysis.ODE.Flow.Defs
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.EuclideanVariationalODE
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

theorem time_block_eq_comp_inr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0}
    {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) {x : E} {t : ℝ}
    (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) (ht : t ∈ Set.Ioo tmin tmax)
    (hΦdiff : DifferentiableAt ℝ Φ (x, t)) :
    (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)
      = timePieceFn f Φ (x, t) := by
  refine ContinuousLinearMap.ext_ring ?_
  simp only [ContinuousLinearMap.comp_apply, timePieceFn_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
  exact flow_joint_fderiv_inr_eq hΦ hx ht hΦdiff

theorem fderiv_flow_eq_spatialBlock_coprod_timePiece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0}
    {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) {x : E} {t : ℝ}
    (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) (ht : t ∈ Set.Ioo tmin tmax)
    (hΦdiff : DifferentiableAt ℝ Φ (x, t)) :
    fderiv ℝ Φ (x, t)
      = (fderiv ℝ (fun y => Φ (y, t)) x).coprod (timePieceFn f Φ (x, t)) := by
  rw [partial_spatial_fderiv_eq_comp_inl hΦdiff,
    ← time_block_eq_comp_inr hΦ hx ht hΦdiff]
  exact (ContinuousLinearMap.coprod_comp_inl_inr (fderiv ℝ Φ (x, t))).symm

theorem fderiv_spatialSlice_initial_eq_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0}
    {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) {x : E}
    (hx : x ∈ Metric.ball x₀ (r : ℝ)) :
    fderiv ℝ (fun y => Φ (y, t₀)) x = ContinuousLinearMap.id ℝ E := by
  have hball : Metric.ball x₀ (r : ℝ) ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hx
  have heqon : Set.EqOn (fun y => Φ (y, t₀)) (fun y => y) (Metric.ball x₀ (r : ℝ)) :=
    fun y hy => hΦ.apply_initial y (Metric.ball_subset_closedBall hy)
  have heq : (fun y => Φ (y, t₀)) =ᶠ[𝓝 x] (fun y => y) :=
    Filter.eventuallyEq_of_mem hball heqon
  rw [heq.fderiv_eq, fderiv_id']

theorem variationalEquation_spatialDerivative_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < (r : ℝ)) (_ : 0 < ε) (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ ∧
      ∃ (T : ℝ) (ρ : ℝ≥0) (_ : 0 < T) (_ : 0 < (ρ : ℝ))
        (W : E × ℝ → (E →L[ℝ] E)),
        (∀ q ∈ (Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T),
          fderiv ℝ Φ q = (W q).coprod (timePieceFn f Φ q)) ∧
        (∀ x ∈ Metric.ball x₀ (ρ : ℝ), W (x, t₀) = ContinuousLinearMap.id ℝ E) ∧
        (∀ x ∈ Metric.ball x₀ (ρ : ℝ), ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
          HasDerivAt (fun s => W (x, s))
            ((fderiv ℝ (f t) (Φ (x, t))).comp (W (x, t))) t) := by
  obtain ⟨r, ε, hr, hε, Φ, hΦ, ρ, T, hρ, hT, hρr, hTε, hΦsmooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := f) (t₀ := t₀) (x₀ := x₀) hf
  set U : Set (E × ℝ) := Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  set W : E × ℝ → (E →L[ℝ] E) := fun q => fderiv ℝ (fun y => Φ (y, q.2)) q.1 with hW
  refine ⟨r, ε, hr, hε, Φ, hΦ, T, ⟨ρ, hρ.le⟩, hT, hρ, W, ?_, ?_, ?_⟩
  · rintro ⟨x, t⟩ hq
    rw [Set.mem_prod] at hq
    obtain ⟨hxρ, htT⟩ := hq
    have hxsU : (x, t) ∈ U := Set.mem_prod.mpr ⟨hxρ, htT⟩
    have hΦdiff : DifferentiableAt ℝ Φ (x, t) :=
      (hΦsmooth.contDiffAt (hUopen.mem_nhds hxsU)).differentiableAt (by simp)
    have hxr : x ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρr hxρ)
    have htε : t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith) htT
    exact fderiv_flow_eq_spatialBlock_coprod_timePiece hΦ hxr htε hΦdiff
  · intro x hxρ
    have hxr : x ∈ Metric.ball x₀ (r : ℝ) := Metric.ball_subset_ball hρr hxρ
    exact fderiv_spatialSlice_initial_eq_id hΦ hxr
  · intro x hxρ t htT
    have hxsU : (x, t) ∈ U := Set.mem_prod.mpr ⟨hxρ, htT⟩
    have hxr : x ∈ Metric.ball x₀ (r : ℝ) := Metric.ball_subset_ball hρr hxρ
    have htε : t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith) htT
    exact hΦ.hasDerivAt_partial_spatial_fderiv hf hUopen hΦsmooth hxsU hxr htε

end DifferentialGeometry.PDE.RicciFlow.ODE
