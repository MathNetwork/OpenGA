import DifferentialGeometry.Analysis.ODE.Flow.Defs
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

theorem augmented_field_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : ℝ → P → E → E} (hf : ContDiff ℝ ∞ (fun q : ℝ × P × E => f q.1 q.2.1 q.2.2)) :
    ContDiff ℝ ∞ (Function.uncurry
      (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))) := by
  have hshuffle :
      ContDiff ℝ ∞ (fun q : ℝ × (E × P) => (q.1, q.2.2, q.2.1) : _ → ℝ × P × E) :=
    contDiff_fst.prodMk ((contDiff_snd.comp contDiff_snd).prodMk
      (contDiff_fst.comp contDiff_snd))
  have hfst : ContDiff ℝ ∞ (fun q : ℝ × (E × P) => f q.1 q.2.2 q.2.1) :=
    hf.comp hshuffle
  exact hfst.prodMk contDiff_const

theorem orbit_param_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {z₀ : E × P} {r : ℝ≥0} {ε : ℝ}
    {Ψ : (E × P) × ℝ → E × P}
    (hΨ : IsLocalFlow (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))
      t₀ z₀ r (t₀ - ε) (t₀ + ε) Ψ) :
    ∀ z ∈ Metric.closedBall z₀ (r : ℝ), ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      (Ψ (z, t)).2 = z.2 := by
  intro z hz t ht
  set g : ℝ → P := fun u => (Ψ (z, u)).2 with hg
  have hA : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt g (0 : P) (Set.Icc (t₀ - ε) (t₀ + ε)) s := by
    intro s hs
    have horbit := hΨ.hasDerivWithinAt z hz s hs
    have hcomp :=
      (ContinuousLinearMap.snd ℝ E P).hasFDerivAt.comp_hasDerivWithinAt s horbit
    simpa [g, Function.comp, ContinuousLinearMap.coe_snd'] using hcomp
  have hB : ∀ s ∈ Set.Ico (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt g (0 : P) (Set.Ici s) s := by
    intro s hs
    exact (hA s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hC : ContinuousOn g (Set.Icc (t₀ - ε) (t₀ + ε)) :=
    continuous_snd.comp_continuousOn (hΨ.orbit_continuousOn z hz)
  have hconst := constant_of_has_deriv_right_zero hC hB
  have ht' : g t = g (t₀ - ε) := hconst t ht
  have ht₀' : g t₀ = g (t₀ - ε) := hconst t₀ hΨ.t₀_mem_Icc
  have hinit : g t₀ = z.2 := by
    simp only [g]
    rw [hΨ.apply_initial z hz]
  change g t = z.2
  rw [ht', ← ht₀', hinit]

theorem projected_ode_initial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {z₀ : E × P} {r : ℝ≥0} {ε : ℝ}
    {Ψ : (E × P) × ℝ → E × P}
    (hΨ : IsLocalFlow (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))
      t₀ z₀ r (t₀ - ε) (t₀ + ε) Ψ)
    (hinv : ∀ z ∈ Metric.closedBall z₀ (r : ℝ), ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      (Ψ (z, t)).2 = z.2) :
    ∀ (x : E) (lam : P), ((x, lam) : E × P) ∈ Metric.closedBall z₀ (r : ℝ) →
      (Ψ ((x, lam), t₀)).1 = x ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s => (Ψ ((x, lam), s)).1) (f t lam (Ψ ((x, lam), t)).1) t := by
  intro x lam hz
  set z : E × P := (x, lam) with hzdef
  refine ⟨?_, ?_⟩
  · have hinit : Ψ (z, t₀) = z := hΨ.apply_initial z hz
    calc (Ψ (z, t₀)).1 = z.1 := congrArg Prod.fst hinit
      _ = x := rfl
  · intro t ht
    have htIcc : t ∈ Set.Icc (t₀ - ε) (t₀ + ε) := Set.Ioo_subset_Icc_self ht
    have horbit := hΨ.hasDerivWithinAt z hz t htIcc
    have horbitAt : HasDerivAt (fun s => Ψ (z, s))
        ((f t (Ψ (z, t)).2 (Ψ (z, t)).1, (0 : P)) : E × P) t :=
      horbit.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hfst :=
      (ContinuousLinearMap.fst ℝ E P).hasFDerivAt.comp_hasDerivAt t horbitAt
    have hpar : (Ψ (z, t)).2 = lam := by
      have := hinv z hz t htIcc
      simpa [hzdef] using this
    simpa [Function.comp, ContinuousLinearMap.coe_fst', hpar] using hfst

theorem reindex_contDiff_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ContDiff ℝ ∞ (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2)) :=
  ((contDiff_snd.fst).prodMk contDiff_fst).prodMk contDiff_snd.snd

theorem projected_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {t₀ : ℝ} {z₀ : E × P} {Ψ : (E × P) × ℝ → E × P} {ρ T : ℝ}
    (hΨsmooth : ContDiffOn ℝ ∞ Ψ (Metric.ball z₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    {lam₀ : P} {x₀ : E} {ρP ρE : ℝ}
    (hmaps : Set.MapsTo (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2))
      (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - T) (t₀ + T))
      (Metric.ball z₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ ∞ (fun w : P × E × ℝ => (Ψ ((w.2.1, w.1), w.2.2)).1)
      (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
  have hg : ContDiffOn ℝ ∞ (fun u : (E × P) × ℝ => (Ψ u).1)
      (Metric.ball z₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := hΨsmooth.fst
  have hf : ContDiffOn ℝ ∞ (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2))
      (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) :=
    (reindex_contDiff_top).contDiffOn
  exact hg.comp hf hmaps

theorem exists_isLocalFlow_param_contDiffOn_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {x₀ : E} {lam₀ : P}
    (hf : ContDiff ℝ ∞ (fun q : ℝ × P × E => f q.1 q.2.1 q.2.2)) :
    ∃ (ρP ρE ε : ℝ) (Φ : P × E × ℝ → E),
      0 < ρP ∧ 0 < ρE ∧ 0 < ε ∧
      (∀ lam ∈ Metric.ball lam₀ ρP, ∀ x ∈ Metric.ball x₀ ρE, Φ (lam, x, t₀) = x) ∧
      (∀ lam ∈ Metric.ball lam₀ ρP, ∀ x ∈ Metric.ball x₀ ρE,
          ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s => Φ (lam, x, s)) (f t lam (Φ (lam, x, t))) t) ∧
      ContDiffOn ℝ ∞ Φ
        (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - ε) (t₀ + ε)) := by
  classical
  set z₀ : E × P := (x₀, lam₀) with hz₀
  set g : ℝ → (E × P) → E × P :=
    fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P) with hg
  have hg_smooth : ContDiff ℝ ∞ (Function.uncurry g) := augmented_field_contDiff hf
  obtain ⟨r, ε, hr_pos, hε_pos, Ψ, hΨ, ρ, T, hρ_pos, hT_pos, hρ_le_r, hT_le_ε, hΨsmooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := g) (t₀ := t₀) (x₀ := z₀) hg_smooth
  have hinv : ∀ z ∈ Metric.closedBall z₀ (r : ℝ), ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      (Ψ (z, t)).2 = z.2 := orbit_param_invariant hΨ
  have htimeε : Set.Ioo (t₀ - min ε T) (t₀ + min ε T) ⊆ Set.Ioo (t₀ - ε) (t₀ + ε) :=
    Set.Ioo_subset_Ioo (by have := min_le_left ε T; linarith)
      (by have := min_le_left ε T; linarith)
  have htimeT : Set.Ioo (t₀ - min ε T) (t₀ + min ε T) ⊆ Set.Ioo (t₀ - T) (t₀ + T) :=
    Set.Ioo_subset_Ioo (by have := min_le_right ε T; linarith)
      (by have := min_le_right ε T; linarith)
  have hmem : ∀ lam ∈ Metric.ball lam₀ (ρ / 2), ∀ x ∈ Metric.ball x₀ (ρ / 2),
      ((x, lam) : E × P) ∈ Metric.closedBall z₀ (r : ℝ) := by
    intro lam hlam x hx
    have h1 : ((x, lam) : E × P) ∈ Metric.ball z₀ (ρ / 2) := by
      rw [hz₀, ← ball_prod_same]; exact ⟨hx, hlam⟩
    exact Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith) h1)
  refine ⟨ρ / 2, ρ / 2, min ε T, fun w : P × E × ℝ => (Ψ ((w.2.1, w.1), w.2.2)).1,
    by positivity, by positivity, lt_min hε_pos hT_pos, ?_, ?_, ?_⟩
  · intro lam hlam x hx
    have hz := hmem lam hlam x hx
    exact (projected_ode_initial hΨ hinv x lam hz).1
  · intro lam hlam x hx t ht
    have hz := hmem lam hlam x hx
    exact (projected_ode_initial hΨ hinv x lam hz).2 t (htimeε ht)
  · have hmaps : Set.MapsTo (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2))
        (Metric.ball lam₀ (ρ / 2) ×ˢ Metric.ball x₀ (ρ / 2) ×ˢ Set.Ioo (t₀ - T) (t₀ + T))
        (Metric.ball z₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
      rintro ⟨lam, x, t⟩ ⟨hlam, hx, ht⟩
      refine ⟨?_, ht⟩
      have h1 : ((x, lam) : E × P) ∈ Metric.ball z₀ (ρ / 2) := by
        rw [hz₀, ← ball_prod_same]; exact ⟨hx, hlam⟩
      exact Metric.ball_subset_ball (by linarith) h1
    have hcd := projected_contDiffOn (t₀ := t₀) (z₀ := z₀) (Ψ := Ψ) (ρ := ρ) (T := T)
      hΨsmooth (lam₀ := lam₀) (x₀ := x₀) (ρP := ρ / 2) (ρE := ρ / 2) hmaps
    refine hcd.mono (Set.prod_mono (le_refl _) (Set.prod_mono (le_refl _) htimeT))

end DifferentialGeometry.PDE.RicciFlow.ODE
