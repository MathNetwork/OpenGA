import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.ContDiffOnTop
import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.VariationalMapContDiffOnK
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension






























noncomputable section

namespace DifferentialGeometry.Analysis.ODE.Flow

open Set Metric Function Real
open scoped ContDiff NNReal Uniformity



section CoefficientRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {Φ : E × ℝ → E}




omit [CompleteSpace E] in
private theorem contDiffOn_variational_coeff_aux_local
    {n : ℕ} {T : ℝ} {ρ : ℝ}
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_succ : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) Ω)
    (hΦ_Cn : ContDiffOn ℝ (n : ℕ∞) Φ ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hΩ_map :
      ∀ q ∈ ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)),
        (q.2, Φ q) ∈ Ω) :
    ContDiffOn ℝ (n : ℕ∞)
      (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set pfD : ℝ × E → (E →L[ℝ] E) := fun p => fderiv ℝ (f p.1) p.2
  set iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  set U := (ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)
  suffices h : ContDiffOn ℝ (n : ℕ∞) (pfD ∘ iM) U by
    exact h.congr (fun _ _ => rfl)
  have hpfd : ContDiffOn ℝ (n : ℕ∞) pfD Ω :=
    contDiffOn_partial_fderiv_of_succ_local hΩ hf_succ
  have hiM : ContDiffOn ℝ (n : ℕ∞) iM U :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ (n : ℕ∞) Prod.snd U).prodMk hΦ_Cn
  exact hpfd.comp hiM hΩ_map

end CoefficientRegularity



section LocalFlowTubeBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}



omit [FiniteDimensional ℝ E] in
omit [CompleteSpace E] in
private theorem continuousOn_fderiv_jointly_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T ρ : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hρ_le : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      (closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  let K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  let G : E × ℝ → E →L[ℝ] E := fun q => fderiv ℝ (f q.2) (Φ q)
  have hK_sub : K ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    exact ⟨closedBall_subset_closedBall hρ_le hq.1, hsub hq.2⟩
  have hΦcont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  let pfD : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (f p.1) p.2
  let iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  have hpfD : ContDiffOn ℝ 0 pfD Ω := by
    simpa [pfD] using
      (contDiffOn_partial_fderiv_of_succ_local
        (f := f) (k := (0 : ℕ∞)) hΩ (by simpa using hf_one))
  have hiM : ContinuousOn iM K := by
    exact continuousOn_snd.prodMk hΦcont
  have hmaps : MapsTo iM K Ω := by
    intro q hq
    exact hΩ_flow q.1 (closedBall_subset_closedBall hρ_le hq.1) q.2 (hsub hq.2)
  have hG : ContinuousOn G K := by
    have hcomp := hpfD.continuousOn.comp hiM hmaps
    exact hcomp.congr (fun q _hq => rfl)
  exact hG


omit [FiniteDimensional ℝ E] in
omit [CompleteSpace E] in
private theorem IsLocalFlow.continuousOn_fderiv_along_orbit_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    (x : E) (hx : x ∈ closedBall x₀ (r : ℝ)) :
    ContinuousOn (fun τ => fderiv ℝ (f τ) (Φ (x, τ))) (Icc tmin tmax) := by
  let pfD : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (f p.1) p.2
  have hpfD : ContDiffOn ℝ 0 pfD Ω := by
    simpa [pfD] using
      (contDiffOn_partial_fderiv_of_succ_local
        (f := f) (k := (0 : ℕ∞)) hΩ (by simpa using hf_one))
  have horbit : ContinuousOn (fun τ : ℝ => (τ, Φ (x, τ))) (Icc tmin tmax) :=
    continuousOn_id.prodMk (hΦ.orbit_continuousOn x hx)
  have hmaps : MapsTo (fun τ : ℝ => (τ, Φ (x, τ))) (Icc tmin tmax) Ω := by
    intro τ hτ
    exact hΩ_flow x hx τ hτ
  have hcomp := hpfD.continuousOn.comp horbit hmaps
  exact hcomp.congr (fun τ _hτ => rfl)



omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem continuousOn_timePiece_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)}
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T ρ : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hρ_le : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun q : E × ℝ => f q.2 (Φ q))
      (closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  let K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  have hK_sub : K ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    exact ⟨closedBall_subset_closedBall hρ_le hq.1, hsub hq.2⟩
  have hΦcont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  let iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  have hiM : ContinuousOn iM K := by
    exact continuousOn_snd.prodMk hΦcont
  have hmaps : MapsTo iM K Ω := by
    intro q hq
    exact hΩ_flow q.1 (closedBall_subset_closedBall hρ_le hq.1) q.2 (hsub hq.2)
  have hcomp := hf_one.continuousOn.comp hiM hmaps
  exact hcomp.congr (fun q _hq => rfl)



omit [CompleteSpace E] in
theorem exists_fderiv_bound_on_flow_tube_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T ρ : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hρ_le : ρ ≤ (r : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ closedBall x₀ ρ, ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
        ‖fderiv ℝ (f τ) (Φ (x, τ))‖ ≤ M := by
  let K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  let G : E × ℝ → E →L[ℝ] E := fun q => fderiv ℝ (f q.2) (Φ q)
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hK : IsCompact K := (isCompact_closedBall x₀ ρ).prod isCompact_Icc
  have hK_sub : K ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    exact ⟨closedBall_subset_closedBall hρ_le hq.1, hsub hq.2⟩
  have hΦcont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  let pfD : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (f p.1) p.2
  let iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  have hpfD : ContDiffOn ℝ 0 pfD Ω := by
    simpa [pfD] using
      (contDiffOn_partial_fderiv_of_succ_local
        (f := f) (k := (0 : ℕ∞)) hΩ (by simpa using hf_one))
  have hiM : ContinuousOn iM K := by
    exact continuousOn_snd.prodMk hΦcont
  have hmaps : MapsTo iM K Ω := by
    intro q hq
    exact hΩ_flow q.1 (closedBall_subset_closedBall hρ_le hq.1) q.2 (hsub hq.2)
  have hG : ContinuousOn G K := by
    have hcomp := hpfD.continuousOn.comp hiM hmaps
    exact hcomp.congr (fun q hq => rfl)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx τ hτ
  have hq : (x, τ) ∈ K := ⟨hx, hτ⟩
  exact (hC (x, τ) hq).trans (le_max_left _ _)

end LocalFlowTubeBounds



section HartmanTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}


omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem contDiffOn_timePieceFn_local
    {k : ℕ∞} {U : Set (E × ℝ)} {Ω : Set (ℝ × E)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) Ω)
    (hΦ_Ck : ContDiffOn ℝ k Φ U)
    (hΩ_map : ∀ q ∈ U, (q.2, Φ q) ∈ Ω) :
    ContDiffOn ℝ k (timePieceFn f Φ) U := by
  set g : E × ℝ → ℝ × E := fun q => (q.2, Φ q) with hg_def
  have hg : ContDiffOn ℝ k g U :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ k Prod.snd U).prodMk hΦ_Ck
  have horbit : ContDiffOn ℝ k (fun q : E × ℝ => f q.2 (Φ q)) U := by
    have hcomp : ContDiffOn ℝ k (uncurry f ∘ g) U := hf_Ck.comp hg hΩ_map
    exact hcomp.congr (fun _ _ => rfl)
  set S : E →L[ℝ] (ℝ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) with hS_def
  have heq : timePieceFn f Φ = S ∘ (fun q : E × ℝ => f q.2 (Φ q)) := by
    funext q
    simp [timePieceFn, S, ContinuousLinearMap.smulRightL]
  rw [heq]
  exact horbit.continuousLinearMap_comp S


omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem contDiffOn_flow_succ_of_spatial_smooth_local
    {U : Set (E × ℝ)} (hU_open : IsOpen U)
    {Ω : Set (ℝ × E)}
    {k : ℕ∞}
    (hf_Csucc : ContDiffOn ℝ (k + 1) (uncurry f) Ω)
    (hΩ_map : ∀ q ∈ U, (q.2, Φ q) ∈ Ω)
    (hΦ_diff : DifferentiableOn ℝ Φ U)
    (hΦ_Ck : ContDiffOn ℝ k Φ U)
    {Lsp : E × ℝ → (E →L[ℝ] E)}
    (hLsp_Ck : ContDiffOn ℝ k Lsp U)
    (hLsp_eq : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ U := by
  have hf_Ck : ContDiffOn ℝ k (uncurry f) Ω := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_Csucc.of_le h_le
  have hLti_Ck : ContDiffOn ℝ k (timePieceFn f Φ) U :=
    contDiffOn_timePieceFn_local hf_Ck hΦ_Ck hΩ_map
  exact contDiffOn_succ_of_fderiv_coprod_smooth hU_open hΦ_diff hLsp_Ck hLti_Ck hLsp_eq














omit [FiniteDimensional ℝ E] in
omit [CompleteSpace E] in
private theorem exists_uniform_partial_fderiv_local
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω)
    {a b : ℝ} (α : ℝ → E) (hα : ContinuousOn α (Icc a b))
    (hgraph : ∀ τ ∈ Icc a b, (τ, α τ) ∈ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc a b, ∀ z : E, ‖z - α τ‖ < δ →
      ‖fderiv ℝ (f τ) z - fderiv ℝ (f τ) (α τ)‖ < ε := by
  set K_graph : Set (ℝ × E) := (fun τ : ℝ => (τ, α τ)) '' Icc a b with hK_graph_def
  have hK_graph_cpt : IsCompact K_graph :=
    isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hα)
  set F : ℝ × E → (E →L[ℝ] E) := fun p => fderiv ℝ (f p.1) p.2 with hF_def
  have hF_contOn : ContinuousOn F Ω := by
    have h := contDiffOn_partial_fderiv_of_succ_local (f := f) (k := (0 : ℕ∞)) hΩ
      (by simpa using hf_C1)
    simpa [F] using h.continuousOn
  have hF_contAt : ∀ p ∈ K_graph, ContinuousAt F p := by
    rintro p ⟨τ, hτ, rfl⟩
    exact hF_contOn.continuousAt (hΩ.mem_nhds (hgraph τ hτ))
  have hr_unif : { x : (E →L[ℝ] E) × (E →L[ℝ] E) | dist x.1 x.2 < ε } ∈ 𝓤 (E →L[ℝ] E) :=
    Metric.dist_mem_uniformity hε
  have h := hK_graph_cpt.uniformContinuousAt_of_continuousAt F hF_contAt hr_unif
  rcases Metric.mem_uniformity_dist.mp h with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro τ hτ z hz
  set p₁ : ℝ × E := (τ, α τ)
  set p₂ : ℝ × E := (τ, z)
  have hp₁_K : p₁ ∈ K_graph := ⟨τ, hτ, rfl⟩
  have h_dist : dist p₁ p₂ < δ := by
    rw [Prod.dist_eq]
    have h1 : dist τ τ = 0 := dist_self _
    rw [h1]
    have h2 : max 0 (dist (α τ) z) = dist (α τ) z := max_eq_right dist_nonneg
    rw [h2, dist_comm, dist_eq_norm]
    exact hz
  have hdistF := hδ h_dist hp₁_K
  change dist (F p₁) (F p₂) < ε at hdistF
  rw [dist_eq_norm] at hdistF
  change ‖fderiv ℝ (f τ) z - fderiv ℝ (f τ) (α τ)‖ < ε
  have h_neg :
      fderiv ℝ (f τ) z - fderiv ℝ (f τ) (α τ)
        = -(fderiv ℝ (f τ) (α τ) - fderiv ℝ (f τ) z) := by abel
  rw [h_neg, norm_neg]
  exact hdistF





omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem exists_orbit_tube_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T : ℝ} (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {x : E} (hx : x ∈ closedBall x₀ (r : ℝ)) :
    ∃ rtube : ℝ, 0 < rtube ∧ ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ∀ z : E,
      ‖z - Φ (x, τ)‖ ≤ rtube → (τ, z) ∈ Ω := by
  set G : Set (ℝ × E) := (fun τ : ℝ => (τ, Φ (x, τ))) '' Icc (t₀ - T) (t₀ + T) with hG_def
  have hG_cpt : IsCompact G :=
    isCompact_Icc.image_of_continuousOn
      (continuousOn_id.prodMk ((hΦ.orbit_continuousOn x hx).mono hsub))
  have hG_sub : G ⊆ Ω := by
    rintro p ⟨τ, hτ, rfl⟩
    exact hΩ_flow x hx τ (hsub hτ)
  obtain ⟨rtube, hrtube_pos, hrtube_sub⟩ := hG_cpt.exists_cthickening_subset_open hΩ hG_sub
  refine ⟨rtube, hrtube_pos, ?_⟩
  intro τ hτ z hz
  apply hrtube_sub
  refine mem_cthickening_of_dist_le (τ, z) (τ, Φ (x, τ)) rtube G ⟨τ, hτ, rfl⟩ ?_
  rw [Prod.dist_eq]
  have h1 : dist τ τ = 0 := dist_self _
  rw [h1]
  have h2 : max 0 (dist z (Φ (x, τ))) = dist z (Φ (x, τ)) := max_eq_right dist_nonneg
  rw [h2, dist_eq_norm]
  exact hz

set_option maxHeartbeats 1200000 in



omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_flow_at_initial_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hA_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩)‖ ≤ M)
    (hr : 0 < r)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    HasFDerivAt (fun x => Φ ⟨x, t⟩)
      (variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
        hT hM hMT
        ((hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow x₀
          (Metric.mem_closedBall_self (le_of_lt (by exact_mod_cast hr)))).mono hsub)
        hA_bd ht) x₀ := by

  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx₀_in_ball : x₀ ∈ closedBall x₀ r := Metric.mem_closedBall_self (le_of_lt hr')
  set hA_cont :=
    (hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow x₀ hx₀_in_ball).mono hsub
      with hA_cont_def
  set A : ℝ → E →L[ℝ] E := fun s => fderiv ℝ (f s) (Φ ⟨x₀, s⟩) with hA_def
  set vSol := variationalSolutionFun (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
    hT hM hMT hA_cont hA_bd with hvSol_def
  set Lmap := variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
    hT hM hMT hA_cont hA_bd ht with hLmap_def

  obtain ⟨L, hL_lip⟩ := hΦ.exists_lipschitz
  have hL_nn : (0 : ℝ) ≤ L := L.coe_nonneg
  have hΦ_lip_diff : ∀ s ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ r,
      ‖Φ ⟨x, s⟩ - Φ ⟨x₀, s⟩‖ ≤ L * ‖x - x₀‖ := by
    intro s hs x hx
    have := (hL_lip s hs).dist_le_mul x hx x₀ hx₀_in_ball
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this

  have horbit_cont' : ContinuousOn (fun s : ℝ => Φ ⟨x₀, s⟩) (Icc (t₀ - T) (t₀ + T)) :=
    (hΦ.orbit_continuousOn x₀ hx₀_in_ball).mono hsub

  have hgraph_Ω : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), (τ, Φ ⟨x₀, τ⟩) ∈ Ω :=
    fun τ hτ => hΩ_flow x₀ hx₀_in_ball τ (hsub hτ)
  obtain ⟨r_tube, hr_tube_pos, hr_tube⟩ :=
    exists_orbit_tube_local hΦ hΩ hΩ_flow hsub hx₀_in_ball

  obtain ⟨δ_K, hδ_K_pos, hδ_K⟩ :=
    exists_uniform_partial_fderiv_local hΩ hf_C1
      (α := fun s => Φ ⟨x₀, s⟩) horbit_cont' hgraph_Ω 1 one_pos

  set δ_K_strict : ℝ := min (δ_K / 2) (r_tube / 2) with hδ_K_strict_def
  have hδ_K_strict_pos : 0 < δ_K_strict :=
    lt_min (by positivity) (by positivity)
  have hδ_K_strict_lt : δ_K_strict < δ_K :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ_K_strict_le_tube : δ_K_strict ≤ r_tube :=
    le_trans (min_le_right _ _) (by linarith)
  have hK_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ∀ z : E, ‖z - Φ ⟨x₀, τ⟩‖ ≤ δ_K_strict →
      ‖fderiv ℝ (f τ) z‖ ≤ M + 1 := by
    intro τ hτ z hz
    have h_diff := hδ_K τ hτ z (lt_of_le_of_lt hz hδ_K_strict_lt)
    have hnorm_add := norm_add_le (fderiv ℝ (f τ) z - fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩))
      (fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩))
    simp at hnorm_add
    linarith [hA_bd τ hτ, h_diff]

  set K_lip : ℝ := M + 1 with hK_lip_def
  have hK_lip_pos : 0 < K_lip := by have : (0 : ℝ) ≤ M := hM; linarith
  have hK_lip_nn : 0 ≤ K_lip := le_of_lt hK_lip_pos
  have hf_diff_pt : ∀ τ : ℝ, ∀ z : E, (τ, z) ∈ Ω → DifferentiableAt ℝ (f τ) z := by
    intro τ z hmem
    have hDiff_joint : DifferentiableAt ℝ (uncurry f) (τ, z) :=
      (hf_C1.contDiffAt (hΩ.mem_nhds hmem)).differentiableAt one_ne_zero
    have hg : DifferentiableAt ℝ (fun y : E => (τ, y)) z :=
      (differentiableAt_const τ).prodMk differentiableAt_id
    have hcomp : DifferentiableAt ℝ ((uncurry f) ∘ (fun y : E => (τ, y))) z :=
      hDiff_joint.comp z hg
    exact hcomp

  have hf_lip_ball : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (f τ)
        (closedBall (Φ ⟨x₀, τ⟩) δ_K_strict) := by
    intro τ hτ
    have hdiff_on : ∀ z ∈ closedBall (Φ ⟨x₀, τ⟩) δ_K_strict,
        DifferentiableAt ℝ (f τ) z := by
      intro z hz
      have h_norm_le : ‖z - Φ ⟨x₀, τ⟩‖ ≤ δ_K_strict := by
        have := Metric.mem_closedBall.mp hz
        rw [dist_eq_norm] at this; exact this
      exact hf_diff_pt τ z (hr_tube τ hτ z (h_norm_le.trans hδ_K_strict_le_tube))
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff_on ?_ (convex_closedBall _ _)
    intro z hz
    have h_norm_le : ‖z - Φ ⟨x₀, τ⟩‖ ≤ δ_K_strict := by
      have := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this; exact this
    change (‖fderiv ℝ (f τ) z‖₊ : ℝ≥0) ≤ ⟨K_lip, hK_lip_nn⟩
    rw [← NNReal.coe_le_coe]
    exact hK_bd τ hτ z h_norm_le

  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc

  set CE := exp (M * T) with hCE_def
  have hCE_pos : 0 < CE := exp_pos _
  have hCE_nn : 0 ≤ CE := le_of_lt hCE_pos
  set GfactorR : ℝ := T * exp (K_lip * T) with hGfactorR_def
  have hGfactorR_pos : 0 < GfactorR := by
    have : 0 < exp (K_lip * T) := exp_pos _
    have hT_pos : 0 < T := hT
    positivity
  set Cmul : ℝ := GfactorR * CE + 1 with hCmul_def
  have hCmul_pos : 0 < Cmul := by
    have : 0 ≤ GfactorR * CE := mul_nonneg (le_of_lt hGfactorR_pos) hCE_nn
    linarith
  set ε_target : ℝ := c / Cmul with hε_target_def
  have hε_target_pos : 0 < ε_target := div_pos hc hCmul_pos
  have hε_target_le_one : ε_target * GfactorR * CE < c := by
    have h1 : ε_target * Cmul = c := by
      rw [hε_target_def]; field_simp
    have h2 : ε_target * GfactorR * CE = ε_target * (GfactorR * CE) := by ring
    have h3 : ε_target * (GfactorR * CE) < ε_target * Cmul := by
      apply mul_lt_mul_of_pos_left _ hε_target_pos
      rw [hCmul_def]; linarith
    linarith

  obtain ⟨δ_uc, hδ_uc_pos, hδ_uc⟩ :=
    exists_uniform_partial_fderiv_local hΩ hf_C1
      (α := fun s => Φ ⟨x₀, s⟩) horbit_cont' hgraph_Ω ε_target hε_target_pos

  set Lpos : ℝ := L + 1 with hLpos_def
  have hLpos_pos : 0 < Lpos := by linarith
  set CEpos : ℝ := CE + 1 with hCEpos_def
  have hCEpos_pos : 0 < CEpos := by linarith
  set δ_final : ℝ :=
    min (min (r : ℝ) (δ_K_strict / Lpos))
        (min (δ_K_strict / CEpos) (δ_uc / CEpos)) with hδ_final_def
  have hδ_final_pos : 0 < δ_final := by
    refine lt_min (lt_min hr' ?_) (lt_min ?_ ?_)
    · exact div_pos hδ_K_strict_pos hLpos_pos
    · exact div_pos hδ_K_strict_pos hCEpos_pos
    · exact div_pos hδ_uc_pos hCEpos_pos
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (0 : E) δ_final, Metric.ball_mem_nhds _ hδ_final_pos, fun h hh => ?_⟩
  rw [mem_ball_zero_iff] at hh

  have hh_nn : 0 ≤ ‖h‖ := norm_nonneg _
  have hh_lt_r : ‖h‖ < (r : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_left _ _)) (min_le_left _ _)
  have hh_le_r : ‖h‖ ≤ (r : ℝ) := le_of_lt hh_lt_r
  have hxh_mem_ball : x₀ + h ∈ closedBall x₀ r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh_le_r
  have mk_bd : ∀ {coef target scale : ℝ}, 0 ≤ coef → coef ≤ scale → 0 < scale →
      ‖h‖ < target / scale → coef * ‖h‖ < target := by
    intros coef target scale hcoef_nn hcoef_le hscale_pos hbd
    have h1 : coef * ‖h‖ ≤ scale * ‖h‖ := mul_le_mul_of_nonneg_right hcoef_le hh_nn
    have h2 : scale * ‖h‖ < scale * (target / scale) := mul_lt_mul_of_pos_left hbd hscale_pos
    have h3 : scale * (target / scale) = target := by
      field_simp
    linarith
  have h_L_le_Lpos : L ≤ Lpos := by rw [hLpos_def]; linarith
  have h_CE_le_CEpos : CE ≤ CEpos := by rw [hCEpos_def]; linarith
  have hh_L_bd : L * ‖h‖ < δ_K_strict :=
    mk_bd hL_nn h_L_le_Lpos hLpos_pos
      (lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_left _ _)) (min_le_right _ _))
  have hh_L_bd_le : L * ‖h‖ ≤ δ_K_strict := le_of_lt hh_L_bd
  have hh_CE_bd : CE * ‖h‖ < δ_K_strict :=
    mk_bd hCE_nn h_CE_le_CEpos hCEpos_pos
      (lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_right _ _)) (min_le_left _ _))
  have hh_CE_bd_le : CE * ‖h‖ ≤ δ_K_strict := le_of_lt hh_CE_bd
  have hh_CE_lt_δuc : CE * ‖h‖ < δ_uc :=
    mk_bd hCE_nn h_CE_le_CEpos hCEpos_pos
      (lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_right _ _)) (min_le_right _ _))

  set y_h : ℝ → E := vSol h with hy_h_def
  have hy_h_sol :
      IsVariationalSolutionOn f (fun s => Φ ⟨x₀, s⟩) h t₀ y_h (Icc (t₀ - T) (t₀ + T)) :=
    variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd h
  have hy_h_init : y_h t₀ = h := hy_h_sol.1
  have hy_h_bd : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖y_h s‖ ≤ CE * ‖h‖ := by
    intro s hs
    exact variationalSolutionFun_norm_le hT hM hMT hA_cont hA_bd h hs
  have hy_h_cont : ContinuousOn y_h (Icc (t₀ - T) (t₀ + T)) := hy_h_sol.continuousOn
  set α_h : ℝ → E := fun s => Φ ⟨x₀ + h, s⟩ with hα_h_def
  set β_h : ℝ → E := fun s => Φ ⟨x₀, s⟩ + y_h s with hβ_h_def
  have hα_h_init : α_h t₀ = x₀ + h := hΦ.apply_initial (x₀ + h) hxh_mem_ball
  have hβ_h_init : β_h t₀ = x₀ + h := by
    change Φ ⟨x₀, t₀⟩ + y_h t₀ = x₀ + h
    rw [hΦ.apply_initial x₀ hx₀_in_ball, hy_h_init]
  have hα_h_deriv_full : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt α_h (f s (α_h s)) (Icc tmin tmax) s :=
    fun s hs => hΦ.hasDerivWithinAt (x₀ + h) hxh_mem_ball s hs
  have hα_h_cont : ContinuousOn α_h (Icc tmin tmax) :=
    hΦ.orbit_continuousOn (x₀ + h) hxh_mem_ball
  have hα_h_cont' : ContinuousOn α_h (Icc (t₀ - T) (t₀ + T)) := hα_h_cont.mono hsub
  have hΦc_deriv_full : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun s => Φ ⟨x₀, s⟩) (f s (Φ ⟨x₀, s⟩)) (Icc tmin tmax) s :=
    fun s hs => hΦ.hasDerivWithinAt x₀ hx₀_in_ball s hs

  have hα_h_close : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      ‖α_h s - Φ ⟨x₀, s⟩‖ ≤ L * ‖h‖ := by
    intro s hs
    have hs' : s ∈ Icc tmin tmax := hsub hs
    have h1 : ‖α_h s - Φ ⟨x₀, s⟩‖ ≤ L * ‖(x₀ + h) - x₀‖ :=
      hΦ_lip_diff s hs' (x₀ + h) hxh_mem_ball
    have h2 : (x₀ + h) - x₀ = h := by abel
    rw [h2] at h1; exact h1

  have hα_h_mem_ball : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      α_h s ∈ closedBall (Φ ⟨x₀, s⟩) δ_K_strict := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans (hα_h_close s hs) hh_L_bd_le
  have hβ_h_mem_ball : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      β_h s ∈ closedBall (Φ ⟨x₀, s⟩) δ_K_strict := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    change ‖Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩‖ ≤ δ_K_strict
    have heq : Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩ = y_h s := by abel
    rw [heq]; exact le_trans (hy_h_bd s hs) hh_CE_bd_le

  have hβ_h_deriv : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt β_h (f s (Φ ⟨x₀, s⟩) + A s (y_h s))
        (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have hs' : s ∈ Icc tmin tmax := hsub hs
    have h1 := (hΦc_deriv_full s hs').mono hsub
    have h2 := hy_h_sol.2 s hs
    exact h1.add h2
  have hβ_h_cont : ContinuousOn β_h (Icc (t₀ - T) (t₀ + T)) := by
    apply ContinuousOn.add (horbit_cont') hy_h_cont

  have h_residual_bound : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      ‖f s (Φ ⟨x₀, s⟩) + A s (y_h s) - f s (β_h s)‖ ≤ ε_target * ‖y_h s‖ := by
    intro s hs
    set ρ_seg : ℝ := CE * ‖h‖ with hρ_seg_def
    have hρ_seg_nn : 0 ≤ ρ_seg := mul_nonneg hCE_nn hh_nn
    set S_seg : Set E := closedBall (Φ ⟨x₀, s⟩) ρ_seg with hS_seg_def
    have hS_seg_conv : Convex ℝ S_seg := convex_closedBall _ _
    have hf_diff : ∀ z ∈ S_seg, DifferentiableAt ℝ (f s) z := by
      intro z hz
      have h_norm_le : ‖z - Φ ⟨x₀, s⟩‖ ≤ ρ_seg := by
        have := Metric.mem_closedBall.mp hz
        rw [dist_eq_norm] at this; exact this
      exact hf_diff_pt s z
        (hr_tube s hs z (h_norm_le.trans ((le_of_lt hh_CE_bd).trans hδ_K_strict_le_tube)))
    have hx_seg : Φ ⟨x₀, s⟩ ∈ S_seg := Metric.mem_closedBall_self hρ_seg_nn
    have hxv_seg : Φ ⟨x₀, s⟩ + y_h s ∈ S_seg := by
      rw [hS_seg_def, mem_closedBall, dist_eq_norm]
      change ‖Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩‖ ≤ ρ_seg
      have heq : Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩ = y_h s := by abel
      rw [heq, hρ_seg_def]; exact hy_h_bd s hs
    have hC : ∀ z ∈ S_seg, ‖fderiv ℝ (f s) z - fderiv ℝ (f s) (Φ ⟨x₀, s⟩)‖ ≤ ε_target := by
      intro z hz
      have h_norm_le : ‖z - Φ ⟨x₀, s⟩‖ ≤ ρ_seg := by
        have := Metric.mem_closedBall.mp hz
        rw [dist_eq_norm] at this; exact this
      have h_norm_lt : ‖z - Φ ⟨x₀, s⟩‖ < δ_uc :=
        lt_of_le_of_lt h_norm_le hh_CE_lt_δuc
      exact le_of_lt (hδ_uc s hs z h_norm_lt)
    have h_residual : ‖f s (Φ ⟨x₀, s⟩ + y_h s) - f s (Φ ⟨x₀, s⟩)
        - (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s)‖ ≤ ε_target * ‖y_h s‖ :=
      norm_residual_le_of_diffOn s (Φ ⟨x₀, s⟩) (y_h s) hS_seg_conv hf_diff hx_seg hxv_seg hC
    have h_eq : f s (Φ ⟨x₀, s⟩) + A s (y_h s) - f s (β_h s)
        = -(f s (Φ ⟨x₀, s⟩ + y_h s) - f s (Φ ⟨x₀, s⟩) - (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s)) := by
      change f s (Φ ⟨x₀, s⟩) + (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s)
        - f s (Φ ⟨x₀, s⟩ + y_h s)
          = -(f s (Φ ⟨x₀, s⟩ + y_h s) - f s (Φ ⟨x₀, s⟩) - (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s))
      abel
    rw [h_eq, norm_neg]
    exact h_residual

  set s_set : ℝ → Set E := fun τ => closedBall (Φ ⟨x₀, τ⟩) δ_K_strict with hs_set_def
  have h_diff_right : ∀ τ ∈ Icc t₀ (t₀ + T),
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    have hsub_R : Icc t₀ (t₀ + T) ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc_left (by linarith)
    have hsub_R_full : Icc t₀ (t₀ + T) ⊆ Icc tmin tmax := hsub_R.trans hsub
    have hv_lip : ∀ τ ∈ Ico t₀ (t₀ + T),
        LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (f τ) (s_set τ) := fun τ hτ =>
      hf_lip_ball τ (hsub_R ⟨hτ.1, le_of_lt hτ.2⟩)
    have hα_h_cont_R : ContinuousOn α_h (Icc t₀ (t₀ + T)) := hα_h_cont.mono hsub_R_full
    have hβ_h_cont_R : ContinuousOn β_h (Icc t₀ (t₀ + T)) := hβ_h_cont.mono hsub_R
    have h_tmax_ge : t₀ + T ≤ tmax := by
      have : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax := hsub
      have h_in : (t₀ + T) ∈ Icc (t₀ - T) (t₀ + T) :=
        Set.right_mem_Icc.mpr (by linarith)
      exact (this h_in).2
    have hα_h_deriv_R : ∀ τ ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt α_h (f τ (α_h τ)) (Ici τ) τ := by
      intro τ hτR
      have hτ_full : τ ∈ Icc tmin tmax := hsub_R_full ⟨hτR.1, le_of_lt hτR.2⟩
      have hτ_Ico : τ ∈ Ico tmin tmax :=
        ⟨hτ_full.1, lt_of_lt_of_le hτR.2 h_tmax_ge⟩
      exact hasDerivWithinAt_Ici_of_Icc (hα_h_deriv_full τ hτ_full) hτ_Ico
    have hβ_h_deriv_R : ∀ τ ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt β_h (f τ (Φ ⟨x₀, τ⟩) + A τ (y_h τ)) (Ici τ) τ := by
      intro τ hτR
      have hτ_sub : τ ∈ Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτR.1, le_of_lt hτR.2⟩
      have hτ_Ico_sub : τ ∈ Ico (t₀ - T) (t₀ + T) := ⟨hτ_sub.1, hτR.2⟩
      exact hasDerivWithinAt_Ici_of_Icc (hβ_h_deriv τ hτ_sub) hτ_Ico_sub
    have hf_bound : ∀ τ ∈ Ico t₀ (t₀ + T), dist (f τ (α_h τ)) (f τ (α_h τ)) ≤ 0 := by
      intro _ _; rw [dist_self]
    have hfs : ∀ τ ∈ Ico t₀ (t₀ + T), α_h τ ∈ s_set τ := by
      intro τ hτR
      exact hα_h_mem_ball τ (hsub_R ⟨hτR.1, le_of_lt hτR.2⟩)
    set εg : ℝ := ε_target * CE * ‖h‖ with hεg_def
    have hεg_nn : 0 ≤ εg := by
      have : 0 ≤ ε_target * CE := mul_nonneg (le_of_lt hε_target_pos) hCE_nn
      exact mul_nonneg this hh_nn
    have hg_bound : ∀ τ ∈ Ico t₀ (t₀ + T),
        dist (f τ (Φ ⟨x₀, τ⟩) + A τ (y_h τ)) (f τ (β_h τ)) ≤ εg := by
      intro τ hτR
      have hτ_sub : τ ∈ Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτR.1, le_of_lt hτR.2⟩
      have h_res := h_residual_bound τ hτ_sub
      have h_ybd := hy_h_bd τ hτ_sub
      have h_combine : ε_target * ‖y_h τ‖ ≤ εg := by
        rw [hεg_def, mul_assoc]
        exact mul_le_mul_of_nonneg_left h_ybd (le_of_lt hε_target_pos)
      rw [dist_eq_norm]
      exact le_trans h_res h_combine
    have hgs : ∀ τ ∈ Ico t₀ (t₀ + T), β_h τ ∈ s_set τ := by
      intro τ hτR
      exact hβ_h_mem_ball τ (hsub_R ⟨hτR.1, le_of_lt hτR.2⟩)
    have ha_init : dist (α_h t₀) (β_h t₀) ≤ 0 := by
      rw [hα_h_init, hβ_h_init, dist_self]
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (v := f) (s := s_set) (K := ⟨K_lip, hK_lip_nn⟩)
      (f := α_h) (g := β_h) (f' := fun τ => f τ (α_h τ))
      (g' := fun τ => f τ (Φ ⟨x₀, τ⟩) + A τ (y_h τ))
      (εf := 0) (εg := εg) (δ := 0)
      hv_lip hα_h_cont_R hα_h_deriv_R hf_bound hfs
      hβ_h_cont_R hβ_h_deriv_R hg_bound hgs ha_init τ hτ
    rw [dist_eq_norm] at hG
    have h_zero_add : (0 : ℝ) + εg = εg := zero_add _
    rw [h_zero_add] at hG
    have hτ_sub_t₀_nn : 0 ≤ τ - t₀ := by linarith [hτ.1]
    have hτ_sub_t₀_le : τ - t₀ ≤ T := by linarith [hτ.2]
    have h_GB :=
      gronwallBound_zero_le (K := K_lip) (ε := εg) (x := τ - t₀)
        hK_lip_pos hεg_nn hτ_sub_t₀_nn
    have h_mono : εg * (τ - t₀) * exp (K_lip * (τ - t₀)) ≤ εg * T * exp (K_lip * T) := by
      have h1 : εg * (τ - t₀) ≤ εg * T := mul_le_mul_of_nonneg_left hτ_sub_t₀_le hεg_nn
      have h2 : exp (K_lip * (τ - t₀)) ≤ exp (K_lip * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ_sub_t₀_le hK_lip_nn)
      exact mul_le_mul h1 h2 (le_of_lt (exp_pos _)) (mul_nonneg hεg_nn (le_of_lt hT))
    have h_GB' : gronwallBound 0 K_lip εg (τ - t₀) ≤ εg * T * exp (K_lip * T) :=
      le_trans h_GB h_mono
    have h_eq_factor : εg * T * exp (K_lip * T) = GfactorR * εg := by
      rw [hGfactorR_def]; ring
    rw [h_eq_factor] at h_GB'
    exact le_trans hG h_GB'

  have h_diff_left : ∀ τ ∈ Icc (t₀ - T) t₀,
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    let ψ : ℝ → ℝ := fun s => 2 * t₀ - s
    set αR : ℝ → E := α_h ∘ ψ with hαR_def
    set βR : ℝ → E := β_h ∘ ψ with hβR_def
    set vR : ℝ → E → E := fun τ x => -f (2 * t₀ - τ) x with hvR_def
    set sR : ℝ → Set E := fun τ => closedBall (Φ ⟨x₀, 2 * t₀ - τ⟩) δ_K_strict with hsR_def
    have hsub_full : Icc t₀ (t₀ + T) ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc_left (by linarith)
    have hψ_reflect_in_sub : ∀ s ∈ Icc t₀ (t₀ + T), 2 * t₀ - s ∈ Icc (t₀ - T) (t₀ + T) := by
      intro s hs
      refine ⟨by linarith [hs.2], by linarith [hs.1, hT.le]⟩
    have hψ_deriv : ∀ s, HasDerivAt ψ (-1 : ℝ) s := fun s => by
      have h1 : HasDerivAt (fun s => 2 * t₀ - s) (-1 : ℝ) s := by
        simpa using (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s)
      exact h1
    have h_neg_lip_one : LipschitzWith 1 (Neg.neg : E → E) := LipschitzWith.id.neg
    have hvR_lip : ∀ τ' ∈ Ico t₀ (t₀ + T),
        LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (vR τ') (sR τ') := by
      intro τ' hτ'R
      have hτ'_sub : 2 * t₀ - τ' ∈ Icc (t₀ - T) (t₀ + T) :=
        hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩
      have h_lip := hf_lip_ball (2 * t₀ - τ') hτ'_sub
      have h_eq : vR τ' = (Neg.neg : E → E) ∘ f (2 * t₀ - τ') := rfl
      rw [h_eq]
      have h_coe : (⟨K_lip, hK_lip_nn⟩ : ℝ≥0) = 1 * ⟨K_lip, hK_lip_nn⟩ := by
        rw [one_mul]
      rw [h_coe]
      exact h_neg_lip_one.comp_lipschitzOnWith h_lip
    have hψ_cont : Continuous ψ := by
      have h_id : Continuous (id : ℝ → ℝ) := continuous_id
      have h_const : Continuous (fun _ : ℝ => 2 * t₀) := continuous_const
      have : Continuous (fun s : ℝ => 2 * t₀ - s) := h_const.sub h_id
      exact this
    have hψ_cont_R : ContinuousOn ψ (Icc t₀ (t₀ + T)) := hψ_cont.continuousOn
    have hψ_maps_full : MapsTo ψ (Icc t₀ (t₀ + T)) (Icc tmin tmax) := by
      intro s hs
      exact hsub (hψ_reflect_in_sub s hs)
    have hαR_cont_R : ContinuousOn αR (Icc t₀ (t₀ + T)) := hα_h_cont.comp hψ_cont_R hψ_maps_full
    have hψ_maps_sub : MapsTo ψ (Icc t₀ (t₀ + T)) (Icc (t₀ - T) (t₀ + T)) :=
      hψ_reflect_in_sub
    have hβR_cont_R : ContinuousOn βR (Icc t₀ (t₀ + T)) := hβ_h_cont.comp hψ_cont_R hψ_maps_sub
    have hαR_deriv_R : ∀ τ' ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt αR (vR τ' (αR τ')) (Ici τ') τ' := by
      intro τ' hτ'R
      have hτ'_full : 2 * t₀ - τ' ∈ Icc tmin tmax :=
        hsub (hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩)
      have hτ'_Ioc_full : 2 * t₀ - τ' ∈ Ioc tmin tmax := by
        refine ⟨?_, hτ'_full.2⟩
        have hτ'_gt : 2 * t₀ - τ' > t₀ - T := by linarith [hτ'R.2]
        have htmin_le : tmin ≤ t₀ - T :=
          (hsub (Set.left_mem_Icc.mpr (by linarith : t₀ - T ≤ t₀ + T))).1
        linarith
      have h_d := hΦ.hasDerivWithinAt (x₀ + h) hxh_mem_ball (2 * t₀ - τ') hτ'_full
      have h_d_left :
          HasDerivWithinAt α_h (f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))) (Iic (2 * t₀ - τ'))
            (2 * t₀ - τ') :=
        hasDerivWithinAt_Iic_of_Icc h_d hτ'_Ioc_full
      have hψ_dwa : HasDerivWithinAt ψ (-1 : ℝ) (Ici τ') τ' :=
        (hψ_deriv τ').hasDerivWithinAt
      have hψ_maps' : MapsTo ψ (Ici τ') (Iic (2 * t₀ - τ')) := by
        intro s hs
        have hs_ge : τ' ≤ s := hs
        change 2 * t₀ - s ≤ 2 * t₀ - τ'
        linarith
      have h_comp := HasDerivWithinAt.scomp (g₁ := α_h) (h := ψ)
        τ' h_d_left hψ_dwa hψ_maps'
      have h_simplify : (-1 : ℝ) • f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))
          = vR τ' (αR τ') := by
        change (-1 : ℝ) • f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))
          = -f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))
        rw [neg_one_smul]
      rw [h_simplify] at h_comp
      exact h_comp
    have hβR_deriv_R : ∀ τ' ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt βR (-(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))))
          (Ici τ') τ' := by
      intro τ' hτ'R
      have hτ'_sub : 2 * t₀ - τ' ∈ Icc (t₀ - T) (t₀ + T) :=
        hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩
      have hτ'_Ioc_sub : 2 * t₀ - τ' ∈ Ioc (t₀ - T) (t₀ + T) := by
        refine ⟨?_, hτ'_sub.2⟩
        linarith [hτ'R.2]
      have h_d := hβ_h_deriv (2 * t₀ - τ') hτ'_sub
      have h_d_left :
          HasDerivWithinAt β_h (f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ')))
            (Iic (2 * t₀ - τ')) (2 * t₀ - τ') :=
        hasDerivWithinAt_Iic_of_Icc h_d hτ'_Ioc_sub
      have hψ_dwa : HasDerivWithinAt ψ (-1 : ℝ) (Ici τ') τ' :=
        (hψ_deriv τ').hasDerivWithinAt
      have hψ_maps' : MapsTo ψ (Ici τ') (Iic (2 * t₀ - τ')) := by
        intro s hs
        have hs_ge : τ' ≤ s := hs
        change 2 * t₀ - s ≤ 2 * t₀ - τ'
        linarith
      have h_comp := HasDerivWithinAt.scomp (g₁ := β_h) (h := ψ)
        τ' h_d_left hψ_dwa hψ_maps'
      have h_simplify :
          (-1 : ℝ) • (f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩)
              + A (2 * t₀ - τ') (y_h (2 * t₀ - τ')))
            = -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩)
              + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))) := by
        rw [neg_one_smul]
      rw [h_simplify] at h_comp
      exact h_comp
    have hf_bound : ∀ τ' ∈ Ico t₀ (t₀ + T), dist (vR τ' (αR τ')) (vR τ' (αR τ')) ≤ 0 := by
      intro _ _; rw [dist_self]
    have hfs : ∀ τ' ∈ Ico t₀ (t₀ + T), αR τ' ∈ sR τ' := by
      intro τ' hτ'R
      change α_h (2 * t₀ - τ') ∈ closedBall (Φ ⟨x₀, 2 * t₀ - τ'⟩) δ_K_strict
      exact hα_h_mem_ball (2 * t₀ - τ') (hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩)
    set εg : ℝ := ε_target * CE * ‖h‖ with hεg_def
    have hεg_nn : 0 ≤ εg := by
      have : 0 ≤ ε_target * CE := mul_nonneg (le_of_lt hε_target_pos) hCE_nn
      exact mul_nonneg this hh_nn
    have hg_bound : ∀ τ' ∈ Ico t₀ (t₀ + T),
        dist (-(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))))
            (vR τ' (βR τ')) ≤ εg := by
      intro τ' hτ'R
      have hτ'_sub : 2 * t₀ - τ' ∈ Icc (t₀ - T) (t₀ + T) :=
        hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩
      have h_res := h_residual_bound (2 * t₀ - τ') hτ'_sub
      have h_ybd := hy_h_bd (2 * t₀ - τ') hτ'_sub
      have h_combine : ε_target * ‖y_h (2 * t₀ - τ')‖ ≤ εg := by
        rw [hεg_def, mul_assoc]
        exact mul_le_mul_of_nonneg_left h_ybd (le_of_lt hε_target_pos)
      change dist _ (-f (2 * t₀ - τ') (β_h (2 * t₀ - τ'))) ≤ εg
      rw [dist_eq_norm]
      have h_diff_eq :
          -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ')))
            - (-f (2 * t₀ - τ') (β_h (2 * t₀ - τ')))
            = -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))
                - f (2 * t₀ - τ') (β_h (2 * t₀ - τ'))) := by abel
      rw [h_diff_eq, norm_neg]
      exact le_trans h_res h_combine
    have hgs : ∀ τ' ∈ Ico t₀ (t₀ + T), βR τ' ∈ sR τ' := by
      intro τ' hτ'R
      change β_h (2 * t₀ - τ') ∈ closedBall (Φ ⟨x₀, 2 * t₀ - τ'⟩) δ_K_strict
      exact hβ_h_mem_ball (2 * t₀ - τ') (hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩)
    have ha_init : dist (αR t₀) (βR t₀) ≤ 0 := by
      change dist (α_h (2 * t₀ - t₀)) (β_h (2 * t₀ - t₀)) ≤ 0
      have h_simp : 2 * t₀ - t₀ = t₀ := by ring
      rw [h_simp, hα_h_init, hβ_h_init, dist_self]
    set s_eval : ℝ := 2 * t₀ - τ with hs_eval_def
    have hs_eval_mem : s_eval ∈ Icc t₀ (t₀ + T) := by
      refine ⟨?_, ?_⟩
      · rw [hs_eval_def]; linarith [hτ.2]
      · rw [hs_eval_def]; linarith [hτ.1]
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (v := vR) (s := sR) (K := ⟨K_lip, hK_lip_nn⟩)
      (f := αR) (g := βR) (f' := fun τ' => vR τ' (αR τ'))
      (g' := fun τ' => -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩)
        + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))))
      (εf := 0) (εg := εg) (δ := 0)
      hvR_lip hαR_cont_R hαR_deriv_R hf_bound hfs
      hβR_cont_R hβR_deriv_R hg_bound hgs ha_init s_eval hs_eval_mem
    rw [dist_eq_norm] at hG
    have h_zero_add : (0 : ℝ) + εg = εg := zero_add _
    rw [h_zero_add] at hG
    have hαR_eval : αR s_eval = α_h τ := by
      change α_h (2 * t₀ - s_eval) = α_h τ
      have : 2 * t₀ - s_eval = τ := by rw [hs_eval_def]; ring
      rw [this]
    have hβR_eval : βR s_eval = β_h τ := by
      change β_h (2 * t₀ - s_eval) = β_h τ
      have : 2 * t₀ - s_eval = τ := by rw [hs_eval_def]; ring
      rw [this]
    rw [hαR_eval, hβR_eval] at hG
    have hs_diff_nn : 0 ≤ s_eval - t₀ := by rw [hs_eval_def]; linarith [hτ.2]
    have hs_diff_le : s_eval - t₀ ≤ T := by rw [hs_eval_def]; linarith [hτ.1]
    have h_GB :=
      gronwallBound_zero_le (K := K_lip) (ε := εg) (x := s_eval - t₀)
        hK_lip_pos hεg_nn hs_diff_nn
    have h_mono : εg * (s_eval - t₀) * exp (K_lip * (s_eval - t₀)) ≤ εg * T * exp (K_lip * T) := by
      have h1 : εg * (s_eval - t₀) ≤ εg * T := mul_le_mul_of_nonneg_left hs_diff_le hεg_nn
      have h2 : exp (K_lip * (s_eval - t₀)) ≤ exp (K_lip * T) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hs_diff_le hK_lip_nn
      exact mul_le_mul h1 h2 (le_of_lt (exp_pos _)) (mul_nonneg hεg_nn (le_of_lt hT))
    have h_GB' : gronwallBound 0 K_lip εg (s_eval - t₀) ≤ εg * T * exp (K_lip * T) :=
      le_trans h_GB h_mono
    have h_eq_factor : εg * T * exp (K_lip * T) = GfactorR * εg := by
      rw [hGfactorR_def]; ring
    rw [h_eq_factor] at h_GB'
    exact le_trans hG h_GB'

  have h_diff_full : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    rcases le_or_gt τ t₀ with hle | hgt
    · exact h_diff_left τ ⟨hτ.1, hle⟩
    · exact h_diff_right τ ⟨le_of_lt hgt, hτ.2⟩
  have h_final_bd : ‖α_h t - β_h t‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := h_diff_full t ht
  have h_lhs : α_h t - β_h t = Φ ⟨x₀ + h, t⟩ - Φ ⟨x₀, t⟩ - Lmap h := by
    change Φ ⟨x₀ + h, t⟩ - (Φ ⟨x₀, t⟩ + y_h t) = _
    have : Lmap h = vSol h t := rfl
    rw [this]; abel
  rw [h_lhs] at h_final_bd
  have h_bound_le : GfactorR * (ε_target * CE * ‖h‖) ≤ c * ‖h‖ := by
    have h1 : GfactorR * (ε_target * CE * ‖h‖) = (ε_target * GfactorR * CE) * ‖h‖ := by ring
    rw [h1]
    apply mul_le_mul_of_nonneg_right (le_of_lt hε_target_le_one) hh_nn
  exact le_trans h_final_bd h_bound_le

set_option maxHeartbeats 1600000 in



omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_flow_jointly_center_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hA_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩)‖ ≤ M)
    (hr : 0 < r)
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasFDerivAt Φ
      (((variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
            hT hM hMT
            ((hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow x₀
              (Metric.mem_closedBall_self (le_of_lt (by exact_mod_cast hr)))).mono hsub)
            hA_bd (Ioo_subset_Icc_self ht))).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x₀, t⟩))))
      (x₀, t) := by

  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx₀_in_ball : x₀ ∈ closedBall x₀ r := Metric.mem_closedBall_self (le_of_lt hr')
  set hA_cont :=
    (hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow x₀ hx₀_in_ball).mono hsub
      with hA_cont_def
  have ht_Icc : t ∈ Icc (t₀ - T) (t₀ + T) := Ioo_subset_Icc_self ht
  set Lmap := variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
    hT hM hMT hA_cont hA_bd ht_Icc with hLmap_def
  have h_space :=
    hasFDerivAt_flow_at_initial_local hΦ hΩ hf_C1 hΩ_flow hT hM hMT hsub hA_bd hr ht_Icc

  set Ltime : ℝ →L[ℝ] E :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x₀, t⟩)) with hLtime_def
  set Ljoint : (E × ℝ) →L[ℝ] E := Lmap.coprod Ltime with hLjoint_def

  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set c2 : ℝ := c / 2 with hc2_def
  have hc2_pos : 0 < c2 := by positivity

  have hf_cont_pt : ContinuousAt (uncurry f) (t, Φ ⟨x₀, t⟩) :=
    hf_C1.continuousOn.continuousAt (hΩ.mem_nhds (hΩ_flow x₀ hx₀_in_ball t (hsub ht_Icc)))
  rcases Metric.continuousAt_iff.mp hf_cont_pt c2 hc2_pos with ⟨η_f, hη_f_pos, hη_f⟩

  have hΦ_cont_pt : ContinuousWithinAt Φ
      (closedBall x₀ r ×ˢ Icc tmin tmax) (x₀, t) := by
    apply hΦ.continuousOn
    exact ⟨hx₀_in_ball, hsub ht_Icc⟩
  rw [Metric.continuousWithinAt_iff] at hΦ_cont_pt
  set η_half : ℝ := η_f / 2 with hη_half_def
  have hη_half_pos : 0 < η_half := by positivity
  have hη_half_lt : η_half < η_f := by linarith
  rcases hΦ_cont_pt η_half hη_half_pos with ⟨ρ₀, hρ₀_pos, hΦ_close⟩

  set ρ_t_raw : ℝ := min ((t - (t₀ - T)) / 2) (((t₀ + T) - t) / 2) with hρ_t_raw_def
  have hρ_t_raw_pos : 0 < ρ_t_raw := by
    refine lt_min ?_ ?_
    · have h : 0 < t - (t₀ - T) := by linarith [ht.1]
      linarith
    · have h : 0 < (t₀ + T) - t := by linarith [ht.2]
      linarith
  have h_t_minus_ρ_t_raw : t₀ - T ≤ t - ρ_t_raw := by
    have h1 : ρ_t_raw ≤ (t - (t₀ - T)) / 2 := min_le_left _ _
    linarith
  have h_t_plus_ρ_t_raw : t + ρ_t_raw ≤ t₀ + T := by
    have h1 : ρ_t_raw ≤ ((t₀ + T) - t) / 2 := min_le_right _ _
    linarith


  have h_space_io := (hasFDerivAt_iff_isLittleO_nhds_zero.mp h_space)
  rw [Asymptotics.isLittleO_iff] at h_space_io
  have h_space_c2 := h_space_io hc2_pos
  rcases Filter.eventually_iff_exists_mem.mp h_space_c2 with ⟨U_space, hU_space_mem, hU_space⟩
  rcases Metric.mem_nhds_iff.mp hU_space_mem with ⟨ρ_s, hρ_s_pos, hρ_s_sub⟩

  set ρ : ℝ := min (min ((r : ℝ)) ρ_s) (min (min ρ_t_raw ρ₀) η_half) with hρ_def
  have hρ_pos : 0 < ρ := by
    refine lt_min (lt_min hr' hρ_s_pos) (lt_min (lt_min hρ_t_raw_pos hρ₀_pos) hη_half_pos)
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (0 : E × ℝ) ρ, Metric.ball_mem_nhds _ hρ_pos, fun p hp => ?_⟩
  rw [mem_ball_zero_iff] at hp
  rcases p with ⟨δ, s⟩
  have hp_norm : ‖(δ, s)‖ < ρ := hp
  rw [Prod.norm_def] at hp_norm
  have hδ_norm : ‖δ‖ < ρ := lt_of_le_of_lt (le_max_left _ _) hp_norm
  have hs_norm_real : ‖s‖ < ρ := lt_of_le_of_lt (le_max_right _ _) hp_norm
  have hs_abs : |s| < ρ := hs_norm_real

  have hδ_lt_r' : ‖δ‖ < (r : ℝ) :=
    lt_of_lt_of_le hδ_norm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_lt_ρ_s : ‖δ‖ < ρ_s :=
    lt_of_lt_of_le hδ_norm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hs_lt_ρ_t_raw : |s| < ρ_t_raw :=
    lt_of_lt_of_le hs_abs (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hδ_lt_ρ₀ : ‖δ‖ < ρ₀ :=
    lt_of_lt_of_le hδ_norm (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hs_lt_ρ₀ : |s| < ρ₀ :=
    lt_of_lt_of_le hs_abs (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hs_lt_η_half : |s| < η_half :=
    lt_of_lt_of_le hs_abs (le_trans (min_le_right _ _) (min_le_right _ _))

  have hx_in_ball : x₀ + δ ∈ closedBall x₀ r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact le_of_lt hδ_lt_r'

  have h_ab_sub_T : Icc (t - ρ_t_raw) (t + ρ_t_raw) ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro u hu
    exact ⟨h_t_minus_ρ_t_raw.trans hu.1, hu.2.trans h_t_plus_ρ_t_raw⟩
  have h_ab_sub_tmin : Icc (t - ρ_t_raw) (t + ρ_t_raw) ⊆ Icc tmin tmax := h_ab_sub_T.trans hsub
  have hts_in_ab : t + s ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw) := by
    refine ⟨?_, ?_⟩
    · have hs_ge : -(|s|) ≤ s := neg_abs_le _
      linarith [hs_lt_ρ_t_raw]
    · have hs_le : s ≤ |s| := le_abs_self _
      linarith [hs_lt_ρ_t_raw]
  have ht_in_ab : t ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw) := by
    refine ⟨?_, ?_⟩ <;> linarith [hρ_t_raw_pos]

  set α : ℝ → E := fun u => Φ ⟨x₀ + δ, u⟩ with hα_def
  have hα_deriv : ∀ u ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw),
      HasDerivWithinAt α (f u (α u)) (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
    intro u hu
    have hu_tmin : u ∈ Icc tmin tmax := h_ab_sub_tmin hu
    exact (hΦ.hasDerivWithinAt (x₀ + δ) hx_in_ball u hu_tmin).mono h_ab_sub_tmin
  set v₀ : E := f t (Φ ⟨x₀, t⟩) with hv₀_def
  set g : ℝ → E := fun u => α u - (u - t) • v₀ with hg_def
  have hg_deriv : ∀ u ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw),
      HasDerivWithinAt g (f u (α u) - v₀) (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
    intro u hu
    have hsubconst :
        HasDerivWithinAt (fun u : ℝ => (u - t) • v₀) v₀
          (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
      have h_lin : HasDerivWithinAt (fun u : ℝ => u - t) (1 : ℝ)
          (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
        have hid : HasDerivAt (fun u : ℝ => u - t) ((1 : ℝ) - 0) u :=
          (hasDerivAt_id' u).sub (hasDerivAt_const u t)
        rw [sub_zero] at hid
        exact hid.hasDerivWithinAt
      have hsmul := h_lin.smul_const v₀
      simpa using hsmul
    exact (hα_deriv u hu).sub hsubconst
  set u_lo : ℝ := min t (t + s) with hu_lo_def
  set u_hi : ℝ := max t (t + s) with hu_hi_def
  have hu_lo_le_t : u_lo ≤ t := min_le_left _ _
  have ht_le_u_hi : t ≤ u_hi := le_max_left _ _
  have hu_lo_le_ts : u_lo ≤ t + s := min_le_right _ _
  have hts_le_u_hi : t + s ≤ u_hi := le_max_right _ _
  have hu_lo_le_u_hi : u_lo ≤ u_hi := hu_lo_le_t.trans ht_le_u_hi

  have h_uloIcc : t - ρ_t_raw ≤ u_lo := by
    rw [hu_lo_def, le_min_iff]
    refine ⟨by linarith [hρ_t_raw_pos], ?_⟩
    have hs_ge : -(|s|) ≤ s := neg_abs_le _
    linarith [hs_lt_ρ_t_raw]
  have h_uhiIcc : u_hi ≤ t + ρ_t_raw := by
    rw [hu_hi_def, max_le_iff]
    refine ⟨by linarith [hρ_t_raw_pos], ?_⟩
    have hs_le : s ≤ |s| := le_abs_self _
    linarith [hs_lt_ρ_t_raw]
  have hseg_sub : Icc u_lo u_hi ⊆ Icc (t - ρ_t_raw) (t + ρ_t_raw) := by
    intro u hu
    exact ⟨h_uloIcc.trans hu.1, hu.2.trans h_uhiIcc⟩

  have h_seg_dist : ∀ u ∈ Icc u_lo u_hi, |u - t| ≤ |s| := by
    intro u hu
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · have hlo : u_lo = t := min_eq_left (by linarith)
      have hhi : u_hi = t + s := max_eq_right (by linarith)
      rw [hlo, hhi] at hu
      have h1 : t ≤ u := hu.1
      have h2 : u ≤ t + s := hu.2
      have h3 : 0 ≤ u - t := by linarith
      have h4 : u - t ≤ s := by linarith
      rw [abs_of_nonneg h3]
      have habs_s : |s| = s := abs_of_nonneg hs_nn
      rw [habs_s]; exact h4
    · have hlo : u_lo = t + s := min_eq_right (by linarith)
      have hhi : u_hi = t := max_eq_left (by linarith)
      rw [hlo, hhi] at hu
      have h1 : t + s ≤ u := hu.1
      have h2 : u ≤ t := hu.2
      have h3 : u - t ≤ 0 := by linarith
      have h4 : -(u - t) ≤ -s := by linarith
      rw [abs_of_nonpos h3]
      have habs_s : |s| = -s := abs_of_neg hs_neg
      rw [habs_s]; exact h4

  have hpair_dist_seg : ∀ u ∈ Icc u_lo u_hi,
      dist ((x₀ + δ, u) : E × ℝ) (x₀, t) < ρ₀ := by
    intro u hu
    rw [Prod.dist_eq]
    have h1 : dist (x₀ + δ) x₀ = ‖δ‖ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    have h2 : dist u t = |u - t| := Real.dist_eq u t
    rw [h1, h2]
    have h3 : ‖δ‖ < ρ₀ := hδ_lt_ρ₀
    have h4 : |u - t| < ρ₀ := lt_of_le_of_lt (h_seg_dist u hu) hs_lt_ρ₀
    exact max_lt h3 h4

  have hΦ_seg : ∀ u ∈ Icc u_lo u_hi,
      dist (α u) (Φ ⟨x₀, t⟩) < η_half := by
    intro u hu
    have hpair_in : (x₀ + δ, u) ∈ closedBall x₀ r ×ˢ Icc tmin tmax := by
      refine ⟨hx_in_ball, ?_⟩
      exact h_ab_sub_tmin (hseg_sub hu)
    exact hΦ_close hpair_in (hpair_dist_seg u hu)

  have hpair_dist_f : ∀ u ∈ Icc u_lo u_hi,
      dist ((u, α u) : ℝ × E) (t, Φ ⟨x₀, t⟩) < η_f := by
    intro u hu
    rw [Prod.dist_eq]
    have h1 : dist u t = |u - t| := Real.dist_eq u t
    rw [h1]
    have hu_t : |u - t| < η_half := by
      have h_le : |u - t| ≤ |s| := h_seg_dist u hu
      exact lt_of_le_of_lt h_le hs_lt_η_half
    have h2 : dist (α u) (Φ ⟨x₀, t⟩) < η_half := hΦ_seg u hu
    have h3 : max (|u - t|) (dist (α u) (Φ ⟨x₀, t⟩)) < η_half := max_lt hu_t h2
    exact lt_trans h3 hη_half_lt

  have hf_close_seg : ∀ u ∈ Icc u_lo u_hi, ‖f u (α u) - v₀‖ ≤ c2 := by
    intro u hu
    have hd := hpair_dist_f u hu
    have h := hη_f hd
    rw [dist_eq_norm] at h
    change ‖f u (α u) - v₀‖ ≤ c2
    exact le_of_lt h

  have hg_deriv_seg : ∀ u ∈ Icc u_lo u_hi,
      HasDerivWithinAt g (f u (α u) - v₀) (Icc u_lo u_hi) u := fun u hu =>
    (hg_deriv u (hseg_sub hu)).mono hseg_sub
  have hf_seg_bound : ∀ u ∈ Ico u_lo u_hi, ‖f u (α u) - v₀‖ ≤ c2 := fun u hu =>
    hf_close_seg u ⟨hu.1, le_of_lt hu.2⟩
  have h_mvt :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
      (f' := fun u => f u (α u) - v₀) (C := c2) (a := u_lo) (b := u_hi)
      hg_deriv_seg hf_seg_bound u_hi (right_mem_Icc.mpr hu_lo_le_u_hi)
  have h_u_diff : u_hi - u_lo = |s| := by
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · have hlo : u_lo = t := min_eq_left (by linarith)
      have hhi : u_hi = t + s := max_eq_right (by linarith)
      rw [hlo, hhi]
      rw [abs_of_nonneg hs_nn]; ring
    · have hlo : u_lo = t + s := min_eq_right (by linarith)
      have hhi : u_hi = t := max_eq_left (by linarith)
      rw [hlo, hhi]
      rw [abs_of_neg hs_neg]; ring
  have h_time_residual : ‖α (t + s) - α t - s • v₀‖ ≤ c2 * |s| := by
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · have hlo : u_lo = t := min_eq_left (by linarith)
      have hhi : u_hi = t + s := max_eq_right (by linarith)
      have h_mvt' : ‖g (t + s) - g t‖ ≤ c2 * (t + s - t) := by
        have := h_mvt
        rw [hlo, hhi] at this
        exact this
      have h_diff_eq : g (t + s) - g t = α (t + s) - α t - s • v₀ := by
        change (α (t + s) - (t + s - t) • v₀) - (α t - (t - t) • v₀)
            = α (t + s) - α t - s • v₀
        have h1 : t + s - t = s := by ring
        have h2 : t - t = (0 : ℝ) := by ring
        rw [h1, h2]; simp; abel
      rw [h_diff_eq] at h_mvt'
      have hs_eq : t + s - t = s := by ring
      rw [hs_eq] at h_mvt'
      rw [abs_of_nonneg hs_nn]; exact h_mvt'
    · have hlo : u_lo = t + s := min_eq_right (by linarith)
      have hhi : u_hi = t := max_eq_left (by linarith)
      have h_mvt' : ‖g t - g (t + s)‖ ≤ c2 * (t - (t + s)) := by
        have := h_mvt
        rw [hlo, hhi] at this
        exact this
      have h_diff_eq : g t - g (t + s) = -(α (t + s) - α t - s • v₀) := by
        change (α t - (t - t) • v₀) - (α (t + s) - (t + s - t) • v₀)
            = -(α (t + s) - α t - s • v₀)
        have h1 : t - t = (0 : ℝ) := by ring
        have h2 : t + s - t = s := by ring
        rw [h1, h2]
        simp
        abel
      rw [h_diff_eq, norm_neg] at h_mvt'
      have hs_eq : t - (t + s) = -s := by ring
      rw [hs_eq] at h_mvt'
      rw [abs_of_neg hs_neg]; exact h_mvt'

  have h_space_piece : ‖Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ‖ ≤ c2 * ‖δ‖ := by
    have hδ_in_U : δ ∈ U_space :=
      hρ_s_sub (by rw [mem_ball_zero_iff]; exact hδ_lt_ρ_s)
    have h := hU_space δ hδ_in_U
    exact h
  have h_total :
      ‖Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀‖
        ≤ c2 * ‖δ‖ + c2 * |s| := by
    have h_decomp :
        Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀
          = (α (t + s) - α t - s • v₀) + (Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ) := by
      change Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀
          = (Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀ + δ, t⟩ - s • v₀)
            + (Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ)
      abel
    rw [h_decomp]
    have hnorm := norm_add_le (α (t + s) - α t - s • v₀)
      (Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ)
    have h_sum_le : c2 * |s| + c2 * ‖δ‖ ≤ c2 * ‖δ‖ + c2 * |s| := by linarith
    linarith [hnorm, h_time_residual, h_space_piece]

  have h_norm_pair : ‖(δ, s)‖ = max ‖δ‖ |s| := by
    rw [Prod.norm_def]
    rfl
  have h_δ_le : ‖δ‖ ≤ ‖(δ, s)‖ := by rw [h_norm_pair]; exact le_max_left _ _
  have h_s_le : |s| ≤ ‖(δ, s)‖ := by rw [h_norm_pair]; exact le_max_right _ _
  have h_final : c2 * ‖δ‖ + c2 * |s| ≤ c * ‖(δ, s)‖ := by
    have hsum : c2 * ‖δ‖ + c2 * |s| ≤ c2 * ‖(δ, s)‖ + c2 * ‖(δ, s)‖ := by
      have h1 : c2 * ‖δ‖ ≤ c2 * ‖(δ, s)‖ :=
        mul_le_mul_of_nonneg_left h_δ_le (le_of_lt hc2_pos)
      have h2 : c2 * |s| ≤ c2 * ‖(δ, s)‖ :=
        mul_le_mul_of_nonneg_left h_s_le (le_of_lt hc2_pos)
      linarith
    have hkey : c2 * ‖(δ, s)‖ + c2 * ‖(δ, s)‖ = c * ‖(δ, s)‖ := by
      rw [hc2_def]; ring
    linarith

  have h_Ljoint : Ljoint (δ, s) = Lmap δ + s • v₀ := by
    rw [hLjoint_def, hLtime_def]
    simp [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
  have h_goal_eq :
      Φ ((x₀, t) + (δ, s)) - Φ (x₀, t) - Ljoint (δ, s)
        = Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀ := by
    rw [h_Ljoint]
    change Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - (Lmap δ + s • v₀) = _
    abel
  rw [h_goal_eq]
  exact le_trans h_total h_final







omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_flow_jointly_at_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasFDerivAt Φ
      (((variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
            hT hM hMT
            (((hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow x
              (by
                have hρ_le_r : (ρ : ℝ) ≤ (r : ℝ) := by
                  have hr'_nonneg : 0 ≤ (r' : ℝ) := NNReal.coe_nonneg _
                  linarith
                exact closedBall_subset_closedBall hρ_le_r hx)).mono hsub))
            (fun τ hτ => hA_bd x hx τ hτ) (Ioo_subset_Icc_self ht))).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))))
      (x, t) := by



  have hd : dist x x₀ + (r' : ℝ) ≤ (r : ℝ) := by
    rw [mem_closedBall] at hx
    linarith
  have hΦ' := hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') hd
  have hΩ_flow' :
      ∀ y ∈ closedBall x (r' : ℝ), ∀ τ ∈ Icc tmin tmax, (τ, Φ (y, τ)) ∈ Ω := by
    intro y hy τ hτ
    refine hΩ_flow y ?_ τ hτ
    rw [mem_closedBall] at hy ⊢
    have htri := dist_triangle y x x₀
    linarith
  exact hasFDerivAt_flow_jointly_center_local hΦ' hΩ hf_C1 hΩ_flow' hT hM hMT hsub
    (fun τ hτ => hA_bd x hx τ hτ) hr' ht











theorem IsLocalFlow.contDiffOn_top_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)}
    (hΩ : IsOpen Ω)
    (hf_top : ContDiffOn ℝ ∞ (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid)
      (hT_mid_lt_out : T_mid < T_out) (hM : 0 ≤ M)
      (hMT_mid : M * T_mid < 1)
      (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
      (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ))
      (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
      (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
      (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ),
       ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
       ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ ∞ Φ (ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  apply contDiffOn_top_of_forall_nat
  intro n
  set U := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hU_open : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax :=
    hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ),
      ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid), ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M :=
    fun x hx τ hτ =>
      hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  have hρ_mid_le_r : (ρ_mid : ℝ) ≤ (r : ℝ) :=
    le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r
  have hρ_le_r : (ρ : ℝ) ≤ (r : ℝ) :=
    le_trans (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hρ_out_le_r
  have hU_sub_flow : U ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    refine ⟨?_, ?_⟩
    · exact closedBall_subset_closedBall hρ_le_r (mem_closedBall.mpr (le_of_lt (mem_ball.mp hq.1)))
    · have ht_out : q.2 ∈ Icc (t₀ - T_out) (t₀ + T_out) :=
        ⟨by linarith [hq.2.1, hT_lt_mid, hT_mid_lt_out],
          by linarith [hq.2.2, hT_lt_mid, hT_mid_lt_out]⟩
      exact hsub ht_out
  have hΩ_map : ∀ q ∈ U, (q.2, Φ q) ∈ Ω := by
    intro q hq
    exact hΩ_flow q.1 (hU_sub_flow hq).1 q.2 (hU_sub_flow hq).2
  have hf_Ck : ∀ k : ℕ, ContDiffOn ℝ (k : ℕ∞) (uncurry f) Ω :=
    fun k => (hf_top : ContDiffOn ℝ ∞ (uncurry f) Ω).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω := by simpa using hf_Ck 1
  have hΦ_C0 : ContDiffOn ℝ (0 : ℕ∞) Φ U := by
    exact contDiffOn_zero.mpr (hΦ.continuousOn.mono hU_sub_flow)
  have hab : t₀ - T < t₀ + T := by linarith
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  induction n with
  | zero =>
      exact hΦ_C0
  | succ n ih =>
      have hf_Csucc : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) Ω := by
        simpa using hf_Ck (n + 1)
      have hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞)
          (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q)) U :=
        contDiffOn_variational_coeff_aux_local hΩ hf_Csucc ih hΩ_map
      set A : E → ℝ → (E →L[ℝ] E) := fun x t => fderiv ℝ (f t) (Φ ⟨x, t⟩)
      have hlinear_Cn : ∀ δ : E, ContDiffOn ℝ (n : ℕ∞)
          (uncurry (linearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ))) U :=
        fun δ => linearODESolution_contDiffOn hab ht₀_mem isOpen_ball n
          (hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry A) _)
          (contDiffOn_const : ContDiffOn ℝ (n : ℕ∞) (fun (_ : E) => δ) (ball x₀ (ρ : ℝ)))
      set Lsp : E × ℝ → E →L[ℝ] E :=
        fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)
      have hΦ_diff : DifferentiableOn ℝ Φ U := by
        intro q hq
        obtain ⟨x, t⟩ := q
        rcases hq with ⟨hx, ht⟩
        have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
          mem_closedBall.mpr (le_of_lt (lt_trans (mem_ball.mp hx) hρ_lt_mid))
        have ht_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
          ⟨by linarith [ht.1, hT_lt_mid],
            by linarith [ht.2, hT_lt_mid]⟩
        have hfd := hasFDerivAt_flow_jointly_at_local
          (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
          (Φ := Φ) hΦ hΩ hf_C1 hΩ_flow hT_mid_pos hM hMT_mid hsub_mid
          hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
        exact hfd.differentiableAt.differentiableWithinAt
      have hfderiv_coprod : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q) := by
        intro q hq
        obtain ⟨x, t⟩ := q
        rcases hq with ⟨hx, ht⟩
        have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
          mem_closedBall.mpr (le_of_lt (lt_trans (mem_ball.mp hx) hρ_lt_mid))
        have ht_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
          ⟨by linarith [ht.1, hT_lt_mid],
            by linarith [ht.2, hT_lt_mid]⟩
        have hfd := hasFDerivAt_flow_jointly_at_local
          (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
          (Φ := Φ) hΦ hΩ hf_C1 hΩ_flow hT_mid_pos hM hMT_mid hsub_mid
          hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
        rw [hfd.fderiv]
        change (variationalLinearMapAt hT_mid_pos hM hMT_mid _ _ _).coprod
              ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ (x, t))))
          = (Lsp (x, t)).coprod (timePieceFn f Φ (x, t))
        congr 1
        · change _ = (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
          rw [hfd.fderiv]
          exact (ContinuousLinearMap.coprod_comp_inl _ _).symm
      have hLsp_Cn : ContDiffOn ℝ (n : ℕ∞) Lsp U := by
        rw [contDiffOn_clm_apply]
        intro δ
        refine (hlinear_Cn δ).congr (fun q hq => ?_)
        obtain ⟨hx_ball, ht_Ioo⟩ := hq
        have hx' : dist q.1 x₀ < ↑ρ := mem_ball.mp hx_ball
        have hx_cb_mid : q.1 ∈ closedBall x₀ (ρ_mid : ℝ) :=
          mem_closedBall.mpr (le_of_lt (lt_trans hx' hρ_lt_mid))
        have hx_cb_r : q.1 ∈ closedBall x₀ (r : ℝ) :=
          closedBall_subset_closedBall hρ_mid_le_r hx_cb_mid
        have ht_mid : q.2 ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
          ⟨by linarith [ht_Ioo.1, hT_lt_mid],
            by linarith [ht_Ioo.2, hT_lt_mid]⟩
        have hA_cont_x : ContinuousOn (A q.1) (Icc (t₀ - T_mid) (t₀ + T_mid)) := by
          simpa [A] using
            ((hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow q.1 hx_cb_r).mono
              hsub_mid)
        have hA_bd_x : ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid), ‖A q.1 τ‖ ≤ M := by
          intro τ hτ
          simpa [A] using hA_bd_mid q.1 hx_cb_mid τ hτ
        have ht_Icc : q.2 ∈ Icc (t₀ - T_mid) (t₀ + T_mid) := Ioo_subset_Icc_self ht_mid
        have hfd := hasFDerivAt_flow_jointly_at_local
          (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
          (Φ := Φ) hΦ hΩ hf_C1 hΩ_flow hT_mid_pos hM hMT_mid hsub_mid
          hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
        have hLsp_eq_vlm : Lsp q =
            variationalLinearMapAt hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x ht_Icc := by
          change (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) = _
          conv_lhs => rw [show q = (q.1, q.2) from Prod.mk.eta.symm]
          rw [hfd.fderiv]
          exact ContinuousLinearMap.coprod_comp_inl _ _
        have hvlm_eq := variationalLinearMapAt_apply hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x
          ht_Icc δ
        have hvsf := variationalSolutionFun_isSolution hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x δ
        have hA_cont_Ioo : ContinuousOn (A q.1) (Ioo (t₀ - T) (t₀ + T)) :=
          hA_cont_x.mono (fun s hs => Ioo_subset_Icc_self
            (⟨by linarith [hs.1, hT_lt_mid],
              by linarith [hs.2, hT_lt_mid]⟩ : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid)))
        have hA_joint_cont : ContinuousOn (uncurry A) U := hcoeff_Cn.continuousOn
        have h_exists : HasLinearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ) q.1 :=
          hasLinearODESolution_of_continuousOn hab ht₀_mem isOpen_ball hA_joint_cont (mem_ball.mpr hx')
        have h_uniq := linearODE_unique_on_Ioo (G := E) ht₀_mem hA_cont_Ioo
          (fun s hs => by
            have hs_mid : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
              ⟨by linarith [hs.1, hT_lt_mid],
                by linarith [hs.2, hT_lt_mid]⟩
            exact (hvsf.2 s (Ioo_subset_Icc_self hs_mid)).hasDerivAt (Icc_mem_nhds_iff.mpr hs_mid))
          (fun s hs => linearODESolution_hasDerivAt_of_hasSolution A (t₀ - T) (t₀ + T) t₀
            (fun _ => δ) h_exists hs)
          (by rw [hvsf.1, linearODESolution_init])
        simp only [hLsp_eq_vlm, hvlm_eq, uncurry]
        have h_eq := h_uniq ht_Ioo
        dsimp at h_eq
        exact h_eq
      simpa using
        contDiffOn_flow_succ_of_spatial_smooth_local
          (f := f) (Φ := Φ) hU_open hf_Csucc hΩ_map hΦ_diff ih hLsp_Cn hfderiv_coprod

end HartmanTheorem

end DifferentialGeometry.Analysis.ODE.Flow

end
