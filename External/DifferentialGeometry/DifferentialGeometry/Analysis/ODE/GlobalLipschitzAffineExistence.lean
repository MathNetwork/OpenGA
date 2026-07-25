import DifferentialGeometry.Analysis.ODE.ForwardVariationalFromZero
import DifferentialGeometry.Analysis.Calculus.BallRetraction
import Mathlib.Analysis.ODE.Gronwall

open Set Function Filter Metric Real
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem forward_solution_of_lipschitzWith_affineBound
    {f : ℝ → E → E} {T : ℝ} (hT : 0 < T) {K : ℝ≥0} {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (f t))
    (hcont : ∀ x : E, ContinuousOn (fun t => f t x) (Icc (0 : ℝ) T))
    (haff : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, ‖f t x‖ ≤ C + (K : ℝ) * ‖x‖)
    (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ContinuousOn γ (Icc (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt γ (f t (γ t)) (Ici (0 : ℝ)) t := by
  set ρ : ℝ := gronwallBound ‖x₀‖ (K : ℝ) C T with hρ_def
  have hx₀_nn : (0 : ℝ) ≤ ‖x₀‖ := norm_nonneg _
  have hK_nn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hρ_nn : 0 ≤ ρ := by
    have hmono := gronwallBound_mono (δ := ‖x₀‖) (K := (K : ℝ)) (ε := C) hx₀_nn hC hK_nn
    have hle := hmono (show (0 : ℝ) ≤ T from le_of_lt hT)
    rw [gronwallBound_x0] at hle
    exact le_trans hx₀_nn hle
  have hret_lip : LipschitzWith 1 (ballRetraction (X := E) ρ) :=
    lipschitzWith_ballRetraction hρ_nn
  have hret_norm_le : ∀ x : E, ‖ballRetraction (X := E) ρ x‖ ≤ ‖x‖ := by
    intro x
    rw [ballRetraction, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_min zero_le_one (div_nonneg hρ_nn (norm_nonneg x)))]
    calc min 1 (ρ / ‖x‖) * ‖x‖ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hret_ball : ∀ x : E, ‖ballRetraction (X := E) ρ x‖ ≤ ρ :=
    fun x => ballRetraction_mem_closedBall hρ_nn x
  set g : ℝ → E → E := fun t x => f t (ballRetraction (X := E) ρ x) with hg_def
  set L : ℝ := C + (K : ℝ) * ρ with hL_def
  have hL_nn : 0 ≤ L := by
    have : 0 ≤ (K : ℝ) * ρ := mul_nonneg hK_nn hρ_nn
    rw [hL_def]; linarith
  have hg_lip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (g t) := by
    intro t ht
    have := (hlip t ht).comp hret_lip
    simpa [hg_def, mul_one] using this
  have hg_norm_all : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, ‖g t x‖ ≤ L := by
    intro t ht x
    have h1 : ‖f t (ballRetraction (X := E) ρ x)‖ ≤
        C + (K : ℝ) * ‖ballRetraction (X := E) ρ x‖ := haff t ht _
    have h2 : (K : ℝ) * ‖ballRetraction (X := E) ρ x‖ ≤ (K : ℝ) * ρ :=
      mul_le_mul_of_nonneg_left (hret_ball x) hK_nn
    rw [hg_def]; rw [hL_def]; linarith
  have hg_aff : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, ‖g t x‖ ≤ C + (K : ℝ) * ‖x‖ := by
    intro t ht x
    have h1 : ‖f t (ballRetraction (X := E) ρ x)‖ ≤
        C + (K : ℝ) * ‖ballRetraction (X := E) ρ x‖ := haff t ht _
    have h2 : (K : ℝ) * ‖ballRetraction (X := E) ρ x‖ ≤ (K : ℝ) * ‖x‖ :=
      mul_le_mul_of_nonneg_left (hret_norm_le x) hK_nn
    rw [hg_def]; linarith
  have hg_cont : ∀ x : E, ContinuousOn (fun t => g t x) (Icc (0 : ℝ) T) := by
    intro x; rw [hg_def]; exact hcont (ballRetraction (X := E) ρ x)
  set LN : ℝ≥0 := ⟨L, hL_nn⟩ with hLN_def
  set aN : ℝ≥0 := ⟨L * T, mul_nonneg hL_nn (le_of_lt hT)⟩ with haN_def
  have hg_lip_ball : ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzOnWith K (g t) (closedBall x₀ aN) :=
    fun t ht => (hg_lip t ht).lipschitzOnWith (s := closedBall x₀ aN)
  have hg_cont_ball : ∀ x ∈ closedBall x₀ aN, ContinuousOn (g · x) (Icc (0 : ℝ) T) :=
    fun x _ => hg_cont x
  have hg_norm_ball : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ closedBall x₀ aN, ‖g t x‖ ≤ LN :=
    fun t ht x _ => hg_norm_all t ht x
  have hmul : (LN : ℝ) * T ≤ (aN : ℝ) - 0 := by
    change L * T ≤ L * T - 0
    rw [sub_zero]
  have hx_mem : x₀ ∈ closedBall x₀ (0 : ℝ≥0) := by
    rw [mem_closedBall, dist_self]; exact le_rfl
  obtain ⟨γ, hγ0, hγcont, hγderiv_g⟩ :=
    forward_picard_solution_from_zero (f := g) (x₀ := x₀) (a := aN) (r := (0 : ℝ≥0))
      (L := LN) (K := K) (δ := T) hT hg_lip_ball hg_cont_ball hg_norm_ball hmul hx_mem
  have hγderiv_Ici : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt γ (g t (γ t)) (Ici t) t :=
    fun t ht => hasDerivWithinAt_Ici_of_Ici_zero (hγderiv_g t ht) ht.1
  have hγ_apriori : ∀ t ∈ Icc (0 : ℝ) T, ‖γ t‖ ≤ ρ := by
    have hbound : ∀ x ∈ Ico (0 : ℝ) T, ‖g x (γ x)‖ ≤ (K : ℝ) * ‖γ x‖ + C := by
      intro x hx
      have := hg_aff x ⟨hx.1, le_of_lt hx.2⟩ (γ x)
      linarith
    have ha : ‖γ 0‖ ≤ ‖x₀‖ := by rw [hγ0]
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := γ) (f' := fun x => g x (γ x)) (δ := ‖x₀‖) (K := (K : ℝ)) (ε := C)
      hγcont hγderiv_Ici ha hbound
    intro t ht
    have hgr_t := hgr t ht
    have hmono := gronwallBound_mono (δ := ‖x₀‖) (K := (K : ℝ)) (ε := C) hx₀_nn hC hK_nn
    have h_le : gronwallBound ‖x₀‖ (K : ℝ) C (t - 0) ≤ gronwallBound ‖x₀‖ (K : ℝ) C T := by
      apply hmono; have : t ≤ T := ht.2; linarith
    rw [hρ_def]; exact le_trans hgr_t h_le
  refine ⟨γ, hγ0, hγcont, ?_⟩
  intro t ht
  have hγt_ball : ‖γ t‖ ≤ ρ := hγ_apriori t ⟨ht.1, le_of_lt ht.2⟩
  have hretγ : ballRetraction (X := E) ρ (γ t) = γ t :=
    ballRetraction_eq_self_of_mem hγt_ball
  have hgeq : g t (γ t) = f t (γ t) := by
    change f t (ballRetraction (X := E) ρ (γ t)) = f t (γ t)
    rw [hretγ]
  have := hγderiv_g t ht
  rwa [hgeq] at this

end DifferentialGeometry.Analysis.ODE
