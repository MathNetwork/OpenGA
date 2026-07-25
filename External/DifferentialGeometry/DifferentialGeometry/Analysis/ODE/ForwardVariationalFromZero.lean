import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Analysis.ODE.ChartLocalPicardIntegral
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.FrechetDerivative

open Set Function Filter Metric Asymptotics Real MeasureTheory
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in

lemma hasDerivWithinAt_Ici_zero_of_Icc {y : ℝ → E} {y' : E} {b τ : ℝ}
    (h : HasDerivWithinAt y y' (Icc (0 : ℝ) b) τ) (hτ : τ ∈ Ico (0 : ℝ) b) :
    HasDerivWithinAt y y' (Ici (0 : ℝ)) τ := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Iio b, Iio_mem_nhds hτ.2, ?_⟩
  intro s hs
  exact ⟨hs.2, le_of_lt hs.1⟩

theorem forward_picard_solution_from_zero
    {f : ℝ → E → E} {x₀ : E} {a r L K : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hlip : ∀ t ∈ Icc (0 : ℝ) δ, LipschitzOnWith K (f t) (closedBall x₀ a))
    (hcont : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc (0 : ℝ) δ))
    (hnorm : ∀ t ∈ Icc (0 : ℝ) δ, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L)
    (hmul : (L : ℝ) * δ ≤ (a : ℝ) - r)
    {x : E} (hx : x ∈ closedBall x₀ r) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ContinuousOn γ (Icc (0 : ℝ) δ) ∧
      ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt γ (f t (γ t)) (Ici (0 : ℝ)) t := by
  have h0le : (0 : ℝ) ≤ δ := le_of_lt hδ
  set t₀ : Icc (0 : ℝ) δ := ⟨0, ⟨le_rfl, h0le⟩⟩ with ht₀_def
  have hPL : IsPicardLindelof f t₀ x₀ a r L K := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · exact hlip
    · exact hcont
    · exact hnorm
    · have hmax : max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) = δ := by
        have h1 : (t₀ : ℝ) = 0 := rfl
        rw [h1]; simp [h0le]
      rw [hmax]; exact hmul
  obtain ⟨γ, hγ0, hγd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨γ, ?_, ?_, ?_⟩
  · have : γ (t₀ : ℝ) = x := hγ0
    simpa [ht₀_def] using this
  · exact fun t ht => (hγd t ht).continuousWithinAt
  · intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) δ := ⟨ht.1, le_of_lt ht.2⟩
    exact hasDerivWithinAt_Ici_zero_of_Icc (hγd t htIcc) ht

theorem forward_field_ftc_from_zero
    {γ : ℝ → E} {f : ℝ → E → E} {δ : ℝ}
    (hγcont : ContinuousOn γ (Icc 0 δ))
    (hγderiv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt γ (f t (γ t)) (Ici (0 : ℝ)) t)
    (hfcont : ContinuousOn (fun r : ℝ => f r (γ r)) (Icc 0 δ)) :
    ∀ s ∈ Icc (0 : ℝ) δ, γ s = γ 0 + ∫ r in (0 : ℝ)..s, f r (γ r) :=
  ode_field_ftc_integral hγcont hγderiv hfcont

theorem forward_variational_solution_from_zero
    {A : ℝ → (E →L[ℝ] E)} {M : ℝ} {δ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    (J₀ : E) :
    ∃ J : ℝ → E, J 0 = J₀ ∧ ContinuousOn J (Icc (0 : ℝ) δ) ∧
      ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt J ((A t) (J t)) (Ici (0 : ℝ)) t := by
  set v : ℝ → E → E := fun t y => (A t) y with hv_def
  set r₀ : ℝ := ‖J₀‖ with hr₀_def
  have hr₀_nn : 0 ≤ r₀ := norm_nonneg _
  have h1mMδ_pos : 0 < 1 - M * δ := by linarith
  set a₀ : ℝ := (r₀ + 1) / (1 - M * δ) with ha₀_def
  have ha₀_pos : 0 < a₀ := div_pos (by linarith [hr₀_nn]) h1mMδ_pos
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have hMaδ_le : M * a₀ * δ ≤ a₀ - r₀ := by
    have hkey : a₀ * (1 - M * δ) = r₀ + 1 := by rw [ha₀_def]; field_simp
    have h1 : a₀ - M * a₀ * δ = r₀ + 1 := by
      have : a₀ - M * a₀ * δ = a₀ * (1 - M * δ) := by ring
      rw [this, hkey]
    linarith
  have h0le : (0 : ℝ) ≤ δ := le_of_lt hδ
  set t₀ : Icc (0 : ℝ) δ := ⟨0, ⟨le_rfl, h0le⟩⟩ with ht₀_def
  set aN : ℝ≥0 := ⟨a₀, ha₀_nn⟩ with haN_def
  set rN : ℝ≥0 := ⟨r₀, hr₀_nn⟩ with hrN_def
  set LN : ℝ≥0 := ⟨M * a₀, mul_nonneg hM ha₀_nn⟩ with hLN_def
  set KN : ℝ≥0 := ⟨M, hM⟩ with hKN_def
  have hPL : IsPicardLindelof v t₀ (0 : E) aN rN LN KN := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le (hAbd t ht)
      exact hlip.lipschitzOnWith (s := closedBall (0 : E) aN)
    · intro y _
      have happly : Continuous (fun B : E →L[ℝ] E => B y) :=
        (ContinuousLinearMap.apply ℝ E y).continuous
      exact happly.comp_continuousOn hAcont
    · intro t ht y hy
      have hy_norm : ‖y‖ ≤ a₀ := by
        simpa [mem_closedBall_zero_iff, haN_def] using hy
      change ‖v t y‖ ≤ (LN : ℝ)
      have hLN_val : (LN : ℝ) = M * a₀ := rfl
      rw [hLN_val]
      calc ‖v t y‖ = ‖(A t) y‖ := rfl
        _ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ M * a₀ := mul_le_mul (hAbd t ht) hy_norm (norm_nonneg _) hM
    · have hmax : max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) = δ := by
        have h1 : (t₀ : ℝ) = 0 := rfl
        rw [h1]; simp [h0le]
      change (LN : ℝ) * max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (aN : ℝ) - (rN : ℝ)
      rw [hmax]
      have hLN_val : (LN : ℝ) = M * a₀ := rfl
      have haN_val : (aN : ℝ) = a₀ := rfl
      have hrN_val : (rN : ℝ) = r₀ := rfl
      rw [hLN_val, haN_val, hrN_val]
      exact hMaδ_le
  have hJ₀_mem : J₀ ∈ closedBall (0 : E) rN := by
    rw [mem_closedBall_zero_iff]
    have : (rN : ℝ) = r₀ := rfl
    rw [this, hr₀_def]
  obtain ⟨J, hJ0, hJd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hJ₀_mem
  refine ⟨J, ?_, ?_, ?_⟩
  · have : J (t₀ : ℝ) = J₀ := hJ0
    simpa [ht₀_def] using this
  · exact fun t ht => (hJd t ht).continuousWithinAt
  · intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) δ := ⟨ht.1, le_of_lt ht.2⟩
    exact hasDerivWithinAt_Ici_zero_of_Icc (hJd t htIcc) ht

omit [CompleteSpace E] in

theorem forward_variational_gronwall_bound
    {A : ℝ → (E →L[ℝ] E)} {J : ℝ → E} {M δ : ℝ} (hM : 0 ≤ M)
    (hJcont : ContinuousOn J (Icc (0 : ℝ) δ))
    (hJderiv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt J ((A t) (J t)) (Ici t) t)
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    {J₀ : E} (hJ0 : J 0 = J₀) :
    ∀ t ∈ Icc (0 : ℝ) δ, ‖J t‖ ≤ ‖J₀‖ * exp (M * δ) := by
  intro t ht
  have hbound : ∀ τ ∈ Ico (0 : ℝ) δ, ‖(A τ) (J τ)‖ ≤ M * ‖J τ‖ + 0 := by
    intro τ hτ
    have hτ_in : τ ∈ Icc (0 : ℝ) δ := ⟨hτ.1, le_of_lt hτ.2⟩
    calc ‖(A τ) (J τ)‖ ≤ ‖A τ‖ * ‖J τ‖ := (A τ).le_opNorm _
      _ ≤ M * ‖J τ‖ := by have := hAbd τ hτ_in; gcongr
      _ = M * ‖J τ‖ + 0 := by ring
  have hinit : ‖J 0‖ ≤ ‖J₀‖ := by rw [hJ0]
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := J) (f' := fun τ => (A τ) (J τ)) (δ := ‖J₀‖) (K := M) (ε := 0)
    hJcont hJderiv hinit hbound
  have hgr_t := hgr t ht
  rw [gronwallBound_ε0, sub_zero] at hgr_t
  have hexp_mono : exp (M * t) ≤ exp (M * δ) := by
    apply exp_le_exp.mpr
    have : t ≤ δ := ht.2
    nlinarith [hM, this, ht.1]
  calc ‖J t‖ ≤ ‖J₀‖ * exp (M * t) := hgr_t
    _ ≤ ‖J₀‖ * exp (M * δ) := by
      apply mul_le_mul_of_nonneg_left hexp_mono (norm_nonneg _)

omit [CompleteSpace E] in

theorem forward_variational_unique
    {A : ℝ → (E →L[ℝ] E)} {J₁ J₂ : ℝ → E} {M δ : ℝ} (hM : 0 ≤ M)
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    (hJ₁cont : ContinuousOn J₁ (Icc (0 : ℝ) δ))
    (hJ₁deriv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt J₁ ((A t) (J₁ t)) (Ici t) t)
    (hJ₂cont : ContinuousOn J₂ (Icc (0 : ℝ) δ))
    (hJ₂deriv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt J₂ ((A t) (J₂ t)) (Ici t) t)
    (hinit : J₁ 0 = J₂ 0) :
    EqOn J₁ J₂ (Icc (0 : ℝ) δ) := by
  set v : ℝ → E → E := fun t y => (A t) y with hv_def
  set KN : ℝ≥0 := ⟨M, hM⟩ with hKN_def
  have hv_lip : ∀ t ∈ Ico (0 : ℝ) δ, LipschitzOnWith KN (v t) (univ : Set E) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) δ := ⟨ht.1, le_of_lt ht.2⟩
    have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le (hAbd t ht')
    exact hlip.lipschitzOnWith (s := (univ : Set E))
  exact ODE_solution_unique_of_mem_Icc_right hv_lip
    hJ₁cont (fun t ht => hJ₁deriv t ht) (fun t _ => mem_univ _)
    hJ₂cont (fun t ht => hJ₂deriv t ht) (fun t _ => mem_univ _) hinit

omit [CompleteSpace E] in

theorem forward_orbit_dist_le
    {f : ℝ → E → E} {γ₁ γ₂ : ℝ → E} {S : Set E} {K : ℝ≥0} {δ : ℝ}
    (hlip : ∀ t ∈ Ico (0 : ℝ) δ, LipschitzOnWith K (f t) S)
    (hγ₁cont : ContinuousOn γ₁ (Icc (0 : ℝ) δ))
    (hγ₁deriv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt γ₁ (f t (γ₁ t)) (Ici t) t)
    (hγ₁mem : ∀ t ∈ Ico (0 : ℝ) δ, γ₁ t ∈ S)
    (hγ₂cont : ContinuousOn γ₂ (Icc (0 : ℝ) δ))
    (hγ₂deriv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt γ₂ (f t (γ₂ t)) (Ici t) t)
    (hγ₂mem : ∀ t ∈ Ico (0 : ℝ) δ, γ₂ t ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) δ, dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ 0) (γ₂ 0) * exp (K * t) := by
  intro t ht
  have h := dist_le_of_trajectories_ODE_of_mem
    (v := f) (s := fun _ => S) (K := K) (f := γ₁) (g := γ₂)
    hlip hγ₁cont hγ₁deriv hγ₁mem hγ₂cont hγ₂deriv hγ₂mem (le_refl _) t ht
  simpa [sub_zero] using h

omit [NormedSpace ℝ E] [CompleteSpace E] in

theorem forward_flow_jointContinuousOn
    {Φ : E → ℝ → E} {x₀ : E} {r : ℝ} {K : ℝ≥0} {δ : ℝ}
    (hcont_t : ∀ x ∈ closedBall x₀ r, ContinuousOn (fun s : ℝ => Φ x s) (Icc (0 : ℝ) δ))
    (hlip_x : ∀ s ∈ Icc (0 : ℝ) δ, LipschitzOnWith K (fun x : E => Φ x s) (closedBall x₀ r)) :
    ContinuousOn (fun p : E × ℝ => Φ p.1 p.2) (closedBall x₀ r ×ˢ Icc (0 : ℝ) δ) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith
    (fun p : E × ℝ => Φ p.1 p.2) K hcont_t hlip_x

omit [NormedSpace ℝ E] [CompleteSpace E] in

theorem forward_orbit_jointContinuousAt_zero
    {Φ : E → ℝ → E} {x₀ : E} {r : ℝ} {K : ℝ≥0} {δ : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hcont_t : ∀ x ∈ closedBall x₀ r, ContinuousOn (fun s : ℝ => Φ x s) (Icc (0 : ℝ) δ))
    (hlip_x : ∀ s ∈ Icc (0 : ℝ) δ, LipschitzOnWith K (fun x : E => Φ x s) (closedBall x₀ r)) :
    ContinuousWithinAt (fun p : E × ℝ => Φ p.1 p.2)
      (closedBall x₀ r ×ˢ Icc (0 : ℝ) δ) (x₀, 0) := by
  have hjoint := forward_flow_jointContinuousOn hcont_t hlip_x
  have hmem : ((x₀, 0) : E × ℝ) ∈ closedBall x₀ r ×ˢ Icc (0 : ℝ) δ :=
    ⟨Metric.mem_closedBall_self hr, ⟨le_rfl, hδ⟩⟩
  exact hjoint (x₀, 0) hmem

section Operator

variable {A : ℝ → (E →L[ℝ] E)} {M δ : ℝ}

omit [CompleteSpace E] in

lemma hasDerivWithinAt_Ici_of_Ici_zero {y : ℝ → E} {y' : E} {τ : ℝ}
    (h : HasDerivWithinAt y y' (Ici (0 : ℝ)) τ) (hτ : 0 ≤ τ) :
    HasDerivWithinAt y y' (Ici τ) τ :=
  h.mono (fun _ hs => le_trans hτ hs)

noncomputable def fwdVariationalSolutionFun
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M) :
    E → ℝ → E :=
  fun J₀ => (forward_variational_solution_from_zero hδ hM hMδ hAcont hAbd J₀).choose

lemma fwdVariationalSolutionFun_spec
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M) (J₀ : E) :
    (fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀) 0 = J₀ ∧
      ContinuousOn (fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀) (Icc (0 : ℝ) δ) ∧
      ∀ t ∈ Ico (0 : ℝ) δ,
        HasDerivWithinAt (fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀)
          ((A t) ((fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀) t)) (Ici (0 : ℝ)) t :=
  (forward_variational_solution_from_zero hδ hM hMδ hAcont hAbd J₀).choose_spec

lemma fwdVariationalSolutionFun_linear
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    (c₁ c₂ : ℝ) (J₁ J₂ : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) δ) :
    fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd (c₁ • J₁ + c₂ • J₂) t
      = c₁ • fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₁ t
        + c₂ • fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₂ t := by
  set F := fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd with hF
  obtain ⟨h1_0, h1_cont, h1_d⟩ := fwdVariationalSolutionFun_spec hδ hM hMδ hAcont hAbd J₁
  obtain ⟨h2_0, h2_cont, h2_d⟩ := fwdVariationalSolutionFun_spec hδ hM hMδ hAcont hAbd J₂
  obtain ⟨h12_0, h12_cont, h12_d⟩ :=
    fwdVariationalSolutionFun_spec hδ hM hMδ hAcont hAbd (c₁ • J₁ + c₂ • J₂)
  set L : ℝ → E := fun s => c₁ • F J₁ s + c₂ • F J₂ s with hL
  have hL_cont : ContinuousOn L (Icc (0 : ℝ) δ) :=
    (h1_cont.const_smul c₁).add (h2_cont.const_smul c₂)
  have hL_deriv : ∀ t ∈ Ico (0 : ℝ) δ, HasDerivWithinAt L ((A t) (L t)) (Ici t) t := by
    intro t ht
    have hd1 := hasDerivWithinAt_Ici_of_Ici_zero (h1_d t ht) ht.1
    have hd2 := hasDerivWithinAt_Ici_of_Ici_zero (h2_d t ht) ht.1
    have hcomb := (hd1.const_smul c₁).add (hd2.const_smul c₂)
    have heq : c₁ • (A t) (F J₁ t) + c₂ • (A t) (F J₂ t) = (A t) (L t) := by
      rw [hL]; simp only; rw [map_add, map_smul, map_smul]
    rw [heq] at hcomb
    exact hcomb
  have h12_d' : ∀ t ∈ Ico (0 : ℝ) δ,
      HasDerivWithinAt (F (c₁ • J₁ + c₂ • J₂))
        ((A t) (F (c₁ • J₁ + c₂ • J₂) t)) (Ici t) t :=
    fun t ht => hasDerivWithinAt_Ici_of_Ici_zero (h12_d t ht) ht.1
  have hL_init : L 0 = c₁ • J₁ + c₂ • J₂ := by
    change c₁ • F J₁ 0 + c₂ • F J₂ 0 = c₁ • J₁ + c₂ • J₂
    rw [hF, h1_0, h2_0]
  have hinit :
      fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd (c₁ • J₁ + c₂ • J₂) 0 = L 0 := by
    rw [h12_0, hL_init]
  exact (forward_variational_unique hM hAbd h12_cont h12_d' hL_cont hL_deriv hinit) ht

lemma fwdVariationalSolutionFun_norm_le
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    (J₀ : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) δ) :
    ‖fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀ t‖ ≤ exp (M * δ) * ‖J₀‖ := by
  obtain ⟨h0, hcont, hd⟩ := fwdVariationalSolutionFun_spec hδ hM hMδ hAcont hAbd J₀
  have hd' : ∀ t ∈ Ico (0 : ℝ) δ,
      HasDerivWithinAt (fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀)
        ((A t) (fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀ t)) (Ici t) t :=
    fun t ht => hasDerivWithinAt_Ici_of_Ici_zero (hd t ht) ht.1
  have hbd := forward_variational_gronwall_bound hM hcont hd' hAbd h0 t ht
  rw [mul_comm] at hbd
  exact hbd

noncomputable def fwdVariationalLinearMapAt
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) δ) : E →L[ℝ] E := by
  let L : E →ₗ[ℝ] E :=
  { toFun := fun J₀ => fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀ t
    map_add' := fun J₁ J₂ => by
      have h := fwdVariationalSolutionFun_linear hδ hM hMδ hAcont hAbd 1 1 J₁ J₂ ht
      simpa using h
    map_smul' := fun c J => by
      have h := fwdVariationalSolutionFun_linear hδ hM hMδ hAcont hAbd c 0 J J ht
      have h_lhs : c • J + (0 : ℝ) • J = c • J := by simp
      have h_rhs : c • fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J t
            + (0 : ℝ) • fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J t
          = c • fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J t := by simp
      rw [h_lhs] at h; rw [h_rhs] at h; exact h }
  refine L.mkContinuous (exp (M * δ)) (fun J₀ => ?_)
  exact fwdVariationalSolutionFun_norm_le hδ hM hMδ hAcont hAbd J₀ ht

@[simp]
lemma fwdVariationalLinearMapAt_apply
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1)
    (hAcont : ContinuousOn A (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖A t‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) δ) (J₀ : E) :
    fwdVariationalLinearMapAt hδ hM hMδ hAcont hAbd ht J₀
      = fwdVariationalSolutionFun hδ hM hMδ hAcont hAbd J₀ t := rfl

end Operator

section Differentiation

open DifferentialGeometry.Analysis.ODE.Flow (gronwallBound_zero_le norm_residual_le_of_diffOn
  exists_uniform_partial_fderiv_of_contDiffOn_univ)

set_option maxHeartbeats 1600000 in

theorem forward_flow_hasFDerivAt_initial
    {f : ℝ → E → E} {Φ : E → ℝ → E} {x₀ : E} {r : ℝ} {M δ : ℝ}
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (univ : Set (ℝ × E)))
    (hδ : 0 < δ) (hM : 0 ≤ M) (hMδ : M * δ < 1) (hr : 0 < r)
    (hΦ0 : ∀ x ∈ closedBall x₀ r, Φ x 0 = x)
    (hΦcont : ∀ x ∈ closedBall x₀ r, ContinuousOn (fun s : ℝ => Φ x s) (Icc (0 : ℝ) δ))
    (hΦderiv : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Ico (0 : ℝ) δ,
      HasDerivWithinAt (fun s : ℝ => Φ x s) (f t (Φ x t)) (Ici t) t)
    (hΦlip : ∃ L' : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) δ,
      LipschitzOnWith L' (fun x : E => Φ x t) (closedBall x₀ r))
    (hAcont : ContinuousOn (fun t => fderiv ℝ (f t) (Φ x₀ t)) (Icc (0 : ℝ) δ))
    (hAbd : ∀ t ∈ Icc (0 : ℝ) δ, ‖fderiv ℝ (f t) (Φ x₀ t)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) δ) :
    HasFDerivAt (fun x => Φ x t)
      (fwdVariationalLinearMapAt (A := fun s => fderiv ℝ (f s) (Φ x₀ s))
        hδ hM hMδ hAcont hAbd ht) x₀ := by
  have hx₀_in_ball : x₀ ∈ closedBall x₀ r := Metric.mem_closedBall_self (le_of_lt hr)
  set A : ℝ → E →L[ℝ] E := fun s => fderiv ℝ (f s) (Φ x₀ s) with hA_def
  set vSol := fwdVariationalSolutionFun (A := A) hδ hM hMδ hAcont hAbd with hvSol_def
  set Lmap := fwdVariationalLinearMapAt (A := A) hδ hM hMδ hAcont hAbd ht with hLmap_def
  obtain ⟨L, hL_lip⟩ := hΦlip
  have hL_nn : (0 : ℝ) ≤ L := L.coe_nonneg
  have hΦ_lip_diff : ∀ s ∈ Icc (0 : ℝ) δ, ∀ x ∈ closedBall x₀ r,
      ‖Φ x s - Φ x₀ s‖ ≤ L * ‖x - x₀‖ := by
    intro s hs x hx
    have := (hL_lip s hs).dist_le_mul x hx x₀ hx₀_in_ball
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this
  have horbit_cont' : ContinuousOn (fun s : ℝ => Φ x₀ s) (Icc (0 : ℝ) δ) :=
    hΦcont x₀ hx₀_in_ball
  obtain ⟨δ_K, hδ_K_pos, hδ_K⟩ :=
    exists_uniform_partial_fderiv_of_contDiffOn_univ hf_C1
      (α := fun s => Φ x₀ s) horbit_cont' 1 one_pos
  set δ_K_strict : ℝ := δ_K / 2 with hδ_K_strict_def
  have hδ_K_strict_pos : 0 < δ_K_strict := by positivity
  have hδ_K_strict_lt : δ_K_strict < δ_K := by linarith
  have hK_bd : ∀ τ ∈ Icc (0 : ℝ) δ, ∀ z : E, ‖z - Φ x₀ τ‖ ≤ δ_K_strict →
      ‖fderiv ℝ (f τ) z‖ ≤ M + 1 := by
    intro τ hτ z hz
    have h_diff := hδ_K τ hτ z (lt_of_le_of_lt hz hδ_K_strict_lt)
    have hnorm_add := norm_add_le (fderiv ℝ (f τ) z - fderiv ℝ (f τ) (Φ x₀ τ))
      (fderiv ℝ (f τ) (Φ x₀ τ))
    simp at hnorm_add
    linarith [hAbd τ hτ, h_diff]
  set K_lip : ℝ := M + 1 with hK_lip_def
  have hK_lip_pos : 0 < K_lip := by have : (0 : ℝ) ≤ M := hM; linarith
  have hK_lip_nn : 0 ≤ K_lip := le_of_lt hK_lip_pos
  have hf_diff_pt : ∀ τ : ℝ, ∀ z : E, DifferentiableAt ℝ (f τ) z := by
    intro τ z
    have hDiff_joint : DifferentiableAt ℝ (uncurry f) (τ, z) :=
      (hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))).differentiableAt one_ne_zero
    have hg : DifferentiableAt ℝ (fun y : E => (τ, y)) z :=
      (differentiableAt_const τ).prodMk differentiableAt_id
    exact hDiff_joint.comp z hg
  have hf_lip_ball : ∀ τ ∈ Icc (0 : ℝ) δ,
      LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (f τ) (closedBall (Φ x₀ τ) δ_K_strict) := by
    intro τ hτ
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun z _ => hf_diff_pt τ z) ?_
      (convex_closedBall _ _)
    intro z hz
    have h_norm_le : ‖z - Φ x₀ τ‖ ≤ δ_K_strict := by
      have := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this; exact this
    change (‖fderiv ℝ (f τ) z‖₊ : ℝ≥0) ≤ ⟨K_lip, hK_lip_nn⟩
    rw [← NNReal.coe_le_coe]
    exact hK_bd τ hτ z h_norm_le
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set CE := exp (M * δ) with hCE_def
  have hCE_pos : 0 < CE := exp_pos _
  have hCE_nn : 0 ≤ CE := le_of_lt hCE_pos
  set GfactorR : ℝ := δ * exp (K_lip * δ) with hGfactorR_def
  have hGfactorR_pos : 0 < GfactorR := by
    have : 0 < exp (K_lip * δ) := exp_pos _
    positivity
  set Cmul : ℝ := GfactorR * CE + 1 with hCmul_def
  have hCmul_pos : 0 < Cmul := by
    have : 0 ≤ GfactorR * CE := mul_nonneg (le_of_lt hGfactorR_pos) hCE_nn
    linarith
  set ε_target : ℝ := c / Cmul with hε_target_def
  have hε_target_pos : 0 < ε_target := div_pos hc hCmul_pos
  have hε_target_le_one : ε_target * GfactorR * CE < c := by
    have h1 : ε_target * Cmul = c := by rw [hε_target_def]; field_simp
    have h3 : ε_target * (GfactorR * CE) < ε_target * Cmul := by
      apply mul_lt_mul_of_pos_left _ hε_target_pos
      rw [hCmul_def]; linarith
    nlinarith [h1, h3]
  obtain ⟨δ_uc, hδ_uc_pos, hδ_uc⟩ :=
    exists_uniform_partial_fderiv_of_contDiffOn_univ hf_C1
      (α := fun s => Φ x₀ s) horbit_cont' ε_target hε_target_pos
  set Lpos : ℝ := L + 1 with hLpos_def
  have hLpos_pos : 0 < Lpos := by linarith
  set CEpos : ℝ := CE + 1 with hCEpos_def
  have hCEpos_pos : 0 < CEpos := by linarith
  set δ_final : ℝ :=
    min (min (r : ℝ) (δ_K_strict / Lpos)) (min (δ_K_strict / CEpos) (δ_uc / CEpos))
      with hδ_final_def
  have hδ_final_pos : 0 < δ_final := by
    refine lt_min (lt_min hr ?_) (lt_min ?_ ?_)
    · exact div_pos hδ_K_strict_pos hLpos_pos
    · exact div_pos hδ_K_strict_pos hCEpos_pos
    · exact div_pos hδ_uc_pos hCEpos_pos
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (0 : E) δ_final, Metric.ball_mem_nhds _ hδ_final_pos, fun h hh => ?_⟩
  rw [mem_ball_zero_iff] at hh
  have hh_nn : 0 ≤ ‖h‖ := norm_nonneg _
  have hh_lt_r : ‖h‖ < r :=
    lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_left _ _)) (min_le_left _ _)
  have hh_le_r : ‖h‖ ≤ r := le_of_lt hh_lt_r
  have hxh_mem_ball : x₀ + h ∈ closedBall x₀ r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh_le_r
  have mk_bd : ∀ {coef target scale : ℝ}, 0 ≤ coef → coef ≤ scale → 0 < scale →
      ‖h‖ < target / scale → coef * ‖h‖ < target := by
    intros coef target scale hcoef_nn hcoef_le hscale_pos hbd
    have h1 : coef * ‖h‖ ≤ scale * ‖h‖ := mul_le_mul_of_nonneg_right hcoef_le hh_nn
    have h2 : scale * ‖h‖ < scale * (target / scale) := mul_lt_mul_of_pos_left hbd hscale_pos
    have h3 : scale * (target / scale) = target := by field_simp
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
  obtain ⟨hyh0, hyh_cont, hyh_d_ici0⟩ :=
    fwdVariationalSolutionFun_spec (A := A) hδ hM hMδ hAcont hAbd h
  set y_h : ℝ → E := vSol h with hy_h_def
  have hy_h_init : y_h 0 = h := hyh0
  have hy_h_cont : ContinuousOn y_h (Icc (0 : ℝ) δ) := hyh_cont
  have hy_h_d : ∀ s ∈ Ico (0 : ℝ) δ, HasDerivWithinAt y_h ((A s) (y_h s)) (Ici s) s :=
    fun s hs => hasDerivWithinAt_Ici_of_Ici_zero (hyh_d_ici0 s hs) hs.1
  have hy_h_bd : ∀ s ∈ Icc (0 : ℝ) δ, ‖y_h s‖ ≤ CE * ‖h‖ := by
    intro s hs
    have := fwdVariationalSolutionFun_norm_le (A := A) hδ hM hMδ hAcont hAbd h hs
    rw [hCE_def]; exact this
  set α_h : ℝ → E := fun s => Φ (x₀ + h) s with hα_h_def
  set β_h : ℝ → E := fun s => Φ x₀ s + y_h s with hβ_h_def
  have hα_h_init : α_h 0 = x₀ + h := hΦ0 (x₀ + h) hxh_mem_ball
  have hβ_h_init : β_h 0 = x₀ + h := by
    change Φ x₀ 0 + y_h 0 = x₀ + h
    rw [hΦ0 x₀ hx₀_in_ball, hy_h_init]
  have hα_h_cont' : ContinuousOn α_h (Icc (0 : ℝ) δ) := hΦcont (x₀ + h) hxh_mem_ball
  have hα_h_close : ∀ s ∈ Icc (0 : ℝ) δ, ‖α_h s - Φ x₀ s‖ ≤ L * ‖h‖ := by
    intro s hs
    have h1 : ‖α_h s - Φ x₀ s‖ ≤ L * ‖(x₀ + h) - x₀‖ :=
      hΦ_lip_diff s hs (x₀ + h) hxh_mem_ball
    have h2 : (x₀ + h) - x₀ = h := by abel
    rw [h2] at h1; exact h1
  have hα_h_mem_ball : ∀ s ∈ Icc (0 : ℝ) δ, α_h s ∈ closedBall (Φ x₀ s) δ_K_strict := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans (hα_h_close s hs) hh_L_bd_le
  have hβ_h_mem_ball : ∀ s ∈ Icc (0 : ℝ) δ, β_h s ∈ closedBall (Φ x₀ s) δ_K_strict := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    change ‖Φ x₀ s + y_h s - Φ x₀ s‖ ≤ δ_K_strict
    have heq : Φ x₀ s + y_h s - Φ x₀ s = y_h s := by abel
    rw [heq]; exact le_trans (hy_h_bd s hs) hh_CE_bd_le
  have hβ_h_deriv : ∀ s ∈ Ico (0 : ℝ) δ,
      HasDerivWithinAt β_h (f s (Φ x₀ s) + A s (y_h s)) (Ici s) s := by
    intro s hs
    have h1 := hΦderiv x₀ hx₀_in_ball s hs
    have h2 := hy_h_d s hs
    exact h1.add h2
  have hβ_h_cont : ContinuousOn β_h (Icc (0 : ℝ) δ) :=
    ContinuousOn.add horbit_cont' hy_h_cont
  have h_residual_bound : ∀ s ∈ Icc (0 : ℝ) δ,
      ‖f s (Φ x₀ s) + A s (y_h s) - f s (β_h s)‖ ≤ ε_target * ‖y_h s‖ := by
    intro s hs
    set ρ_seg : ℝ := CE * ‖h‖ with hρ_seg_def
    have hρ_seg_nn : 0 ≤ ρ_seg := mul_nonneg hCE_nn hh_nn
    set S_seg : Set E := closedBall (Φ x₀ s) ρ_seg with hS_seg_def
    have hS_seg_conv : Convex ℝ S_seg := convex_closedBall _ _
    have hf_diff : ∀ z ∈ S_seg, DifferentiableAt ℝ (f s) z := fun z _ => hf_diff_pt s z
    have hx_seg : Φ x₀ s ∈ S_seg := Metric.mem_closedBall_self hρ_seg_nn
    have hxv_seg : Φ x₀ s + y_h s ∈ S_seg := by
      rw [hS_seg_def, mem_closedBall, dist_eq_norm]
      change ‖Φ x₀ s + y_h s - Φ x₀ s‖ ≤ ρ_seg
      have heq : Φ x₀ s + y_h s - Φ x₀ s = y_h s := by abel
      rw [heq, hρ_seg_def]; exact hy_h_bd s hs
    have hC : ∀ z ∈ S_seg, ‖fderiv ℝ (f s) z - fderiv ℝ (f s) (Φ x₀ s)‖ ≤ ε_target := by
      intro z hz
      have h_norm_le : ‖z - Φ x₀ s‖ ≤ ρ_seg := by
        have := Metric.mem_closedBall.mp hz; rw [dist_eq_norm] at this; exact this
      have h_norm_lt : ‖z - Φ x₀ s‖ < δ_uc := lt_of_le_of_lt h_norm_le hh_CE_lt_δuc
      exact le_of_lt (hδ_uc s hs z h_norm_lt)
    have h_residual : ‖f s (Φ x₀ s + y_h s) - f s (Φ x₀ s)
        - (fderiv ℝ (f s) (Φ x₀ s)) (y_h s)‖ ≤ ε_target * ‖y_h s‖ :=
      norm_residual_le_of_diffOn s (Φ x₀ s) (y_h s) hS_seg_conv hf_diff hx_seg hxv_seg hC
    have h_eq : f s (Φ x₀ s) + A s (y_h s) - f s (β_h s)
        = -(f s (Φ x₀ s + y_h s) - f s (Φ x₀ s) - (fderiv ℝ (f s) (Φ x₀ s)) (y_h s)) := by
      change f s (Φ x₀ s) + (fderiv ℝ (f s) (Φ x₀ s)) (y_h s) - f s (Φ x₀ s + y_h s)
          = -(f s (Φ x₀ s + y_h s) - f s (Φ x₀ s) - (fderiv ℝ (f s) (Φ x₀ s)) (y_h s))
      abel
    rw [h_eq, norm_neg]; exact h_residual
  set s_set : ℝ → Set E := fun τ => closedBall (Φ x₀ τ) δ_K_strict with hs_set_def
  have h_diff_right : ∀ τ ∈ Icc (0 : ℝ) δ,
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    have hv_lip : ∀ τ ∈ Ico (0 : ℝ) δ,
        LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (f τ) (s_set τ) := fun τ hτ =>
      hf_lip_ball τ ⟨hτ.1, le_of_lt hτ.2⟩
    have hα_h_deriv_R : ∀ τ ∈ Ico (0 : ℝ) δ,
        HasDerivWithinAt α_h (f τ (α_h τ)) (Ici τ) τ :=
      fun τ hτR => hΦderiv (x₀ + h) hxh_mem_ball τ hτR
    have hf_bound : ∀ τ ∈ Ico (0 : ℝ) δ, dist (f τ (α_h τ)) (f τ (α_h τ)) ≤ 0 := by
      intro _ _; rw [dist_self]
    have hfs : ∀ τ ∈ Ico (0 : ℝ) δ, α_h τ ∈ s_set τ :=
      fun τ hτR => hα_h_mem_ball τ ⟨hτR.1, le_of_lt hτR.2⟩
    set εg : ℝ := ε_target * CE * ‖h‖ with hεg_def
    have hεg_nn : 0 ≤ εg := by
      have : 0 ≤ ε_target * CE := mul_nonneg (le_of_lt hε_target_pos) hCE_nn
      exact mul_nonneg this hh_nn
    have hg_bound : ∀ τ ∈ Ico (0 : ℝ) δ,
        dist (f τ (Φ x₀ τ) + A τ (y_h τ)) (f τ (β_h τ)) ≤ εg := by
      intro τ hτR
      have hτ_sub : τ ∈ Icc (0 : ℝ) δ := ⟨hτR.1, le_of_lt hτR.2⟩
      have h_res := h_residual_bound τ hτ_sub
      have h_ybd := hy_h_bd τ hτ_sub
      have h_combine : ε_target * ‖y_h τ‖ ≤ εg := by
        rw [hεg_def, mul_assoc]
        exact mul_le_mul_of_nonneg_left h_ybd (le_of_lt hε_target_pos)
      rw [dist_eq_norm]; exact le_trans h_res h_combine
    have hgs : ∀ τ ∈ Ico (0 : ℝ) δ, β_h τ ∈ s_set τ :=
      fun τ hτR => hβ_h_mem_ball τ ⟨hτR.1, le_of_lt hτR.2⟩
    have ha_init : dist (α_h 0) (β_h 0) ≤ 0 := by
      rw [hα_h_init, hβ_h_init, dist_self]
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (v := f) (s := s_set) (K := ⟨K_lip, hK_lip_nn⟩)
      (f := α_h) (g := β_h) (f' := fun τ => f τ (α_h τ))
      (g' := fun τ => f τ (Φ x₀ τ) + A τ (y_h τ))
      (εf := 0) (εg := εg) (δ := 0)
      hv_lip hα_h_cont' hα_h_deriv_R hf_bound hfs
      hβ_h_cont hβ_h_deriv hg_bound hgs ha_init τ hτ
    rw [dist_eq_norm] at hG
    rw [zero_add] at hG
    have hτ_nn : 0 ≤ τ - 0 := by simp [hτ.1]
    have hτ_le : τ - 0 ≤ δ := by simp [hτ.2]
    have h_GB := gronwallBound_zero_le (K := K_lip) (ε := εg) (x := τ - 0)
      hK_lip_pos hεg_nn hτ_nn
    have h_mono : εg * (τ - 0) * exp (K_lip * (τ - 0)) ≤ εg * δ * exp (K_lip * δ) := by
      have h1 : εg * (τ - 0) ≤ εg * δ := mul_le_mul_of_nonneg_left hτ_le hεg_nn
      have h2 : exp (K_lip * (τ - 0)) ≤ exp (K_lip * δ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ_le hK_lip_nn)
      exact mul_le_mul h1 h2 (le_of_lt (exp_pos _)) (mul_nonneg hεg_nn (le_of_lt hδ))
    have h_GB' : gronwallBound 0 K_lip εg (τ - 0) ≤ εg * δ * exp (K_lip * δ) :=
      le_trans h_GB h_mono
    have h_eq_factor : εg * δ * exp (K_lip * δ) = GfactorR * εg := by
      rw [hGfactorR_def]; ring
    rw [h_eq_factor] at h_GB'
    exact le_trans hG h_GB'
  have h_final_bd : ‖α_h t - β_h t‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := h_diff_right t ht
  have h_lhs : α_h t - β_h t = Φ (x₀ + h) t - Φ x₀ t - Lmap h := by
    change Φ (x₀ + h) t - (Φ x₀ t + y_h t) = _
    have : Lmap h = vSol h t := rfl
    rw [this]; abel
  rw [h_lhs] at h_final_bd
  have h_bound_le : GfactorR * (ε_target * CE * ‖h‖) ≤ c * ‖h‖ := by
    have h1 : GfactorR * (ε_target * CE * ‖h‖) = (ε_target * GfactorR * CE) * ‖h‖ := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (le_of_lt hε_target_le_one) hh_nn
  have h_goal_eq :
      (fun x => Φ x t) (x₀ + h) - (fun x => Φ x t) x₀ - Lmap h
        = Φ (x₀ + h) t - Φ x₀ t - Lmap h := rfl
  rw [h_goal_eq]
  exact le_trans h_final_bd h_bound_le

end Differentiation

end DifferentialGeometry.Analysis.ODE
