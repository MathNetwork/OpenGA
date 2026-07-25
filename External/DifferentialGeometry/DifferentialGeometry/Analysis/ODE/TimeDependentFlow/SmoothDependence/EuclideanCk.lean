import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.VariationalMapContDiffOnK
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

theorem linearizationNorm_continuousOn_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {ε : ℝ} {Φ : E × ℝ → E}
    (hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)))
    (horbit : ContinuousOn (fun q : E × ℝ => (q.2, Φ q))
      (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε))) :
    ContinuousOn (fun q : E × ℝ => ‖fderiv ℝ (f q.2) (Φ q)‖)
      (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε)) := by
  have hfull :
      ContinuousOn (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
        (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε)) :=
    hpartial.comp horbit (fun _ _ => Set.mem_univ _)
  exact continuous_norm.comp_continuousOn hfull

theorem exists_uniform_norm_fderiv_le_on_flow_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {ε : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ)
    (hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Metric.closedBall x₀ (r : ℝ), ∀ τ ∈ Set.Icc (t₀ - ε) (t₀ + ε),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
  set B : Set (E × ℝ) := Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε) with hB
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := DifferentialGeometry.Analysis.ODE.continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have horbit : ContinuousOn (fun q : E × ℝ => (q.2, Φ q)) B :=
    continuousOn_snd.prodMk hΦ.continuousOn
  have hnorm : ContinuousOn (fun q : E × ℝ => ‖fderiv ℝ (f q.2) (Φ q)‖) B :=
    linearizationNorm_continuousOn_box hpartial horbit
  have hK : IsCompact B :=
    (ProperSpace.isCompact_closedBall x₀ (r : ℝ)).prod isCompact_Icc
  have hne : B.Nonempty :=
    ⟨⟨x₀, t₀⟩, Set.mem_prod.mpr
      ⟨Metric.mem_closedBall_self r.coe_nonneg,
       Set.mem_Icc.mpr ⟨hΦ.htmin_le, hΦ.ht₀_le⟩⟩⟩
  obtain ⟨q₀, _, hq₀_max⟩ := hK.exists_isMaxOn hne hnorm
  refine ⟨‖fderiv ℝ (f q₀.2) (Φ q₀)‖, norm_nonneg _, fun x hx τ hτ => ?_⟩
  exact hq₀_max (show (x, τ) ∈ B from ⟨hx, hτ⟩)

theorem isVariationalFlowProjection_mono_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}
    {hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ}
    {T T' : ℝ} {ρ ρ' : ℝ≥0} {Y : E × ℝ → (E →L[ℝ] E)} {k : ℕ∞}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k)
    (hT' : T' ≤ T) (hρ' : (ρ' : ℝ) ≤ (ρ : ℝ)) :
    IsVariationalFlowProjection hΦ T' ρ' Y k := by
  have hbox :
      (Metric.ball x₀ (ρ' : ℝ)) ×ˢ Set.Ioo (t₀ - T') (t₀ + T') ⊆
        (Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T) :=
    Set.prod_mono (Metric.ball_subset_ball hρ')
      (Set.Ioo_subset_Ioo (by linarith) (by linarith))
  exact
    { contDiffOn := hY.contDiffOn.mono hbox
      fderiv_eq := fun q hq => hY.fderiv_eq q (hbox hq) }

theorem exists_isLocalFlow_contDiffOn_Ck
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {k : ℕ∞} (hk : 1 ≤ k)
    (hf : ContDiff ℝ k (Function.uncurry f)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < (r : ℝ)) (_ : 0 < ε) (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ ∧
      ∃ (ρ : ℝ) (T : ℝ), 0 < ρ ∧ 0 < T ∧ ρ ≤ (r : ℝ) ∧ T ≤ ε ∧
        ContDiffOn ℝ k Φ (Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
  induction k using ENat.recTopCoe with
  | top =>
    exact exists_isLocalFlow_contDiffOn_top (f := f) (t₀ := t₀) (x₀ := x₀) hf
  | coe n =>
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by
      have : 1 ≤ n := by exact_mod_cast hk
      omega⟩
    have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
      apply hf.contDiffOn.of_le
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)
    have hf_Ck : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞) (Function.uncurry f)
        (Set.univ : Set (ℝ × E)) := hf.contDiffOn
    have hf_C : ContDiffOn ℝ ((m : ℕ∞) + 1) (Function.uncurry f)
        (Set.univ : Set (ℝ × E)) := by
      have hcast : ((m : ℕ∞) + 1 : WithTop ℕ∞) = (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
        push_cast; ring
      rw [hcast]; exact hf_Ck
    obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
      exists_isLocalFlow_of_contDiffOn_univ f hf_C1 t₀ x₀
    have hrN_pos : (0 : ℝ) < (rN : ℝ) := hrN
    have ht₀_Ioo : t₀ ∈ Set.Ioo (t₀ - εN) (t₀ + εN) := ⟨by linarith, by linarith⟩
    obtain ⟨T_Y, ρ_Y, hT_Y, hρ_Y, Y, hY_raw⟩ :=
      exists_isVariationalFlowProjection_of_C hΦ ht₀_Ioo hrN_pos m hf_C
    obtain ⟨Mglob, hMglob_nn, hMglob_bound⟩ :=
      exists_uniform_norm_fderiv_le_on_flow_box hΦ hf_C1
    set Tcap : ℝ := min εN (min (1 / (2 * (Mglob + 1))) (2 * T_Y)) with hTcap_def
    have hTcap_pos : 0 < Tcap := lt_min hεN (lt_min (by positivity) (by linarith))
    set T_out : ℝ := Tcap / 2
    set T_mid : ℝ := Tcap / 4
    set T : ℝ := Tcap / 8
    have hT_pos : 0 < T := by change 0 < Tcap / 8; linarith
    have hT_lt_mid : T < T_mid := by change Tcap / 8 < Tcap / 4; linarith
    have hT_mid_lt_out : T_mid < T_out := by change Tcap / 4 < Tcap / 2; linarith
    have hTcap_le_eps : Tcap ≤ εN := min_le_left _ _
    have hT_out_le_eps : T_out ≤ εN := by change Tcap / 2 ≤ εN; linarith
    have hTcap_le_inner : Tcap ≤ min (1 / (2 * (Mglob + 1))) (2 * T_Y) := min_le_right _ _
    have hTcap_le_M : Tcap ≤ 1 / (2 * (Mglob + 1)) :=
      le_trans hTcap_le_inner (min_le_left _ _)
    have hTcap_le_TY : Tcap ≤ 2 * T_Y := le_trans hTcap_le_inner (min_le_right _ _)
    have hT_le_TY : T ≤ T_Y := by change Tcap / 8 ≤ T_Y; linarith
    have hMT_mid_lt_one : Mglob * T_mid < 1 := by
      have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
        change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
        have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
          field_simp; ring
        linarith
      have hMplus_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
      calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) :=
              mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
        _ = Mglob / (8 * (Mglob + 1)) := by ring
        _ ≤ 1 / 8 := by
              rw [div_le_div_iff₀ hMplus_pos (by norm_num : (0 : ℝ) < 8)]
              nlinarith [hMglob_nn]
        _ < 1 := by norm_num
    have hsub_T_out : Set.Icc (t₀ - T_out) (t₀ + T_out) ⊆ Set.Icc (t₀ - εN) (t₀ + εN) :=
      Set.Icc_subset_Icc (by linarith) (by linarith)
    set R₀ : ℝ := min (rN : ℝ) (ρ_Y : ℝ) with hR₀_def
    have hR₀_pos : 0 < R₀ := lt_min hrN_pos hρ_Y
    have hR₀_le_rN : R₀ ≤ (rN : ℝ) := min_le_left _ _
    have hR₀_le_ρY : R₀ ≤ (ρ_Y : ℝ) := min_le_right _ _
    set ρ_out : ℝ≥0 := ⟨R₀ / 2, by positivity⟩
    set ρ_mid : ℝ≥0 := ⟨R₀ / 4, by positivity⟩
    set ρ : ℝ≥0 := ⟨R₀ / 8, by positivity⟩
    set r' : ℝ≥0 := ⟨R₀ / 8, by positivity⟩
    have hr'_pos : 0 < r' := by change (0 : ℝ) < R₀ / 8; linarith
    have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by change (0 : ℝ) < R₀ / 8; linarith
    have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by change R₀ / 8 < R₀ / 4; linarith
    have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by change R₀ / 4 < R₀ / 2; linarith
    have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
      change R₀ / 4 + R₀ / 8 ≤ (rN : ℝ); linarith
    have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by change R₀ / 2 ≤ (rN : ℝ); linarith
    have hρ_le_ρY : (ρ : ℝ) ≤ (ρ_Y : ℝ) := by change R₀ / 8 ≤ (ρ_Y : ℝ); linarith
    have hA_bd : ∀ x ∈ Metric.closedBall x₀ (ρ_out : ℝ),
        ∀ τ ∈ Set.Icc (t₀ - T_out) (t₀ + T_out),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ Mglob := by
      intro x hx τ hτ
      exact hMglob_bound x (Metric.closedBall_subset_closedBall hρ_out_le_r hx) τ
        (hsub_T_out hτ)
    have hY : IsVariationalFlowProjection hΦ T ρ Y (m : ℕ∞) :=
      isVariationalFlowProjection_mono_box hY_raw hT_le_TY hρ_le_ρY
    have hYlevel : IsVariationalFlowProjection hΦ T ρ Y (((m + 1) - 1 : ℕ) : ℕ∞) := by
      have hmm : ((m + 1) - 1 : ℕ) = m := by omega
      rw [hmm]; exact hY
    have hSmooth :
        ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞) Φ
          ((Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) :=
      contDiffOn_flow_of_isVariationalFlowProjection_top hΦ hT_pos hT_lt_mid hT_mid_lt_out
        hMglob_nn hMT_mid_lt_one hsub_T_out hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r
        hA_bd (m + 1) (by omega) hf_Ck hYlevel
    refine ⟨rN, εN, hrN, hεN, Φ, hΦ, (ρ : ℝ), T, hρ_pos, hT_pos, ?_, ?_, hSmooth⟩
    · change R₀ / 8 ≤ (rN : ℝ); linarith
    · change Tcap / 8 ≤ εN; linarith

end DifferentialGeometry.PDE.RicciFlow.ODE
