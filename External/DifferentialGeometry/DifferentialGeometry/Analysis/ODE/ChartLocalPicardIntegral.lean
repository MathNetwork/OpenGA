import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import DifferentialGeometry.Analysis.ODE.IntegralGronwall

open MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem ode_right_solution_ftc_integral
    {γ : ℝ → E} {v : ℝ → E} {T : ℝ}
    (hγcont : ContinuousOn γ (Set.Icc 0 T))
    (hγderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt γ (v t) (Set.Ici (0 : ℝ)) t)
    (hvcont : ContinuousOn v (Set.Icc 0 T)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, γ s = γ 0 + ∫ r in (0 : ℝ)..s, v r := by
  intro s hs
  have hsT : s ≤ T := hs.2
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hγcont_s : ContinuousOn γ (Set.Icc 0 s) :=
    hγcont.mono (Set.Icc_subset_Icc le_rfl hsT)
  have hderiv_right : ∀ x ∈ Set.Ioo (0 : ℝ) s, HasDerivWithinAt γ (v x) (Set.Ioi x) x := by
    intro x hx
    have hxIco : x ∈ Set.Ico (0 : ℝ) T :=
      ⟨le_of_lt hx.1, lt_of_lt_of_le hx.2 hsT⟩
    have hsub : Set.Ioi x ⊆ Set.Ici (0 : ℝ) := fun y hy =>
      le_of_lt (lt_of_le_of_lt (le_of_lt hx.1) hy)
    exact (hγderiv x hxIco).mono hsub
  have hint : IntervalIntegrable v volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs0]
    exact hvcont.mono (Set.Icc_subset_Icc le_rfl hsT)
  have hftc : ∫ r in (0 : ℝ)..s, v r = γ s - γ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs0 hγcont_s hderiv_right hint
  rw [hftc]; abel

theorem ode_field_ftc_integral
    {γ : ℝ → E} {f : ℝ → E → E} {T : ℝ}
    (hγcont : ContinuousOn γ (Set.Icc 0 T))
    (hγderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ (f t (γ t)) (Set.Ici (0 : ℝ)) t)
    (hfcont : ContinuousOn (fun r : ℝ => f r (γ r)) (Set.Icc 0 T)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, γ s = γ 0 + ∫ r in (0 : ℝ)..s, f r (γ r) :=
  ode_right_solution_ftc_integral hγcont hγderiv hfcont

theorem linear_ode_variational_integral
    {J : ℝ → E} {A : ℝ → (E →L[ℝ] E)} {T : ℝ}
    (hJcont : ContinuousOn J (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hJderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt J (A t (J t)) (Set.Ici (0 : ℝ)) t) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, J s = J 0 + ∫ r in (0 : ℝ)..s, A r (J r) :=
  ode_right_solution_ftc_integral hJcont hJderiv (hAcont.clm_apply hJcont)

omit [CompleteSpace E] in

theorem variational_jacobian_gronwall_bound
    {J : ℝ → E} {A : ℝ → (E →L[ℝ] E)} {T CA : ℝ} (hT : 0 ≤ T) (hCA : 0 ≤ CA)
    (hJcont : ContinuousOn J (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAbound : ∀ r ∈ Set.Icc (0 : ℝ) T, ‖A r‖ ≤ CA)
    (hJint : ∀ s ∈ Set.Icc (0 : ℝ) T, J s = J 0 + ∫ r in (0 : ℝ)..s, A r (J r)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ‖J s‖ ≤ ‖J 0‖ * Real.exp (CA * s) := by
  set f : ℝ → ℝ := fun s => ‖J s‖ with hf_def
  have hf_cont : ContinuousOn f (Set.Icc 0 T) := hJcont.norm
  have hf_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ f t := fun t _ => norm_nonneg _
  have hAfJ_cont : ContinuousOn (fun r : ℝ => A r (J r)) (Set.Icc 0 T) :=
    hAcont.clm_apply hJcont
  have hf_int : ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ ‖J 0‖ + CA * ∫ τ in (0:ℝ)..t, f τ := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have hJt : J t = J 0 + ∫ r in (0 : ℝ)..t, A r (J r) := hJint t ht
    have hstep1 : f t ≤ ‖J 0‖ + ‖∫ r in (0 : ℝ)..t, A r (J r)‖ := by
      rw [hf_def]; dsimp only; rw [hJt]; exact norm_add_le _ _
    have hint_AfJ : IntervalIntegrable (fun r : ℝ => A r (J r)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht0]
      exact hAfJ_cont.mono (Set.Icc_subset_Icc le_rfl ht.2)
    have hnormint : ‖∫ r in (0 : ℝ)..t, A r (J r)‖ ≤ ∫ r in (0:ℝ)..t, ‖A r (J r)‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht0
    have hint_normAfJ : IntervalIntegrable (fun r : ℝ => ‖A r (J r)‖) volume 0 t :=
      hint_AfJ.norm
    have hint_CAf : IntervalIntegrable (fun r : ℝ => CA * f r) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht0]
      exact continuous_const.continuousOn.mul (hf_cont.mono (Set.Icc_subset_Icc le_rfl ht.2))
    have hmono : (∫ r in (0:ℝ)..t, ‖A r (J r)‖) ≤ ∫ r in (0:ℝ)..t, CA * f r := by
      refine intervalIntegral.integral_mono_on ht0 hint_normAfJ hint_CAf ?_
      intro r hr
      have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, le_trans hr.2 ht.2⟩
      calc ‖A r (J r)‖ ≤ ‖A r‖ * ‖J r‖ := (A r).le_opNorm _
        _ ≤ CA * ‖J r‖ := mul_le_mul_of_nonneg_right (hAbound r hrT) (norm_nonneg _)
        _ = CA * f r := rfl
    have hconstmul : (∫ r in (0:ℝ)..t, CA * f r) = CA * ∫ r in (0:ℝ)..t, f r :=
      intervalIntegral.integral_const_mul CA f
    calc f t ≤ ‖J 0‖ + ‖∫ r in (0 : ℝ)..t, A r (J r)‖ := hstep1
      _ ≤ ‖J 0‖ + ∫ r in (0:ℝ)..t, ‖A r (J r)‖ := by gcongr
      _ ≤ ‖J 0‖ + ∫ r in (0:ℝ)..t, CA * f r := by gcongr
      _ = ‖J 0‖ + CA * ∫ r in (0:ℝ)..t, f r := by rw [hconstmul]
  exact gronwall_integral_le hT (norm_nonneg _) hCA hf_cont hf_nn hf_int
theorem ode_right_ftc
    {γ : ℝ → E} {v : ℝ → E} {T : ℝ}
    (hγcont : ContinuousOn γ (Set.Icc 0 T))
    (hγderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ (v t) (Set.Ici t) t)
    (hvcont : ContinuousOn v (Set.Icc 0 T)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, γ s = γ 0 + ∫ r in (0 : ℝ)..s, v r := by
  intro s hs
  have hγcont_s : ContinuousOn γ (Set.Icc 0 s) :=
    hγcont.mono (Set.Icc_subset_Icc le_rfl hs.2)
  have hderiv_right : ∀ x ∈ Set.Ioo (0 : ℝ) s,
      HasDerivWithinAt γ (v x) (Set.Ioi x) x := by
    intro x hx
    have hxIco : x ∈ Set.Ico (0 : ℝ) T :=
      ⟨hx.1.le, hx.2.trans_le hs.2⟩
    exact (hγderiv x hxIco).mono Set.Ioi_subset_Ici_self
  have hint : IntervalIntegrable v volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs.1]
    exact hvcont.mono (Set.Icc_subset_Icc le_rfl hs.2)
  have hftc : ∫ r in (0 : ℝ)..s, v r = γ s - γ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1 hγcont_s
      hderiv_right hint
  rw [hftc]
  abel


end DifferentialGeometry.Analysis.ODE
