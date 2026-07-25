import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false















namespace DifferentialGeometry

open Set MeasureTheory intervalIntegral
open scoped ContDiff



theorem exists_smooth_clamp (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t ∈ Set.Icc a b, ψ t = t) ∧
      ∀ t : ℝ, |ψ t| ≤ b - a + 2 := by
  classical
  set c : ℝ := (a + b) / 2 with hc
  have hrIn_pos : 0 < (b - a) / 2 := by linarith
  set χb : ContDiffBump c :=
    { rIn := (b - a) / 2
      rOut := (b - a) / 2 + 1
      rIn_pos := hrIn_pos
      rIn_lt_rOut := by linarith } with hχb
  have hrIn_eq : χb.rIn = (b - a) / 2 := rfl
  have hrOut_eq : χb.rOut = (b - a) / 2 + 1 := rfl
  set χ : ℝ → ℝ := fun u => χb u with hχ
  have hχ_cont : Continuous χ := χb.continuous
  have hχ_int : ∀ s t : ℝ, IntervalIntegrable χ volume s t :=
    fun s t => hχ_cont.intervalIntegrable s t
  have h1_int : ∀ s t : ℝ, IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume s t :=
    fun s t => continuous_const.intervalIntegrable s t
  have hχ_nonneg : ∀ u : ℝ, 0 ≤ χ u := fun u => χb.nonneg
  have hχ_le_one : ∀ u : ℝ, χ u ≤ 1 := fun u => χb.le_one
  have hχ_one : ∀ u ∈ Set.Icc a b, χ u = 1 := by
    intro u hu
    refine χb.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, hrIn_eq, abs_le, hc]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hχ_zero_right : ∀ u : ℝ, b + 1 ≤ u → χ u = 0 := by
    intro u hu
    have hnot : u ∉ Function.support χ := by
      rw [show Function.support χ = Metric.ball c χb.rOut from χb.support_eq]
      rw [Metric.mem_ball, Real.dist_eq, not_lt, hrOut_eq]
      have h1 : (b - a) / 2 + 1 ≤ u - c := by rw [hc]; linarith
      exact h1.trans (le_abs_self _)
    exact Function.notMem_support.mp hnot
  have hχ_zero_left : ∀ u : ℝ, u ≤ a - 1 → χ u = 0 := by
    intro u hu
    have hnot : u ∉ Function.support χ := by
      rw [show Function.support χ = Metric.ball c χb.rOut from χb.support_eq]
      rw [Metric.mem_ball, Real.dist_eq, not_lt, hrOut_eq]
      have h1 : (b - a) / 2 + 1 ≤ -(u - c) := by rw [hc]; linarith
      exact h1.trans (neg_le_abs _)
    exact Function.notMem_support.mp hnot
  set ψ : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, χ u with hψ
  have hψ_sderiv : ∀ t : ℝ, HasStrictDerivAt ψ (χ t) t :=
    fun t => hχ_cont.integral_hasStrictDerivAt 0 t
  have hψ_diff : Differentiable ℝ ψ :=
    fun t => (hψ_sderiv t).hasDerivAt.differentiableAt
  have hψ_deriv : deriv ψ = χ := funext fun t => (hψ_sderiv t).hasDerivAt.deriv
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    refine contDiff_infty_iff_deriv.mpr ⟨hψ_diff, ?_⟩
    rw [hψ_deriv]
    exact χb.contDiff

  have hψ_id : ∀ t ∈ Set.Icc a b, ψ t = t := by
    intro t ht
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨ha.le, hb.le⟩ ⟨ht.1, ht.2⟩
    have hcongr : Set.EqOn χ (fun _ : ℝ => (1 : ℝ)) (Set.uIcc 0 t) :=
      fun u hu => hχ_one u (hsub hu)
    rw [hψ]
    simp only
    rw [intervalIntegral.integral_congr hcongr]
    simp

  have hψ_le_pos : ∀ t : ℝ, 0 ≤ t → ψ t ≤ t := by
    intro t ht
    have hmono := intervalIntegral.integral_mono_on (μ := volume) ht (hχ_int 0 t) (h1_int 0 t)
      (fun u _ => hχ_le_one u)
    rw [hψ]
    simp only
    calc ∫ u in (0 : ℝ)..t, χ u ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) := hmono
      _ = t := by simp
  have hψ_nonneg_pos : ∀ t : ℝ, 0 ≤ t → 0 ≤ ψ t := by
    intro t ht
    rw [hψ]
    simp only
    exact intervalIntegral.integral_nonneg ht (fun u _ => hχ_nonneg u)
  have hψ_nonpos_neg : ∀ t : ℝ, t ≤ 0 → ψ t ≤ 0 := by
    intro t ht
    rw [hψ]
    simp only
    rw [intervalIntegral.integral_symm]
    have h0 : 0 ≤ ∫ u in t..(0 : ℝ), χ u :=
      intervalIntegral.integral_nonneg ht (fun u _ => hχ_nonneg u)
    linarith
  have hψ_ge_neg : ∀ t : ℝ, t ≤ 0 → t ≤ ψ t := by
    intro t ht
    have hmono := intervalIntegral.integral_mono_on (μ := volume) ht (hχ_int t 0) (h1_int t 0)
      (fun u _ => hχ_le_one u)
    have h1 : (∫ _ in t..(0 : ℝ), (1 : ℝ)) = -t := by simp
    rw [hψ]
    simp only
    rw [intervalIntegral.integral_symm]
    have h2 : (∫ u in t..(0 : ℝ), χ u) ≤ -t := by rw [← h1]; exact hmono
    linarith
  have hψ_ub : ∀ t : ℝ, ψ t ≤ b + 1 := by
    intro t
    by_cases htb : t ≤ b + 1
    · by_cases ht0 : 0 ≤ t
      · exact (hψ_le_pos t ht0).trans htb
      · exact (hψ_nonpos_neg t (not_le.mp ht0).le).trans (by linarith)
    · push Not at htb
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hχ_int 0 (b + 1)) (hχ_int (b + 1) t)
      have hzero : (∫ u in (b + 1)..t, χ u) = 0 := by
        have hcongr : Set.EqOn χ (fun _ : ℝ => (0 : ℝ)) (Set.uIcc (b + 1) t) := by
          intro u hu
          have hmin : b + 1 ≤ u := by
            have := hu.1
            rw [Set.uIcc_of_le htb.le] at hu
            exact hu.1
          exact hχ_zero_right u hmin
        rw [intervalIntegral.integral_congr hcongr]
        simp
      have hval : ψ t = ψ (b + 1) := by
        rw [hψ]
        simp only
        rw [← hadd, hzero, add_zero]
      rw [hval]
      exact hψ_le_pos (b + 1) (by linarith)
  have hψ_lb : ∀ t : ℝ, a - 1 ≤ ψ t := by
    intro t
    by_cases hta : a - 1 ≤ t
    · by_cases ht0 : t ≤ 0
      · exact (hψ_ge_neg t ht0).trans' hta
      · exact (hψ_nonneg_pos t (not_le.mp ht0).le).trans' (by linarith)
    · push Not at hta
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hχ_int 0 (a - 1)) (hχ_int (a - 1) t)
      have hzero : (∫ u in (a - 1)..t, χ u) = 0 := by
        have hcongr : Set.EqOn χ (fun _ : ℝ => (0 : ℝ)) (Set.uIcc (a - 1) t) := by
          intro u hu
          have hmax : u ≤ a - 1 := by
            rw [Set.uIcc_of_ge hta.le] at hu
            exact hu.2
          exact hχ_zero_left u hmax
        rw [intervalIntegral.integral_congr hcongr]
        simp
      have hval : ψ t = ψ (a - 1) := by
        rw [hψ]
        simp only
        rw [← hadd, hzero, add_zero]
      rw [hval]
      exact hψ_ge_neg (a - 1) (by linarith)
  refine ⟨ψ, hψ_smooth, hψ_id, fun t => ?_⟩
  rw [abs_le]
  exact ⟨by linarith [hψ_lb t], by linarith [hψ_ub t]⟩

end DifferentialGeometry
