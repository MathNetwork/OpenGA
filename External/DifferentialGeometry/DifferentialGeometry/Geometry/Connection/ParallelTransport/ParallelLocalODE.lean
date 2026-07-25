import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.Basic
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.OneForm
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.TwoTensor
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic


omit [NeZero (Module.finrank ℝ E)] in
theorem chart_christoffel_clm_continuous_on_compact [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b : ℝ}
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    ContinuousOn (fun t : ℝ =>
      chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)) (Set.Icc a b) := by
  classical
  refine (continuousOn_clm_apply (𝕜 := ℝ) (E := E) (F := E)
    (s := Set.Icc a b)).mpr ?_
  intro w
  have hcurve_int : ∀ t ∈ Set.Icc a b,
      chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target := by
    intro t ht
    have hsrc : γ t ∈ (chartAt H α).source := hsource t ht
    have hxsrc : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hsrc
    have hxtarget : chartCurve (I := I) α γ t ∈ (extChartAt I α).target := by
      change extChartAt I α (γ t) ∈ (extChartAt I α).target
      exact (extChartAt I α).map_source hxsrc
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hxtarget
  have hcoord : ∀ i : Fin (Module.finrank ℝ E),
      Continuous fun v : E => chartCoord (E := E) i v := by
    intro i
    have heq : (fun v : E => chartCoord (E := E) i v)
        = fun v : E => (chartModelBasis E).equivFun v i := by
      funext v
      simp [chartCoord, Module.Basis.equivFun_apply]
    rw [heq]
    have hef : Continuous fun v : E => (chartModelBasis E).equivFun v :=
      ((chartModelBasis E).equivFun.toLinearMap).continuous_of_finiteDimensional
    exact (continuous_apply i).comp hef
  have hΓ : ∀ i j k : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ =>
        chartChristoffel (I := I) g α i j k (chartCurve (I := I) α γ t))
        (Set.Icc a b) := by
    intro i j k
    have hsm : ContinuousOn (chartChristoffel (I := I) g α i j k)
        (interior (extChartAt I α).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn
    exact hsm.comp hγ hcurve_int
  set F : ℝ → E := fun t : ℝ =>
    ∑ k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k
              (chartCurve (I := I) α γ t) *
            chartCoord (E := E) i (uPrime t) *
            chartCoord (E := E) j w) •
        chartModelBasis E k with hF_def
  have hEq : ∀ t ∈ Set.Icc a b,
      chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) w = F t := by
    intro t _
    simp [F, chartChristoffelContractionRightCLM_apply,
      chartChristoffelContraction_def]
  suffices hF_cont : ContinuousOn F (Set.Icc a b) from
    hF_cont.congr (fun t ht => (hEq t ht).symm)
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  refine ContinuousOn.smul ?_ continuousOn_const
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact hΓ i j k
  · exact ((hcoord i).comp_continuousOn hu)
  · exact continuousOn_const


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_lipschitz_bound_on_compact [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    ∃ K : NNReal,
      ParallelTransportLipschitzBound (I := I) g α γ uPrime K
        (Set.Icc a b) := by
  have hCLM : ContinuousOn
      (fun t : ℝ => chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)) (Set.Icc a b) :=
    chart_christoffel_clm_continuous_on_compact g α γ uPrime hu hγ hsource
  have hN : ContinuousOn
      (fun t : ℝ => ‖chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)‖₊) (Set.Icc a b) :=
    hCLM.nnnorm
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  obtain ⟨tmax, htmax_mem, htmax_max⟩ := hcpt.exists_isMaxOn hne hN
  refine ⟨‖chartChristoffelContractionRightCLM (I := I) g α (uPrime tmax)
    (chartCurve (I := I) α γ tmax)‖₊, ?_⟩
  intro t ht
  exact htmax_max ht


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem parallel_picard_lindelof_data
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    True := trivial


omit [NeZero (Module.finrank ℝ E)] in
private theorem parallel_local_existence_step [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {aa bb : ℝ}
    (hu : ContinuousOn uPrime (Set.Icc aa bb))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc aa bb))
    (hsource : ∀ t ∈ Set.Icc aa bb, γ t ∈ (chartAt H α).source)
    {K : NNReal}
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K
            (Set.Icc aa bb))
    {c d t_in : ℝ} (hcd : c ≤ d) (hca : aa ≤ c) (hdb : d ≤ bb)
    (ht_in_c : c ≤ t_in) (ht_in_d : t_in ≤ d)
    (hlen : (2 * (K : ℝ) + 2) * (d - c) ≤ 1)
    (w₀ : E) :
    ∃ Y : ℝ → E,
      (∀ t ∈ Set.Icc c d, HasDerivWithinAt Y
        (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t) (Y t)) (Set.Icc c d) t) ∧
      Y t_in = w₀ := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdc_nn : 0 ≤ d - c := sub_nonneg.mpr hcd
  have hK_nn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hsub_Icc : Set.Icc c d ⊆ Set.Icc aa bb :=
    fun τ hτ => ⟨hca.trans hτ.1, hτ.2.trans hdb⟩
  set A : ℝ → E →L[ℝ] E := fun t =>
    chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) with hA_def
  have hA_cont : ContinuousOn (fun t : ℝ => A t) (Set.Icc aa bb) :=
    chart_christoffel_clm_continuous_on_compact (I := I) g α γ uPrime hu hγ hsource
  set v : ℝ → E → E := fun t y => - A t y with hv_def
  set rB : ℝ := ‖w₀‖ + 1 with hrB_def
  have hrB_nn : 0 ≤ rB := by have := norm_nonneg w₀; linarith
  set LB : ℝ := (K : ℝ) * (2 * ‖w₀‖ + 1) with hLB_def
  have hLB_nn : 0 ≤ LB := by
    have h1 : 0 ≤ 2 * ‖w₀‖ + 1 := by have := norm_nonneg w₀; linarith
    exact mul_nonneg hK_nn h1
  have h_KdcHalf : (K : ℝ) * (d - c) ≤ 1 / 2 := by
    have h1 : 2 * (K : ℝ) * (d - c) ≤ 1 := by nlinarith [hlen, hdc_nn]
    linarith
  have h_2KdcOne : 2 * (K : ℝ) * (d - c) ≤ 1 := by linarith
  have h_LBdc : LB * (d - c) ≤ rB := by
    have hnw : 0 ≤ ‖w₀‖ := norm_nonneg _
    have key1 : 2 * (K : ℝ) * (d - c) * ‖w₀‖ ≤ ‖w₀‖ := by
      have := mul_le_mul_of_nonneg_right h_2KdcOne hnw; linarith
    have key2 : (K : ℝ) * (d - c) ≤ 1 := by linarith
    have heq : LB * (d - c) = 2 * (K : ℝ) * (d - c) * ‖w₀‖ + (K : ℝ) * (d - c) := by
      show (K : ℝ) * (2 * ‖w₀‖ + 1) * (d - c) = _; ring
    rw [heq]
    show 2 * (K : ℝ) * (d - c) * ‖w₀‖ + (K : ℝ) * (d - c) ≤ ‖w₀‖ + 1
    linarith
  let aN : NNReal := ⟨rB, hrB_nn⟩
  let rN : NNReal := 0
  let LN : NNReal := ⟨LB, hLB_nn⟩
  let KN : NNReal := K
  let t_inIcc : Set.Icc c d := ⟨t_in, ⟨ht_in_c, ht_in_d⟩⟩
  have hPL : IsPicardLindelof v t_inIcc w₀ aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro τ hτ
      have hclm : LipschitzWith ‖A τ‖₊ (A τ) := (A τ).lipschitz
      have hclm_neg : LipschitzWith ‖A τ‖₊ (fun y => v τ y) := hclm.neg
      have hτ_full : τ ∈ Set.Icc aa bb := hsub_Icc hτ
      have hweak : LipschitzWith KN (fun y => v τ y) := hclm_neg.weaken (hK τ hτ_full)
      exact hweak.lipschitzOnWith
    · intro y _
      have hA_cont_cd : ContinuousOn (fun τ : ℝ => A τ) (Set.Icc c d) := hA_cont.mono hsub_Icc
      have hApply : Continuous fun B : E →L[ℝ] E => B y :=
        (ContinuousLinearMap.apply ℝ E y).continuous
      have hAy : ContinuousOn (fun τ : ℝ => A τ y) (Set.Icc c d) :=
        hApply.comp_continuousOn hA_cont_cd
      exact hAy.neg
    · intro τ hτ y hy
      have hτ_full : τ ∈ Set.Icc aa bb := hsub_Icc hτ
      have hAτ_norm : ‖A τ‖ ≤ (K : ℝ) := hK τ hτ_full
      have hy_norm : ‖y - w₀‖ ≤ rB := by
        have h1 : dist y w₀ ≤ (aN : ℝ) := hy
        rw [dist_eq_norm] at h1; exact h1
      have hy_total : ‖y‖ ≤ ‖w₀‖ + rB := by
        have heq : y = (y - w₀) + w₀ := by abel
        calc ‖y‖ = ‖(y - w₀) + w₀‖ := by rw [← heq]
          _ ≤ ‖y - w₀‖ + ‖w₀‖ := norm_add_le _ _
          _ ≤ rB + ‖w₀‖ := by linarith
          _ = ‖w₀‖ + rB := by ring
      have hy_total' : ‖y‖ ≤ 2 * ‖w₀‖ + 1 := by
        have heq : ‖w₀‖ + rB = 2 * ‖w₀‖ + 1 := by show ‖w₀‖ + (‖w₀‖ + 1) = _; ring
        linarith
      change ‖v τ y‖ ≤ (LN : ℝ)
      calc ‖v τ y‖ = ‖A τ y‖ := by simp [v]
        _ ≤ ‖A τ‖ * ‖y‖ := (A τ).le_opNorm y
        _ ≤ (K : ℝ) * (2 * ‖w₀‖ + 1) := by
            apply mul_le_mul hAτ_norm hy_total' (norm_nonneg _) hK_nn
        _ = LB := by show (K : ℝ) * (2 * ‖w₀‖ + 1) = (K : ℝ) * (2 * ‖w₀‖ + 1); rfl
        _ = (LN : ℝ) := rfl
    · change LB * max (d - t_in) (t_in - c) ≤ rB - 0
      have hmax_le : max (d - t_in) (t_in - c) ≤ d - c := by
        refine max_le ?_ ?_
        · linarith
        · linarith
      have hmax_nn : 0 ≤ max (d - t_in) (t_in - c) := by
        refine le_max_of_le_left ?_; linarith
      have hLB_dc : LB * max (d - t_in) (t_in - c) ≤ LB * (d - c) :=
        mul_le_mul_of_nonneg_left hmax_le hLB_nn
      linarith [h_LBdc]
  have hw₀_mem : w₀ ∈ Metric.closedBall w₀ (rN : ℝ) := by
    show dist w₀ w₀ ≤ (rN : ℝ); simp
  obtain ⟨Y, hY_init, hY_deriv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hw₀_mem
  refine ⟨Y, ?_, ?_⟩
  · intro t ht
    have h := hY_deriv t ht
    have heq : v t (Y t) = - chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t) (Y t) := rfl
    rw [heq] at h; exact h
  · have : Y (t_inIcc : ℝ) = w₀ := hY_init
    show Y t_in = w₀; exact this


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_local_existence_on_Icc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : E) :
    ∃ Y : ℝ → E,
      (∀ t ∈ Set.Icc a b, HasDerivWithinAt Y
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
            (chartCurve (I := I) α γ t)) (Set.Icc a b) t) ∧
      Y t₀ = v₀ := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨ht₀_a, ht₀_b⟩ := ht₀
  obtain ⟨K, hK⟩ :=
    parallel_lipschitz_bound_on_compact (I := I) g α γ uPrime hab hu hγ hsource
  set h : ℝ := 1 / (2 * (K : ℝ) + 2) with hh_def
  have h2K2_pos : (0 : ℝ) < 2 * (K : ℝ) + 2 := by positivity
  have hh_pos : 0 < h := by rw [hh_def]; positivity
  have hh_eq : (2 * (K : ℝ) + 2) * h = 1 := by
    rw [hh_def]; field_simp
  obtain ⟨N, hN⟩ : ∃ N : ℕ, b - a ≤ N * h := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / h)
    refine ⟨N, ?_⟩
    have h1 : (b - a) / h < N := hN
    have : (b - a) = (b - a) / h * h := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right h1.le hh_pos.le
  let Tn : ℕ → ℝ := fun n => min b (t₀ + n * h)
  have hTn_zero : Tn 0 = t₀ := by
    show min b (t₀ + (0 : ℕ) * h) = t₀
    have h0 : t₀ + ((0 : ℕ) : ℝ) * h = t₀ := by push_cast; ring
    rw [h0]; exact min_eq_right ht₀_b
  have hTn_le_b : ∀ n, Tn n ≤ b := fun n => min_le_left _ _
  have hTn_ge_t₀ : ∀ n, t₀ ≤ Tn n := by
    intro n
    refine le_min ht₀_b ?_
    have : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
    linarith
  have hTn_mono : ∀ n, Tn n ≤ Tn (n + 1) := by
    intro n
    refine min_le_min (le_refl _) ?_
    have hcast : (((n + 1 : ℕ) : ℝ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h2 : (n : ℝ) * h ≤ ((n : ℝ) + 1) * h :=
      mul_le_mul_of_nonneg_right h1 hh_pos.le
    rw [hcast]; linarith
  have hTn_diff_bound : ∀ n, (2 * (K : ℝ) + 2) * (Tn (n + 1) - Tn n) ≤ 1 := by
    intro n
    have h_step : Tn (n + 1) - Tn n ≤ h := by
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      have hX : t₀ + ((n + 1 : ℕ) : ℝ) * h - (t₀ + ((n : ℕ) : ℝ) * h) = h := by
        rw [hcast]; ring
      rcases le_or_gt (t₀ + ((n + 1 : ℕ) : ℝ) * h) b with hle | hgt
      · have hmono_le : t₀ + ((n : ℕ) : ℝ) * h ≤ t₀ + ((n + 1 : ℕ) : ℝ) * h := by
          rw [hcast]; nlinarith [hh_pos.le]
        have hle' : t₀ + ((n : ℕ) : ℝ) * h ≤ b := hmono_le.trans hle
        have hT1 : Tn (n + 1) = t₀ + ((n + 1 : ℕ) : ℝ) * h := min_eq_right hle
        have hT0 : Tn n = t₀ + ((n : ℕ) : ℝ) * h := min_eq_right hle'
        rw [hT1, hT0]; linarith
      · have hT1 : Tn (n + 1) = b := min_eq_left hgt.le
        rcases le_or_gt (t₀ + ((n : ℕ) : ℝ) * h) b with hle2 | hgt2
        · have hT0 : Tn n = t₀ + ((n : ℕ) : ℝ) * h := min_eq_right hle2
          rw [hT1, hT0]; linarith
        · have hT0 : Tn n = b := min_eq_left hgt2.le
          rw [hT1, hT0]; linarith [hh_pos]
    have h2K_nn : 0 ≤ 2 * (K : ℝ) + 2 := h2K2_pos.le
    have := mul_le_mul_of_nonneg_left h_step h2K_nn
    linarith [hh_eq]
  have rightExist : ∀ n, ∃ Y : ℝ → E, Y t₀ = v₀ ∧
      ∀ t ∈ Set.Icc t₀ (Tn n), HasDerivWithinAt Y
        (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t) (Y t)) (Set.Icc t₀ (Tn n)) t := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => v₀, rfl, ?_⟩
      intro t ht
      rw [hTn_zero] at ht
      have ht_eq : t = t₀ := le_antisymm ht.2 ht.1
      rw [hTn_zero]
      have hsub : (Set.Icc t₀ t₀).Subsingleton := by
        rw [Set.Icc_self]; exact Set.subsingleton_singleton
      have hF : HasFDerivWithinAt (fun _ : ℝ => v₀)
          (ContinuousLinearMap.toSpanSingleton ℝ
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                (chartCurve (I := I) α γ t) v₀))
          (Set.Icc t₀ t₀) t :=
        HasFDerivWithinAt.of_subsingleton hsub
      have := (hasDerivWithinAt_iff_hasFDerivWithinAt
        (f := fun _ : ℝ => v₀)
        (f' := - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t) v₀)
        (s := Set.Icc t₀ t₀) (x := t)).mpr hF
      convert this using 2
    | succ n IH =>
      obtain ⟨Y₀, hY₀_init, hY₀_deriv⟩ := IH
      by_cases hsame : Tn n = Tn (n + 1)
      · refine ⟨Y₀, hY₀_init, ?_⟩
        intro t ht
        rw [← hsame] at ht ⊢
        exact hY₀_deriv t ht
      · have hlt : Tn n < Tn (n + 1) := lt_of_le_of_ne (hTn_mono n) hsame
        have hT_t₀ : t₀ ≤ Tn n := hTn_ge_t₀ n
        have hT_a : a ≤ Tn n := ht₀_a.trans hT_t₀
        have hT'_b : Tn (n + 1) ≤ b := hTn_le_b (n + 1)
        have hlen' : (2 * (K : ℝ) + 2) * (Tn (n + 1) - Tn n) ≤ 1 := hTn_diff_bound n
        obtain ⟨Z, hZ_deriv, hZ_init⟩ :=
          parallel_local_existence_step (I := I) g α γ uPrime hu hγ hsource hK
            (le_of_lt hlt) hT_a hT'_b (le_refl _) (le_of_lt hlt) hlen' (Y₀ (Tn n))
        refine ⟨fun t => if t ≤ Tn n then Y₀ t else Z t, ?_, ?_⟩
        · show (if t₀ ≤ Tn n then Y₀ t₀ else Z t₀) = v₀
          rw [if_pos hT_t₀]; exact hY₀_init
        · intro t ht
          set Yp : ℝ → E := fun t => if t ≤ Tn n then Y₀ t else Z t with hYp
          show HasDerivWithinAt Yp
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                (chartCurve (I := I) α γ t) (Yp t)) (Set.Icc t₀ (Tn (n + 1))) t
          by_cases hT : t ≤ Tn n
          · by_cases hT_strict : t < Tn n
            · have ht_in : t ∈ Set.Icc t₀ (Tn n) := ⟨ht.1, hT⟩
              have hY₀_at := hY₀_deriv t ht_in
              have hcongr : ∀ s ∈ Set.Icc t₀ (Tn n), Yp s = Y₀ s := by
                intro s hs
                show (if s ≤ Tn n then Y₀ s else Z s) = Y₀ s
                rw [if_pos hs.2]
              have hsmall := hY₀_at.congr hcongr (hcongr t ht_in)
              have hself : Yp t = Y₀ t := hcongr t ht_in
              have hopen : Set.Iio (Tn n) ∈ 𝓝 t := isOpen_Iio.mem_nhds hT_strict
              have hmem : Set.Icc t₀ (Tn n) ∈ 𝓝[Set.Icc t₀ (Tn (n + 1))] t := by
                have hint :
                    Set.Icc t₀ (Tn (n + 1)) ∩ Set.Iio (Tn n)
                      ∈ 𝓝[Set.Icc t₀ (Tn (n + 1))] t :=
                  inter_mem_nhdsWithin (Set.Icc t₀ (Tn (n + 1))) hopen
                refine mem_of_superset hint ?_
                intro s hs
                exact ⟨hs.1.1, le_of_lt hs.2⟩
              rw [hself]
              exact hsmall.mono_of_mem_nhdsWithin hmem
            · push Not at hT_strict
              have ht_eq : t = Tn n := le_antisymm hT hT_strict
              have hY₀_at_Tn : HasDerivWithinAt Y₀
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Tn n))
                      (chartCurve (I := I) α γ (Tn n)) (Y₀ (Tn n)))
                  (Set.Icc t₀ (Tn n)) (Tn n) :=
                hY₀_deriv (Tn n) ⟨hT_t₀, le_refl _⟩
              have hcongr_L : ∀ s ∈ Set.Icc t₀ (Tn n), Yp s = Y₀ s := by
                intro s hs
                show (if s ≤ Tn n then Y₀ s else Z s) = Y₀ s
                rw [if_pos hs.2]
              have hYp_L : HasDerivWithinAt Yp
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Tn n))
                      (chartCurve (I := I) α γ (Tn n)) (Y₀ (Tn n)))
                  (Set.Icc t₀ (Tn n)) (Tn n) :=
                hY₀_at_Tn.congr hcongr_L (hcongr_L (Tn n) ⟨hT_t₀, le_refl _⟩)
              have hZ_at_Tn : HasDerivWithinAt Z
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Tn n))
                      (chartCurve (I := I) α γ (Tn n)) (Z (Tn n)))
                  (Set.Icc (Tn n) (Tn (n + 1))) (Tn n) :=
                hZ_deriv (Tn n) ⟨le_refl _, le_of_lt hlt⟩
              have hZ_init_eq : Z (Tn n) = Y₀ (Tn n) := hZ_init
              have hcongr_R : ∀ s ∈ Set.Icc (Tn n) (Tn (n + 1)), Yp s = Z s := by
                intro s hs
                show (if s ≤ Tn n then Y₀ s else Z s) = Z s
                by_cases hs_le : s ≤ Tn n
                · have : s = Tn n := le_antisymm hs_le hs.1
                  rw [if_pos hs_le, this, hZ_init_eq]
                · rw [if_neg hs_le]
              have hYp_R : HasDerivWithinAt Yp
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Tn n))
                      (chartCurve (I := I) α γ (Tn n)) (Z (Tn n)))
                  (Set.Icc (Tn n) (Tn (n + 1))) (Tn n) :=
                hZ_at_Tn.congr hcongr_R (hcongr_R (Tn n) ⟨le_refl _, le_of_lt hlt⟩)
              rw [hZ_init_eq] at hYp_R
              have hUeq : Set.Icc t₀ (Tn n) ∪ Set.Icc (Tn n) (Tn (n + 1))
                  = Set.Icc t₀ (Tn (n + 1)) :=
                Set.Icc_union_Icc_eq_Icc hT_t₀ (le_of_lt hlt)
              have hYp_self : Yp (Tn n) = Y₀ (Tn n) := by
                show (if Tn n ≤ Tn n then Y₀ (Tn n) else Z (Tn n)) = Y₀ (Tn n)
                rw [if_pos (le_refl _)]
              rw [ht_eq, hYp_self]
              rw [← hUeq]
              exact hYp_L.union hYp_R
          · push Not at hT
            have ht_in_right : t ∈ Set.Icc (Tn n) (Tn (n + 1)) :=
              ⟨le_of_lt hT, ht.2⟩
            have hZ_at := hZ_deriv t ht_in_right
            have hZ_init_eq : Z (Tn n) = Y₀ (Tn n) := hZ_init
            have hcongr_R : ∀ s ∈ Set.Icc (Tn n) (Tn (n + 1)), Yp s = Z s := by
              intro s hs
              show (if s ≤ Tn n then Y₀ s else Z s) = Z s
              by_cases hs_le : s ≤ Tn n
              · have : s = Tn n := le_antisymm hs_le hs.1
                rw [if_pos hs_le, this, hZ_init_eq]
              · rw [if_neg hs_le]
            have hsmall := hZ_at.congr hcongr_R (hcongr_R t ht_in_right)
            have hself : Yp t = Z t := hcongr_R t ht_in_right
            have hopen : Set.Ioi (Tn n) ∈ 𝓝 t := isOpen_Ioi.mem_nhds hT
            have hmem : Set.Icc (Tn n) (Tn (n + 1)) ∈ 𝓝[Set.Icc t₀ (Tn (n + 1))] t := by
              have hint :
                  Set.Icc t₀ (Tn (n + 1)) ∩ Set.Ioi (Tn n)
                    ∈ 𝓝[Set.Icc t₀ (Tn (n + 1))] t :=
                inter_mem_nhdsWithin (Set.Icc t₀ (Tn (n + 1))) hopen
              refine mem_of_superset hint ?_
              intro s hs
              exact ⟨le_of_lt hs.2, hs.1.2⟩
            rw [hself]
            exact hsmall.mono_of_mem_nhdsWithin hmem
  have hTn_N_eq : Tn N = b := by
    have h1 : b ≤ t₀ + (N : ℝ) * h := by
      have : b - a ≤ (N : ℝ) * h := hN
      linarith
    show min b (t₀ + (N : ℕ) * h) = b
    have : t₀ + ((N : ℕ) : ℝ) * h ≥ b := by linarith
    exact min_eq_left this
  obtain ⟨Y_R, hY_R_init, hY_R_deriv⟩ := rightExist N
  rw [hTn_N_eq] at hY_R_deriv
  let Sn : ℕ → ℝ := fun n => max a (t₀ - n * h)
  have hSn_zero : Sn 0 = t₀ := by
    show max a (t₀ - (0 : ℕ) * h) = t₀
    have h0 : t₀ - ((0 : ℕ) : ℝ) * h = t₀ := by push_cast; ring
    rw [h0]; exact max_eq_right ht₀_a
  have hSn_ge_a : ∀ n, a ≤ Sn n := fun n => le_max_left _ _
  have hSn_le_t₀ : ∀ n, Sn n ≤ t₀ := by
    intro n
    refine max_le ht₀_a ?_
    have : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
    linarith
  have hSn_mono : ∀ n, Sn (n + 1) ≤ Sn n := by
    intro n
    refine max_le_max (le_refl _) ?_
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h2 : (n : ℝ) * h ≤ ((n : ℝ) + 1) * h :=
      mul_le_mul_of_nonneg_right h1 hh_pos.le
    rw [hcast]; linarith
  have hSn_diff_bound : ∀ n, (2 * (K : ℝ) + 2) * (Sn n - Sn (n + 1)) ≤ 1 := by
    intro n
    have h_step : Sn n - Sn (n + 1) ≤ h := by
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rcases le_or_gt a (t₀ - ((n + 1 : ℕ) : ℝ) * h) with hge | hlt
      · have hmono : t₀ - ((n + 1 : ℕ) : ℝ) * h ≤ t₀ - ((n : ℕ) : ℝ) * h := by
          rw [hcast]; nlinarith [hh_pos.le]
        have hge' : a ≤ t₀ - ((n : ℕ) : ℝ) * h := hge.trans hmono
        have hS1 : Sn (n + 1) = t₀ - ((n + 1 : ℕ) : ℝ) * h := max_eq_right hge
        have hS0 : Sn n = t₀ - ((n : ℕ) : ℝ) * h := max_eq_right hge'
        rw [hS1, hS0, hcast]; ring_nf; linarith
      · have hS1 : Sn (n + 1) = a := max_eq_left hlt.le
        rcases le_or_gt a (t₀ - ((n : ℕ) : ℝ) * h) with hge2 | hlt2
        · have hS0 : Sn n = t₀ - ((n : ℕ) : ℝ) * h := max_eq_right hge2
          rw [hS1, hS0]
          have hlt' : t₀ - ((n : ℝ) + 1) * h < a := by rw [← hcast]; exact hlt
          nlinarith [hh_pos]
        · have hS0 : Sn n = a := max_eq_left hlt2.le
          rw [hS1, hS0]; linarith [hh_pos]
    have h2K_nn : 0 ≤ 2 * (K : ℝ) + 2 := h2K2_pos.le
    have := mul_le_mul_of_nonneg_left h_step h2K_nn
    linarith [hh_eq]
  have leftExist : ∀ n, ∃ Y : ℝ → E, Y t₀ = v₀ ∧
      ∀ t ∈ Set.Icc (Sn n) t₀, HasDerivWithinAt Y
        (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t) (Y t)) (Set.Icc (Sn n) t₀) t := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => v₀, rfl, ?_⟩
      intro t ht
      rw [hSn_zero] at ht
      have ht_eq : t = t₀ := le_antisymm ht.2 ht.1
      rw [hSn_zero]
      have hsub : (Set.Icc t₀ t₀).Subsingleton := by
        rw [Set.Icc_self]; exact Set.subsingleton_singleton
      have hF : HasFDerivWithinAt (fun _ : ℝ => v₀)
          (ContinuousLinearMap.toSpanSingleton ℝ
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                (chartCurve (I := I) α γ t) v₀))
          (Set.Icc t₀ t₀) t :=
        HasFDerivWithinAt.of_subsingleton hsub
      have := (hasDerivWithinAt_iff_hasFDerivWithinAt
        (f := fun _ : ℝ => v₀)
        (f' := - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t) v₀)
        (s := Set.Icc t₀ t₀) (x := t)).mpr hF
      convert this using 2
    | succ n IH =>
      obtain ⟨Y₀, hY₀_init, hY₀_deriv⟩ := IH
      by_cases hsame : Sn n = Sn (n + 1)
      · refine ⟨Y₀, hY₀_init, ?_⟩
        intro t ht
        rw [← hsame] at ht ⊢
        exact hY₀_deriv t ht
      · have hlt : Sn (n + 1) < Sn n := lt_of_le_of_ne (hSn_mono n) (Ne.symm hsame)
        have hSn1_a : a ≤ Sn (n + 1) := hSn_ge_a (n + 1)
        have hSn_b : Sn n ≤ b := (hSn_le_t₀ n).trans ht₀_b
        obtain ⟨Z, hZ_deriv, hZ_init⟩ :=
          parallel_local_existence_step (I := I) g α γ uPrime hu hγ hsource hK
            (le_of_lt hlt) hSn1_a hSn_b (le_of_lt hlt) (le_refl _)
            (hSn_diff_bound n) (Y₀ (Sn n))
        refine ⟨fun t => if t < Sn n then Z t else Y₀ t, ?_, ?_⟩
        · show (if t₀ < Sn n then Z t₀ else Y₀ t₀) = v₀
          rw [if_neg (not_lt.mpr (hSn_le_t₀ n))]; exact hY₀_init
        · intro t ht
          set Yp : ℝ → E := fun t => if t < Sn n then Z t else Y₀ t with hYp
          show HasDerivWithinAt Yp
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                (chartCurve (I := I) α γ t) (Yp t)) (Set.Icc (Sn (n + 1)) t₀) t
          by_cases hSn_lt : t < Sn n
          · have ht_in : t ∈ Set.Icc (Sn (n + 1)) (Sn n) :=
              ⟨ht.1, le_of_lt hSn_lt⟩
            have hZ_at := hZ_deriv t ht_in
            have hZ_init_eq : Z (Sn n) = Y₀ (Sn n) := hZ_init
            have hcongr : ∀ s ∈ Set.Icc (Sn (n + 1)) (Sn n), Yp s = Z s := by
              intro s hs
              show (if s < Sn n then Z s else Y₀ s) = Z s
              by_cases hs_lt : s < Sn n
              · rw [if_pos hs_lt]
              · push Not at hs_lt
                have : s = Sn n := le_antisymm hs.2 hs_lt
                rw [if_neg (not_lt.mpr hs_lt), this, hZ_init_eq]
            have hsmall := hZ_at.congr hcongr (hcongr t ht_in)
            have hself : Yp t = Z t := hcongr t ht_in
            have hopen : Set.Iio (Sn n) ∈ 𝓝 t := isOpen_Iio.mem_nhds hSn_lt
            have hmem : Set.Icc (Sn (n + 1)) (Sn n) ∈ 𝓝[Set.Icc (Sn (n + 1)) t₀] t := by
              have hint :
                  Set.Icc (Sn (n + 1)) t₀ ∩ Set.Iio (Sn n)
                    ∈ 𝓝[Set.Icc (Sn (n + 1)) t₀] t :=
                inter_mem_nhdsWithin (Set.Icc (Sn (n + 1)) t₀) hopen
              refine mem_of_superset hint ?_
              intro s hs
              exact ⟨hs.1.1, le_of_lt hs.2⟩
            rw [hself]
            exact hsmall.mono_of_mem_nhdsWithin hmem
          · push Not at hSn_lt
            by_cases hSn_eq : t = Sn n
            · have hZ_at_Sn : HasDerivWithinAt Z
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Sn n))
                      (chartCurve (I := I) α γ (Sn n)) (Z (Sn n)))
                  (Set.Icc (Sn (n + 1)) (Sn n)) (Sn n) :=
                hZ_deriv (Sn n) ⟨le_of_lt hlt, le_refl _⟩
              have hZ_init_eq : Z (Sn n) = Y₀ (Sn n) := hZ_init
              have hcongr_L : ∀ s ∈ Set.Icc (Sn (n + 1)) (Sn n), Yp s = Z s := by
                intro s hs
                show (if s < Sn n then Z s else Y₀ s) = Z s
                by_cases hs_lt : s < Sn n
                · rw [if_pos hs_lt]
                · push Not at hs_lt
                  have : s = Sn n := le_antisymm hs.2 hs_lt
                  rw [if_neg (not_lt.mpr hs_lt), this, hZ_init_eq]
              have hYp_L : HasDerivWithinAt Yp
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Sn n))
                      (chartCurve (I := I) α γ (Sn n)) (Z (Sn n)))
                  (Set.Icc (Sn (n + 1)) (Sn n)) (Sn n) :=
                hZ_at_Sn.congr hcongr_L (hcongr_L (Sn n) ⟨le_of_lt hlt, le_refl _⟩)
              have hY₀_at_Sn : HasDerivWithinAt Y₀
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Sn n))
                      (chartCurve (I := I) α γ (Sn n)) (Y₀ (Sn n)))
                  (Set.Icc (Sn n) t₀) (Sn n) :=
                hY₀_deriv (Sn n) ⟨le_refl _, hSn_le_t₀ n⟩
              have hcongr_R : ∀ s ∈ Set.Icc (Sn n) t₀, Yp s = Y₀ s := by
                intro s hs
                show (if s < Sn n then Z s else Y₀ s) = Y₀ s
                rw [if_neg (not_lt.mpr hs.1)]
              have hYp_R : HasDerivWithinAt Yp
                  (- chartChristoffelContractionRightCLM (I := I) g α (uPrime (Sn n))
                      (chartCurve (I := I) α γ (Sn n)) (Y₀ (Sn n)))
                  (Set.Icc (Sn n) t₀) (Sn n) :=
                hY₀_at_Sn.congr hcongr_R (hcongr_R (Sn n) ⟨le_refl _, hSn_le_t₀ n⟩)
              rw [hZ_init_eq] at hYp_L
              have hUeq : Set.Icc (Sn (n + 1)) (Sn n) ∪ Set.Icc (Sn n) t₀
                  = Set.Icc (Sn (n + 1)) t₀ :=
                Set.Icc_union_Icc_eq_Icc (le_of_lt hlt) (hSn_le_t₀ n)
              have hYp_self : Yp (Sn n) = Y₀ (Sn n) := by
                show (if Sn n < Sn n then Z (Sn n) else Y₀ (Sn n)) = Y₀ (Sn n)
                rw [if_neg (lt_irrefl _)]
              rw [hSn_eq, hYp_self, ← hUeq]
              exact hYp_L.union hYp_R
            · have hSn_strict : Sn n < t := lt_of_le_of_ne hSn_lt (Ne.symm hSn_eq)
              have ht_in_right : t ∈ Set.Icc (Sn n) t₀ := ⟨le_of_lt hSn_strict, ht.2⟩
              have hY₀_at := hY₀_deriv t ht_in_right
              have hcongr_R : ∀ s ∈ Set.Icc (Sn n) t₀, Yp s = Y₀ s := by
                intro s hs
                show (if s < Sn n then Z s else Y₀ s) = Y₀ s
                rw [if_neg (not_lt.mpr hs.1)]
              have hsmall := hY₀_at.congr hcongr_R (hcongr_R t ht_in_right)
              have hself : Yp t = Y₀ t := hcongr_R t ht_in_right
              have hopen : Set.Ioi (Sn n) ∈ 𝓝 t := isOpen_Ioi.mem_nhds hSn_strict
              have hmem : Set.Icc (Sn n) t₀ ∈ 𝓝[Set.Icc (Sn (n + 1)) t₀] t := by
                have hint :
                    Set.Icc (Sn (n + 1)) t₀ ∩ Set.Ioi (Sn n)
                      ∈ 𝓝[Set.Icc (Sn (n + 1)) t₀] t :=
                  inter_mem_nhdsWithin (Set.Icc (Sn (n + 1)) t₀) hopen
                refine mem_of_superset hint ?_
                intro s hs
                exact ⟨le_of_lt hs.2, hs.1.2⟩
              rw [hself]
              exact hsmall.mono_of_mem_nhdsWithin hmem
  have hSn_N_eq : Sn N = a := by
    have h1 : t₀ - (N : ℝ) * h ≤ a := by
      have : b - a ≤ (N : ℝ) * h := hN
      linarith
    show max a (t₀ - (N : ℕ) * h) = a
    have : t₀ - ((N : ℕ) : ℝ) * h ≤ a := by linarith
    exact max_eq_left this
  obtain ⟨Y_L, hY_L_init, hY_L_deriv⟩ := leftExist N
  rw [hSn_N_eq] at hY_L_deriv
  have h_unfold :
      ∀ (s : ℝ) (Yv : E),
        chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s) Yv =
          chartChristoffelContraction (I := I) g α (uPrime s) Yv
            (chartCurve (I := I) α γ s) := fun s Yv => rfl
  refine ⟨fun t => if t ≤ t₀ then Y_L t else Y_R t, ?_, ?_⟩
  · intro t ht
    set Y : ℝ → E := fun t => if t ≤ t₀ then Y_L t else Y_R t with hY
    have hLR_eq : Y_L t₀ = Y_R t₀ := by rw [hY_L_init, hY_R_init]
    by_cases ht_t₀ : t ≤ t₀
    · by_cases ht_strict : t < t₀
      · have ht_in : t ∈ Set.Icc a t₀ := ⟨ht.1, ht_t₀⟩
        have hL_at := hY_L_deriv t ht_in
        have hcongr : ∀ s ∈ Set.Icc a t₀, Y s = Y_L s := by
          intro s hs
          show (if s ≤ t₀ then Y_L s else Y_R s) = Y_L s
          rw [if_pos hs.2]
        have hsmall := hL_at.congr hcongr (hcongr t ht_in)
        have hself : Y t = Y_L t := hcongr t ht_in
        have hopen : Set.Iio t₀ ∈ 𝓝 t := isOpen_Iio.mem_nhds ht_strict
        have hmem : Set.Icc a t₀ ∈ 𝓝[Set.Icc a b] t := by
          have hint : Set.Icc a b ∩ Set.Iio t₀ ∈ 𝓝[Set.Icc a b] t :=
            inter_mem_nhdsWithin (Set.Icc a b) hopen
          refine mem_of_superset hint ?_
          intro s hs; exact ⟨hs.1.1, le_of_lt hs.2⟩
        rw [show (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t)) =
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
              (chartCurve (I := I) α γ t) (Y_L t)) from by rw [h_unfold, hself]]
        exact hsmall.mono_of_mem_nhdsWithin hmem
      · push Not at ht_strict
        have ht_eq : t = t₀ := le_antisymm ht_t₀ ht_strict
        have hL_at_t₀ : HasDerivWithinAt Y_L
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t₀)
                (chartCurve (I := I) α γ t₀) (Y_L t₀))
            (Set.Icc a t₀) t₀ :=
          hY_L_deriv t₀ ⟨ht₀_a, le_refl _⟩
        have hR_at_t₀ : HasDerivWithinAt Y_R
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t₀)
                (chartCurve (I := I) α γ t₀) (Y_R t₀))
            (Set.Icc t₀ b) t₀ :=
          hY_R_deriv t₀ ⟨le_refl _, ht₀_b⟩
        have hcongr_L : ∀ s ∈ Set.Icc a t₀, Y s = Y_L s := by
          intro s hs
          show (if s ≤ t₀ then Y_L s else Y_R s) = Y_L s
          rw [if_pos hs.2]
        have hYp_L : HasDerivWithinAt Y
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t₀)
                (chartCurve (I := I) α γ t₀) (Y_L t₀))
            (Set.Icc a t₀) t₀ :=
          hL_at_t₀.congr hcongr_L (hcongr_L t₀ ⟨ht₀_a, le_refl _⟩)
        have hcongr_R : ∀ s ∈ Set.Icc t₀ b, Y s = Y_R s := by
          intro s hs
          show (if s ≤ t₀ then Y_L s else Y_R s) = Y_R s
          by_cases hs_le : s ≤ t₀
          · have : s = t₀ := le_antisymm hs_le hs.1
            rw [if_pos hs_le, this, hLR_eq]
          · rw [if_neg hs_le]
        have hYp_R : HasDerivWithinAt Y
            (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t₀)
                (chartCurve (I := I) α γ t₀) (Y_R t₀))
            (Set.Icc t₀ b) t₀ :=
          hR_at_t₀.congr hcongr_R (hcongr_R t₀ ⟨le_refl _, ht₀_b⟩)
        rw [hLR_eq] at hYp_L
        have hUeq : Set.Icc a t₀ ∪ Set.Icc t₀ b = Set.Icc a b :=
          Set.Icc_union_Icc_eq_Icc ht₀_a ht₀_b
        have hY_self : Y t₀ = Y_R t₀ := by
          show (if t₀ ≤ t₀ then Y_L t₀ else Y_R t₀) = Y_R t₀
          rw [if_pos (le_refl _)]; exact hLR_eq
        rw [ht_eq, ← h_unfold, hY_self, ← hUeq]
        exact hYp_L.union hYp_R
    · push Not at ht_t₀
      have ht_in : t ∈ Set.Icc t₀ b := ⟨le_of_lt ht_t₀, ht.2⟩
      have hR_at := hY_R_deriv t ht_in
      have hcongr : ∀ s ∈ Set.Icc t₀ b, Y s = Y_R s := by
        intro s hs
        show (if s ≤ t₀ then Y_L s else Y_R s) = Y_R s
        by_cases hs_le : s ≤ t₀
        · have : s = t₀ := le_antisymm hs_le hs.1
          rw [if_pos hs_le, this, hLR_eq]
        · rw [if_neg hs_le]
      have hsmall := hR_at.congr hcongr (hcongr t ht_in)
      have hself : Y t = Y_R t := hcongr t ht_in
      have hopen : Set.Ioi t₀ ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht_t₀
      have hmem : Set.Icc t₀ b ∈ 𝓝[Set.Icc a b] t := by
        have hint : Set.Icc a b ∩ Set.Ioi t₀ ∈ 𝓝[Set.Icc a b] t :=
          inter_mem_nhdsWithin (Set.Icc a b) hopen
        refine mem_of_superset hint ?_
        intro s hs; exact ⟨le_of_lt hs.2, hs.1.2⟩
      rw [show (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
            (chartCurve (I := I) α γ t)) =
          (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t) (Y_R t)) from by rw [h_unfold, hself]]
      exact hsmall.mono_of_mem_nhdsWithin hmem
  · show (if t₀ ≤ t₀ then Y_L t₀ else Y_R t₀) = v₀
    rw [if_pos (le_refl _)]; exact hY_L_init


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_local_uniqueness_on_Icc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    {Y₁ Y₂ : ℝ → E}
    (hY₁ : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y₁
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
            (chartCurve (I := I) α γ t)) (Set.Icc a b) t)
    (hY₂ : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y₂
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
            (chartCurve (I := I) α γ t)) (Set.Icc a b) t)
    (h_eq : Y₁ t₀ = Y₂ t₀) :
    Set.EqOn Y₁ Y₂ (Set.Icc a b) := by
  classical
  set v : ℝ → E → E := fun t Y =>
    - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t) Y with hv_def
  obtain ⟨K, hK⟩ :=
    parallel_lipschitz_bound_on_compact (I := I) g α γ uPrime hab hu hγ hsource
  have hLip : ∀ t ∈ Set.Icc a b,
      LipschitzOnWith K (v t) (Set.univ : Set E) := by
    intro t ht
    have hclm :
        LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
              (uPrime t) (chartCurve (I := I) α γ t)‖₊
          (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
            (chartCurve (I := I) α γ t)) :=
      (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)).lipschitz
    have hclm_neg :
        LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
              (uPrime t) (chartCurve (I := I) α γ t)‖₊
          (fun Y => v t Y) := hclm.neg
    exact (hclm_neg.weaken (hK t ht)).lipschitzOnWith
  have hY₁' : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt Y₁ (v t (Y₁ t)) (Set.Icc a b) t := by
    intro t ht
    exact hY₁ t ht
  have hY₂' : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt Y₂ (v t (Y₂ t)) (Set.Icc a b) t := by
    intro t ht
    exact hY₂ t ht
  have hY₁_cont : ContinuousOn Y₁ (Set.Icc a b) :=
    HasDerivWithinAt.continuousOn (f' := fun t => v t (Y₁ t)) hY₁'
  have hY₂_cont : ContinuousOn Y₂ (Set.Icc a b) :=
    HasDerivWithinAt.continuousOn (f' := fun t => v t (Y₂ t)) hY₂'
  rcases ht₀ with ⟨ht₀_a, ht₀_b⟩
  have h_right : Set.EqOn Y₁ Y₂ (Set.Icc t₀ b) := by
    have hLip_r : ∀ t ∈ Set.Ico t₀ b,
        LipschitzOnWith K (v t) (Set.univ : Set E) := by
      intro t ht
      have ht_mem : t ∈ Set.Icc a b :=
        ⟨ht₀_a.trans ht.1, ht.2.le⟩
      exact hLip t ht_mem
    have hY₁_cont_r : ContinuousOn Y₁ (Set.Icc t₀ b) :=
      hY₁_cont.mono (Set.Icc_subset_Icc_left ht₀_a)
    have hY₂_cont_r : ContinuousOn Y₂ (Set.Icc t₀ b) :=
      hY₂_cont.mono (Set.Icc_subset_Icc_left ht₀_a)
    have hY₁_diff_r : ∀ t ∈ Set.Ico t₀ b,
        HasDerivWithinAt Y₁ (v t (Y₁ t)) (Set.Ici t) t := by
      intro t ht
      have ht_mem : t ∈ Set.Icc a b :=
        ⟨ht₀_a.trans ht.1, ht.2.le⟩
      have h := hY₁' t ht_mem
      have ht_Ico : t ∈ Set.Ico a b := ⟨ht_mem.1, ht.2⟩
      have hmem : Set.Icc a b ∈ 𝓝[≥] t := Icc_mem_nhdsGE_of_mem ht_Ico
      exact h.mono_of_mem_nhdsWithin hmem
    have hY₂_diff_r : ∀ t ∈ Set.Ico t₀ b,
        HasDerivWithinAt Y₂ (v t (Y₂ t)) (Set.Ici t) t := by
      intro t ht
      have ht_mem : t ∈ Set.Icc a b :=
        ⟨ht₀_a.trans ht.1, ht.2.le⟩
      have h := hY₂' t ht_mem
      have ht_Ico : t ∈ Set.Ico a b := ⟨ht_mem.1, ht.2⟩
      have hmem : Set.Icc a b ∈ 𝓝[≥] t := Icc_mem_nhdsGE_of_mem ht_Ico
      exact h.mono_of_mem_nhdsWithin hmem
    exact ODE_solution_unique_of_mem_Icc_right
      (v := v) (s := fun _ => Set.univ) (K := K)
      (f := Y₁) (g := Y₂) (a := t₀) (b := b)
      hLip_r hY₁_cont_r hY₁_diff_r (fun _ _ => Set.mem_univ _)
      hY₂_cont_r hY₂_diff_r (fun _ _ => Set.mem_univ _) h_eq
  have h_left : Set.EqOn Y₁ Y₂ (Set.Icc a t₀) := by
    have hLip_l : ∀ t ∈ Set.Ioc a t₀,
        LipschitzOnWith K (v t) (Set.univ : Set E) := by
      intro t ht
      have ht_mem : t ∈ Set.Icc a b :=
        ⟨ht.1.le, ht.2.trans ht₀_b⟩
      exact hLip t ht_mem
    have hY₁_cont_l : ContinuousOn Y₁ (Set.Icc a t₀) :=
      hY₁_cont.mono (Set.Icc_subset_Icc_right ht₀_b)
    have hY₂_cont_l : ContinuousOn Y₂ (Set.Icc a t₀) :=
      hY₂_cont.mono (Set.Icc_subset_Icc_right ht₀_b)
    have hY₁_diff_l : ∀ t ∈ Set.Ioc a t₀,
        HasDerivWithinAt Y₁ (v t (Y₁ t)) (Set.Iic t) t := by
      intro t ht
      have ht_mem : t ∈ Set.Icc a b :=
        ⟨ht.1.le, ht.2.trans ht₀_b⟩
      have h := hY₁' t ht_mem
      have ht_Ioc : t ∈ Set.Ioc a b := ⟨ht.1, ht.2.trans ht₀_b⟩
      have hmem : Set.Icc a b ∈ 𝓝[≤] t := Icc_mem_nhdsLE_of_mem ht_Ioc
      exact h.mono_of_mem_nhdsWithin hmem
    have hY₂_diff_l : ∀ t ∈ Set.Ioc a t₀,
        HasDerivWithinAt Y₂ (v t (Y₂ t)) (Set.Iic t) t := by
      intro t ht
      have ht_mem : t ∈ Set.Icc a b :=
        ⟨ht.1.le, ht.2.trans ht₀_b⟩
      have h := hY₂' t ht_mem
      have ht_Ioc : t ∈ Set.Ioc a b := ⟨ht.1, ht.2.trans ht₀_b⟩
      have hmem : Set.Icc a b ∈ 𝓝[≤] t := Icc_mem_nhdsLE_of_mem ht_Ioc
      exact h.mono_of_mem_nhdsWithin hmem
    exact ODE_solution_unique_of_mem_Icc_left
      (v := v) (s := fun _ => Set.univ) (K := K)
      (f := Y₁) (g := Y₂) (a := a) (b := t₀)
      hLip_l hY₁_cont_l hY₁_diff_l (fun _ _ => Set.mem_univ _)
      hY₂_cont_l hY₂_diff_l (fun _ _ => Set.mem_univ _) h_eq
  have hunion : Set.Icc a t₀ ∪ Set.Icc t₀ b = Set.Icc a b :=
    Set.Icc_union_Icc_eq_Icc ht₀_a ht₀_b
  intro t ht
  have : t ∈ Set.Icc a t₀ ∪ Set.Icc t₀ b := by rw [hunion]; exact ht
  rcases this with htl | htr
  · exact h_left htl
  · exact h_right htr

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
