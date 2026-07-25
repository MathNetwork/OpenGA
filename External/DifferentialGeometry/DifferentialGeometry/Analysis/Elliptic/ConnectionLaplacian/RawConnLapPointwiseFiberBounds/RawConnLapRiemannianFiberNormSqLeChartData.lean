import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapChartCoeffsUniformBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_sq_le_iteratedFDeriv_two_sq
    {f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : ContDiffAt ℝ 2 f y)
    (k l : Fin (Module.finrank ℝ E)) :
    (euclidPartial (E := E) l (euclidPartial (E := E) k f) y) ^ 2 ≤
      ‖iteratedFDeriv ℝ 2 f y‖ ^ 2 := by
  classical
  have hf_fderiv_cd1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := by
    have h2 : ContDiffAt ℝ ((1 : ℕ) + 1) f y := by
      simpa using hf
    exact h2.fderiv_right_succ
  have hf_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) y :=
    hf_fderiv_cd1.differentiableAt_one
  set ek : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := EuclideanSpace.single k 1
  set el : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := EuclideanSpace.single l 1
  set evalEk : (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ek with hEvalEk_def
  have h_apply_def :
      (fun z => fderiv ℝ f z ek) = evalEk ∘ (fderiv ℝ f) := by
    funext z; rfl
  have h_diff_evalEk : DifferentiableAt ℝ evalEk (fderiv ℝ f y) :=
    evalEk.differentiable.differentiableAt
  have h_fderiv_evalEk_at :
      fderiv ℝ evalEk (fderiv ℝ f y) = evalEk :=
    ContinuousLinearMap.fderiv evalEk
  have h_diff_app : DifferentiableAt ℝ
      (fun z => fderiv ℝ f z ek) y := by
    rw [h_apply_def]
    exact h_diff_evalEk.comp y hf_fderiv_diff
  have h_fderiv_app :
      fderiv ℝ (fun z => fderiv ℝ f z ek) y =
        evalEk.comp (fderiv ℝ (fderiv ℝ f) y) := by
    rw [h_apply_def]
    rw [fderiv_comp y h_diff_evalEk hf_fderiv_diff]
    rw [h_fderiv_evalEk_at]
  have h_eval_el :
      fderiv ℝ (fun z => fderiv ℝ f z ek) y el =
        fderiv ℝ (fderiv ℝ f) y el ek := by
    rw [h_fderiv_app]
    simp [evalEk, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply]
  have h_two_apply :
      iteratedFDeriv ℝ 2 f y (![el, ek] : Fin 2 → _) =
        fderiv ℝ (fderiv ℝ f) y el ek := by
    have := iteratedFDeriv_two_apply (𝕜 := ℝ) f y (![el, ek])
    simpa using this
  have h_lhs_value :
      euclidPartial (E := E) l (euclidPartial (E := E) k f) y =
        fderiv ℝ (fun z => fderiv ℝ f z ek) y el := by
    unfold euclidPartial
    rfl
  have h_opNorm :
      ‖iteratedFDeriv ℝ 2 f y (![el, ek] : Fin 2 → _)‖ ≤
        ‖iteratedFDeriv ℝ 2 f y‖ *
          ∏ i : Fin 2, ‖(![el, ek] : Fin 2 → _) i‖ :=
    (iteratedFDeriv ℝ 2 f y).le_opNorm _
  have h_norm_el : ‖el‖ = 1 := by simp [el]
  have h_norm_ek : ‖ek‖ = 1 := by simp [ek]
  have h_prod : (∏ i : Fin 2, ‖(![el, ek] : Fin 2 → _) i‖) = 1 := by
    rw [Fin.prod_univ_two]
    simp [h_norm_el, h_norm_ek]
  have h_value :
      euclidPartial (E := E) l (euclidPartial (E := E) k f) y =
        iteratedFDeriv ℝ 2 f y (![el, ek] : Fin 2 → _) := by
    rw [h_lhs_value, h_eval_el, ← h_two_apply]
  have h_abs : |euclidPartial (E := E) l (euclidPartial (E := E) k f) y| ≤
      ‖iteratedFDeriv ℝ 2 f y‖ := by
    rw [h_value]
    have h := h_opNorm
    rw [h_prod, mul_one] at h
    have h_norm_eq : ‖iteratedFDeriv ℝ 2 f y (![el, ek] : Fin 2 → _)‖ =
        |iteratedFDeriv ℝ 2 f y (![el, ek] : Fin 2 → _)| := by rfl
    rw [h_norm_eq] at h
    exact h
  have h_sq :
      (euclidPartial (E := E) l (euclidPartial (E := E) k f) y) ^ 2 =
        |euclidPartial (E := E) l (euclidPartial (E := E) k f) y| ^ 2 := by
    rw [sq_abs]
  rw [h_sq]
  exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2

theorem rawTensorConnLap_riemannianFiberNormSq_le_chart_α_data_on_pouTsupport_goodSet
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        riemannianFiberNormSq (I := I) (M := M) g r s b
            (rawTensorConnLap (I := I) g r s
              (fun z : M => T₀.toSection z) b) ≤
          C *
            ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                ((‖iteratedFDeriv ℝ 2
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
                    ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                    ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) + 1) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨C_H, hC_H_nn, hH⟩ :=
    riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g r s α
  set S : SmoothCcTensor g r s :=
    rawTensorConnLapSmooth (I := I) g r s T₀ with hS_def
  have hB_each : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ (b : M),
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          (tensorChartComponentRaw (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b) ^ 2 ≤
            K * (∑ k : Fin n, ∑ l : Fin n,
                  (euclidPartial (E := E) l
                    (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw
                          (I := I) (M := M) g r s T₀ α Idx Jdx)))
                    ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2 + 1) := by
    intro Idx Jdx
    exact rawTensorConnLap_chartα_coeffs_uniform_bound_on_pouTsupport
      (I := I) (M := M) g r s α Idx Jdx T₀
  choose K_fn hK_fn_nn hK_fn_bd using hB_each
  set IJ_set : Finset ((Fin r → Fin n) × (Fin s → Fin n)) := Finset.univ
  have hIJ_ne : IJ_set.Nonempty := Finset.univ_nonempty
  set K_max : ℝ := IJ_set.sup' hIJ_ne (fun p => K_fn p.1 p.2) with hKmax_def
  have hKmax_nn : 0 ≤ K_max := by
    rcases hIJ_ne with ⟨p₀, hp₀⟩
    exact (hK_fn_nn p₀.1 p₀.2).trans
      (Finset.le_sup'_of_le (fun p => K_fn p.1 p.2) hp₀ (le_refl _))
  have hKmax_bd : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      K_fn Idx Jdx ≤ K_max := fun Idx Jdx =>
    Finset.le_sup'_of_le (fun p => K_fn p.1 p.2) (Finset.mem_univ (Idx, Jdx)) (le_refl _)
  set cardIJ : ℝ := (n : ℝ) ^ r * (n : ℝ) ^ s with hcardIJ_def
  have hcardIJ_nn : 0 ≤ cardIJ :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg n) r) (pow_nonneg (Nat.cast_nonneg n) s)
  set nSq : ℝ := (n : ℝ) ^ 2 with hnSq_def
  have hnSq_nn : 0 ≤ nSq := pow_nonneg (Nat.cast_nonneg n) 2
  set C : ℝ := C_H * cardIJ * K_max * (nSq + 1) with hC_def
  have hC_nn : 0 ≤ C :=
    mul_nonneg (mul_nonneg (mul_nonneg hC_H_nn hcardIJ_nn) hKmax_nn) (by linarith)
  refine ⟨C, hC_nn, ?_⟩
  intro b hb_inter
  have hH_at := hH (S := S) (b := b) hb_inter.1
  have hS_value : S.toSection b =
      rawTensorConnLap (I := I) g r s (fun z : M => T₀.toSection z) b := by
    rw [hS_def]; exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T₀ b
  have hH_rewritten :
      riemannianFiberNormSq (I := I) (M := M) g r s b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b) ≤
        C_H *
          (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              (tensorChartComponentRaw (I := I) (M := M) g r s
                S α Idx Jdx b) ^ 2) := by
    rw [← hS_value]; exact hH_at
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hPerIJ : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      (tensorChartComponentRaw (I := I) (M := M) g r s
            S α Idx Jdx b) ^ 2 ≤
        K_max * (∑ k : Fin n, ∑ l : Fin n,
            (euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2
          + 1) := by
    intro Idx Jdx
    have h_sum_nn :
        0 ≤ (∑ k : Fin n, ∑ l : Fin n,
            (euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2
          + 1) := by
      have h_inner :
          0 ≤ (∑ k : Fin n, ∑ l : Fin n,
            (euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2) :=
        Finset.sum_nonneg (fun _ _ =>
          Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      linarith
    calc (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2
        = (tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b) ^ 2 := by rw [hS_def]
      _ ≤ K_fn Idx Jdx *
            (∑ k : Fin n, ∑ l : Fin n,
                (euclidPartial (E := E) l
                  (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2
              + 1) := hK_fn_bd Idx Jdx b hb_inter
      _ ≤ K_max * _ := mul_le_mul_of_nonneg_right (hKmax_bd Idx Jdx) h_sum_nn
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb_inter.2
    have hb_src : b ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
    have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hb_src
    exact ⟨(extChartAt I α) b, hb_tgt, rfl⟩
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_y_mem_nhds : chartTargetEuclid (I := I) (M := M) α ∈ nhds y :=
    h_open.mem_nhds hy_target
  have hPartialSum_le : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      (∑ k : Fin n, ∑ l : Fin n,
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2) ≤
      nSq * ‖iteratedFDeriv ℝ 2
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖ ^ 2 := by
    intro Idx Jdx
    have h_cd_on : ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) α) :=
      chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s T₀ α Idx Jdx
    have h_cd_at_inf : ContDiffAt ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y :=
      h_cd_on.contDiffAt h_y_mem_nhds
    have h_cd_at_2 : ContDiffAt ℝ 2
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y := by
      apply h_cd_at_inf.of_le
      decide
    set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
      chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
      with hf_def
    have h_each : ∀ k l : Fin n,
        (euclidPartial (E := E) l (euclidPartial (E := E) k f) y) ^ 2 ≤
          ‖iteratedFDeriv ℝ 2 f y‖ ^ 2 := by
      intro k l
      exact euclidPartial_sq_le_iteratedFDeriv_two_sq h_cd_at_2 k l
    have h_sum :
        (∑ k : Fin n, ∑ l : Fin n,
          (euclidPartial (E := E) l (euclidPartial (E := E) k f) y) ^ 2) ≤
        (∑ k : Fin n, ∑ l : Fin n, ‖iteratedFDeriv ℝ 2 f y‖ ^ 2) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      refine Finset.sum_le_sum (fun l _ => ?_)
      exact h_each k l
    have h_const_sum :
        (∑ _k : Fin n, ∑ _l : Fin n, ‖iteratedFDeriv ℝ 2 f y‖ ^ 2) =
          nSq * ‖iteratedFDeriv ℝ 2 f y‖ ^ 2 := by
      rw [Finset.sum_const, Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hnSq_def]
      ring
    calc (∑ k : Fin n, ∑ l : Fin n,
          (euclidPartial (E := E) l (euclidPartial (E := E) k f) y) ^ 2)
        ≤ (∑ k : Fin n, ∑ l : Fin n, ‖iteratedFDeriv ℝ 2 f y‖ ^ 2) := h_sum
      _ = nSq * ‖iteratedFDeriv ℝ 2 f y‖ ^ 2 := h_const_sum
  set bigSumPartial : ℝ :=
    ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
      (∑ k : Fin n, ∑ l : Fin n,
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2)
    with hBigSumPartial_def
  set bigSumIterFD : ℝ :=
    ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
      ‖iteratedFDeriv ℝ 2
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖ ^ 2
    with hBigSumIterFD_def
  set bigSumChartPushed : ℝ :=
    ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2
    with hBigSumChartPushed_def
  set bigSumGoal : ℝ :=
    ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
      (‖iteratedFDeriv ℝ 2
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖ ^ 2 +
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2)
    with hBigSumGoal_def
  have hBigSumGoal_eq : bigSumGoal = bigSumIterFD + bigSumChartPushed := by
    rw [hBigSumGoal_def, hBigSumIterFD_def, hBigSumChartPushed_def]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    rw [← Finset.sum_add_distrib]
  have hBigSumPartial_nn : 0 ≤ bigSumPartial := by
    rw [hBigSumPartial_def]
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    exact sq_nonneg _
  have hBigSumIterFD_nn : 0 ≤ bigSumIterFD := by
    rw [hBigSumIterFD_def]
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    exact sq_nonneg _
  have hBigSumChartPushed_nn : 0 ≤ bigSumChartPushed := by
    rw [hBigSumChartPushed_def]
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    exact sq_nonneg _
  have hBigSumGoal_nn : 0 ≤ bigSumGoal := by
    rw [hBigSumGoal_eq]
    linarith [hBigSumIterFD_nn, hBigSumChartPushed_nn]
  have hSumOverIJ_constSum :
      (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, K_max *
        ((∑ k : Fin n, ∑ l : Fin n,
          (euclidPartial (E := E) l
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2)
          + 1)) =
        K_max * (bigSumPartial + cardIJ) := by
    rw [hBigSumPartial_def, hcardIJ_def]
    have h_inner_jdx : ∀ Idx : Fin r → Fin n,
        (∑ Jdx : Fin s → Fin n, K_max *
          ((∑ k : Fin n, ∑ l : Fin n,
            (euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2)
            + 1)) =
        K_max * (∑ Jdx : Fin s → Fin n,
          (∑ k : Fin n, ∑ l : Fin n,
            (euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2))
        + K_max * (n : ℝ) ^ s := by
      intro Idx
      rw [Finset.sum_congr rfl (fun Jdx _ => by ring :
        ∀ Jdx ∈ (Finset.univ : Finset (Fin s → Fin n)), K_max *
          ((∑ k : Fin n, ∑ l : Fin n,
            (euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2)
            + 1) =
          K_max *
            (∑ k : Fin n, ∑ l : Fin n,
              (euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2)
          + K_max)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [Finset.sum_congr rfl (fun Idx _ => h_inner_jdx Idx)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hSumIJ_rawCompSq :
      (∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          (tensorChartComponentRaw (I := I) (M := M) g r s
            S α Idx Jdx b) ^ 2) ≤
      K_max * (bigSumPartial + cardIJ) := by
    calc (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
            (tensorChartComponentRaw (I := I) (M := M) g r s
              S α Idx Jdx b) ^ 2)
        ≤ (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
            K_max * ((∑ k : Fin n, ∑ l : Fin n,
              (euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw
                      (I := I) (M := M) g r s T₀ α Idx Jdx))) y) ^ 2) + 1)) := by
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact hPerIJ Idx Jdx
      _ = K_max * (bigSumPartial + cardIJ) := hSumOverIJ_constSum
  have hBigSumPartial_le :
      bigSumPartial ≤ nSq * bigSumIterFD := by
    rw [hBigSumPartial_def, hBigSumIterFD_def, Finset.mul_sum]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact hPartialSum_le Idx Jdx
  have hCard_one_le : (1 : ℝ) ≤ cardIJ := by
    have hN_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
    have h_n_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN_pos
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ r := one_le_pow₀ h_n_one
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ s := one_le_pow₀ h_n_one
    rw [hcardIJ_def]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (n : ℝ) ^ r * (n : ℝ) ^ s :=
          mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
  have hBigSumIterFD_le_Goal : bigSumIterFD ≤ bigSumGoal := by
    rw [hBigSumGoal_eq]; linarith [hBigSumChartPushed_nn]
  have h_key :
      bigSumPartial + cardIJ ≤ cardIJ * (nSq + 1) * (bigSumGoal + 1) := by
    have h_bsp_le_goal : bigSumPartial ≤ nSq * bigSumGoal :=
      hBigSumPartial_le.trans (mul_le_mul_of_nonneg_left hBigSumIterFD_le_Goal hnSq_nn)
    have h1 : nSq * bigSumGoal ≤ cardIJ * (nSq * bigSumGoal) := by
      have hh : (0 : ℝ) ≤ nSq * bigSumGoal := mul_nonneg hnSq_nn hBigSumGoal_nn
      nlinarith [hCard_one_le, hh]
    have h2 : (0 : ℝ) ≤ cardIJ * nSq := mul_nonneg hcardIJ_nn hnSq_nn
    have h3 : (0 : ℝ) ≤ cardIJ * bigSumGoal :=
      mul_nonneg hcardIJ_nn hBigSumGoal_nn
    nlinarith [h_bsp_le_goal, h1, h2, h3]
  calc riemannianFiberNormSq (I := I) (M := M) g r s b
        (rawTensorConnLap (I := I) g r s (fun z : M => T₀.toSection z) b)
      ≤ C_H *
          (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              (tensorChartComponentRaw (I := I) (M := M) g r s
                S α Idx Jdx b) ^ 2) := hH_rewritten
    _ ≤ C_H * (K_max * (bigSumPartial + cardIJ)) :=
        mul_le_mul_of_nonneg_left hSumIJ_rawCompSq hC_H_nn
    _ ≤ C_H * (K_max * (cardIJ * (nSq + 1) * (bigSumGoal + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_key hKmax_nn) hC_H_nn
    _ = C * (bigSumGoal + 1) := by rw [hC_def]; ring

end Connection
end Integral
end DifferentialGeometry

end
