import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapRiemannianFiberNormSqLeChartDataT0Uniform
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.IteratedFDerivChartPushedRawBridge
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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

theorem rawTensorConnLap_riemannianFiberNormSq_le_chartPouSobolevSummand_T0_uniform
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          riemannianFiberNormSq (I := I) (M := M) g r s b
              (rawTensorConnLap (I := I) g r s
                (fun z : M => T₀.toSection z) b) ≤
            C *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∑ j ∈ Finset.range 3,
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                            T₀ α Idx Jdx
                          ∘ (extChartAt I α).symm)
                        ((extChartAt I α) b)‖ ^ 2) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨C_B, hC_B_nn, hB⟩ :=
    rawTensorConnLap_riemannianFiberNormSq_le_chart_α_data_T0_uniform
      (I := I) (M := M) g r s α
  set Lop : ℝ :=
      ‖((toEuclidean (E := E)).symm :
          EuclideanSpace ℝ (Fin n) ≃L[ℝ] E).toContinuousLinearMap‖
      with hLop_def
  have hLop_nn : 0 ≤ Lop := by rw [hLop_def]; exact norm_nonneg _
  set Lmax : ℝ := max 1 (Lop ^ 4) with hLmax_def
  have h_one_le_Lmax : (1 : ℝ) ≤ Lmax := by rw [hLmax_def]; exact le_max_left _ _
  have h_Lmax_nn : 0 ≤ Lmax := le_trans (by linarith : (0 : ℝ) ≤ 1) h_one_le_Lmax
  have h_Lop2_le_Lmax : Lop ^ 2 ≤ Lmax := by
    have h_Lop2_nn : 0 ≤ Lop ^ 2 := sq_nonneg _
    have h_Lop2_le_Lop4 : Lop ^ 2 ≤ max 1 (Lop ^ 2) ^ 2 := by
      have h_le : Lop ^ 2 ≤ max 1 (Lop ^ 2) := le_max_right _ _
      have h_one_le : (1 : ℝ) ≤ max 1 (Lop ^ 2) := le_max_left _ _
      calc Lop ^ 2 ≤ max 1 (Lop ^ 2) := h_le
        _ = max 1 (Lop ^ 2) * 1 := by ring
        _ ≤ max 1 (Lop ^ 2) * max 1 (Lop ^ 2) :=
            mul_le_mul_of_nonneg_left h_one_le
              (le_trans (by linarith : (0 : ℝ) ≤ 1) h_one_le)
        _ = max 1 (Lop ^ 2) ^ 2 := by ring
    by_cases h_Lop_le_one : Lop ≤ 1
    · have h_Lop2_le_one : Lop ^ 2 ≤ 1 := by
        have h_sq : Lop ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hLop_nn h_Lop_le_one 2
        simpa using h_sq
      exact le_trans h_Lop2_le_one h_one_le_Lmax
    · have h_one_lt_Lop : (1 : ℝ) < Lop := lt_of_not_ge h_Lop_le_one
      have h_one_le_Lop : (1 : ℝ) ≤ Lop := le_of_lt h_one_lt_Lop
      have h_Lop2_le_Lop4 : Lop ^ 2 ≤ Lop ^ 4 :=
        pow_le_pow_right₀ h_one_le_Lop (by norm_num : 2 ≤ 4)
      exact le_trans h_Lop2_le_Lop4 (le_max_right _ _)
  have h_Lop4_le_Lmax : Lop ^ 4 ≤ Lmax := by rw [hLmax_def]; exact le_max_right _ _
  set C : ℝ := C_B * 3 * Lmax with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact mul_nonneg (mul_nonneg hC_B_nn (by norm_num : (0 : ℝ) ≤ 3)) h_Lmax_nn
  refine ⟨C, hC_nn, ?_⟩
  intro T₀ b hb_inter
  have hB_at := hB T₀ (b := b) hb_inter
  set y : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) ((extChartAt I α) b)
    with hy_def
  have hb_src : b ∈ (chartAt H α).source := by
    have h_sub : tsupport
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
          (chartAt H α).source := by
      have := chartAtlasPOU_isSubordinate (I := I) (M := M) α
      exact this
    exact h_sub hb_inter.1
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_src
  have h_extat_b_in_target : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_extsrc
  have hy_in_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [hy_def]
    refine ⟨(extChartAt I α) b, h_extat_b_in_target, ?_⟩
    rfl
  have hsymm_y : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
    rw [hy_def]; exact (toEuclidean (E := E)).symm_apply_apply _
  have hcontDiff_comp : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      ContDiffOn ℝ ∞
        ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
          (extChartAt I α).symm)
        (extChartAt I α).target := by
    intro Idx Jdx
    have hraw_src : ContMDiffOn I 𝓘(ℝ) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
        ((chartAt H α).source) :=
      tensorChartComponentRaw_contMDiffOn_chart_source (I := I) (M := M)
        g r s T₀ α Idx Jdx
    have hraw_extsrc : ContMDiffOn I 𝓘(ℝ) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
        ((extChartAt I α).source) := by
      rw [extChartAt_source]; exact hraw_src
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
    have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
        (extChartAt I α).source := fun y' hy' => (extChartAt I α).map_target hy'
    exact (hraw_extsrc.comp hsymm hmaps).contDiffOn
  have h_per_IJ : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      ((‖iteratedFDeriv ℝ 2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
        (‖fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
        (chartPushedRaw I α
           (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2) ≤
      Lmax * (∑ j ∈ Finset.range 3,
        ‖iteratedFDeriv ℝ j
            ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
              (extChartAt I α).symm)
            ((extChartAt I α) b)‖ ^ 2) := by
    intro Idx Jdx
    set u : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
      with hu_def
    set v : E → ℝ := u ∘ (extChartAt I α).symm with hv_def
    set p : E := (extChartAt I α) b with hp_def
    have hp_eq : p = (toEuclidean (E := E)).symm y := by rw [hp_def, hsymm_y]
    set a0 : ℝ := ‖iteratedFDeriv ℝ 0 v p‖ ^ 2 with ha0_def
    set a1 : ℝ := ‖iteratedFDeriv ℝ 1 v p‖ ^ 2 with ha1_def
    set a2 : ℝ := ‖iteratedFDeriv ℝ 2 v p‖ ^ 2 with ha2_def
    have ha0_nn : 0 ≤ a0 := sq_nonneg _
    have ha1_nn : 0 ≤ a1 := sq_nonneg _
    have ha2_nn : 0 ≤ a2 := sq_nonneg _
    have h_sum_eq :
        (∑ j ∈ Finset.range 3,
          ‖iteratedFDeriv ℝ j
              ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
                (extChartAt I α).symm)
              ((extChartAt I α) b)‖ ^ 2) =
          a0 + a1 + a2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add]
    have h_order0 :
        (chartPushedRaw I α u y) ^ 2 = a0 := by
      have h_eq_sq :
          (chartPushedRaw I α u y) ^ 2 =
            (u ((extChartAt I α).symm
              ((toEuclidean (E := E)).symm y))) ^ 2 :=
        chartPushedRaw_sq_eq_compositionSq (I := I) (M := M)
          (α := α) (u := u) hy_in_target
      have h_arg_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) =
          (extChartAt I α).symm p := by rw [hp_eq]
      have h_uniqueLeftInv :
          (extChartAt I α).symm p = b := by
        rw [hp_def]
        exact (extChartAt I α).left_inv hb_extsrc
      have h_v_p_eq : v p = u b := by
        rw [hv_def]
        change u ((extChartAt I α).symm p) = u b
        rw [h_uniqueLeftInv]
      have h_a0_eq_v_sq : a0 = (v p) ^ 2 := by
        rw [ha0_def, norm_iteratedFDeriv_zero]
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_eq_sq, h_arg_eq, h_uniqueLeftInv, h_a0_eq_v_sq, h_v_p_eq]
    have h_order1 :
        (‖fderiv ℝ (chartPushedRaw I α u) y‖) ^ 2 ≤ Lop ^ 2 * a1 := by
      have hbridge :=
        fderiv_chartPushedRaw_sq_le_compFderivSq (I := I) (M := M)
          (α := α) (u := u)
          (by
            have hc := hcontDiff_comp Idx Jdx
            refine hc.of_le ?_
            exact (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)))
          (y := y) hy_in_target
      have h_norm_eq : ‖fderiv ℝ (u ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 = a1 := by
        rw [ha1_def, ← hp_eq]
        rw [show (‖iteratedFDeriv ℝ 1 v p‖ ^ 2) =
              (‖fderiv ℝ v p‖ ^ 2) from by rw [norm_iteratedFDeriv_one]]
      refine hbridge.trans ?_
      rw [h_norm_eq]
    have h_order2 :
        (‖iteratedFDeriv ℝ 2 (chartPushedRaw I α u) y‖) ^ 2 ≤ Lop ^ 4 * a2 := by
      have hbridge :=
        iteratedFDeriv_two_chartPushedRaw_sq_le_compIterSq (I := I) (M := M)
          (α := α) (u := u)
          (by
            have hc := hcontDiff_comp Idx Jdx
            refine hc.of_le ?_
            exact (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
          (y := y) hy_in_target
      have h_norm_eq : ‖iteratedFDeriv ℝ 2 (u ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 = a2 := by
        rw [ha2_def, ← hp_eq]
      refine hbridge.trans ?_
      rw [h_norm_eq]
    rw [h_sum_eq]
    have h_o0_le : (chartPushedRaw I α u y) ^ 2 ≤ Lmax * a0 := by
      rw [h_order0]
      calc a0 = 1 * a0 := by ring
        _ ≤ Lmax * a0 := mul_le_mul_of_nonneg_right h_one_le_Lmax ha0_nn
    have h_o1_le : (‖fderiv ℝ (chartPushedRaw I α u) y‖) ^ 2 ≤ Lmax * a1 := by
      calc (‖fderiv ℝ (chartPushedRaw I α u) y‖) ^ 2
          ≤ Lop ^ 2 * a1 := h_order1
        _ ≤ Lmax * a1 := mul_le_mul_of_nonneg_right h_Lop2_le_Lmax ha1_nn
    have h_o2_le : (‖iteratedFDeriv ℝ 2 (chartPushedRaw I α u) y‖) ^ 2 ≤ Lmax * a2 := by
      calc (‖iteratedFDeriv ℝ 2 (chartPushedRaw I α u) y‖) ^ 2
          ≤ Lop ^ 4 * a2 := h_order2
        _ ≤ Lmax * a2 := mul_le_mul_of_nonneg_right h_Lop4_le_Lmax ha2_nn
    calc ((‖iteratedFDeriv ℝ 2 (chartPushedRaw I α u) y‖) ^ 2 +
          (‖fderiv ℝ (chartPushedRaw I α u) y‖) ^ 2 +
          (chartPushedRaw I α u y) ^ 2)
        ≤ Lmax * a2 + Lmax * a1 + Lmax * a0 := by
          exact add_le_add (add_le_add h_o2_le h_o1_le) h_o0_le
      _ = Lmax * (a0 + a1 + a2) := by ring
  have hSumIJ :
      (∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          ((‖iteratedFDeriv ℝ 2
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
          (‖fderiv ℝ
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
          (chartPushedRaw I α
             (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2)) ≤
        Lmax * (∑ Idx : Fin r → Fin n,
                ∑ Jdx : Fin s → Fin n,
                  ∑ j ∈ Finset.range 3,
                    ‖iteratedFDeriv ℝ j
                        ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                          ∘ (extChartAt I α).symm)
                        ((extChartAt I α) b)‖ ^ 2) := by
    have h_inner :
        (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            ((‖iteratedFDeriv ℝ 2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
            (‖fderiv ℝ
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
            (chartPushedRaw I α
               (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2)) ≤
          ∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              Lmax * (∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                      ∘ (extChartAt I α).symm)
                    ((extChartAt I α) b)‖ ^ 2) :=
      Finset.sum_le_sum (fun Idx _ =>
        Finset.sum_le_sum (fun Jdx _ => h_per_IJ Idx Jdx))
    have h_pull :
        (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            Lmax * (∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                    ∘ (extChartAt I α).symm)
                  ((extChartAt I α) b)‖ ^ 2)) =
          Lmax * (∑ Idx : Fin r → Fin n,
                  ∑ Jdx : Fin s → Fin n,
                    ∑ j ∈ Finset.range 3,
                      ‖iteratedFDeriv ℝ j
                          ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                            ∘ (extChartAt I α).symm)
                          ((extChartAt I α) b)‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [Finset.mul_sum]
    calc (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              ((‖iteratedFDeriv ℝ 2
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
              (‖fderiv ℝ
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
              (chartPushedRaw I α
                 (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2))
        ≤ ∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              Lmax * (∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                      ∘ (extChartAt I α).symm)
                    ((extChartAt I α) b)‖ ^ 2) := h_inner
      _ = Lmax * (∑ Idx : Fin r → Fin n,
                  ∑ Jdx : Fin s → Fin n,
                    ∑ j ∈ Finset.range 3,
                      ‖iteratedFDeriv ℝ j
                          ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                            ∘ (extChartAt I α).symm)
                          ((extChartAt I α) b)‖ ^ 2) := h_pull
  have h_chain : C_B *
      (∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          ((‖iteratedFDeriv ℝ 2
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
              ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
          (‖fderiv ℝ
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
              ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
          (chartPushedRaw I α
             (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
             ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) ≤
      C * (∑ Idx : Fin r → Fin n,
                ∑ Jdx : Fin s → Fin n,
                  ∑ j ∈ Finset.range 3,
                    ‖iteratedFDeriv ℝ j
                        ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                          ∘ (extChartAt I α).symm)
                        ((extChartAt I α) b)‖ ^ 2) := by
    have h_euclSum_eq :
        (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            ((‖iteratedFDeriv ℝ 2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
                ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
            (‖fderiv ℝ
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
                ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
            (chartPushedRaw I α
               (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
               ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) =
          (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              ((‖iteratedFDeriv ℝ 2
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
              (‖fderiv ℝ
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
              (chartPushedRaw I α
                 (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2)) := by
      rw [hy_def]
    set BigPat : ℝ :=
      ∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          ∑ j ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ j
                ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                  ∘ (extChartAt I α).symm)
                ((extChartAt I α) b)‖ ^ 2
      with hBigPat_def
    have hBigPat_nn : 0 ≤ BigPat := by
      rw [hBigPat_def]
      exact Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ =>
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    rw [h_euclSum_eq]
    have h_inner_le : C_B *
        (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            ((‖iteratedFDeriv ℝ 2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
            (‖fderiv ℝ
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
            (chartPushedRaw I α
               (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2)) ≤
        C_B * (Lmax * BigPat) := by
      apply mul_le_mul_of_nonneg_left _ hC_B_nn
      exact hSumIJ
    calc C_B *
        (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            ((‖iteratedFDeriv ℝ 2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
            (‖fderiv ℝ
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y‖) ^ 2 +
            (chartPushedRaw I α
               (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) y) ^ 2))
        ≤ C_B * (Lmax * BigPat) := h_inner_le
      _ ≤ C_B * 3 * Lmax * BigPat := by
        have h1 : C_B * (Lmax * BigPat) = C_B * Lmax * BigPat := by ring
        have h2 : C_B * Lmax * BigPat ≤ C_B * 3 * Lmax * BigPat := by
          apply mul_le_mul_of_nonneg_right _ hBigPat_nn
          have h3 : C_B * Lmax ≤ C_B * 3 * Lmax := by
            have : C_B * Lmax = C_B * 1 * Lmax := by ring
            rw [this]
            apply mul_le_mul_of_nonneg_right _ h_Lmax_nn
            apply mul_le_mul_of_nonneg_left _ hC_B_nn
            norm_num
          exact h3
        linarith
      _ = C * BigPat := by rw [hC_def]
  exact le_trans hB_at h_chain

end Connection
end Integral
end DifferentialGeometry

end
