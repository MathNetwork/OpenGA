import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.CompactInclusion
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.TensorChartComponentSobolev.TensorChartComponentSobolevIntrinsic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_smooth_close_to_TensorH1_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (v : TensorH1Compl g r s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : SmoothCcTensorH1 g r s,
      ‖v - smoothToTensorH1Compl (I := I) (M := M) g r s S‖ < δ := by
  have h_dense : DenseRange (smoothToTensorH1Compl (I := I) (M := M) g r s) :=
    denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall] at h_dense
  have hv_in : v ∈ closure
      (Set.range (smoothToTensorH1Compl (I := I) (M := M) g r s)) :=
    h_dense v
  rw [Metric.mem_closure_iff] at hv_in
  obtain ⟨q, ⟨S, hS_eq⟩, hS_close⟩ := hv_in δ hδ
  refine ⟨S, ?_⟩
  rw [show smoothToTensorH1Compl (I := I) (M := M) g r s S = q from hS_eq]
  rw [dist_eq_norm] at hS_close
  exact hS_close

set_option maxHeartbeats 4000000 in

omit [CompleteSpace E] in
theorem tensorH1ComplToTensorL2_isCompactOperator_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (TensorH1ComplToTensorL2 (I := I) (M := M) g r s) := by
  classical
  have h_uniform :=
    tensorChartComponent_wkpNormChart_le (I := I) (M := M) g r s
  have h_iff := isCompactOperator_iff_isCompact_closure_image_closedBall
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s :
        TensorH1Compl g r s →ₗ[ℝ] TensorL2 r s g) zero_lt_one
  refine h_iff.mpr ?_
  rw [isCompact_iff_isSeqCompact]
  set T : TensorH1Compl g r s →L[ℝ] TensorL2 r s g :=
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s with hT_def
  intro y hy_in_closure
  have h_choose_z : ∀ n : ℕ, ∃ z ∈ T '' Metric.closedBall (0 : TensorH1Compl g r s) 1,
      dist (y n) z < 1 / (n + 1 : ℝ) := by
    intro n
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hy_n := hy_in_closure n
    rw [Metric.mem_closure_iff] at hy_n
    exact hy_n _ h_pos
  choose z hz_mem hz_close using h_choose_z
  have h_choose_x : ∀ n : ℕ,
      ∃ x ∈ Metric.closedBall (0 : TensorH1Compl g r s) 1, T x = z n :=
    fun n => hz_mem n
  choose x hx_mem hx_eq using h_choose_x
  have h_choose_S : ∀ n : ℕ, ∃ S : SmoothCcTensorH1 g r s,
      ‖x n - smoothToTensorH1Compl (I := I) (M := M) g r s S‖ <
        1 / (n + 1 : ℝ) := by
    intro n
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    exact exists_smooth_close_to_TensorH1_intrinsic
      (I := I) (M := M) g r s (x n) h_pos
  choose S hS_close using h_choose_S
  have h_xn_norm : ∀ n : ℕ, ‖x n‖ ≤ 1 := by
    intro n
    have hxn_mem : x n ∈ Metric.closedBall (0 : TensorH1Compl g r s) 1 := hx_mem n
    rw [Metric.mem_closedBall, dist_zero_right] at hxn_mem
    exact hxn_mem
  have h_S_isometric : ∀ n : ℕ,
      ‖smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ = ‖S n‖ := by
    intro n
    rw [smoothToTensorH1Compl_apply]
    exact UniformSpace.Completion.norm_coe (S n)
  have h_Sn_norm_le_two : ∀ n : ℕ, ‖S n‖ ≤ 2 := by
    intro n
    have h_iso := h_S_isometric n
    have h_close :
        ‖x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ ≤ 1 := by
      have h_lt :
          ‖x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ <
            1 / (n + 1) := hS_close n
      have h_inv_le_one : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    have h_xn_le : ‖x n‖ ≤ 1 := h_xn_norm n
    have h_tri : ‖smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ ≤
        ‖x n‖ + ‖x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ := by
      have h_id : smoothToTensorH1Compl (I := I) (M := M) g r s (S n) =
          x n - (x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n)) := by
        abel
      have h_norm_le :
          ‖x n - (x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n))‖ ≤
              ‖x n‖ +
                ‖x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ :=
        norm_sub_le (x n)
          (x n - smoothToTensorH1Compl (I := I) (M := M) g r s (S n))
      have h_id' :
          ‖smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ =
              ‖x n - (x n -
                smoothToTensorH1Compl (I := I) (M := M) g r s (S n))‖ := by
        rw [← h_id]
      rw [h_id']
      exact h_norm_le
    have h_smooth_le :
        ‖smoothToTensorH1Compl (I := I) (M := M) g r s (S n)‖ ≤ 2 := by linarith
    rw [← h_iso]
    exact h_smooth_le
  obtain ⟨C, hC_nn, h_uniform_bound⟩ := h_uniform
  have h_wkp_bound : ∀ (α : M)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s (S n).toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal (2 * C) := by
    intro α Idx Jdx n
    have h := h_uniform_bound (S n) α Idx Jdx
    have h_coe : (‖S n‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖S n‖ := by
      rw [show ((‖S n‖₊ : ℝ≥0∞)) = ‖S n‖ₑ from (enorm_eq_nnnorm (S n)).symm,
        ← ofReal_norm_eq_enorm (S n)]
    rw [h_coe] at h
    have h_mul : ENNReal.ofReal C * ENNReal.ofReal ‖S n‖ =
        ENNReal.ofReal (C * ‖S n‖) :=
      (ENNReal.ofReal_mul hC_nn).symm
    rw [h_mul] at h
    have h_le : C * ‖S n‖ ≤ 2 * C := by
      have h_Sn_le := h_Sn_norm_le_two n
      nlinarith [hC_nn, h_Sn_le, norm_nonneg (S n)]
    exact h.trans (ENNReal.ofReal_le_ofReal h_le)
  obtain ⟨φ, hφ_mono, T_lim, h_tendsto_T⟩ :=
    tensorH1Compl_to_tensorL2_relatively_compact
      (I := I) (M := M) g r s (S := S) (R := 2 * C) h_wkp_bound
  have h_smooth_tendsto :
      Tendsto (fun k =>
          TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))))
        atTop (𝓝 T_lim) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact h_tendsto_T
  have h_y_tendsto : Tendsto (fun k => y (φ k)) atTop (𝓝 T_lim) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun k : ℕ =>
        dist (y (φ k)) T_lim) (fun _ => dist_nonneg)
      (g := fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) +
              dist
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))))
                T_lim)
      (fun k => ?_)
      ?_
    · have h_t1 : dist (y (φ k)) T_lim ≤
          dist (y (φ k)) (z (φ k)) + dist (z (φ k)) T_lim := dist_triangle _ _ _
      have h_t2 : dist (z (φ k)) T_lim ≤
          dist (z (φ k))
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k)))) +
            dist
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))))
              T_lim :=
        dist_triangle _ _ _
      have h_yz : dist (y (φ k)) (z (φ k)) < 1 / ((φ k : ℝ) + 1) :=
        hz_close (φ k)
      have hT_S_eq :
          TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))) =
            T (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))) := by
        rw [hT_def]
      have h_zS_eq : z (φ k) -
            TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))) =
          T (x (φ k) -
            smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))) := by
        rw [← hx_eq (φ k), hT_S_eq, ← T.map_sub]
      have h_zS_dist : dist (z (φ k))
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k)))) =
          ‖T (x (φ k) -
            smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k)))‖ := by
        rw [dist_eq_norm]
        rw [h_zS_eq]
      have h_zS_le : dist (z (φ k))
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k)))) ≤
          ‖x (φ k) -
            smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))‖ := by
        rw [h_zS_dist]
        rw [hT_def]
        exact norm_TensorH1ComplToTensorL2_apply_le
          (I := I) (M := M) g r s _
      have h_xS_lt : ‖x (φ k) -
            smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))‖ <
          1 / ((φ k : ℝ) + 1) :=
        hS_close (φ k)
      have h_phi_ge : (k : ℝ) + 1 ≤ (φ k : ℝ) + 1 := by
        have h_phi_ge_k : k ≤ φ k := hφ_mono.le_apply
        exact_mod_cast Nat.add_le_add_right h_phi_ge_k 1
      have h_phi_pos : (0 : ℝ) < (φ k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (φ k : ℝ) := Nat.cast_nonneg _
        linarith
      have h_k_pos : (0 : ℝ) < (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith
      have h_inv_le : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le h_k_pos h_phi_ge
      calc
        dist (y (φ k)) T_lim
            ≤ dist (y (φ k)) (z (φ k)) + dist (z (φ k)) T_lim := h_t1
        _ ≤ dist (y (φ k)) (z (φ k)) +
              (dist (z (φ k))
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (smoothToTensorH1Compl (I := I) (M := M) g r s
                    (S (φ k)))) +
                dist
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (smoothToTensorH1Compl (I := I) (M := M) g r s
                      (S (φ k))))
                  T_lim) :=
              add_le_add le_rfl h_t2
        _ ≤ 1 / ((φ k : ℝ) + 1) + 1 / ((φ k : ℝ) + 1) +
              dist
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (smoothToTensorH1Compl (I := I) (M := M) g r s
                    (S (φ k))))
                T_lim := by
              have hzS_lt : dist (z (φ k))
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (smoothToTensorH1Compl (I := I) (M := M) g r s
                        (S (φ k)))) <
                  1 / ((φ k : ℝ) + 1) :=
                lt_of_le_of_lt h_zS_le h_xS_lt
              linarith [le_of_lt h_yz, le_of_lt hzS_lt]
        _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) +
              dist
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (smoothToTensorH1Compl (I := I) (M := M) g r s
                    (S (φ k))))
                T_lim := by
              linarith
        _ = 2 * (1 / ((k : ℝ) + 1)) +
              dist
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (smoothToTensorH1Compl (I := I) (M := M) g r s
                    (S (φ k))))
                T_lim := by ring
    · have h1 : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)))
          atTop (𝓝 0) := by
        rw [show (0 : ℝ) = 2 * 0 by ring]
        exact (tendsto_const_nhds (x := (2 : ℝ))).mul
          tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun k : ℕ =>
          dist
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (smoothToTensorH1Compl (I := I) (M := M) g r s (S (φ k))))
            T_lim) atTop (𝓝 0) :=
        tendsto_iff_dist_tendsto_zero.mp h_smooth_tendsto
      rw [show (0 : ℝ) = 0 + 0 by ring]
      exact h1.add h2
  refine ⟨T_lim, ?_, φ, hφ_mono, h_y_tendsto⟩
  · exact IsClosed.mem_of_tendsto isClosed_closure h_y_tendsto
      (Filter.Eventually.of_forall (fun k => hy_in_closure (φ k)))

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
