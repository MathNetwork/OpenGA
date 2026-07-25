import DifferentialGeometry.Analysis.Sobolev.Solutions.WeakSolution
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientWeakLimit

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.H2WeakSolution

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

private lemma contDiff_kdi_partial_aux
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
        (EuclideanSpace.single k 1)) := by
  have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_i : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff
  have h_partial : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    h_apply_i.comp h_fderiv_smooth
  have h_fderiv_partial : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1))) :=
    h_partial.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_k : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single k 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ))).contDiff
  exact h_apply_k.comp h_fderiv_partial

omit [NeZero d] in

private lemma contDiff_partial_aux
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
  have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_i : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff
  exact h_apply_i.comp h_fderiv_smooth

omit [NeZero d] in

private lemma hasCompactSupport_partial_aux
    {u : E → ℝ} (hu_supp : HasCompactSupport u) (i : Fin d) :
    HasCompactSupport
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
  hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)

omit [NeZero d] in

private lemma hasCompactSupport_kdi_partial_aux
    {u : E → ℝ} (hu_supp : HasCompactSupport u) (i k : Fin d) :
    HasCompactSupport (fun y : E =>
      (fderiv ℝ (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
        (EuclideanSpace.single k 1)) := by
  have h_partial_supp : HasCompactSupport
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    hasCompactSupport_partial_aux hu_supp i
  exact h_partial_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)

omit [NeZero d] in

private lemma memLp_two_continuous_compact_support_restrict
    {f : E → ℝ} (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    (S : Set E) :
    MemLp f 2 (volume.restrict S) :=
  (hf_cont.memLp_of_hasCompactSupport hf_supp).restrict S

omit [NeZero d] in

theorem hasWeakPartialDeriv_kdi_partial_of_smooth
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {Ω : Set E} (hΩ : IsOpen Ω) (i k : Fin d) :
    DeGiorgi.HasWeakPartialDeriv (d := d) k
      (fun y : E =>
        (fderiv ℝ (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
          (EuclideanSpace.single k 1))
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))
      Ω := by
  have h_partial : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    contDiff_partial_aux hu i
  have h_partial_C1 : ContDiff ℝ 1
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    h_partial.of_le (by norm_cast)
  exact DeGiorgi.HasWeakPartialDeriv.of_contDiff (d := d) hΩ
    (i := k)
    (f := fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))
    h_partial_C1

omit [NeZero d] in

theorem eLpNorm_kdi_partial_le_of_uniform_diffQuot
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {Ω'' : Set E}
    (i k : Fin d) {M : ℝ} (_hM_nn : 0 ≤ M)
    (h_uniform_bound : ∀ h : ℝ, 0 < |h| → |h| ≤ 1 →
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)))
        2 (volume.restrict Ω'') ≤ ENNReal.ofReal M) :
    eLpNorm (fun y : E =>
        (fderiv ℝ (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
          (EuclideanSpace.single k 1))
      2 (volume.restrict Ω'') ≤ ENNReal.ofReal M := by
  classical
  set ψ : E → ℝ := fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1) with hψ_def
  set gψ : E → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single k 1) with hgψ_def
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_partial_aux hu i
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_C1 : ContDiff ℝ 1 ψ := hψ_smooth.of_le (by norm_cast)
  have h_seq_pos : ∀ j : ℕ, 0 < |((1 : ℝ) / (j + 1))| := fun j => by
    have h_pos : (0 : ℝ) < 1 / (j + 1) := by positivity
    rwa [abs_of_pos h_pos]
  have h_seq_le_one : ∀ j : ℕ, |((1 : ℝ) / (j + 1))| ≤ 1 := fun j => by
    have h_pos : (0 : ℝ) < 1 / (j + 1) := by positivity
    rw [abs_of_pos h_pos]
    rw [div_le_one (by positivity : (0 : ℝ) < (j + 1))]
    have h0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  have h_seq_ne : ∀ j : ℕ, ((1 : ℝ) / (j + 1)) ≠ 0 := fun j => by
    have h_pos : (0 : ℝ) < 1 / (j + 1) := by positivity
    exact h_pos.ne'
  have h_tendsto_pt : ∀ x,
      Tendsto (fun j : ℕ =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (j + 1)) ψ x) atTop (𝓝 (gψ x)) := by
    intro x
    have h_seq_tendsto : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1))
        atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ),
        Filter.Eventually.of_forall h_seq_ne⟩
    have h_dq_tendsto :=
      DifferentialGeometry.Analysis.Sobolev.tendsto_diffQuot_of_contDiff
        (d := d) hψ_C1 k x
    exact h_dq_tendsto.comp h_seq_tendsto
  have h_dq_bound : ∀ j : ℕ,
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot k
        ((1 : ℝ) / (j + 1)) ψ) 2 (volume.restrict Ω'') ≤
      ENNReal.ofReal M := fun j =>
    h_uniform_bound ((1 : ℝ) / (j + 1)) (h_seq_pos j) (h_seq_le_one j)
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_2toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
  have h_eLpNorm_to_lint : ∀ {f : E → ℝ},
      eLpNorm f 2 (volume.restrict Ω'') ^ (2 : ℝ) =
        ∫⁻ x in Ω'', (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(volume : Measure E) := by
    intro f
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_2_ne_zero h_2_ne_top]
    rw [h_2toReal]
    rw [← ENNReal.rpow_mul]
    rw [show (1 : ℝ) / 2 * 2 = 1 from by norm_num, ENNReal.rpow_one]
  have h_lint_dq_bound : ∀ j : ℕ,
      ∫⁻ x in Ω'', (‖DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (j + 1)) ψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
        ∂(volume : Measure E) ≤
      (ENNReal.ofReal M) ^ (2 : ℝ) := fun j => by
    rw [← h_eLpNorm_to_lint]
    exact ENNReal.rpow_le_rpow (h_dq_bound j) (by norm_num : (0 : ℝ) ≤ 2)
  have h_meas_dq : ∀ j : ℕ, Measurable
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k ((1 : ℝ) / (j + 1)) ψ) :=
    fun j => (DifferentialGeometry.Analysis.Sobolev.continuous_diffQuot_of_continuous
      (d := d) k _ hψ_cont).measurable
  have h_meas_lint : ∀ j : ℕ, Measurable (fun x : E =>
      (‖DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (j + 1)) ψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) := fun j =>
    ((h_meas_dq j).enorm).pow_const _
  have h_enorm_sq_tendsto : ∀ x,
      Tendsto (fun j : ℕ =>
        (‖DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (j + 1)) ψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) atTop
          (𝓝 ((‖gψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ))) := by
    intro x
    have h_enorm := (h_tendsto_pt x).enorm
    exact (ENNReal.continuous_rpow_const.tendsto _).comp h_enorm
  have h_liminf_bound :
      ∫⁻ x in Ω'',
        liminf (fun j : ℕ =>
          (‖DifferentialGeometry.Analysis.Sobolev.diffQuot k
              ((1 : ℝ) / (j + 1)) ψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) atTop
        ∂(volume : Measure E) ≤
      (ENNReal.ofReal M) ^ (2 : ℝ) := by
    refine (lintegral_liminf_le h_meas_lint).trans ?_
    refine liminf_le_of_frequently_le' ?_
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall h_lint_dq_bound)
  have h_liminf_pt : ∀ x,
      liminf (fun j : ℕ =>
        (‖DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (j + 1)) ψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) atTop
      = (‖gψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) :=
    fun x => (h_enorm_sq_tendsto x).liminf_eq
  have h_int_eq :
      ∫⁻ x in Ω'',
        liminf (fun j : ℕ =>
          (‖DifferentialGeometry.Analysis.Sobolev.diffQuot k
              ((1 : ℝ) / (j + 1)) ψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) atTop
        ∂(volume : Measure E) =
      ∫⁻ x in Ω'', (‖gψ x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(volume : Measure E) := by
    refine lintegral_congr_ae ?_
    exact Filter.Eventually.of_forall h_liminf_pt
  rw [h_int_eq] at h_liminf_bound
  have h_eLpNorm_sq_le :
      (eLpNorm gψ 2 (volume.restrict Ω'')) ^ (2 : ℝ) ≤
      (ENNReal.ofReal M) ^ (2 : ℝ) := by
    rw [h_eLpNorm_to_lint]
    exact h_liminf_bound
  have h_2_pos : (0 : ℝ) < 2 := by norm_num
  exact (ENNReal.rpow_le_rpow_iff h_2_pos).mp h_eLpNorm_sq_le

omit [NeZero d] in

theorem hasWeakPartialDeriv_of_strong_L2_limit
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (i k : Fin d)
    {w_i_func g : E → ℝ}
    (hw_i_l2 : MemLp w_i_func 2 (volume.restrict Ω''))
    (hg_l2 : MemLp g 2 (volume.restrict Ω''))
    {u_seq : ℕ → E → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (hu_seq_supp : ∀ n, HasCompactSupport (u_seq n))
    (h_partial_converges_Ω'' : Tendsto
      (fun n => eLpNorm
        (fun x : E => (fderiv ℝ (u_seq n) x) (EuclideanSpace.single i 1) -
          w_i_func x) 2 (volume.restrict Ω''))
      atTop (𝓝 0))
    (h_kdi_converges_Ω'' : Tendsto
      (fun n => eLpNorm
        (fun x : E =>
          (fderiv ℝ (fun z : E =>
            (fderiv ℝ (u_seq n) z) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single k 1) - g x) 2 (volume.restrict Ω''))
      atTop (𝓝 0)) :
    DeGiorgi.HasWeakPartialDeriv (d := d) k g w_i_func Ω'' := by
  classical
  set ψ : ℕ → E → ℝ := fun n y =>
    (fderiv ℝ (u_seq n) y) (EuclideanSpace.single i 1) with hψ_def
  set gψ : ℕ → E → ℝ := fun n y =>
    (fderiv ℝ (fun z : E => (fderiv ℝ (u_seq n) z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single k 1) with hgψ_def
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
    fun n => contDiff_partial_aux (hu_seq_smooth n) i
  have hψ_supp : ∀ n, HasCompactSupport (ψ n) :=
    fun n => hasCompactSupport_partial_aux (hu_seq_supp n) i
  have hψ_cont : ∀ n, Continuous (ψ n) := fun n => (hψ_smooth n).continuous
  have hgψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (gψ n) :=
    fun n => contDiff_kdi_partial_aux (hu_seq_smooth n) i k
  have hgψ_supp : ∀ n, HasCompactSupport (gψ n) :=
    fun n => hasCompactSupport_kdi_partial_aux (hu_seq_supp n) i k
  have hgψ_cont : ∀ n, Continuous (gψ n) := fun n => (hgψ_smooth n).continuous
  have hψ_l2 : ∀ n, MemLp (ψ n) 2 (volume.restrict Ω'') := fun n =>
    memLp_two_continuous_compact_support_restrict (hψ_cont n) (hψ_supp n) Ω''
  have hgψ_l2 : ∀ n, MemLp (gψ n) 2 (volume.restrict Ω'') := fun n =>
    memLp_two_continuous_compact_support_restrict (hgψ_cont n) (hgψ_supp n) Ω''
  have hψ_diff_lp : ∀ n, MemLp (fun x : E => ψ n x - w_i_func x) 2
      (volume.restrict Ω'') := fun n => (hψ_l2 n).sub hw_i_l2
  have hgψ_diff_lp : ∀ n, MemLp (fun x : E => gψ n x - g x) 2
      (volume.restrict Ω'') := fun n => (hgψ_l2 n).sub hg_l2
  have h_weak_n : ∀ n,
      DeGiorgi.HasWeakPartialDeriv (d := d) k (gψ n) (ψ n) Ω'' := by
    intro n
    rw [hgψ_def, hψ_def]
    exact hasWeakPartialDeriv_kdi_partial_of_smooth (d := d)
      (hu_seq_smooth n) hΩ''_open i k
  have h_ofReal_2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast]
    rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
    exact ENNReal.ofReal_natCast 2
  refine DeGiorgi.HasWeakPartialDeriv.of_eLpNormApprox_p (d := d) hΩ''_open
    (p := 2) (by norm_num : (1 : ℝ) < 2)
    (i := k) (f := w_i_func) (g := g) (ψ := ψ) (gψ := gψ)
    (hf_memLp := ?_) (hg_memLp := ?_) (hψ_wd := h_weak_n)
    (hψ_fun_memLp := ?_) (hψ_fun := ?_)
    (hψ_grad_memLp := ?_) (hψ_grad := ?_)
  · rw [h_ofReal_2]; exact hw_i_l2
  · rw [h_ofReal_2]; exact hg_l2
  · intro n; rw [h_ofReal_2]; exact hψ_diff_lp n
  · rw [h_ofReal_2]; exact h_partial_converges_Ω''
  · intro n; rw [h_ofReal_2]; exact hgψ_diff_lp n
  · rw [h_ofReal_2]; exact h_kdi_converges_Ω''

end DifferentialGeometry.Analysis.Sobolev.H2WeakSolution
