import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.NonSmooth

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.SmoothApproximationConstruction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

private lemma exists_abs_bound_of_continuous_compactSupport
    {h : E → ℝ} (h_cont : Continuous h) (h_cs : HasCompactSupport h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, |h x| ≤ M := by
  rcases h_cont.bounded_above_of_compact_support h_cs with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  exact (hM x).trans (le_max_left _ _)

omit [NeZero d] in

private lemma memLp_two_restrict_of_continuous_compactSupport
    {h : E → ℝ} (h_cont : Continuous h) (h_cs : HasCompactSupport h)
    (S : Set E) :
    MemLp h 2 (volume.restrict S) := by
  have hMemLp_volume : MemLp h 2 (volume : Measure E) :=
    h_cont.memLp_of_hasCompactSupport (μ := (volume : Measure E)) h_cs
  exact hMemLp_volume.restrict S

omit [NeZero d] in

private lemma exists_grad_component_bound
    {u : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u) (hu_cs : HasCompactSupport u) :
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ j : Fin d, ∀ x : E,
        |(fderiv ℝ u x) (EuclideanSpace.single j 1)| ≤ N := by
  classical
  have h_each : ∀ j : Fin d, ∃ N_j : ℝ, 0 ≤ N_j ∧
      ∀ x : E, |(fderiv ℝ u x) (EuclideanSpace.single j 1)| ≤ N_j := by
    intro j
    have h_cont : Continuous
        (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single j 1)) :=
      (hu_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have h_cs : HasCompactSupport
        (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single j 1)) :=
      hu_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact exists_abs_bound_of_continuous_compactSupport h_cont h_cs
  let N_fun : Fin d → ℝ := fun j => Classical.choose (h_each j)
  have hN_fun_nn : ∀ j, 0 ≤ N_fun j := fun j =>
    (Classical.choose_spec (h_each j)).1
  have hN_fun_le : ∀ j : Fin d, ∀ x : E,
      |(fderiv ℝ u x) (EuclideanSpace.single j 1)| ≤ N_fun j :=
    fun j => (Classical.choose_spec (h_each j)).2
  let N : ℝ := ∑ j : Fin d, N_fun j
  have hN_nn : 0 ≤ N := Finset.sum_nonneg (fun j _ => hN_fun_nn j)
  refine ⟨N, hN_nn, fun j x => ?_⟩
  have hsingle : N_fun j ≤ N := by
    refine Finset.single_le_sum (f := N_fun) (s := Finset.univ) ?_
      (Finset.mem_univ j)
    intro k _
    exact hN_fun_nn k
  exact (hN_fun_le j x).trans hsingle

theorem exists_smoothApproximation_of_smooth_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_cs : HasCompactSupport u)
    (hf_cont : Continuous f)
    (hf_cs : HasCompactSupport f)
    (h_weak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ω →
        B.bilin u φ = ∫ x in Ω, f x * φ x) :
    Nonempty (SmoothApproximation B u f) := by
  classical
  obtain ⟨M_u, hM_u_nn, hM_u_le⟩ :=
    exists_abs_bound_of_continuous_compactSupport
      (h_cont := hu_smooth.continuous) (h_cs := hu_cs)
  obtain ⟨N_grad, hN_grad_nn, hN_grad_le⟩ :=
    exists_grad_component_bound (u := u) hu_smooth hu_cs
  obtain ⟨M_f, hM_f_nn, hM_f_le⟩ :=
    exists_abs_bound_of_continuous_compactSupport
      (h_cont := hf_cont) (h_cs := hf_cs)
  set D : ℝ := M_u ^ 2 + (Fintype.card (Fin d) : ℝ) * N_grad ^ 2 + M_f ^ 2
    with hD_def
  have hD_nn : 0 ≤ D := by
    refine add_nonneg (add_nonneg (sq_nonneg _) ?_) (sq_nonneg _)
    exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (sq_nonneg _)
  have hu_cont : Continuous u := hu_smooth.continuous
  have h_grad_cont : ∀ j : Fin d, Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single j 1)) := by
    intro j
    exact (hu_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hu_grad_cs : ∀ j : Fin d, HasCompactSupport
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single j 1)) := by
    intro j
    exact hu_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  refine ⟨{
    u_seq := fun _ => u
    f_seq := fun _ => f
    u_seq_smooth := fun _ => hu_smooth
    is_smooth_weak_sol := fun _ => ?_
    f_seq_l2_loc := fun _ {S} _hS_cc =>
      memLp_two_restrict_of_continuous_compactSupport hf_cont hf_cs S
    u_seq_l2_loc := fun _ {S} _hS_cc =>
      memLp_two_restrict_of_continuous_compactSupport hu_cont hu_cs S
    grad_seq_l2_loc := fun _ {S} _hS_cc j =>
      memLp_two_restrict_of_continuous_compactSupport
        (h_grad_cont j) (hu_grad_cs j) S
    data_bound := D
    data_bound_nn := hD_nn
    data_integrated_bound := ?_
  }⟩
  · refine ⟨hu_smooth, ?_⟩
    intro φ hφ_smooth hφ_cs hφ_supp
    exact h_weak φ hφ_smooth hφ_cs hφ_supp
  · intro Ω' hΩ'_open hΩ'_cc
    have h_volume_lt_top : volume Ω' < ⊤ :=
      lt_of_le_of_lt (measure_mono subset_closure) hΩ'_cc.measure_lt_top
    set V : ℝ := (volume Ω').toReal with hV_def
    have hV_nn : 0 ≤ V := ENNReal.toReal_nonneg
    haveI : IsFiniteMeasure (volume.restrict Ω') := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact h_volume_lt_top
    have h_const_int : ∀ c : ℝ,
        ∫ _x in Ω', c ∂(volume : Measure E) = c * V := by
      intro c
      rw [setIntegral_const, smul_eq_mul, mul_comm, hV_def]
      rfl
    refine ⟨V, hV_nn, fun _ => ?_⟩
    have h_grad_each_int : ∀ j : Fin d,
        ∫ y in Ω', ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure E) ≤ N_grad ^ 2 * V := by
      intro j
      have h_pt : ∀ y : E,
          ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2 ≤ N_grad ^ 2 := by
        intro y
        have h_abs := hN_grad_le j y
        rw [show ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2 =
              |(fderiv ℝ u y) (EuclideanSpace.single j 1)| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
      have h_int_lhs : Integrable
          (fun y : E => ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2)
          (volume.restrict Ω') := by
        have h_cont_sq : Continuous
            (fun y : E => ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2) :=
          (h_grad_cont j).pow 2
        refine MemLp.integrable (le_refl 1) ?_
        refine MemLp.of_bound h_cont_sq.aestronglyMeasurable (N_grad ^ 2) ?_
        rw [ae_restrict_iff' hΩ'_open.measurableSet]
        refine Filter.Eventually.of_forall ?_
        intro y _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_pt y
      have h_int_rhs : Integrable (fun _ : E => N_grad ^ 2)
          (volume.restrict Ω') := integrable_const _
      have h_le_int :
          ∫ y in Ω', ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
              ∂(volume : Measure E) ≤
          ∫ _y in Ω', N_grad ^ 2 ∂(volume : Measure E) := by
        refine integral_mono_ae h_int_lhs h_int_rhs ?_
        refine Filter.Eventually.of_forall ?_; exact h_pt
      rw [h_const_int (N_grad ^ 2)] at h_le_int
      exact h_le_int
    have h_u_sq_int : ∫ y in Ω', (u y) ^ 2 ∂(volume : Measure E) ≤ M_u ^ 2 * V := by
      have h_pt : ∀ y : E, (u y) ^ 2 ≤ M_u ^ 2 := by
        intro y
        have h_abs := hM_u_le y
        rw [show (u y) ^ 2 = |u y| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
      have h_int_lhs : Integrable (fun y : E => (u y) ^ 2)
          (volume.restrict Ω') := by
        have h_cont_sq : Continuous (fun y : E => (u y) ^ 2) :=
          hu_cont.pow 2
        refine MemLp.integrable (le_refl 1) ?_
        refine MemLp.of_bound h_cont_sq.aestronglyMeasurable (M_u ^ 2) ?_
        rw [ae_restrict_iff' hΩ'_open.measurableSet]
        refine Filter.Eventually.of_forall ?_
        intro y _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_pt y
      have h_int_rhs : Integrable (fun _ : E => M_u ^ 2)
          (volume.restrict Ω') := integrable_const _
      have h_le_int :
          ∫ y in Ω', (u y) ^ 2 ∂(volume : Measure E) ≤
          ∫ _y in Ω', M_u ^ 2 ∂(volume : Measure E) := by
        refine integral_mono_ae h_int_lhs h_int_rhs ?_
        refine Filter.Eventually.of_forall ?_; exact h_pt
      rw [h_const_int (M_u ^ 2)] at h_le_int
      exact h_le_int
    have h_f_sq_int : ∫ y in Ω', (f y) ^ 2 ∂(volume : Measure E) ≤ M_f ^ 2 * V := by
      have h_pt : ∀ y : E, (f y) ^ 2 ≤ M_f ^ 2 := by
        intro y
        have h_abs := hM_f_le y
        rw [show (f y) ^ 2 = |f y| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
      have h_int_lhs : Integrable (fun y : E => (f y) ^ 2)
          (volume.restrict Ω') := by
        have h_cont_sq : Continuous (fun y : E => (f y) ^ 2) :=
          hf_cont.pow 2
        refine MemLp.integrable (le_refl 1) ?_
        refine MemLp.of_bound h_cont_sq.aestronglyMeasurable (M_f ^ 2) ?_
        rw [ae_restrict_iff' hΩ'_open.measurableSet]
        refine Filter.Eventually.of_forall ?_
        intro y _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_pt y
      have h_int_rhs : Integrable (fun _ : E => M_f ^ 2)
          (volume.restrict Ω') := integrable_const _
      have h_le_int :
          ∫ y in Ω', (f y) ^ 2 ∂(volume : Measure E) ≤
          ∫ _y in Ω', M_f ^ 2 ∂(volume : Measure E) := by
        refine integral_mono_ae h_int_lhs h_int_rhs ?_
        refine Filter.Eventually.of_forall ?_; exact h_pt
      rw [h_const_int (M_f ^ 2)] at h_le_int
      exact h_le_int
    have h_grad_sum_int :
        ∫ y in Ω', ∑ j : Fin d,
            ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E) ≤
          (Fintype.card (Fin d) : ℝ) * N_grad ^ 2 * V := by
      have h_sum_swap :
          ∫ y in Ω', ∑ j : Fin d,
              ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure E) =
          ∑ j : Fin d, ∫ y in Ω',
              ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure E) := by
        refine integral_finset_sum (μ := volume.restrict Ω') Finset.univ ?_
        intro j _
        have h_cont_sq : Continuous
            (fun y : E => ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2) :=
          (h_grad_cont j).pow 2
        have h_pt : ∀ y : E,
            ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2 ≤ N_grad ^ 2 := by
          intro y
          have h_abs := hN_grad_le j y
          rw [show ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2 =
                |(fderiv ℝ u y) (EuclideanSpace.single j 1)| ^ 2 from (sq_abs _).symm]
          exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
        refine MemLp.integrable (le_refl 1) ?_
        refine MemLp.of_bound h_cont_sq.aestronglyMeasurable (N_grad ^ 2) ?_
        rw [ae_restrict_iff' hΩ'_open.measurableSet]
        refine Filter.Eventually.of_forall ?_
        intro y _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_pt y
      rw [h_sum_swap]
      have h_sum_le :
          ∑ j : Fin d, ∫ y in Ω',
              ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure E) ≤
          ∑ _j : Fin d, N_grad ^ 2 * V :=
        Finset.sum_le_sum (fun j _ => h_grad_each_int j)
      have h_const_sum :
          ∑ _j : Fin d, N_grad ^ 2 * V =
            (Fintype.card (Fin d) : ℝ) * N_grad ^ 2 * V := by
        rw [Finset.sum_const, Finset.card_univ]
        ring
      rw [h_const_sum] at h_sum_le
      exact h_sum_le
    have h_combined :
        (∫ y in Ω',
            ∑ j : Fin d,
              ((fderiv ℝ u y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E)) +
        (∫ y in Ω', (u y) ^ 2 ∂(volume : Measure E)) +
        (∫ y in Ω', (f y) ^ 2 ∂(volume : Measure E)) ≤
          (Fintype.card (Fin d) : ℝ) * N_grad ^ 2 * V + M_u ^ 2 * V + M_f ^ 2 * V := by
      have h1 := h_grad_sum_int
      have h2 := h_u_sq_int
      have h3 := h_f_sq_int
      linarith
    have h_combine_eq :
        (Fintype.card (Fin d) : ℝ) * N_grad ^ 2 * V + M_u ^ 2 * V + M_f ^ 2 * V =
          V * D := by
      rw [hD_def]; ring
    rw [h_combine_eq] at h_combined
    exact h_combined

theorem exists_smoothApproximation_of_isSmoothWeakSolution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (h_sws : B.IsSmoothWeakSolution u f)
    (hu_cs : HasCompactSupport u)
    (hf_cont : Continuous f)
    (hf_cs : HasCompactSupport f) :
    Nonempty (SmoothApproximation B u f) :=
  exists_smoothApproximation_of_smooth_compactSupport (B := B)
    (u := u) (f := f) h_sws.1 hu_cs hf_cont hf_cs h_sws.2

end DifferentialGeometry.Analysis.Sobolev.SmoothApproximationConstruction
