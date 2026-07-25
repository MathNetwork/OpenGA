import DifferentialGeometry.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBounds
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientWeakLimit

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem uniform_nirenberg_estimate
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : E → ℝ}, B.IsSmoothWeakSolution u f →
        (∀ {Ω' : Set E}, IsCompact (closure Ω') →
          MemLp f 2 (volume.restrict Ω')) →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (η x)^2 *
          ∑ i : Fin d,
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
        ∂(volume : Measure E) ≤
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    nirenberg_master_inequality_after_young (d := d) B
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
      hη_in_Ω' hh_supp_in_Ω' k
  set C : ℝ := (2 / B.lam) * C₀ with hC_def
  have hlam_pos : 0 < B.lam := B.hlam_pos
  have hC_nn : 0 ≤ C := by
    rw [hC_def]; exact mul_nonneg (by positivity) hC₀_nn
  refine ⟨C, hC_nn, ?_⟩
  intro u f h_weak hf_l2_loc h hh hh_le
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
    ∂(volume : Measure E) with hI_def
  set R : ℝ := ∫ x in Ω',
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
    ∂(volume : Measure E) +
    ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
    ∫ x in Ω', (f x)^2 ∂(volume : Measure E) with hR_def
  have hY : B.lam * I ≤ (B.lam / 2) * I + C₀ * R := hC₀ h_weak hf_l2_loc hh hh_le
  have h_step1 : (B.lam / 2) * I ≤ C₀ * R := by linarith
  have h_two_lam : (0 : ℝ) ≤ 2 / B.lam := by positivity
  have h_mul : (2 / B.lam) * ((B.lam / 2) * I) ≤ (2 / B.lam) * (C₀ * R) :=
    mul_le_mul_of_nonneg_left h_step1 h_two_lam
  have h_simp : (2 / B.lam) * ((B.lam / 2) * I) = I := by field_simp
  rw [h_simp] at h_mul
  have h_assoc : (2 / B.lam) * (C₀ * R) = (2 / B.lam) * C₀ * R := by ring
  rw [h_assoc] at h_mul
  rw [← hC_def] at h_mul
  exact h_mul

omit [NeZero d] in

private lemma contDiff_secondPartialDeriv
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ
        (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
        (EuclideanSpace.single k 1)) := by
  have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_i_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single i (1 : ℝ))).contDiff
  have h_partial_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    h_apply_i_smooth.comp h_fderiv_smooth
  have h_fderiv_smooth_partial : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ
        (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1))) :=
    h_partial_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_k_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single k 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single k (1 : ℝ))).contDiff
  exact h_apply_k_smooth.comp h_fderiv_smooth_partial

omit [NeZero d] in

private lemma hasWeakPartialDeriv_partialDeriv_of_contDiff
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (i k : Fin d) :
    DeGiorgi.HasWeakPartialDeriv (d := d) k
      (fun y : E =>
        (fderiv ℝ
          (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
          (EuclideanSpace.single k 1))
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))
      Ω := by
  have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single i (1 : ℝ))).contDiff
  have h_partial_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    h_apply_smooth.comp h_fderiv_smooth
  have h_partial_C1 : ContDiff ℝ 1
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    h_partial_smooth.of_le (by norm_cast)
  exact DeGiorgi.HasWeakPartialDeriv.of_contDiff (d := d) hΩ
    (i := k) (f := fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))
    h_partial_C1

omit [NeZero d] in

private lemma memLp_two_continuous_compact_closure
    {f : E → ℝ} (hf : Continuous f)
    {Ω : Set E} (hΩ_open : IsOpen Ω) (hΩ_compact : IsCompact (closure Ω)) :
    MemLp f 2 (volume.restrict Ω) := by
  have h_volume_closure_lt_top : volume (closure Ω) < ⊤ :=
    hΩ_compact.measure_lt_top
  have h_volume_lt_top : volume Ω < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) h_volume_closure_lt_top
  haveI : IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  obtain ⟨M, hM⟩ := hΩ_compact.bddAbove_image hf.abs.continuousOn
  have h_aestrong : AEStronglyMeasurable f (volume.restrict Ω) :=
    hf.aestronglyMeasurable
  refine MemLp.of_bound h_aestrong (max M 0) ?_
  rw [ae_restrict_iff' hΩ_open.measurableSet]
  refine Filter.Eventually.of_forall ?_
  intro x hx
  have h_in_closure : x ∈ closure Ω := subset_closure hx
  have h := hM (Set.mem_image_of_mem _ h_in_closure)
  rw [Real.norm_eq_abs]
  exact h.trans (le_max_left _ _)

theorem loc_smooth_solution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (_hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : E → ℝ}, B.IsSmoothWeakSolution u f →
        (∀ {Ω' : Set E}, IsCompact (closure Ω') →
          MemLp f 2 (volume.restrict Ω')) →
      ∀ i k : Fin d, ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set E, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧ closure Ω' ⊆ Ω ∧
        IsCompact (closure Ω') ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single j 1))^2
                ∂(volume : Measure E) +
              ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
              ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  set K : Set E := closure Ω'' with hK_def
  have hK_compact : IsCompact K := hΩ''_compact_closure
  have h_K_in_thick34 : K ⊆ Metric.thickening (3/4) K :=
    Metric.self_subset_thickening (by norm_num) K
  have h_thick34_open : IsOpen (Metric.thickening (3/4 : ℝ) K) :=
    Metric.isOpen_thickening
  obtain ⟨η, hη_smooth, hη_compact, hη_range, hη_one_on_K, hη_tsupport_in,
      N, hN_nn, h_fderiv_eta⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound (d := d)
      (K := K) (Ω' := Metric.thickening (3/4) K)
      hK_compact h_thick34_open h_K_in_thick34
  set Ω' : Set E := Metric.thickening 2 K with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hΩ'_K_subset : K ⊆ Ω' := by
    rw [hΩ'_def]
    exact Metric.self_subset_thickening (by norm_num) K
  have hΩ'_closure_in_cthickening : closure Ω' ⊆ Metric.cthickening 2 K := by
    rw [hΩ'_def]
    exact Metric.closure_thickening_subset_cthickening _ K
  have hΩ'_closure_in_Ω : closure Ω' ⊆ Ω :=
    hΩ'_closure_in_cthickening.trans h_room
  have hΩ'_closure_compact : IsCompact (closure Ω') :=
    hK_compact.cthickening (r := 2) |>.of_isClosed_subset isClosed_closure
      hΩ'_closure_in_cthickening
  have hη_tsupport_in_thick34 : tsupport η ⊆ Metric.cthickening (3/4) K :=
    hη_tsupport_in.trans (Metric.thickening_subset_cthickening _ _)
  have hη_tsupport_in_Ω' : tsupport η ⊆ Ω' := by
    rw [hΩ'_def]
    exact hη_tsupport_in.trans (Metric.thickening_mono (by norm_num : (3/4 : ℝ) ≤ 2) K)
  have hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ (1 : ℝ) →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh_le
    refine subset_trans (Metric.cthickening_mono hh_le _) ?_
    refine subset_trans (Metric.cthickening_subset_of_subset 1 hη_tsupport_in_thick34) ?_
    refine subset_trans (Metric.cthickening_cthickening_subset (by norm_num) (by norm_num) K) ?_
    rw [hΩ'_def]
    exact Metric.cthickening_subset_thickening' (by norm_num) (by norm_num) K
  have h_unif : ∀ k' : Fin d, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : E → ℝ}, B.IsSmoothWeakSolution u f →
        (∀ {Ω' : Set E}, IsCompact (closure Ω') →
          MemLp f 2 (volume.restrict Ω')) →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ (1 : ℝ) →
        ∫ x, (η x)^2 *
            ∑ i : Fin d,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k' h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) ≤
          C * (∫ x in Ω',
                ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
              ∂(volume : Measure E) +
            ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
            ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) :=
    fun k' => uniform_nirenberg_estimate (d := d) B hη_smooth hη_compact
      hη_range hN_nn h_fderiv_eta hΩ'_open hΩ'_closure_in_Ω hΩ'_closure_compact
      hη_tsupport_in_Ω' (R₀ := 1) hh_supp_in_Ω' k'
  choose Cfun hCfun_nn hCfun using h_unif
  set C : ℝ := ∑ k' : Fin d, Cfun k' with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact Finset.sum_nonneg (fun k' _ => hCfun_nn k')
  have hCfun_le_C : ∀ k' : Fin d, Cfun k' ≤ C := by
    intro k'
    rw [hC_def]
    exact Finset.single_le_sum (f := fun k' => Cfun k')
      (fun k' _ => hCfun_nn k') (Finset.mem_univ k')
  refine ⟨C, hC_nn, ?_⟩
  intro u f h_weak hf_l2_loc i k
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  set g : E → ℝ := fun y =>
    (fderiv ℝ
      (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
      (EuclideanSpace.single k 1) with hg_def
  have h_weak_partial :
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) Ω'' :=
    hasWeakPartialDeriv_partialDeriv_of_contDiff (d := d) hu hΩ'' i k
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_secondPartialDeriv (d := d) hu i k
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_memLp : MemLp g 2 (volume.restrict Ω'') :=
    memLp_two_continuous_compact_closure (d := d) hg_cont hΩ''
      hΩ''_compact_closure
  set C₀ : ℝ := Cfun k with hC₀_def
  have hC₀_nn : 0 ≤ C₀ := hCfun_nn k
  have hC₀_le_C : C₀ ≤ C := hCfun_le_C k
  refine ⟨g, hg_memLp, h_weak_partial, Ω', hΩ'_open, ?_, hΩ'_closure_in_Ω,
    hΩ'_closure_compact, ?_⟩
  · exact hΩ'_K_subset
  have h_seq : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≠ 0 := by
    intro n
    refine div_ne_zero one_ne_zero ?_
    exact_mod_cast (n + 1).succ_ne_zero
  have h_seq_pos : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := fun n => by positivity
  have h_seq_le_one : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_seq_abs_le_one : ∀ n : ℕ, |(1 : ℝ) / (n + 1)| ≤ 1 := by
    intro n
    rw [abs_of_pos (h_seq_pos n)]
    exact h_seq_le_one n
  have h_seq_tendsto : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h_partial_C1 : ∀ j : Fin d, ContDiff ℝ 1
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) := by
    intro j
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact (h_apply_smooth.comp h_fderiv_smooth).of_le (by norm_cast)
  have h_diffQuot_tendsto : ∀ (j : Fin d) (x : E),
      Tendsto (fun n : ℕ =>
          DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (n + 1))
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
        atTop
        (𝓝 ((fderiv ℝ
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single k 1))) := by
    intro j x
    have h_tendsto_h0 := DifferentialGeometry.Analysis.Sobolev.tendsto_diffQuot_of_contDiff
      (d := d) (h_partial_C1 j) k x
    have h_seq_in_punctured :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h_seq_tendsto, ?_⟩
      refine Filter.Eventually.of_forall ?_
      intro n
      exact h_seq n
    exact h_tendsto_h0.comp h_seq_in_punctured
  have h_pointwise_converges : ∀ x : E,
      Tendsto (fun n : ℕ => ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k ((1 : ℝ) / (n + 1))
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2)
        atTop
        (𝓝 (∑ j : Fin d, ((fderiv ℝ
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single k 1))^2)) := by
    intro x
    refine tendsto_finset_sum Finset.univ ?_
    intro j _
    have h := h_diffQuot_tendsto j x
    exact h.pow 2
  set RHS_real : ℝ := ∫ x in Ω',
      ∑ j : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single j 1))^2
    ∂(volume : Measure E) +
    ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
    ∫ x in Ω', (f x)^2 ∂(volume : Measure E) with hRHS_real_def
  have hRHS_real_nn : 0 ≤ RHS_real := by
    rw [hRHS_real_def]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact integral_nonneg (fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · exact integral_nonneg (fun x => sq_nonneg _)
    · exact integral_nonneg (fun x => sq_nonneg _)
  have hC₀_n : ∀ n : ℕ, ∫ x, (η x)^2 *
      ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
        ((1 : ℝ) / (n + 1))
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2
    ∂(volume : Measure E) ≤ C₀ * RHS_real := by
    intro n
    rw [hRHS_real_def]
    exact hCfun k h_weak hf_l2_loc (h_seq n) (h_seq_abs_le_one n)
  have h_indicator_le_eta_sq : ∀ x : E,
      (Ω''.indicator (fun _ => (1 : ℝ)) x) ≤ (η x)^2 := by
    intro x
    by_cases hx : x ∈ Ω''
    · have hx_in_K : x ∈ K := by
        rw [hK_def]; exact subset_closure hx
      have hηx : η x = 1 := hη_one_on_K x hx_in_K
      rw [Set.indicator_of_mem hx, hηx]
      norm_num
    · rw [Set.indicator_of_notMem hx]
      exact sq_nonneg _
  have h_int_Ω''_le_int_eta_sq : ∀ n : ℕ,
      ∫ x in Ω'',
        ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (n + 1))
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 *
        ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (n + 1))
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2
        ∂(volume : Measure E) := by
    intro n
    have h_q_nn : ∀ x : E, 0 ≤ ∑ j : Fin d,
        DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (n + 1))
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2 :=
      fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [show (∫ x in Ω'',
        ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (n + 1))
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2
        ∂(volume : Measure E)) =
      ∫ x, Ω''.indicator (fun y =>
          ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (n + 1))
            (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) y ^ 2)
        x ∂(volume : Measure E) from
        (integral_indicator hΩ''.measurableSet).symm]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ Ω''
      · rw [Set.indicator_of_mem hx]
        exact h_q_nn x
      · rw [Set.indicator_of_notMem hx]
        exact le_refl 0
    · have h_eta_sq_cont : Continuous (fun x : E => (η x)^2) :=
        hη_smooth.continuous.pow 2
      have h_q_n_cont : Continuous (fun x : E => ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (n + 1))
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2) := by
        refine continuous_finset_sum Finset.univ ?_
        intro j _
        have h_partial_smooth_j : ContDiff ℝ (⊤ : ℕ∞)
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) := by
          have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
            hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
          have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
              (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) :=
            (ContinuousLinearMap.apply ℝ ℝ
              (EuclideanSpace.single j (1 : ℝ))).contDiff
          exact h_apply_smooth.comp h_fderiv_smooth
        have h_diffQuot_cont : Continuous
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k
              ((1 : ℝ) / (n + 1))
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1))) :=
          DifferentialGeometry.Analysis.Sobolev.continuous_diffQuot_of_continuous
            (d := d) k _ h_partial_smooth_j.continuous
        exact h_diffQuot_cont.pow 2
      have h_prod_cont : Continuous (fun x : E => (η x)^2 *
          ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (n + 1))
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2) :=
        h_eta_sq_cont.mul h_q_n_cont
      have h_prod_supp : HasCompactSupport (fun x : E => (η x)^2 *
          ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (n + 1))
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2) := by
        have h_eta_sq_supp : HasCompactSupport (fun x : E => (η x)^2) := by
          have heq : (fun x : E => η x ^ 2) = (fun x : E => η x * η x) := by
            funext x; ring
          rw [heq]
          exact hη_compact.mul_right
        exact h_eta_sq_supp.mul_right
      exact h_prod_cont.integrable_of_hasCompactSupport h_prod_supp
    · refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ Ω''
      · have hx_in_K : x ∈ K := subset_closure hx
        have hηx : η x = 1 := hη_one_on_K x hx_in_K
        rw [Set.indicator_of_mem hx]
        have h1 : (η x) ^ 2 * (∑ j : Fin d,
            DifferentialGeometry.Analysis.Sobolev.diffQuot k ((1 : ℝ) / (n + 1))
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2) =
            ∑ j : Fin d,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k ((1 : ℝ) / (n + 1))
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2 := by
          rw [hηx]; ring
        linarith [h1, h_q_nn x]
      · rw [Set.indicator_of_notMem hx]
        refine mul_nonneg (sq_nonneg _) (h_q_nn x)
  have h_int_Ω''_q_n_bound : ∀ n : ℕ,
      ∫ x in Ω'',
        ∑ j : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k
          ((1 : ℝ) / (n + 1))
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2
        ∂(volume : Measure E) ≤ C₀ * RHS_real :=
    fun n => (h_int_Ω''_le_int_eta_sq n).trans (hC₀_n n)
  set q : E → ℝ := fun x => ∑ j : Fin d, ((fderiv ℝ
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      (EuclideanSpace.single k 1))^2 with hq_def
  set q_n : ℕ → E → ℝ := fun n x => ∑ j : Fin d,
      DifferentialGeometry.Analysis.Sobolev.diffQuot k
        ((1 : ℝ) / (n + 1))
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x ^ 2
    with hq_n_def
  have hq_nn : ∀ x : E, 0 ≤ q x :=
    fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq_n_nn : ∀ n x, 0 ≤ q_n n x :=
    fun n x => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_q_n_tendsto_q : ∀ x : E, Tendsto (fun n => q_n n x) atTop (𝓝 (q x)) := by
    intro x
    have h := h_pointwise_converges x
    rw [hq_n_def, hq_def]
    exact h
  have h_lint_q_n_bound : ∀ n : ℕ,
      ∫⁻ x in Ω'', ENNReal.ofReal (q_n n x) ∂(volume : Measure E) ≤
        ENNReal.ofReal (C₀ * RHS_real) := by
    intro n
    have h_int_le : ∫ x in Ω'', q_n n x ∂(volume : Measure E) ≤ C₀ * RHS_real :=
      h_int_Ω''_q_n_bound n
    have h_q_n_nn_ae : 0 ≤ᵐ[volume.restrict Ω''] q_n n :=
      Filter.Eventually.of_forall (hq_n_nn n)
    have h_q_n_int : Integrable (q_n n) (volume.restrict Ω'') := by
      have hq_n_cont : Continuous (q_n n) := by
        rw [hq_n_def]
        refine continuous_finset_sum Finset.univ ?_
        intro j _
        have h_partial_smooth_j : ContDiff ℝ (⊤ : ℕ∞)
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) := by
          have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
            hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
          have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
              (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) :=
            (ContinuousLinearMap.apply ℝ ℝ
              (EuclideanSpace.single j (1 : ℝ))).contDiff
          exact h_apply_smooth.comp h_fderiv_smooth
        have h_dq_cont : Continuous
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k
              ((1 : ℝ) / (n + 1))
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1))) :=
          DifferentialGeometry.Analysis.Sobolev.continuous_diffQuot_of_continuous
            (d := d) k _ h_partial_smooth_j.continuous
        exact h_dq_cont.pow 2
      have h_volume_lt_top : volume Ω'' < ⊤ :=
        lt_of_le_of_lt (measure_mono subset_closure)
          hΩ''_compact_closure.measure_lt_top
      haveI : IsFiniteMeasure (volume.restrict Ω'') := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact h_volume_lt_top
      obtain ⟨M, hM⟩ := hΩ''_compact_closure.bddAbove_image hq_n_cont.abs.continuousOn
      have h_q_n_bound : ∀ x ∈ closure Ω'', |q_n n x| ≤ max M 0 := by
        intro x hx
        have h := hM (Set.mem_image_of_mem _ hx)
        exact h.trans (le_max_left _ _)
      refine MemLp.integrable (le_refl 1) ?_
      refine MemLp.of_bound hq_n_cont.aestronglyMeasurable (max M 0) ?_
      rw [ae_restrict_iff' hΩ''.measurableSet]
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have h_in_closure : x ∈ closure Ω'' := subset_closure hx
      rw [Real.norm_eq_abs]
      exact h_q_n_bound x h_in_closure
    have h_int_eq :
        ∫⁻ x in Ω'', ENNReal.ofReal (q_n n x) ∂(volume : Measure E) =
          ENNReal.ofReal (∫ x in Ω'', q_n n x ∂(volume : Measure E)) :=
      ofReal_integral_eq_lintegral_ofReal h_q_n_int h_q_n_nn_ae |>.symm
    rw [h_int_eq]
    exact ENNReal.ofReal_le_ofReal h_int_le
  have hq_n_meas : ∀ n : ℕ, Measurable (fun x : E => ENNReal.ofReal (q_n n x)) := by
    intro n
    have hq_n_cont : Continuous (q_n n) := by
      rw [hq_n_def]
      refine continuous_finset_sum Finset.univ ?_
      intro j _
      have h_partial_smooth_j : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) := by
        have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
          hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
            (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) :=
          (ContinuousLinearMap.apply ℝ ℝ
            (EuclideanSpace.single j (1 : ℝ))).contDiff
        exact h_apply_smooth.comp h_fderiv_smooth
      have h_dq_cont : Continuous
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k
            ((1 : ℝ) / (n + 1))
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1))) :=
        DifferentialGeometry.Analysis.Sobolev.continuous_diffQuot_of_continuous
          (d := d) k _ h_partial_smooth_j.continuous
      exact h_dq_cont.pow 2
    exact ENNReal.measurable_ofReal.comp hq_n_cont.measurable
  have h_ofReal_tendsto : ∀ x : E, Tendsto (fun n => ENNReal.ofReal (q_n n x))
      atTop (𝓝 (ENNReal.ofReal (q x))) := by
    intro x
    exact ENNReal.tendsto_ofReal (h_q_n_tendsto_q x)
  have h_liminf_eq : ∀ x : E,
      liminf (fun n => ENNReal.ofReal (q_n n x)) atTop = ENNReal.ofReal (q x) := by
    intro x
    exact (h_ofReal_tendsto x).liminf_eq
  have h_lint_q_eq_liminf :
      ∫⁻ x in Ω'', ENNReal.ofReal (q x) ∂(volume : Measure E) =
        ∫⁻ x in Ω'', liminf (fun n => ENNReal.ofReal (q_n n x)) atTop
          ∂(volume : Measure E) := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact (h_liminf_eq x).symm
  have h_fatou : ∫⁻ x in Ω'', liminf (fun n => ENNReal.ofReal (q_n n x)) atTop
        ∂(volume : Measure E) ≤
      liminf (fun n => ∫⁻ x in Ω'', ENNReal.ofReal (q_n n x)
          ∂(volume : Measure E)) atTop :=
    lintegral_liminf_le (fun n => hq_n_meas n)
  have h_liminf_bound :
      liminf (fun n => ∫⁻ x in Ω'', ENNReal.ofReal (q_n n x)
          ∂(volume : Measure E)) atTop ≤ ENNReal.ofReal (C₀ * RHS_real) := by
    refine liminf_le_of_frequently_le' ?_
    exact Filter.Eventually.frequently
      (Filter.Eventually.of_forall h_lint_q_n_bound)
  have h_lint_q_bound : ∫⁻ x in Ω'', ENNReal.ofReal (q x)
        ∂(volume : Measure E) ≤ ENNReal.ofReal (C₀ * RHS_real) := by
    rw [h_lint_q_eq_liminf]
    exact h_fatou.trans h_liminf_bound
  have h_g_sq_le_q : ∀ x : E, g x ^ 2 ≤ q x := by
    intro x
    rw [hq_def, hg_def]
    refine Finset.single_le_sum (f := fun j : Fin d =>
        ((fderiv ℝ
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single k 1))^2) ?_ (Finset.mem_univ i)
    intro j _
    exact sq_nonneg _
  have h_lint_g_sq_le : ∫⁻ x in Ω'', ENNReal.ofReal (g x ^ 2)
        ∂(volume : Measure E) ≤ ENNReal.ofReal (C₀ * RHS_real) := by
    refine le_trans ?_ h_lint_q_bound
    have hq_cont : Continuous q := by
      rw [hq_def]
      refine continuous_finset_sum Finset.univ ?_
      intro j _
      exact (contDiff_secondPartialDeriv (d := d) hu j k).continuous.pow 2
    have hq_meas : Measurable (fun x : E => ENNReal.ofReal (q x)) :=
      ENNReal.measurable_ofReal.comp hq_cont.measurable
    refine setLIntegral_mono_ae hq_meas.aemeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro x _
    exact ENNReal.ofReal_le_ofReal (h_g_sq_le_q x)
  have hg_sq_nn : ∀ x : E, 0 ≤ g x ^ 2 := fun x => sq_nonneg _
  have hg_sq_int : Integrable (fun x => g x ^ 2) (volume.restrict Ω'') := by
    have h_g_sq_cont : Continuous (fun x : E => g x ^ 2) := hg_cont.pow 2
    have h_volume_lt_top : volume Ω'' < ⊤ :=
      lt_of_le_of_lt (measure_mono subset_closure)
        hΩ''_compact_closure.measure_lt_top
    haveI : IsFiniteMeasure (volume.restrict Ω'') := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact h_volume_lt_top
    obtain ⟨M, hM⟩ := hΩ''_compact_closure.bddAbove_image h_g_sq_cont.abs.continuousOn
    have h_bound : ∀ x ∈ closure Ω'', |g x ^ 2| ≤ max M 0 := by
      intro x hx
      have h := hM (Set.mem_image_of_mem _ hx)
      exact h.trans (le_max_left _ _)
    refine MemLp.integrable (le_refl 1) ?_
    refine MemLp.of_bound h_g_sq_cont.aestronglyMeasurable (max M 0) ?_
    rw [ae_restrict_iff' hΩ''.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have h_in_closure : x ∈ closure Ω'' := subset_closure hx
    rw [Real.norm_eq_abs]
    exact h_bound x h_in_closure
  have hg_sq_nn_ae : 0 ≤ᵐ[volume.restrict Ω''] (fun x => g x ^ 2) :=
    Filter.Eventually.of_forall hg_sq_nn
  have h_int_eq : ∫⁻ x in Ω'', ENNReal.ofReal (g x ^ 2)
        ∂(volume : Measure E) =
      ENNReal.ofReal (∫ x in Ω'', g x ^ 2 ∂(volume : Measure E)) :=
    ofReal_integral_eq_lintegral_ofReal hg_sq_int hg_sq_nn_ae |>.symm
  rw [h_int_eq] at h_lint_g_sq_le
  have hC₀_RHS_nn : 0 ≤ C₀ * RHS_real := mul_nonneg hC₀_nn hRHS_real_nn
  have h_int_le_C₀ : ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤ C₀ * RHS_real :=
    (ENNReal.ofReal_le_ofReal_iff hC₀_RHS_nn).mp h_lint_g_sq_le
  exact h_int_le_C₀.trans (mul_le_mul_of_nonneg_right hC₀_le_C hRHS_real_nn)

end DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
