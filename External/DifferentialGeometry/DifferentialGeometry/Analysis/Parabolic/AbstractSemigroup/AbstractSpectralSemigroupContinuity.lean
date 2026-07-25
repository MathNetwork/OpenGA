import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralSemigroupLaw

noncomputable section

open Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

theorem abstractSpectralSemigroup_continuous_at_zero (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (v : X) :
    Filter.Tendsto
      (fun t : ℝ => abstractSpectralSemigroup b hlam t v)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 v) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h_summable_sq := summable_basis_coeff_sq' b v
  have hε16_pos : (0 : ℝ) < ε ^ 2 / 16 := by positivity
  obtain ⟨T_fin, hT_fin⟩ : ∃ T_fin : Finset ι,
      ∑' i : { i : ι // i ∉ T_fin },
        (⟪b (i : ι), v⟫_ℝ) ^ 2 < ε ^ 2 / 16 := by
    have h_hsum := h_summable_sq.hasSum
    rw [HasSum, Metric.tendsto_nhds] at h_hsum
    have h_evt := h_hsum (ε ^ 2 / 16) hε16_pos
    obtain ⟨T_fin, hT_T⟩ := h_evt.exists
    refine ⟨T_fin, ?_⟩
    have h_split : ∑' i : ι, (⟪b i, v⟫_ℝ) ^ 2 =
        (∑ i ∈ T_fin, (⟪b i, v⟫_ℝ) ^ 2) +
        ∑' i : { i : ι // i ∉ T_fin }, (⟪b (i : ι), v⟫_ℝ) ^ 2 :=
      (h_summable_sq.sum_add_tsum_subtype_compl T_fin).symm
    rw [dist_eq_norm, h_split] at hT_T
    have h_simp : ∑ i ∈ T_fin, (⟪b i, v⟫_ℝ) ^ 2 -
        ((∑ i ∈ T_fin, (⟪b i, v⟫_ℝ) ^ 2) +
          ∑' i : { i : ι // i ∉ T_fin }, (⟪b (i : ι), v⟫_ℝ) ^ 2) =
        -(∑' i : { i : ι // i ∉ T_fin }, (⟪b (i : ι), v⟫_ℝ) ^ 2) := by ring
    rw [h_simp, norm_neg, Real.norm_eq_abs] at hT_T
    have h_tail_nn : 0 ≤
        ∑' i : { i : ι // i ∉ T_fin }, (⟪b (i : ι), v⟫_ℝ) ^ 2 := by
      apply tsum_nonneg; intro i; exact sq_nonneg _
    rwa [abs_of_nonneg h_tail_nn] at hT_T
  have h_head_tendsto : Tendsto (fun t : ℝ =>
      ∑ i ∈ T_fin,
        (heatCoeff lam t i - 1) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h_each : ∀ i ∈ T_fin, Tendsto (fun t : ℝ =>
        (heatCoeff lam t i - 1) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2) (𝓝 0) (𝓝 0) := by
      intro i _
      have h_arg : Tendsto (fun t : ℝ => -(lam i) * t) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h_id : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
        have := h_id.const_mul (-(lam i))
        simpa using this
      have h_exp_to_one : Tendsto (fun t : ℝ => heatCoeff lam t i)
          (𝓝 (0 : ℝ)) (𝓝 1) := by
        have := h_arg.rexp
        simp only [heatCoeff_def]
        simpa [Real.exp_zero] using this
      have h_diff_to_zero : Tendsto (fun t : ℝ => heatCoeff lam t i - 1)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := h_exp_to_one.sub_const 1
        simpa using this
      have h_sq_to_zero : Tendsto (fun t : ℝ => (heatCoeff lam t i - 1) ^ 2)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := h_diff_to_zero.pow 2
        simpa using this
      have := h_sq_to_zero.mul_const ((⟪b i, v⟫_ℝ) ^ 2)
      simpa using this
    have h_total := tendsto_finset_sum T_fin h_each
    simpa using h_total
  rw [Metric.tendsto_nhds] at h_head_tendsto
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp
    (h_head_tendsto (ε ^ 2 / 4) (by positivity))
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{t : ℝ | 0 ≤ t ∧ t < δ}, ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio δ, Iio_mem_nhds hδ_pos, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  intro t ht_in
  obtain ⟨ht_nn, ht_lt⟩ := ht_in
  rw [dist_eq_norm]
  suffices h_sq : ‖abstractSpectralSemigroup b hlam t v - v‖ ^ 2 < ε ^ 2 by
    exact (abs_lt_of_sq_lt_sq' h_sq hε.le).2
  rw [abstractSpectralSemigroup_apply_of_nonneg b hlam ht_nn v]
  have h_summable_heat := summable_heatTerm b hlam ht_nn v
  have h_hsum_heat : HasSum (fun i : ι => heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i)
      (∑' i, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) := h_summable_heat.hasSum
  have h_hsum_basis : HasSum (fun i : ι => ⟪b i, v⟫_ℝ • b i) v := by
    have h_repr : HasSum (fun i => b.repr v i • b i) v := b.hasSum_repr v
    have h_eq : (fun i => b.repr v i • b i) = (fun i => ⟪b i, v⟫_ℝ • b i) := by
      funext i; rw [b.repr_apply_apply]
    rwa [h_eq] at h_repr
  have h_hsum_diff : HasSum (fun i : ι =>
      heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i - ⟪b i, v⟫_ℝ • b i)
      ((∑' i, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) - v) :=
    h_hsum_heat.sub h_hsum_basis
  have h_sum_diff :
      (∑' i : ι, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) - v =
      ∑' i : ι, (heatCoeff lam t i - 1) • ⟪b i, v⟫_ℝ • b i := by
    have h_summand_eq : (fun i : ι =>
        heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i - ⟪b i, v⟫_ℝ • b i) =
        (fun i => (heatCoeff lam t i - 1) • ⟪b i, v⟫_ℝ • b i) := by
      funext i; rw [sub_smul, one_smul]
    rw [h_summand_eq] at h_hsum_diff
    exact h_hsum_diff.tsum_eq.symm
  rw [h_sum_diff]
  have h_sum_eq : (fun i : ι => (heatCoeff lam t i - 1) • ⟪b i, v⟫_ℝ • b i) =
      (fun i => ((heatCoeff lam t i - 1) * ⟪b i, v⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_sum_eq]
  set f : ι → ℝ := fun i => (heatCoeff lam t i - 1) * ⟪b i, v⟫_ℝ
  have h_f_sq_le : ∀ i, (f i) ^ 2 ≤ 4 * (⟪b i, v⟫_ℝ) ^ 2 := by
    intro i
    have h_pos : 0 < heatCoeff lam t i := Real.exp_pos _
    have h_le : heatCoeff lam t i ≤ 1 := (heatCoeff_mem_unit_interval hlam ht_nn i).2
    have h_diff_sq : (heatCoeff lam t i - 1) ^ 2 ≤ 4 := by
      nlinarith [h_pos, h_le, sq_nonneg (heatCoeff lam t i - 1)]
    have h_inner_sq_nn : 0 ≤ (⟪b i, v⟫_ℝ) ^ 2 := sq_nonneg _
    change ((heatCoeff lam t i - 1) * ⟪b i, v⟫_ℝ) ^ 2 ≤ 4 * (⟪b i, v⟫_ℝ) ^ 2
    have h_factor : ((heatCoeff lam t i - 1) * ⟪b i, v⟫_ℝ) ^ 2 =
        (heatCoeff lam t i - 1) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by ring
    rw [h_factor]
    nlinarith [h_diff_sq, h_inner_sq_nn]
  have h_summable_f_sq : Summable (fun i : ι => (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (h_summable_sq.mul_left 4)
    · intro i; positivity
    · intro i; exact h_f_sq_le i
  have h_norm_sq_eq := orthonormal_norm_sq_eq_tsum_sq b f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 < ε ^ 2
  rw [h_norm_sq_eq]
  have h_split : ∑' i : ι, (f i) ^ 2 =
      (∑ i ∈ T_fin, (f i) ^ 2) +
      ∑' i : { i : ι // i ∉ T_fin }, (f (i : ι)) ^ 2 :=
    (h_summable_f_sq.sum_add_tsum_subtype_compl T_fin).symm
  rw [h_split]
  have h_head_bound : ∑ i ∈ T_fin, (f i) ^ 2 < ε ^ 2 / 4 := by
    have h_in_ball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht_nn]
      exact ht_lt
    have h_dist := hδ t h_in_ball
    rw [dist_zero_right, Real.norm_eq_abs] at h_dist
    have h_head_eq_f : ∀ i,
        (heatCoeff lam t i - 1) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 = (f i) ^ 2 := by
      intro i
      change _ = ((heatCoeff lam t i - 1) * ⟪b i, v⟫_ℝ) ^ 2
      ring
    have h_sum_eq' : ∑ i ∈ T_fin,
        (heatCoeff lam t i - 1) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 =
        ∑ i ∈ T_fin, (f i) ^ 2 := by
      apply Finset.sum_congr rfl; intros i _; exact h_head_eq_f i
    rw [h_sum_eq'] at h_dist
    have h_nn : 0 ≤ ∑ i ∈ T_fin, (f i) ^ 2 := by
      apply Finset.sum_nonneg; intros; exact sq_nonneg _
    rwa [abs_of_nonneg h_nn] at h_dist
  have h_tail_bound :
      ∑' i : { i : ι // i ∉ T_fin }, (f (i : ι)) ^ 2 < ε ^ 2 / 4 := by
    have h_tail_le :
        ∑' i : { i : ι // i ∉ T_fin }, (f (i : ι)) ^ 2 ≤
        4 * ∑' i : { i : ι // i ∉ T_fin }, (⟪b (i : ι), v⟫_ℝ) ^ 2 := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => h_f_sq_le i) ?_ ?_
      · exact h_summable_f_sq.subtype _
      · exact (h_summable_sq.subtype _).mul_left 4
    have h_lt : 4 *
        ∑' i : { i : ι // i ∉ T_fin }, (⟪b (i : ι), v⟫_ℝ) ^ 2 <
        4 * (ε ^ 2 / 16) :=
      mul_lt_mul_of_pos_left hT_fin (by norm_num : (0 : ℝ) < 4)
    have h_eq : 4 * (ε ^ 2 / 16) = ε ^ 2 / 4 := by ring
    linarith [h_tail_le, h_lt, h_eq]
  linarith [h_head_bound, h_tail_bound]

private lemma norm_abstractSpectralSemigroup_sub_le_diff (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t t₀ : ℝ} (ht : 0 ≤ t) (ht₀ : 0 ≤ t₀)
    (v : X) :
    ‖abstractSpectralSemigroup b hlam t v -
        abstractSpectralSemigroup b hlam t₀ v‖ ≤
      ‖abstractSpectralSemigroup b hlam |t - t₀| v - v‖ := by
  rcases le_or_gt t₀ t with h | h
  · have h_diff_nn : 0 ≤ t - t₀ := sub_nonneg.mpr h
    have h_abs : |t - t₀| = t - t₀ := abs_of_nonneg h_diff_nn
    have h_law : abstractSpectralSemigroup b hlam t =
        (abstractSpectralSemigroup b hlam t₀).comp
          (abstractSpectralSemigroup b hlam (t - t₀)) := by
      have h_add := abstractSpectralSemigroup_apply_add b hlam ht₀ h_diff_nn
      rwa [show t₀ + (t - t₀) = t from by ring] at h_add
    have h_apply : abstractSpectralSemigroup b hlam t v =
        abstractSpectralSemigroup b hlam t₀
          (abstractSpectralSemigroup b hlam (t - t₀) v) := by rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        abstractSpectralSemigroup b hlam t₀
            (abstractSpectralSemigroup b hlam (t - t₀) v) -
          abstractSpectralSemigroup b hlam t₀ v =
        abstractSpectralSemigroup b hlam t₀
          (abstractSpectralSemigroup b hlam (t - t₀) v - v) := by
      rw [← (abstractSpectralSemigroup b hlam t₀).map_sub]
    rw [h_sub_eq]
    have h_op_le_one := abstractSpectralSemigroup_opNorm_le_one b hlam t₀
    have h_norm_nn :
        0 ≤ ‖abstractSpectralSemigroup b hlam (t - t₀) v - v‖ := norm_nonneg _
    calc ‖abstractSpectralSemigroup b hlam t₀
              (abstractSpectralSemigroup b hlam (t - t₀) v - v)‖
        ≤ ‖abstractSpectralSemigroup b hlam t₀‖ *
            ‖abstractSpectralSemigroup b hlam (t - t₀) v - v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖abstractSpectralSemigroup b hlam (t - t₀) v - v‖ :=
          mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖abstractSpectralSemigroup b hlam (t - t₀) v - v‖ := one_mul _
      _ = ‖abstractSpectralSemigroup b hlam |t - t₀| v - v‖ := by rw [h_abs]
  · have h_diff_nn : 0 ≤ t₀ - t := sub_nonneg.mpr h.le
    have h_abs : |t - t₀| = t₀ - t := by rw [abs_sub_comm, abs_of_nonneg h_diff_nn]
    have h_law : abstractSpectralSemigroup b hlam t₀ =
        (abstractSpectralSemigroup b hlam t).comp
          (abstractSpectralSemigroup b hlam (t₀ - t)) := by
      have h_add := abstractSpectralSemigroup_apply_add b hlam ht h_diff_nn
      rwa [show t + (t₀ - t) = t₀ from by ring] at h_add
    have h_apply : abstractSpectralSemigroup b hlam t₀ v =
        abstractSpectralSemigroup b hlam t
          (abstractSpectralSemigroup b hlam (t₀ - t) v) := by rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        abstractSpectralSemigroup b hlam t v -
          abstractSpectralSemigroup b hlam t
            (abstractSpectralSemigroup b hlam (t₀ - t) v) =
        abstractSpectralSemigroup b hlam t
          (v - abstractSpectralSemigroup b hlam (t₀ - t) v) := by
      rw [← (abstractSpectralSemigroup b hlam t).map_sub]
    rw [h_sub_eq]
    have h_op_le_one := abstractSpectralSemigroup_opNorm_le_one b hlam t
    have h_norm_nn :
        0 ≤ ‖v - abstractSpectralSemigroup b hlam (t₀ - t) v‖ := norm_nonneg _
    have h_norm_swap :
        ‖v - abstractSpectralSemigroup b hlam (t₀ - t) v‖ =
          ‖abstractSpectralSemigroup b hlam (t₀ - t) v - v‖ := by rw [norm_sub_rev]
    calc ‖abstractSpectralSemigroup b hlam t
              (v - abstractSpectralSemigroup b hlam (t₀ - t) v)‖
        ≤ ‖abstractSpectralSemigroup b hlam t‖ *
            ‖v - abstractSpectralSemigroup b hlam (t₀ - t) v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v - abstractSpectralSemigroup b hlam (t₀ - t) v‖ :=
          mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖abstractSpectralSemigroup b hlam (t₀ - t) v - v‖ := by
          rw [one_mul, h_norm_swap]
      _ = ‖abstractSpectralSemigroup b hlam |t - t₀| v - v‖ := by rw [h_abs]

private theorem abstractSpectralSemigroup_continuous_at_pos (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t) (v : X) :
    ContinuousAt (fun u : ℝ => abstractSpectralSemigroup b hlam u v) t := by
  change Filter.Tendsto (fun u : ℝ => abstractSpectralSemigroup b hlam u v)
      (𝓝 t) (𝓝 (abstractSpectralSemigroup b hlam t v))
  rw [show (𝓝 (abstractSpectralSemigroup b hlam t v)) =
      𝓝 (0 + abstractSpectralSemigroup b hlam t v) by rw [zero_add]]
  have h_diff_to_zero :
      Tendsto (fun u : ℝ =>
          abstractSpectralSemigroup b hlam u v -
            abstractSpectralSemigroup b hlam t v) (𝓝 t) (𝓝 0) := by
    have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
    have h_bound_event : ∀ᶠ u : ℝ in 𝓝 t,
        ‖abstractSpectralSemigroup b hlam u v -
            abstractSpectralSemigroup b hlam t v‖ ≤
          ‖abstractSpectralSemigroup b hlam |u - t| v - v‖ := by
      filter_upwards [h_pos_nhds] with u hu_pos
      exact norm_abstractSpectralSemigroup_sub_le_diff b hlam
        (le_of_lt hu_pos) ht.le v
    have h_abs_to_zero : Tendsto (fun u : ℝ => |u - t|) (𝓝 t) (𝓝 0) := by
      have h_sub : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (0 : ℝ)) := by
        have : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (t - t)) :=
          Filter.Tendsto.sub tendsto_id tendsto_const_nhds
        simpa using this
      have := h_sub.abs
      simpa using this
    have h_abs_to_zero_within :
        Tendsto (fun u : ℝ => |u - t|) (𝓝 t) (𝓝[≥] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_abs_to_zero,
        Eventually.of_forall (fun _ => Set.mem_Ici.mpr (abs_nonneg _))⟩
    have h_strong := abstractSpectralSemigroup_continuous_at_zero b hlam v
    have h_compose :
        Tendsto (fun u : ℝ => abstractSpectralSemigroup b hlam |u - t| v)
          (𝓝 t) (𝓝 v) := h_strong.comp h_abs_to_zero_within
    have h_diff_to_zero' :
        Tendsto (fun u : ℝ => abstractSpectralSemigroup b hlam |u - t| v - v)
          (𝓝 t) (𝓝 0) := by
      have := h_compose.sub (tendsto_const_nhds (x := v))
      simpa using this
    have h_norm_to_zero :
        Tendsto (fun u : ℝ => ‖abstractSpectralSemigroup b hlam |u - t| v - v‖)
          (𝓝 t) (𝓝 0) := by
      have := h_diff_to_zero'.norm
      simpa using this
    exact squeeze_zero_norm' h_bound_event h_norm_to_zero
  have h_added := h_diff_to_zero.add (tendsto_const_nhds
    (x := abstractSpectralSemigroup b hlam t v))
  simpa using h_added

theorem abstractSpectralSemigroup_continuousOn (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (v : X) :
    ContinuousOn (fun u : ℝ => abstractSpectralSemigroup b hlam u v)
      (Set.Ici (0 : ℝ)) := by
  intro t ht
  rcases lt_or_eq_of_le (Set.mem_Ici.mp ht) with ht_pos | ht_eq
  · exact (abstractSpectralSemigroup_continuous_at_pos b hlam ht_pos v).continuousWithinAt
  · subst ht_eq
    have h_zero : abstractSpectralSemigroup b hlam 0 v = v := by
      rw [abstractSpectralSemigroup_apply_zero b hlam]; rfl
    rw [ContinuousWithinAt, h_zero]
    exact abstractSpectralSemigroup_continuous_at_zero b hlam v

end Parabolic
end Analysis
end DifferentialGeometry

end
