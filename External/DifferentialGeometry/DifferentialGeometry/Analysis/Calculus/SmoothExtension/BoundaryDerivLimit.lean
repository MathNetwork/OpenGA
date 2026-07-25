import Mathlib.Analysis.Calculus.MeanValue















noncomputable section

open Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem hasDerivWithinAt_Ici_of_tendsto_nhdsGT
    {f f' : ℝ → F} {L : F} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hlim : Tendsto f' (𝓝[>] a) (𝓝 L)) :
    HasDerivWithinAt f L (Ici a) a := by
  have hids : Tendsto (fun s : ℝ => s) (𝓝[>] a) (𝓝 a) :=
    (continuous_id.tendsto a).mono_left nhdsWithin_le_nhds
  have hIccmem : Icc a b ∈ 𝓝[>] a := by
    have h : Ioo a b ∈ 𝓝[>] a := by
      have := inter_mem_nhdsWithin (Ioi a) (Iio_mem_nhds hab)
      rwa [Set.Ioi_inter_Iio] at this
    exact mem_of_superset h Ioo_subset_Icc_self
  have hfa : Tendsto f (𝓝[>] a) (𝓝 (f a)) :=
    (hcont.continuousWithinAt (left_mem_Icc.2 hab.le)).tendsto.mono_left
      (nhdsWithin_le_of_mem hIccmem)

  have key : ∀ ε : ℝ, 0 < ε → ∃ c, a < c ∧
      ∀ t ∈ Ioo a c, ‖f t - f a - (t - a) • L‖ ≤ ε * (t - a) := by
    intro ε hε
    have hball : ∀ᶠ x in 𝓝[>] a, ‖f' x - L‖ ≤ ε := by
      have h := hlim (Metric.closedBall_mem_nhds L hε)
      filter_upwards [h] with x hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hball
    obtain ⟨η, hη, hηball⟩ := hball
    refine ⟨min (a + η) b, lt_min (by linarith) hab, fun t ht => ?_⟩
    have hta : a < t := ht.1
    have htη : t < a + η := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htb : t < b := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have hmvt : ∀ s ∈ Ioo a t, ‖f t - f s - (t - s) • L‖ ≤ ε * (t - s) := by
      intro s hs
      have hsa : a < s := hs.1
      have hst : s < t := hs.2
      have hgcont : ContinuousOn (fun x => f x - x • L) (Icc s t) :=
        (hcont.mono (Icc_subset_Icc hsa.le htb.le)).sub
          (continuous_id.smul continuous_const).continuousOn
      have hgderiv : ∀ x ∈ Ico s t,
          HasDerivWithinAt (fun x => f x - x • L) (f' x - L) (Ici x) x := by
        intro x hx
        have hxab : x ∈ Ioo a b := ⟨lt_of_lt_of_le hsa hx.1, lt_trans hx.2 htb⟩
        have h1 : HasDerivAt (fun x => f x - x • L) (f' x - L) x := by
          simpa using (hderiv x hxab).sub ((hasDerivAt_id x).smul_const L)
        exact h1.hasDerivWithinAt
      have hbound : ∀ x ∈ Ico s t, ‖f' x - L‖ ≤ ε := by
        intro x hx
        have hxa : a < x := lt_of_lt_of_le hsa hx.1
        have hxη : x < a + η := lt_trans hx.2 htη
        exact hηball (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith) hxa
      have hmain := norm_image_sub_le_of_norm_deriv_right_le_segment hgcont hgderiv hbound t
        (right_mem_Icc.2 hst.le)
      have heq : (fun x => f x - x • L) t - (fun x => f x - x • L) s
          = f t - f s - (t - s) • L := by simp only [sub_smul]; abel
      rw [heq] at hmain
      exact hmain
    have hL1 : Tendsto (fun s => ‖f t - f s - (t - s) • L‖) (𝓝[>] a)
        (𝓝 ‖f t - f a - (t - a) • L‖) :=
      ((tendsto_const_nhds.sub hfa).sub ((tendsto_const_nhds.sub hids).smul_const L)).norm
    have hL2 : Tendsto (fun s => ε * (t - s)) (𝓝[>] a) (𝓝 (ε * (t - a))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub hids)
    refine le_of_tendsto_of_tendsto hL1 hL2 ?_
    have hIoomem : Ioo a t ∈ 𝓝[>] a := by
      have := inter_mem_nhdsWithin (Ioi a) (Iio_mem_nhds hta)
      rwa [Set.Ioi_inter_Iio] at this
    filter_upwards [hIoomem] with s hs using hmvt s hs

  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_diff_left, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨c, hac, hest⟩ := key (ε / 2) (by linarith)
  refine ⟨c - a, by linarith, fun t ht hdist => ?_⟩
  have hta : a < t := ht
  have htc : t < c := by rw [Real.dist_eq, abs_of_pos (by linarith)] at hdist; linarith
  have hta' : (0 : ℝ) < t - a := by linarith
  have h := hest t ⟨hta, htc⟩
  have hid : (t - a)⁻¹ • (f t - f a - (t - a) • L) = (t - a)⁻¹ • (f t - f a) - L := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hta'), one_smul]
  rw [dist_eq_norm, slope_def_module, ← hid, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hta']
  calc (t - a)⁻¹ * ‖f t - f a - (t - a) • L‖
      ≤ (t - a)⁻¹ * (ε / 2 * (t - a)) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.2 hta'))
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
