import DifferentialGeometry.Geometry.Metric.TensorInner.PosDefBilinBoundedUnitBall

set_option autoImplicit false












noncomputable section

open Bornology Metric



theorem posDef_bilin_quadratic_lower_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hPD : ∀ v : F, v ≠ 0 → 0 < B v v)
    (hNN : ∀ v : F, 0 ≤ B v v)
    (hsl : ∀ (c : ℝ) (v w : F), B (c • v) w = c * B v w)
    (hsr : ∀ (c : ℝ) (v w : F), B v (c • w) = c * B v w) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : F, c * ‖v‖ ^ 2 ≤ B v v := by
  classical
  by_cases hF : Nontrivial F
  · haveI := hF
    haveI : ProperSpace F := FiniteDimensional.proper ℝ _
    set Q : F → ℝ := fun v => B v v with hQ_def
    have hQ_cont : Continuous Q := Continuous.clm_apply B.continuous continuous_id
    have hsc : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere _ _
    have hsne : (Metric.sphere (0 : F) 1).Nonempty := by
      rcases exists_ne (0 : F) with ⟨v₀, hv₀⟩
      refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀)
    obtain ⟨vm, hvm_mem, hvm_min⟩ := hsc.exists_isMinOn hsne hQ_cont.continuousOn
    have hvm_ne : vm ≠ 0 := by
      intro h
      rw [Metric.mem_sphere, dist_zero_right, h, norm_zero] at hvm_mem
      exact one_ne_zero hvm_mem.symm
    refine ⟨B vm vm, hPD vm hvm_ne, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hvne : ‖v‖ ≠ 0 := ne_of_gt hvnorm
      have hu_mem : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : F) 1 := by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hvnorm]
        exact inv_mul_cancel₀ hvne
      have hBu : B vm vm ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := hvm_min hu_mem
      have hBuu : B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = ‖v‖⁻¹ ^ 2 * B v v := by
        rw [hsl, hsr]; ring
      rw [hBuu] at hBu
      have hvsq_pos : 0 < ‖v‖ ^ 2 := by positivity
      calc B vm vm * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * B v v) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hBu hvsq_pos.le
        _ = B v v := by field_simp
  · rw [not_nontrivial_iff_subsingleton] at hF
    refine ⟨1, one_pos, ?_⟩
    intro v
    have hv0 : v = 0 := Subsingleton.elim v 0
    subst hv0
    simp
