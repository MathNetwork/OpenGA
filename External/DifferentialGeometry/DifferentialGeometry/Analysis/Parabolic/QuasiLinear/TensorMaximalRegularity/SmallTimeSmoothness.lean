import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

private theorem perModeConv_sq_le_time_mul_integral (lam : ℝ) (hlam : 0 ≤ lam)
    {c : ℝ → ℝ} (hc : Continuous c) {t : ℝ} (ht : 0 ≤ t) :
    (perModeConv lam c t) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 := by
  set k : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s))) * c s with hk_def
  have hk_cont : Continuous k := by fun_prop
  have hconv_eq : perModeConv lam c t = ∫ s in (0 : ℝ)..t, k s := by
    rw [perModeConv]
  have hCS : (∫ s in (0 : ℝ)..t, (1 : ℝ) * k s) ^ 2
      ≤ (∫ s in (0 : ℝ)..t, (1 : ℝ)) * ∫ s in (0 : ℝ)..t, (1 : ℝ) * (k s) ^ 2 :=
    weighted_cauchy_schwarz ht continuous_const hk_cont (fun _ _ => zero_le_one)
  simp only [one_mul] at hCS
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hCS
  have hk_sq_le : ∀ s ∈ Set.Icc (0 : ℝ) t, (k s) ^ 2 ≤ (c s) ^ 2 := by
    intro s hs
    have hexp : Real.exp (-(lam * (t - s))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs.1, hs.2, mul_nonneg hlam (sub_nonneg.mpr hs.2)])
    have hexp_nonneg : 0 ≤ Real.exp (-(lam * (t - s))) := (Real.exp_pos _).le
    rw [hk_def]
    rw [mul_pow]
    have hsq_le_one : Real.exp (-(lam * (t - s))) ^ 2 ≤ 1 := by
      nlinarith [hexp, hexp_nonneg]
    nlinarith [sq_nonneg (c s), hsq_le_one]
  have hk_sq_int : (∫ s in (0 : ℝ)..t, (k s) ^ 2) ≤ ∫ s in (0 : ℝ)..t, (c s) ^ 2 := by
    refine intervalIntegral.integral_mono_on ht ?_ ?_ ?_
    · exact (hk_cont.pow 2).intervalIntegrable 0 t
    · exact (hc.pow 2).intervalIntegrable 0 t
    · exact hk_sq_le
  have ht_int_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, (k s) ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun s _ => sq_nonneg _)
  calc (perModeConv lam c t) ^ 2
      = (∫ s in (0 : ℝ)..t, k s) ^ 2 := by rw [hconv_eq]
    _ ≤ t * ∫ s in (0 : ℝ)..t, (k s) ^ 2 := hCS
    _ ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hk_sq_int ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHs_smallTime_norm_le_of_perModeConv
    (a : ℝ) {T : ℝ} (hT : 0 < T)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hc_cont : ∀ i, Continuous (c i))
    {B : TensorEigenIdx (I := I) (M := M) g r s → ℝ} (hB_sum : Summable B)
    (hB_le : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
      tensorSobolevWeight (I := I) (M := M) i (a + 2) * (c i s) ^ 2 ≤ B i)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d₂,
        ∀ W : tensorHs (I := I) (M := M) g r s (a + 2),
          (∀ i, W.coeff i =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (c i) t) →
          ‖W‖ ≤ R₀ := by
  classical

  have hB_nonneg : ∀ i, 0 ≤ B i := by
    intro i
    refine le_trans ?_ (hB_le i 0 ⟨le_refl 0, hT.le⟩)
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)
  set Mass : ℝ := ∑' i, B i with hMass_def
  have hMass_nonneg : 0 ≤ Mass := tsum_nonneg hB_nonneg

  set d₂ : ℝ := min T (R₀ ^ 2 / (T * Mass + 1)) with hd₂_def
  have hden_pos : 0 < T * Mass + 1 := by positivity
  have hd₂_pos : 0 < d₂ := by
    refine lt_min hT ?_
    positivity
  have hd₂_le : d₂ ≤ T := min_le_left _ _
  refine ⟨d₂, hd₂_pos, hd₂_le, ?_⟩
  intro t ht W hWcoeff
  obtain ⟨ht0, htd₂⟩ := ht
  have htT : t ≤ T := le_trans htd₂ hd₂_le
  have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩

  have hper_mode : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (a + 2) * (W.coeff i) ^ 2 ≤ t * (T * B i) := by
    intro i
    rw [hWcoeff i]
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hwt_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)

    have hCS := perModeConv_sq_le_time_mul_integral
      lam hlam_nonneg (hc_cont i) ht0

    have hstep1 : tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          (perModeConv lam (c i) t) ^ 2 ≤
        t * (tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          ∫ s in (0 : ℝ)..t, (c i s) ^ 2) := by
      calc tensorSobolevWeight (I := I) (M := M) i (a + 2) * (perModeConv lam (c i) t) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) *
              (t * ∫ s in (0 : ℝ)..t, (c i s) ^ 2) :=
            mul_le_mul_of_nonneg_left hCS hwt_nonneg
        _ = t * (tensorSobolevWeight (I := I) (M := M) i (a + 2) *
              ∫ s in (0 : ℝ)..t, (c i s) ^ 2) := by ring

    have hweight_int : tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          ∫ s in (0 : ℝ)..t, (c i s) ^ 2 ≤ t * B i := by
      rw [← intervalIntegral.integral_const_mul]
      have hmono : (∫ s in (0 : ℝ)..t,
            tensorSobolevWeight (I := I) (M := M) i (a + 2) * (c i s) ^ 2)
          ≤ ∫ _s in (0 : ℝ)..t, B i := by
        refine intervalIntegral.integral_mono_on ht0 ?_ intervalIntegrable_const ?_
        · exact (((hc_cont i).pow 2).const_mul _).intervalIntegrable 0 t
        · intro s hs
          exact hB_le i s ⟨hs.1, le_trans hs.2 htT⟩
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
      exact hmono
    calc tensorSobolevWeight (I := I) (M := M) i (a + 2) * (perModeConv lam (c i) t) ^ 2
        ≤ t * (tensorSobolevWeight (I := I) (M := M) i (a + 2) *
            ∫ s in (0 : ℝ)..t, (c i s) ^ 2) := hstep1
      _ ≤ t * (t * B i) :=
          mul_le_mul_of_nonneg_left hweight_int ht0
      _ ≤ t * (T * B i) := by
          refine mul_le_mul_of_nonneg_left ?_ ht0
          exact mul_le_mul_of_nonneg_right htT (hB_nonneg i)

  have hW_sum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 2) *
      (W.coeff i) ^ 2) := W.weighted_summable
  have hmaj_sum : Summable (fun i => t * (T * B i)) :=
    (hB_sum.mul_left T).mul_left t
  have hnorm_sq_le : ‖W‖ ^ 2 ≤ t * (T * Mass) := by
    rw [tensorHs.norm_sq_eq_tsum]
    have htsum_le : (∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 2) * (W.coeff i) ^ 2)
        ≤ ∑' i, t * (T * B i) :=
      Summable.tsum_le_tsum hper_mode hW_sum hmaj_sum
    calc (∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 2) * (W.coeff i) ^ 2)
        ≤ ∑' i, t * (T * B i) := htsum_le
      _ = t * (T * Mass) := by
          rw [tsum_mul_left, tsum_mul_left, hMass_def]

  have hTMass_nonneg : 0 ≤ T * Mass := mul_nonneg hT.le hMass_nonneg
  have htTMass_le : t * (T * Mass) ≤ d₂ * (T * Mass) :=
    mul_le_mul_of_nonneg_right htd₂ hTMass_nonneg
  have hd₂TMass_le : d₂ * (T * Mass) ≤ R₀ ^ 2 := by
    have hd₂_le2 : d₂ ≤ R₀ ^ 2 / (T * Mass + 1) := min_le_right _ _
    calc d₂ * (T * Mass) ≤ (R₀ ^ 2 / (T * Mass + 1)) * (T * Mass) :=
          mul_le_mul_of_nonneg_right hd₂_le2 hTMass_nonneg
      _ ≤ (R₀ ^ 2 / (T * Mass + 1)) * (T * Mass + 1) := by
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          positivity
      _ = R₀ ^ 2 := by field_simp
  have hnorm_sq_le_R₀ : ‖W‖ ^ 2 ≤ R₀ ^ 2 :=
    le_trans hnorm_sq_le (le_trans htTMass_le hd₂TMass_le)

  nlinarith [norm_nonneg W, hR₀.le, hnorm_sq_le_R₀]

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
