import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation

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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_const_inclusion
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) i =
      TimeSobolev.const T (u₀.coeff i) := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (TimeSobolev.const T
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀)) i
  have hconst := TimeSobolev.coeFn_const (X := tensorHs (I := I) (M := M) g r s (a + 1))
    (T := T)
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show (a + 1) ≤ a + 2 by linarith) u₀)
  have hrhs := TimeSobolev.coeFn_const (X := ℝ) (T := T) (u₀.coeff i)
  filter_upwards [hlhs, hconst, hrhs] with t htlhs htconst htrhs
  rw [htlhs, htconst, htrhs, tensorHsInclusion_coeff_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_homog_sub_const_coeFn
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ⇑(timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)) i) =ᵐ[timeMeasure T]
      fun t => (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
        u₀.coeff i := by
  have hhom : timeModeCoeff (I := I) (M := M)
      (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀) i =
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := a) hT u₀ i
  have hneg : timeModeCoeff (I := I) (M := M)
      (-TimeSobolev.const T
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show (a + 1) ≤ a + 2 by linarith) u₀)) i =
        -TimeSobolev.const T (u₀.coeff i) := by
    rw [show (-TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) =
        (-1 : ℝ) • TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀) by rw [neg_one_smul],
      timeModeCoeff_smul (I := I) (M := M),
      timeModeCoeff_const_inclusion (I := I) (M := M) u₀ i, neg_one_smul]
  rw [show (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ -
        TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) =
      maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ +
        (-TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) from by rw [sub_eq_add_neg],
    timeModeCoeff_add (I := I) (M := M), hhom, hneg]
  have hmode : ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hconst := TimeSobolev.coeFn_const (X := ℝ) (T := T) (u₀.coeff i)
  have hadd := Lp.coeFn_add (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
    (-TimeSobolev.const T (u₀.coeff i))
  have hnegc := Lp.coeFn_neg (TimeSobolev.const T (u₀.coeff i))
  filter_upwards [hadd, hmode, hconst, hnegc] with t htadd htmode htconst htnegc
  rw [htadd, Pi.add_apply, htmode, htnegc, Pi.neg_apply, htconst]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_timeModeCoeff_homog_sub_const_sq_le
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)) i‖ ^ 2 ≤
      T * (u₀.coeff i) ^ 2 := by
  set fdiff : ℝ → ℝ :=
    fun t => (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
      u₀.coeff i with hfdiff_def
  have hcont : Continuous fdiff := by rw [hfdiff_def]; fun_prop
  have hae := timeModeCoeff_homog_sub_const_coeFn (I := I) (M := M) u₀ hT i
  have heq : timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)) i =
      TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
        (hcont.continuousOn) := by
    refine Lp.ext ?_
    exact hae.trans (TimeSobolev.coeFn_ofContinuousOn _).symm
  rw [heq]
  have hbound : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
        (hcont.continuousOn)‖ ≤ Real.sqrt T * |u₀.coeff i| := by
    refine TimeSobolev.norm_ofContinuousOn_le_of_bound _ (fun t ht => ?_)
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hexp_le : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have hexp_pos : 0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
      Real.exp_pos _
    rw [hfdiff_def, Real.norm_eq_abs, abs_mul]
    have habs_le : |Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hexp_le, hexp_pos]
    calc |Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1| * |u₀.coeff i|
        ≤ 1 * |u₀.coeff i| :=
          mul_le_mul_of_nonneg_right habs_le (abs_nonneg _)
      _ = |u₀.coeff i| := one_mul _
  have hrhs_nonneg : 0 ≤ Real.sqrt T * |u₀.coeff i| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsq : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
        (hcont.continuousOn)‖ ^ 2 ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := by
    nlinarith [hbound, norm_nonneg (TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
      (f := fdiff) (hcont.continuousOn)), hrhs_nonneg]
  calc ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
          (hcont.continuousOn)‖ ^ 2
      ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := hsq
    _ = T * (u₀.coeff i) ^ 2 := by rw [mul_pow, Real.sq_sqrt hT, sq_abs]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousSolFieldHa1_sub_const_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T) :
    ‖maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ -
        TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)‖ ≤
      Real.sqrt T *
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show (a + 1) ≤ a + 2 by linarith) u₀‖ := by
  set ιu₀ := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hιu₀
  rw [show Real.sqrt T * ‖ιu₀‖ = 1 * ‖TimeSobolev.const T ιu₀‖ by
    rw [TimeSobolev.norm_const, one_mul]]
  refine norm_le_of_weighted_perMode_le (I := I) (M := M)
    (a := a + 1) (b := a + 1)
    (h_compact := h_compact) (C := 1) (by norm_num) _ _ (fun i => ?_)
  have hdefect := norm_timeModeCoeff_homog_sub_const_sq_le (I := I) (M := M) u₀ hT i
  have hconst : timeModeCoeff (I := I) (M := M) (TimeSobolev.const T ιu₀) i =
      TimeSobolev.const T (u₀.coeff i) :=
    timeModeCoeff_const_inclusion (I := I) (M := M) u₀ i
  have hconst_norm : ‖timeModeCoeff (I := I) (M := M) (TimeSobolev.const T ιu₀) i‖ ^ 2 =
      T * (u₀.coeff i) ^ 2 := by
    rw [hconst, TimeSobolev.norm_const, mul_pow, Real.sq_sqrt hT, Real.norm_eq_abs,
      sq_abs]
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a + 1) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)
  rw [one_pow, one_mul, hconst_norm]
  exact mul_le_mul_of_nonneg_left hdefect hw_nonneg

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelSolFieldHa1_sub_const_norm_le_ofCompact (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
        TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)‖ ≤
      Real.sqrt T *
          ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀‖ +
        2 * Real.sqrt T * ‖gforce‖ := by
  set ιu₀ := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hιu₀
  have hsplit : maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
        TimeSobolev.const T ιu₀ =
      (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ -
          TimeSobolev.const T ιu₀) +
        maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 gforce := by
    rw [maxRegDuhamelSolFieldHa1]; abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hhom := maxRegHomogeneousSolFieldHa1_sub_const_norm_le (I := I) (M := M)
    (h_compact := h_compact) u₀ hT.le
  have hduh := maximalRegularitySolFieldHa1_norm_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce
  exact add_le_add hhom hduh

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelSolFieldTraceScale_tendsto_const_ofCompact
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (_hTT₀ : T ≤ T₀)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
        (_hgB : ‖gforce‖ ≤ B),
      ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)‖ ≤ ε := by
  set ιu₀ := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hιu₀
  set Mcoef := ‖ιu₀‖ + 2 * max B 0 with hMcoef
  have hMcoef_nonneg : 0 ≤ Mcoef := by
    have : 0 ≤ 2 * max B 0 := by positivity
    positivity
  refine ⟨min 1 ((ε / (Mcoef + 1)) ^ 2), ?_, ?_⟩
  · have hden : 0 < Mcoef + 1 := by positivity
    have : 0 < (ε / (Mcoef + 1)) ^ 2 := by positivity
    exact lt_min one_pos this
  intro T hT hT1 hTT₀ gforce hgB
  have hden : 0 < Mcoef + 1 := by positivity
  have hT_le : T ≤ (ε / (Mcoef + 1)) ^ 2 := le_trans hTT₀ (min_le_right _ _)
  have hsqrtT_le : Real.sqrt T ≤ ε / (Mcoef + 1) := by
    rw [show ε / (Mcoef + 1) = Real.sqrt ((ε / (Mcoef + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hT_le
  have hsqrtT_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  refine le_trans (maxRegDuhamelSolFieldHa1_sub_const_norm_le_ofCompact (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce) ?_
  have hgforce_le : ‖gforce‖ ≤ max B 0 := le_trans hgB (le_max_left _ _)
  have hcombine : Real.sqrt T * ‖ιu₀‖ + 2 * Real.sqrt T * ‖gforce‖ ≤
      Real.sqrt T * Mcoef := by
    rw [hMcoef, mul_add]
    refine add_le_add (le_refl _) ?_
    rw [show Real.sqrt T * (2 * max B 0) = 2 * Real.sqrt T * max B 0 by ring]
    exact mul_le_mul_of_nonneg_left hgforce_le (by positivity)
  refine le_trans hcombine ?_
  calc Real.sqrt T * Mcoef
      ≤ (ε / (Mcoef + 1)) * Mcoef :=
        mul_le_mul_of_nonneg_right hsqrtT_le hMcoef_nonneg
    _ = ε * (Mcoef / (Mcoef + 1)) := by rw [div_mul_eq_mul_div, mul_div_assoc]
    _ ≤ ε * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hε.le
        rw [div_le_one hden]; linarith
    _ = ε := mul_one _

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
