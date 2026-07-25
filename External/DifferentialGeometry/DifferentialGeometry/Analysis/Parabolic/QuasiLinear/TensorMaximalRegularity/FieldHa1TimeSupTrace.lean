import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DuhamelSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

private theorem integrableOn_sq_timeL2 (f : timeL2 ℝ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => (f s) ^ 2) volume 0 t := by
  obtain ⟨ht0, htT⟩ := ht
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le ht0]
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl htT
  have hL2 : IntegrableOn (fun s => (f s) ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hmem : MemLp (fun s => f s) 2 (timeMeasure T) := Lp.memLp f
    have hint : Integrable (fun s => (f s) ^ 2) (timeMeasure T) := hmem.integrable_sq
    exact hint
  exact hL2.mono_set hsub

private theorem integral_sq_Icc_le_norm_sq (f : timeL2 ℝ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, (f s) ^ 2) ≤ ‖f‖ ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hnorm : ‖f‖ ^ 2 = ∫ s in Set.Icc (0 : ℝ) T, ‖f s‖ ^ 2 :=
    TimeSobolev.norm_sq_eq_integral f
  have hnorm' : ‖f‖ ^ 2 = ∫ s in Set.Icc (0 : ℝ) T, (f s) ^ 2 := by
    rw [hnorm]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
  have hintT : IntegrableOn (fun s => (f s) ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hmem : MemLp (fun s => f s) 2 (timeMeasure T) := Lp.memLp f
    exact hmem.integrable_sq
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT)
  calc (∫ s in (0 : ℝ)..t, (f s) ^ 2)
      = ∫ s in Set.Ioc (0 : ℝ) t, (f s) ^ 2 :=
        intervalIntegral.integral_of_le ht0
    _ ≤ ∫ s in Set.Icc (0 : ℝ) T, (f s) ^ 2 := by
        refine setIntegral_mono_set hintT
          (Eventually.of_forall fun s => sq_nonneg _) ?_
        exact HasSubset.Subset.eventuallyLE hsub
    _ = ‖f‖ ^ 2 := hnorm'.symm

private theorem perModeConv_endpoint_sq_le_timeL2 (lam : ℝ) (f : timeL2 ℝ T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (perModeConv lam (fun s => f s) t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, (f s) ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  set k : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s))) with hk_def
  have hconv_eq : perModeConv lam (fun s => f s) t = ∫ s in (0 : ℝ)..t, k s * f s := rfl
  set A : ℝ := ∫ s in (0 : ℝ)..t, (f s) ^ 2 with hA
  set B : ℝ := ∫ s in (0 : ℝ)..t, k s * f s with hB
  set C : ℝ := ∫ s in (0 : ℝ)..t, k s ^ 2 with hC
  have hi_f2 : IntervalIntegrable (fun s => (f s) ^ 2) volume 0 t :=
    integrableOn_sq_timeL2 (T := T) f ⟨ht0, htT⟩
  have hi_kf : IntervalIntegrable (fun s => k s * f s) volume 0 t := by
    rw [hk_def]
    exact intervalIntegrable_kernel_mul_timeL2 lam t f 0 t
      ⟨le_rfl, le_trans ht0 htT⟩ ⟨ht0, htT⟩
  have hi_k2 : IntervalIntegrable (fun s => k s ^ 2) volume 0 t := by
    apply Continuous.intervalIntegrable; rw [hk_def]; fun_prop
  have hC_eq : C = duhamelKernelSqIntegral lam t := by
    rw [hC]; unfold duhamelKernelSqIntegral
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [hk_def, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have hquad : ∀ c : ℝ, 0 ≤ A * (c * c) + (-(2 * B)) * c + C := by
    intro c
    have hintegrand : (fun s => (k s - c * f s) ^ 2)
        = fun s => (c * c) * (f s) ^ 2 + (-(2 * c)) * (k s * f s) + k s ^ 2 := by
      funext s; ring
    have hexpand : (∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2)
        = (c * c) * A + (-(2 * c)) * B + C := by
      rw [hintegrand,
        intervalIntegral.integral_add
          ((hi_f2.const_mul (c * c)).add (hi_kf.const_mul (-(2 * c)))) hi_k2,
        intervalIntegral.integral_add (hi_f2.const_mul (c * c))
          (hi_kf.const_mul (-(2 * c))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2 :=
      intervalIntegral.integral_nonneg ht0 (fun s _ => sq_nonneg _)
    rw [hexpand] at hnonneg
    nlinarith [hnonneg]
  have hdiscrim : discrim A (-(2 * B)) C ≤ 0 :=
    discrim_le_zero (fun c => by nlinarith [hquad c])
  rw [discrim] at hdiscrim
  rw [hC_eq] at hdiscrim
  rw [hconv_eq]
  nlinarith [hdiscrim]

private theorem one_add_lambda_mul_perModeConv_sq_le_timeL2 (lam : ℝ)
    (hlam : 0 ≤ lam) (f : timeL2 ℝ T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (1 + lam) * (perModeConv lam (fun s => f s) t) ^ 2 ≤ (1 + T) * ‖f‖ ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hcs := perModeConv_endpoint_sq_le_timeL2 (T := T) lam f ⟨ht0, htT⟩
  have hkernel := one_add_lambda_mul_duhamel_kernel_sq_integral_le hlam ht0
  have hf2_nn : 0 ≤ ∫ s in (0 : ℝ)..t, (f s) ^ 2 :=
    intervalIntegral.integral_nonneg ht0 (fun s _ => sq_nonneg _)
  have h1plus_nn : 0 ≤ 1 + lam := by linarith
  have hf2_le : (∫ s in (0 : ℝ)..t, (f s) ^ 2) ≤ ‖f‖ ^ 2 :=
    integral_sq_Icc_le_norm_sq (T := T) f ⟨ht0, htT⟩
  have hfac_le : t + 1 / 2 ≤ 1 + T := by linarith
  have hfac_nn : 0 ≤ t + 1 / 2 := by linarith
  calc (1 + lam) * (perModeConv lam (fun s => f s) t) ^ 2
      ≤ (1 + lam) * (duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, (f s) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs h1plus_nn
    _ = ((1 + lam) * duhamelKernelSqIntegral lam t) * ∫ s in (0 : ℝ)..t, (f s) ^ 2 := by
        ring
    _ ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, (f s) ^ 2 :=
        mul_le_mul_of_nonneg_right hkernel hf2_nn
    _ ≤ (1 + T) * ‖f‖ ^ 2 := by
        refine le_trans (mul_le_mul_of_nonneg_left hf2_le hfac_nn) ?_
        exact mul_le_mul_of_nonneg_right hfac_le (sq_nonneg _)

variable {g₀ : SmoothRiemannianMetric I M}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem weighted_perModeConv_forcing_sq_le
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t) ^ 2 ≤
      (1 + T) * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) F i‖ ^ 2) := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_pos : (0 : ℝ) < 1 + lam := lt_of_lt_of_le one_pos (by linarith)
  have hweight_split :
      tensorSobolevWeight (I := I) (M := M) i (a + 1) =
        tensorSobolevWeight (I := I) (M := M) i a * (1 + lam) := by
    rw [tensorSobolevWeight, tensorSobolevWeight, hlam_def, Real.rpow_add hbase_pos,
      Real.rpow_one]
  have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hperMode := one_add_lambda_mul_perModeConv_sq_le_timeL2 (T := T) lam hlam_nn
    (timeModeCoeff (I := I) (M := M) F i) ht
  calc tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          (perModeConv lam (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t) ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          ((1 + lam) *
            (perModeConv lam (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t) ^ 2) := by
        rw [hweight_split]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((1 + T) * ‖timeModeCoeff (I := I) (M := M) F i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hperMode hwa_nn
    _ = (1 + T) * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) F i‖ ^ 2) := by ring

theorem maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le
    {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) :
    ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show a + 1 ≤ a + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2)) F)) t‖ ≤
        Real.sqrt (1 + T) * ‖F‖ := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  haveI := countable_tensorEigenIdx (I := I) (M := M)
    (g := g₀) (r := 0) (s := 2) h_compact
  set field := maxRegDuhamelSolField (I := I) (M := M) a hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2)) F with hfield_def
  set inclField := timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (show a + 1 ≤ a + 2 by linarith) field with hinclField_def
  have hincl_coeFn :
      ⇑inclField =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show a + 1 ≤ a + 2 by linarith) (field t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show a + 1 ≤ a + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) field
  have hcoeff_ae : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      (fun t => (field t).coeff i) =ᵐ[timeMeasure T]
        fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t :=
    fun i => timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 F i
  have hcoeff_all : ∀ᵐ t ∂(timeMeasure T),
      ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        (field t).coeff i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t :=
    (MeasureTheory.ae_all_iff).2 hcoeff_ae
  filter_upwards [hincl_coeFn, hcoeff_all, ae_restrict_mem measurableSet_Icc]
    with t htincl htcoeff htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have hnormsq : ‖inclField t‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t) ^ 2 := by
    rw [htincl, tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    refine tsum_congr (fun i => ?_)
    rw [tensorHsInclusion_coeff_apply (I := I) (M := M), htcoeff i]
  have hsummable_rhs : Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
      (1 + T) * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) F i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) h_compact (f := F)).mul_left _
  have hsummable_lhs : Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) F i) u) t) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsummable_rhs
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1))
        (sq_nonneg _)
    · exact weighted_perModeConv_forcing_sq_le (I := I) (M := M) F i htmem'
  have hsq_le : ‖inclField t‖ ^ 2 ≤ (1 + T) * ‖F‖ ^ 2 := by
    rw [hnormsq]
    have hmass : ∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        (1 + T) * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) F i‖ ^ 2) = (1 + T) * ‖F‖ ^ 2 := by
      rw [tsum_mul_left,
        ← norm_sq_eq_tsum_timeModeCoeff (I := I) (M := M) h_compact (f := F)]
    rw [← hmass]
    exact Summable.tsum_le_tsum
      (fun i => weighted_perModeConv_forcing_sq_le (I := I) (M := M) F i htmem')
      hsummable_lhs hsummable_rhs
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have hrhs_nn : 0 ≤ Real.sqrt (1 + T) * ‖F‖ :=
    mul_nonneg (Real.sqrt_nonneg _) hF_nn
  have hsqrt : Real.sqrt (‖inclField t‖ ^ 2) ≤ Real.sqrt ((1 + T) * ‖F‖ ^ 2) :=
    Real.sqrt_le_sqrt hsq_le
  rw [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  refine le_trans hsqrt ?_
  rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 + T), Real.sqrt_sq (norm_nonneg _)]

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
