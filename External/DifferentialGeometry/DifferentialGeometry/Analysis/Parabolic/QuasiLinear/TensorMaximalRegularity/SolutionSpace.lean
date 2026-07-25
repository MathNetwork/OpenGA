import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

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

abbrev MaxRegSolutionSpace (a : ℝ) (T : ℝ) : Type _ :=
  timeH1 (tensorHs (I := I) (M := M) g r s a) T

def homModeCoeff {a : ℝ}
    {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
      u₀.coeff i)
    (Continuous.continuousOn (by fun_prop))

def homDerivModeCoeff {a : ℝ}
    {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => -(TensorEigenIdx.lambda (I := I) (M := M) i) *
      (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * u₀.coeff i))
    (Continuous.continuousOn (by fun_prop))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem homDerivModeCoeff_eq_smul
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i := by
  refine Lp.ext ?_
  have hderiv : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T)
        u₀ i) =ᵐ[timeMeasure T]
      fun t => -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * u₀.coeff i) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hmode : ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T)
        u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hsmul := Lp.coeFn_smul (-(TensorEigenIdx.lambda (I := I) (M := M) i))
    (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
  filter_upwards [hderiv, hmode, hsmul] with t htderiv htmode htsmul
  rw [htderiv, htsmul, Pi.smul_apply, htmode, smul_eq_mul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_homModeCoeff_sq_le (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (u₀.coeff i) ^ 2 := by
  rw [show homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i =
        TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
          (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            u₀.coeff i)
          (Continuous.continuousOn (by fun_prop)) from rfl]
  have hbound : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ≤
      Real.sqrt T * |u₀.coeff i| := by
    refine TimeSobolev.norm_ofContinuousOn_le_of_bound _ (fun t ht => ?_)
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hexp_le : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have hexp_pos : 0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
      Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt hexp_pos)]
    nlinarith [abs_nonneg (u₀.coeff i), hexp_le, hexp_pos]
  have hsq : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ^ 2 ≤
      (Real.sqrt T * |u₀.coeff i|) ^ 2 := by
    have hrhs_nonneg : 0 ≤ Real.sqrt T * |u₀.coeff i| :=
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    nlinarith [hbound, norm_nonneg (TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
      (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i)
      (Continuous.continuousOn (by fun_prop))), hrhs_nonneg]
  calc ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
          (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            u₀.coeff i)
          (Continuous.continuousOn (by fun_prop))‖ ^ 2
      ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := hsq
    _ = T * (u₀.coeff i) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hT, sq_abs]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem weighted_homModeCoeff_le (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (a + 2) *
        ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
  have hbase :=
    norm_homModeCoeff_sq_le (I := I) (M := M) (a := a) (T := T) hT u₀ i
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
  calc tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) * (T * (u₀.coeff i) ^ 2) :=
        mul_le_mul_of_nonneg_left hbase hw_nonneg
    _ = T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
        ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_homModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 2) *
      ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => T *
      (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left T
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2))
      (sq_nonneg _)
  · exact weighted_homModeCoeff_le (I := I) (M := M) (a := a) (T := T) hT u₀ i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem weighted_homDerivModeCoeff_le (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i a *
        ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hderiv_eq :=
    homDerivModeCoeff_eq_smul (I := I) (M := M) (a := a) (T := T) u₀ i
  have hnorm : ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 =
      lam ^ 2 *
        ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 := by
    rw [hderiv_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_pow,
      neg_one_sq, one_mul]
  have hmode :=
    norm_homModeCoeff_sq_le (I := I) (M := M) (a := a) (T := T) hT u₀ i
  have hweight : tensorSobolevWeight (I := I) (M := M) i a * (1 + lam) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (a + 2) := by
    have hexpand : tensorSobolevWeight (I := I) (M := M) i (a + 2) =
        (1 + lam) ^ (a + 2 : ℝ) := by rw [tensorSobolevWeight, hlam_def]
    have hbase : tensorSobolevWeight (I := I) (M := M) i a =
        (1 + lam) ^ (a : ℝ) := by rw [tensorSobolevWeight, hlam_def]
    rw [hexpand, hbase, ← Real.rpow_natCast (1 + lam) 2,
      ← Real.rpow_add hbase_pos]
    norm_num
  have hlam_sq_le : lam ^ 2 ≤ (1 + lam) ^ 2 := by nlinarith
  calc tensorSobolevWeight (I := I) (M := M) i a *
          ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          (lam ^ 2 *
            ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
        rw [hnorm]
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((1 + lam) ^ 2 * (T * (u₀.coeff i) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hw_nonneg
        have hmode_nn : 0 ≤ ‖homModeCoeff (I := I) (M := M)
            (a := a) (T := T) u₀ i‖ ^ 2 := sq_nonneg _
        have hT_c_nn : 0 ≤ T * (u₀.coeff i) ^ 2 :=
          mul_nonneg hT (sq_nonneg _)
        calc lam ^ 2 *
                ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2
            ≤ (1 + lam) ^ 2 *
                ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hlam_sq_le hmode_nn
          _ ≤ (1 + lam) ^ 2 * (T * (u₀.coeff i) ^ 2) :=
              mul_le_mul_of_nonneg_left hmode (sq_nonneg _)
    _ = T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
        rw [← hweight]; ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_homDerivModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i a *
      ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => T *
      (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left T
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a)
      (sq_nonneg _)
  · exact weighted_homDerivModeCoeff_le (I := I) (M := M) (a := a) (T := T) hT u₀ i

def maxRegHomogeneousSolField (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T :=
  timeL2OfModes (I := I) (M := M) (σ := a + 2)
    (fun i => homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousSolField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) i =
      homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a + 2) _
    (summable_homModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀) i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_homModeCoeff_Ha1 (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    (summable_homModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀)
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1))
      (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (tensorSobolevWeight_mono (I := I) (M := M) i (by linarith)) (sq_nonneg _)

def maxRegHomogeneousSolFieldTraceScale (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T :=
  timeL2OfModes (I := I) (M := M) (σ := a + 1)
    (fun i => homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousSolFieldHa1_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀) i =
      homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a + 1) _
    (summable_homModeCoeff_Ha1 (I := I) (M := M) (a := a) (T := T) hT u₀) i

def maxRegHomogeneousDerivField (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  timeL2OfModes (I := I) (M := M) (σ := a)
    (fun i => homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousDerivField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousDerivField (I := I) (M := M) a T u₀) i =
      homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a) _
    (summable_homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀) i

def maxRegHomogeneous (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := r) (s := s) a T :=
  TimeSobolev.timeH1.mk
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) u₀)
    (maxRegHomogeneousDerivField (I := I) (M := M) a T u₀)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem maxRegHomogeneous_init
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    (maxRegHomogeneous (I := I) (M := M) a T u₀).init =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneous_trace0
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    TimeSobolev.timeH1.trace0 _ T
        (maxRegHomogeneous (I := I) (M := M) a T u₀) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem maxRegHomogeneous_deriv
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    (maxRegHomogeneous (I := I) (M := M) a T u₀).deriv =
      maxRegHomogeneousDerivField (I := I) (M := M) a T u₀ :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousDerivField_eq_scaleLaplacian (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    maxRegHomogeneousDerivField (I := I) (M := M) a T u₀ =
      timeScaleLaplacian (I := I) (M := M) a
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maxRegHomogeneousDerivField_timeModeCoeff (I := I) (M := M) (a := a)
      (T := T) hT u₀ i,
    timeModeCoeff_timeScaleLaplacian (I := I) (M := M) (τ := a)
      (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) i,
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a)
      (T := T) hT u₀ i]
  exact homDerivModeCoeff_eq_smul (I := I) (M := M) (a := a) (T := T) u₀ i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneous_timeDeriv_eq (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maxRegHomogeneous (I := I) (M := M) a T u₀) =
      timeScaleLaplacian (I := I) (M := M) a
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) := by
  rw [TimeSobolev.timeH1.timeDeriv_apply, maxRegHomogeneous_deriv (I := I) (M := M)
    (a := a) (T := T) u₀]
  exact maxRegHomogeneousDerivField_eq_scaleLaplacian (I := I) (M := M)
    (h_compact := h_compact) (a := a) (T := T) hT u₀

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDerivField_add (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT (f + f') =
      maximalRegularityDerivField (I := I) (M := M) a hT f +
        maximalRegularityDerivField (I := I) (M := M) a hT f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f' i]
  rw [derivModeCoeff, derivModeCoeff, derivModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDerivField_smul (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (c : ℝ) (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT (c • f) =
      c • maximalRegularityDerivField (I := I) (M := M) a hT f := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT (c • f) i,
    timeModeCoeff_smul (I := I) (M := M),
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i]
  rw [derivModeCoeff, derivModeCoeff, timeModeCoeff_smul (I := I) (M := M),
    map_smul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_add (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityOp (I := I) (M := M) a hT hT1 (f + f') =
      maximalRegularityOp (I := I) (M := M) a hT hT1 f +
        maximalRegularityOp (I := I) (M := M) a hT hT1 f' := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [TimeSobolev.timeH1.init_add]
    change (0 : tensorHs (I := I) (M := M) g r s a) =
      (0 : tensorHs (I := I) (M := M) g r s a) +
        (0 : tensorHs (I := I) (M := M) g r s a)
    rw [add_zero]
  · rw [TimeSobolev.timeH1.deriv_add]
    exact maximalRegularityDerivField_add (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le f f'

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_smul (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (c : ℝ) (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityOp (I := I) (M := M) a hT hT1 (c • f) =
      c • maximalRegularityOp (I := I) (M := M) a hT hT1 f := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [TimeSobolev.timeH1.init_smul]
    change (0 : tensorHs (I := I) (M := M) g r s a) =
      c • (0 : tensorHs (I := I) (M := M) g r s a)
    rw [smul_zero]
  · rw [TimeSobolev.timeH1.deriv_smul]
    exact maximalRegularityDerivField_smul (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le c f

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityOp (I := I) (M := M) a hT hT1 (f - f') =
      maximalRegularityOp (I := I) (M := M) a hT hT1 f -
        maximalRegularityOp (I := I) (M := M) a hT hT1 f' := by
  have hadd := maximalRegularityOp_add (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

def maxRegDuhamelSolField (a : ℝ) {T : ℝ} (hT : 0 < T) (_hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T :=
  maxRegHomogeneousSolField (I := I) (M := M) a T u₀ +
    maximalRegularitySolField (I := I) (M := M) a hT.le gforce

def maxRegDuhamelSolFieldHa1 (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T :=
  maxRegHomogeneousSolFieldTraceScale (I := I) (M := M) a T u₀ +
    maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 gforce

def maxRegDuhamelMap (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := r) (s := s) a T :=
  maxRegHomogeneous (I := I) (M := M) a T u₀ +
    maximalRegularityOp (I := I) (M := M) a hT hT1 gforce

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem maxRegDuhamelMap_init (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).init =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ := by
  rw [maxRegDuhamelMap, TimeSobolev.timeH1.init_add,
    maxRegHomogeneous_init (I := I) (M := M) (a := a) (T := T) u₀]
  rw [show (maximalRegularityOp (I := I) (M := M) a hT hT1 gforce).init =
        (0 : tensorHs (I := I) (M := M) g r s a) from rfl, add_zero]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelMap_trace0 (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ := by
  rw [TimeSobolev.timeH1.trace0_apply]
  exact maxRegDuhamelMap_init (I := I) (M := M) (a := a) (T := T) hT hT1 u₀ gforce

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem maxRegDuhamelMap_deriv (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv =
      maxRegHomogeneousDerivField (I := I) (M := M) a T u₀ +
        maximalRegularityDerivField (I := I) (M := M) a hT.le gforce := by
  rw [maxRegDuhamelMap, TimeSobolev.timeH1.deriv_add]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelMap_timeDeriv_eq (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) =
      timeScaleLaplacian (I := I) (M := M) a
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
        gforce := by
  rw [TimeSobolev.timeH1.timeDeriv_apply,
    maxRegDuhamelMap_deriv (I := I) (M := M) (a := a) (T := T) hT hT1 u₀ gforce]
  rw [maxRegHomogeneousDerivField_eq_scaleLaplacian (I := I) (M := M)
    (h_compact := h_compact) (a := a) (T := T) hT.le u₀]
  have hsolve := maximalRegularityOp_solves (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce
  rw [maximalRegularityOp_timeDeriv (I := I) (M := M)
    (a := a) hT hT1 gforce] at hsolve
  rw [hsolve]
  rw [maxRegDuhamelSolField, map_add]
  abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelMap_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce'‖ ≤
      2 * ‖gforce - gforce'‖ := by
  have hdiff : maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce' =
      maximalRegularityOp (I := I) (M := M) a hT hT1
        (gforce - gforce') := by
    rw [maximalRegularityOp_sub (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce gforce']
    change (maxRegHomogeneous (I := I) (M := M) a T u₀ +
          maximalRegularityOp (I := I) (M := M) a hT hT1 gforce) -
        (maxRegHomogeneous (I := I) (M := M) a T u₀ +
          maximalRegularityOp (I := I) (M := M) a hT hT1 gforce') =
      maximalRegularityOp (I := I) (M := M) a hT hT1 gforce -
        maximalRegularityOp (I := I) (M := M) a hT hT1 gforce'
    abel
  rw [hdiff]
  exact maximalRegularityOp_norm_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (gforce - gforce')

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelMap_lipschitzWith (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    LipschitzWith 2 (fun gforce :
        timeL2 (tensorHs (I := I) (M := M) g r s a) T =>
      maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) := by
  refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have h := maxRegDuhamelMap_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce'
  rw [show ((2 : ℝ≥0) : ℝ) = (2 : ℝ) from by norm_num]
  exact h

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
