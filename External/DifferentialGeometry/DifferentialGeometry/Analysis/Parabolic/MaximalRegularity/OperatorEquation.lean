import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

variable {τ : ℝ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lambda_sq_le (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
  have hlam := tensor_lambda_nonneg (I := I) (M := M) i
  nlinarith

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem scaleLaplacianWeightMulTwo
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight,
    ← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) 2,
    ← Real.rpow_add hbase_pos]
  norm_num

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem weightLambdaMulSqLe
    (v : tensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) * (v.coeff i) ^ 2 := by
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i τ
  have hsq : (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2 ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 * (v.coeff i) ^ 2 := by
    have h := lambda_sq_le (I := I) (M := M) i
    nlinarith [sq_nonneg (v.coeff i), h]
  calc tensorSobolevWeight (I := I) (M := M) i τ *
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i τ *
          ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 *
            (v.coeff i) ^ 2) := mul_le_mul_of_nonneg_left hsq hw_nonneg
    _ = tensorSobolevWeight (I := I) (M := M) i (τ + 2) * (v.coeff i) ^ 2 := by
        rw [← mul_assoc, scaleLaplacianWeightMulTwo (I := I) (M := M) i]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem scaleLaplacianWeightedSummable
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i τ *
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) v.weighted_summable
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i τ)
      (sq_nonneg _)
  · exact weightLambdaMulSqLe (I := I) (M := M) v i

def scaleLaplacianFun (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    tensorHs (I := I) (M := M) g r s τ where
  coeff i := -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i
  weighted_summable := scaleLaplacianWeightedSummable (I := I) (M := M) v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scaleLaplacianFun_coeff
    (v : tensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (scaleLaplacianFun (I := I) (M := M) v).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scaleLaplacianFun_add
    (v w : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    scaleLaplacianFun (I := I) (M := M) (v + w) =
      scaleLaplacianFun (I := I) (M := M) v + scaleLaplacianFun (I := I) (M := M) w := by
  refine tensorHs.ext (funext (fun i => ?_))
  simp only [scaleLaplacianFun_coeff, tensorHs.add_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scaleLaplacianFun_smul (c : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    scaleLaplacianFun (I := I) (M := M) (c • v) =
      c • scaleLaplacianFun (I := I) (M := M) v := by
  refine tensorHs.ext (funext (fun i => ?_))
  simp only [scaleLaplacianFun_coeff, tensorHs.smul_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_scaleLaplacianFun_le
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    ‖scaleLaplacianFun (I := I) (M := M) v‖ ≤ ‖v‖ := by
  have hsq : ‖scaleLaplacianFun (I := I) (M := M) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M),
      tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((scaleLaplacianFun (I := I) (M := M) v).weighted_summable)
      v.weighted_summable
    rw [scaleLaplacianFun_coeff]
    exact weightLambdaMulSqLe (I := I) (M := M) v i
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def tensorScaleLaplacian (τ : ℝ) :
    tensorHs (I := I) (M := M) g r s (τ + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s τ :=
  LinearMap.mkContinuous
    { toFun := scaleLaplacianFun (I := I) (M := M)
      map_add' := scaleLaplacianFun_add (I := I) (M := M)
      map_smul' := fun c v => scaleLaplacianFun_smul (I := I) (M := M) c v }
    1
    (fun v => by
      change ‖scaleLaplacianFun (I := I) (M := M) v‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact norm_scaleLaplacianFun_le (I := I) (M := M) v)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorScaleLaplacian_apply (τ : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    tensorScaleLaplacian (I := I) (M := M) τ v =
      scaleLaplacianFun (I := I) (M := M) v := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorScaleLaplacian_coeff (τ : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorScaleLaplacian (I := I) (M := M) τ v).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i := rfl

variable {τ : ℝ} {T : ℝ}

def timeScaleLaplacian (τ : ℝ) {T : ℝ} :
    timeL2 (tensorHs (I := I) (M := M) g r s (τ + 2)) T →L[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g r s τ) T :=
  (tensorScaleLaplacian (I := I) (M := M) τ).compLpL 2 (timeMeasure T)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeScaleLaplacian_coeFn
    (v : timeL2 (tensorHs (I := I) (M := M) g r s (τ + 2)) T) :
    timeScaleLaplacian (I := I) (M := M) τ v =ᵐ[timeMeasure T]
      fun t => tensorScaleLaplacian (I := I) (M := M) τ (v t) :=
  (tensorScaleLaplacian (I := I) (M := M) τ).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_timeScaleLaplacian
    (v : timeL2 (tensorHs (I := I) (M := M) g r s (τ + 2)) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (timeScaleLaplacian (I := I) (M := M) τ v) i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
        timeModeCoeff (I := I) (M := M) v i := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (timeScaleLaplacian (I := I) (M := M) τ v) i
  have hΔ := timeScaleLaplacian_coeFn (I := I) (M := M)
    (τ := τ) v
  have hsmul := Lp.coeFn_smul (-(TensorEigenIdx.lambda (I := I) (M := M) i))
    (timeModeCoeff (I := I) (M := M) v i)
  have hvcoe := timeModeCoeff_coeFn (I := I) (M := M) v i
  filter_upwards [hlhs, hΔ, hsmul, hvcoe] with t ht hΔt hsmt hvt
  rw [ht, hΔt, tensorScaleLaplacian_coeff, hsmt, Pi.smul_apply, hvt, smul_eq_mul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_solves_perMode {a : ℝ} (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularityDerivField (I := I) (M := M) a hT f) i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
          timeModeCoeff (I := I) (M := M)
            (maximalRegularitySolField (I := I) (M := M) a hT f) i +
        timeModeCoeff (I := I) (M := M) f i := by
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i]
  rw [derivModeCoeff, perModeConvDerivL2_apply, solModeCoeff, neg_smul,
    ← sub_eq_neg_add]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_solves {a : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT hT1 f) =
      timeScaleLaplacian (I := I) (M := M) a
          (maximalRegularitySolField (I := I) (M := M) a hT.le f) +
        f := by
  rw [maximalRegularityOp_timeDeriv (I := I) (M := M)
    (a := a) hT hT1 f]
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_timeScaleLaplacian (I := I) (M := M) (τ := a)
      (maximalRegularitySolField (I := I) (M := M) a hT.le f) i]
  exact maximalRegularityOp_solves_perMode (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
