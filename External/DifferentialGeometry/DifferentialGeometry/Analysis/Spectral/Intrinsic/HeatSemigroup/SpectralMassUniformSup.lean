import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ} {T : ℝ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem forcingMass_summable_of_couple (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) (σ : ℝ) :
    Summable (forcingMass (I := I) (M := M) f σ) :=
  hcouple σ
    (solFieldMass_summable_all (I := I) (M := M) hT f hcouple hbase (σ + 1))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem weighted_perModeConv_sq_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (σ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
      T * forcingMass (I := I) (M := M) f σ i := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  have habs := abs_perModeConv_timeL2_le lam hlam_nn
    (timeModeCoeff (I := I) (M := M) f i) ht
  have hconv_sq :
      (perModeConv lam
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
        T * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
    have hsq : (perModeConv lam
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
        (Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
      have habs_nn : 0 ≤ |perModeConv lam
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t| := abs_nonneg _
      have hrhs_nn : 0 ≤ Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      have hbase :
          (perModeConv lam
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 =
            |perModeConv lam
              (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t| ^ 2 := by
        rw [sq_abs]
      rw [hbase]
      exact pow_le_pow_left₀ habs_nn habs 2
    calc (perModeConv lam
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2
        ≤ (Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := hsq
      _ = T * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hT]
  calc tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv lam
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i σ *
          (T * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hconv_sq hwt_nn
    _ = T * (tensorSobolevWeight (I := I) (M := M) i σ *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring
    _ = T * forcingMass (I := I) (M := M) f σ i := by rw [forcingMass]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem spectralMass_sup_le_of_timeL2_allHs (hT : 0 < T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT.le f b)) :
    ∀ σ : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤ C := by
  intro σ
  have hforce : Summable (forcingMass (I := I) (M := M) f σ) :=
    forcingMass_summable_of_couple (I := I) (M := M) hT.le f hcouple hbase σ
  have hmaj : Summable (fun i => T * forcingMass (I := I) (M := M) f σ i) :=
    hforce.mul_left T
  refine ⟨T * ∑' i, forcingMass (I := I) (M := M) f σ i, fun t ht => ?_⟩
  have hle : ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
      T * forcingMass (I := I) (M := M) f σ i :=
    fun i => weighted_perModeConv_sq_le (I := I) (M := M) hT.le f σ i ht
  have hnn : ∀ i, 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 :=
    fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  have hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2) :=
    Summable.of_nonneg_of_le hnn hle hmaj
  refine ⟨hsum, ?_⟩
  calc ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2
      ≤ ∑' i, T * forcingMass (I := I) (M := M) f σ i :=
        hsum.tsum_le_tsum hle hmaj
    _ = T * ∑' i, forcingMass (I := I) (M := M) f σ i := by
        rw [tsum_mul_left]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
