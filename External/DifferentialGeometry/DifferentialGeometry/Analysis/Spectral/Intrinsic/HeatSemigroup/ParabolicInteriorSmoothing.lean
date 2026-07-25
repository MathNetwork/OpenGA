import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DuhamelSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000

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

def forcingMass (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorSobolevWeight (I := I) (M := M) i c *
    ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2

def solFieldMass (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorSobolevWeight (I := I) (M := M) i c *
    ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma forcingMass_nonneg (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (c : ℝ) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ forcingMass (I := I) (M := M) f c i :=
  mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) (sq_nonneg _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma solFieldMass_nonneg (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ solFieldMass (I := I) (M := M) hT f c i :=
  mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) (sq_nonneg _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solFieldMass_le_forcingMass (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    solFieldMass (I := I) (M := M) hT f (c + 2) i ≤
      (1 + T) ^ 2 * forcingMass (I := I) (M := M) f c i := by
  have hbound :
      tensorSobolevWeight (I := I) (M := M) i (c + 2) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
        (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i c *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
    have h := weighted_solModeCoeff_le (I := I) (M := M) (a := a) hT f i
    have hperMode := one_add_lambda_mul_norm_solModeCoeff_le (I := I) (M := M)
      (a := a) hT f i
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have hwc_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i c
    have hsol_nn : 0 ≤ ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
      norm_nonneg _
    have hweight_split :
        tensorSobolevWeight (I := I) (M := M) i (c + 2) =
          tensorSobolevWeight (I := I) (M := M) i c * (1 + lam) ^ 2 := by
      rw [tensorSobolevWeight, tensorSobolevWeight, hlam_def,
        Real.rpow_add hbase_pos,
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    have hsq : ((1 + lam) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2 ≤
        ((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
      have hlhs_nn : 0 ≤ (1 + lam) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
        mul_nonneg hbase_pos.le hsol_nn
      have hrhs_nn : 0 ≤ (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      nlinarith [hperMode, hlhs_nn, hrhs_nn]
    calc tensorSobolevWeight (I := I) (M := M) i (c + 2) *
            ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2
        = tensorSobolevWeight (I := I) (M := M) i c *
            (((1 + lam) *
              ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2) := by
          rw [hweight_split]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i c *
            (((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hwc_nn
      _ = (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i c *
            ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring
  simpa [solFieldMass, forcingMass] using hbound

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solFieldMass_summable_of_forcingMass_summable (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (hf : Summable (forcingMass (I := I) (M := M) f c)) :
    Summable (solFieldMass (I := I) (M := M) hT f (c + 2)) := by
  refine Summable.of_nonneg_of_le
    (fun i => solFieldMass_nonneg (I := I) (M := M) hT f (c + 2) i)
    (fun i => solFieldMass_le_forcingMass (I := I) (M := M) hT f c i)
    (hf.mul_left ((1 + T) ^ 2))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solFieldMass_summable_succ (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (c : ℝ)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hc : Summable (solFieldMass (I := I) (M := M) hT f (c + 1))) :
    Summable (solFieldMass (I := I) (M := M) hT f (c + 2)) :=
  solFieldMass_summable_of_forcingMass_summable (I := I) (M := M) hT f c
    (hcouple c hc)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solFieldMass_summable_bootstrap (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) :
    ∀ n : ℕ, Summable (solFieldMass (I := I) (M := M) hT f (b + n)) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ k ih =>
    have hstep := solFieldMass_summable_succ (I := I) (M := M) hT f (b + k - 1)
      hcouple
    have hrw1 : (b + (k : ℝ) - 1) + 1 = b + (k : ℝ) := by ring
    have hrw2 : (b + (k : ℝ) - 1) + 2 = b + ((k : ℕ) + 1 : ℕ) := by push_cast; ring
    rw [hrw1] at hstep
    rw [hrw2] at hstep
    exact hstep ih

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solFieldMass_summable_all (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) :
    ∀ σ : ℝ, Summable (solFieldMass (I := I) (M := M) hT f σ) := by
  intro σ
  obtain ⟨n, hn⟩ := exists_nat_ge (σ - b)
  have hσ_le : σ ≤ b + n := by linarith
  have hgain := solFieldMass_summable_bootstrap (I := I) (M := M) hT f
    hcouple hbase n
  refine Summable.of_nonneg_of_le
    (fun i => solFieldMass_nonneg (I := I) (M := M) hT f σ i)
    (fun i => ?_) hgain
  have hbase_ge : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    one_le_one_add_lambda (I := I) (M := M) i
  have hwle : tensorSobolevWeight (I := I) (M := M) i σ ≤
      tensorSobolevWeight (I := I) (M := M) i (b + n) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge hσ_le
  simpa only [solFieldMass] using
    mul_le_mul_of_nonneg_right hwle (sq_nonneg _)

def solFieldAtOrder (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (σ : ℝ)
    (_hσ : Summable (solFieldMass (I := I) (M := M) hT f σ)) :
    timeL2 (tensorHs (I := I) (M := M) g r s σ) T :=
  timeL2OfModes (I := I) (M := M) (σ := σ)
    (fun i => solModeCoeff (I := I) (M := M) (a := a) hT f i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solFieldAtOrder_timeModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (σ : ℝ)
    (hσ : Summable (solFieldMass (I := I) (M := M) hT f σ))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (solFieldAtOrder (I := I) (M := M) hT f σ hσ) i =
      solModeCoeff (I := I) (M := M) (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := σ)
    (fun i => solModeCoeff (I := I) (M := M) (a := a) hT f i) hσ i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem solField_into_all_tensorHs_interior (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) :
    ∀ σ : ℝ,
      ∃ v : timeL2 (tensorHs (I := I) (M := M) g r s σ) T,
        ∀ i, timeModeCoeff (I := I) (M := M) v i =
          solModeCoeff (I := I) (M := M) (a := a) hT f i :=
  fun σ =>
    let hσ := solFieldMass_summable_all (I := I) (M := M) hT f hcouple hbase σ
    ⟨solFieldAtOrder (I := I) (M := M) hT f σ hσ,
      solFieldAtOrder_timeModeCoeff (I := I) (M := M) hT f σ hσ⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
