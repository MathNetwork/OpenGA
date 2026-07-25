import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma eLpNorm_add_add_sub_le
    {β : Type*} [MeasurableSpace β] {ν : Measure β} {a b c : β → ℝ}
    (ha : AEStronglyMeasurable a ν) (hb : AEStronglyMeasurable b ν)
    (hc : AEStronglyMeasurable c ν) :
    eLpNorm (fun y => a y + b y - c y) 2 ν ≤
      eLpNorm a 2 ν + eLpNorm b 2 ν + eLpNorm c 2 ν := by
  have h_ab : eLpNorm (fun y => a y + b y) 2 ν ≤
      eLpNorm a 2 ν + eLpNorm b 2 ν :=
    eLpNorm_add_le ha hb (by norm_num)
  have h_full : eLpNorm (fun y => (a y + b y) - c y) 2 ν ≤
      eLpNorm (fun y => a y + b y) 2 ν + eLpNorm c 2 ν :=
    eLpNorm_sub_le (ha.add hb) hc (by norm_num)
  exact h_full.trans (by gcongr)

lemma abs_prod_kronecker_le_one'
    {ι : Type*} (t : Finset ι) (f : ι → Prop) [DecidablePred f] :
    |∏ i ∈ t, (if f i then (1 : ℝ) else 0)| ≤ 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, abs_mul]
      by_cases hf : f i
      · rw [if_pos hf, abs_one, one_mul]; exact ih
      · rw [if_neg hf, abs_zero, zero_mul]; exact zero_le_one

private lemma abs_kronecker_le_one' {P : Prop} [Decidable P] :
    |if P then (1 : ℝ) else 0| ≤ 1 := by
  by_cases h : P
  · rw [if_pos h, abs_one]
  · rw [if_neg h, abs_zero]; exact zero_le_one

lemma abs_sum_coeff_kronecker_le'
    {ι : Type*} (t : Finset ι) (f : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ) (hf : ∀ i ∈ t, |f i| ≤ Cχ) :
    |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)| ≤ t.card * Cχ := by
  classical
  have hbound : ∀ i ∈ t,
      |f i * (if P i then (1 : ℝ) else 0)| ≤ Cχ := by
    intro i hi
    rw [abs_mul]
    calc |f i| * |if P i then (1 : ℝ) else 0|
        ≤ Cχ * 1 :=
          mul_le_mul (hf i hi) abs_kronecker_le_one' (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  calc |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)|
      ≤ ∑ i ∈ t, |f i * (if P i then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ t, Cχ := Finset.sum_le_sum hbound
    _ = t.card * Cχ := by rw [Finset.sum_const, nsmul_eq_mul]

lemma sq_eLpNorm_two_eq_lintegral_enorm_sq'
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

lemma le_sqrt_of_sq_le' {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma sqrt_ofReal_eq_ofReal_sqrt' {a : ℝ} (ha : 0 ≤ a) :
    (ENNReal.ofReal a) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt a) := by
  rw [show a = Real.sqrt a * Real.sqrt a from (Real.mul_self_sqrt ha).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt a)) * (ENNReal.ofReal (Real.sqrt a)) =
      (ENNReal.ofReal (Real.sqrt a)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
