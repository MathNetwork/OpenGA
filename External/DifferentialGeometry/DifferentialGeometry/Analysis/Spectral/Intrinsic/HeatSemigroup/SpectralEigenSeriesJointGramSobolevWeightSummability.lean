import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.EigensectionSobolevDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame
import DifferentialGeometry.Analysis.Calculus.AnisotropicJointContDiff

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma weight_two_rpow_eq_sq (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (pp : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (2 * pp)
      = ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pp) ^ 2 := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  unfold tensorSobolevWeight
  rw [show (2 : ℝ) * pp = pp * 2 by ring, Real.rpow_mul hbase_pos.le, Real.rpow_two]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma abs_le_sqrt_of_weight_sq_le (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (pp : ℝ) {v C : ℝ}
    (h : tensorSobolevWeight (I := I) (M := M) i (2 * pp) * v ^ 2 ≤ C) :
    |v| ≤ Real.sqrt C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-pp) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hw := weight_two_rpow_eq_sq (I := I) (M := M) g i pp
  rw [hw] at h
  set W : ℝ := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pp with hW_def
  have hW_pos : 0 < W := Real.rpow_pos_of_pos hbase_pos _
  have hC_nn : 0 ≤ C := le_trans (by positivity) h
  have habs : |v| ≤ Real.sqrt C / W := by
    rw [le_div_iff₀ hW_pos]
    have h2 : (|v| * W) ^ 2 ≤ (Real.sqrt C) ^ 2 := by
      rw [Real.sq_sqrt hC_nn, mul_pow, sq_abs]
      nlinarith [h, hW_pos.le]
    have hlhs_nn : 0 ≤ |v| * W := by positivity
    nlinarith [Real.sqrt_nonneg C, h2, hlhs_nn,
      sq_nonneg (|v| * W - Real.sqrt C)]
  rw [Real.rpow_neg hbase_pos.le]
  rw [div_eq_mul_inv] at habs
  rwa [← hW_def]

omit [BoundarylessManifold I M] in
lemma summable_sqrt_mul_weight_neg (g : SmoothRiemannianMetric I M)
    (Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (hCm : Summable Cm)
    (hCm_nn : ∀ i, 0 ≤ Cm i) {sW : ℝ} (hsW : ((weylSobolevExp (E := E) : ℕ) : ℝ) < sW) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)) := by
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(2 * sW))) := by
    refine tensorEigen_summable_negpow (I := I) (M := M) g (2 * sW) ?_
    have h0 : (0 : ℝ) ≤ ((weylSobolevExp (E := E) : ℕ) : ℝ) := by positivity
    nlinarith [h0]
  have hw_sq : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorSobolevWeight (I := I) (M := M) i (-sW) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-(2 * sW)) := by
    intro i
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-sW)) 2,
      ← Real.rpow_mul (hbase_pos i).le]
    congr 1; push_cast; ring
  have hbound : ∀ i, Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)
      ≤ (Cm i + tensorSobolevWeight (I := I) (M := M) i (-(2 * sW))) / 2 := by
    intro i
    have h1 : Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)
        ≤ (Real.sqrt (Cm i) ^ 2 + tensorSobolevWeight (I := I) (M := M) i (-sW) ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt (Cm i) - tensorSobolevWeight (I := I) (M := M) i (-sW)),
        Real.sq_sqrt (hCm_nn i)]
    rw [Real.sq_sqrt (hCm_nn i), hw_sq i] at h1
    exact h1
  have hnn : ∀ i, 0 ≤ Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW) :=
    fun i => mul_nonneg (Real.sqrt_nonneg _)
      (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  exact Summable.of_nonneg_of_le hnn hbound ((hCm.add hweyl).div_const 2)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
