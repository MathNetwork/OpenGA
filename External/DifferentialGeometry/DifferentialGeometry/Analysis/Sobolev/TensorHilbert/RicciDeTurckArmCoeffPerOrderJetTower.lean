import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (linearizedRicciArm0BaseCoeff linearizedRicciArm1BaseCoeff ricciArmPrincipalCoeff
    traceHessianCoeff)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def coeffPerOrderJetBound (R δ₀ : ℝ) (curvWeight : ℕ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (curvWeight + 2) * (1 + R) ^ (2 * i + 6) *
    (1 / (1 - δ₀)) ^ (4 * i + 12)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem coeffPerOrderJetBound_nonneg (R δ₀ : ℝ) (hR : 0 ≤ R) (hδ₀ : δ₀ < 1)
    (curvWeight i : ℕ) : 0 ≤ coeffPerOrderJetBound (E := E) R δ₀ curvWeight i := by
  have hpos : 0 < 1 - δ₀ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  simp only [coeffPerOrderJetBound]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact pow_nonneg (Nat.cast_nonneg _) _
  · exact pow_nonneg (by linarith) _
  · exact pow_nonneg hinv_nn _

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem l2_of_pointwise_rfns_iteratedCovGrad_perOrder
    (g₀ : SmoothRiemannianMetric I M) (r i : ℕ)
    (C : SmoothCcTensor g₀ r 2) (Ki : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
          ((iteratedCovGrad (I := I) g₀ r 2 i C).toSection x) ≤ Ki) :
    ‖iteratedCovGrad (I := I) g₀ r 2 i C‖ ^ 2 ≤
      Ki * (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal :=
  norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) (M := M) g₀ r (2 + i)
    (iteratedCovGrad (I := I) g₀ r 2 i C) Ki hpt

end DifferentialGeometry.Integral.Connection

end
