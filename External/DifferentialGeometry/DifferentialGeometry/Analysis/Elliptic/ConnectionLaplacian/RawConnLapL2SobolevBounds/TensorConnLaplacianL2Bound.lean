import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawTensorConnLapPerChartL2Bound
import DifferentialGeometry.Analysis.Integration.Measure.ManifoldL2NormChartTargetBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open MeasureTheory
open scoped Manifold Topology ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def chartSobolevRawNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
        (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b : M =>
            rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) b)
          y)
      ∂(volume : Measure EuclN)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartSobolevRawNorm_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    chartSobolevRawNorm (I := I) (M := M) g r s T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M =>
                rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) b)
              y)
          ∂(volume : Measure EuclN) := rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_L2NormSq_le_chartSobolevRawNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        Measurable
          (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) x‖ ^ 2) →
          ∫⁻ x,
              (‖rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartTargetL2BridgeConstant (I := I) (M := M) g) *
              chartSobolevRawNorm (I := I) (M := M) g r s T := by
  classical
  refine ⟨chartTargetL2BridgeConstant (I := I) (M := M) g,
    chartTargetL2BridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T hΔT_meas
  have hbound :=
    uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq
      (I := I) (M := M) g r s
      (S := fun b : M =>
        rawTensorConnLap (I := I) g r s
          (fun z : M => T.toSection z) b)
      hΔT_meas
  rw [chartSobolevRawNorm_def]
  exact hbound

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_L2NormSq_le_chartSobolevRawNorm_of_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₀ : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯)
        (_hT₀_cc : HasCompactSupport
          (fun x : M => TensorRSSpace.toModel (T₀ x))),
        Measurable
          (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T₀ z) x‖ ^ 2) →
          ∫⁻ x,
              (‖rawTensorConnLap (I := I) g r s
                  (fun z : M => T₀ z) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartTargetL2BridgeConstant (I := I) (M := M) g) *
              ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M =>
                        rawTensorConnLap (I := I) g r s
                          (fun z : M => T₀ z) b)
                      y)
                  ∂(volume : Measure EuclN) := by
  classical
  refine ⟨chartTargetL2BridgeConstant (I := I) (M := M) g,
    chartTargetL2BridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T₀ _hT₀_cc hΔT_meas
  exact
    uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq
      (I := I) (M := M) g r s
      (S := fun b : M =>
        rawTensorConnLap (I := I) g r s
          (fun z : M => T₀ z) b)
      hΔT_meas

end Connection
end Integral
end DifferentialGeometry

end
