import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIntrinsicL2LePouSobolevNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem rawTensorConnLapIter_intrinsicL2_le_tensorPouSobolevNorm_sq_one
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ b, ENNReal.ofReal
            (riemannianFiberNormSq (I := I) (M := M) g r s b
              ((rawTensorConnLapIter (I := I) g r s 1 T).toSection b))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  obtain ⟨C, hC_ne_top, hbound⟩ :=
    rawTensorConnLap_intrinsicL2_le_tensorPouSobolevNorm_sq (I := I) (M := M) g r s
  refine ⟨C, hC_ne_top, ?_⟩
  intro T
  have h_iter_section : ∀ x : M,
      (rawTensorConnLapIter (I := I) g r s 1 T).toSection x =
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
    intro x
    rw [rawTensorConnLapIter_one]
    exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T x
  have h_integral_eq :
      ∫⁻ b, ENNReal.ofReal
          (riemannianFiberNormSq (I := I) (M := M) g r s b
            ((rawTensorConnLapIter (I := I) g r s 1 T).toSection b))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ b, ENNReal.ofReal
          (riemannianFiberNormSq (I := I) (M := M) g r s b
            (rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) b))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine lintegral_congr ?_
    intro b
    rw [h_iter_section b]
  rw [h_integral_eq]
  exact hbound T

end Connection
end Integral
end DifferentialGeometry

end
