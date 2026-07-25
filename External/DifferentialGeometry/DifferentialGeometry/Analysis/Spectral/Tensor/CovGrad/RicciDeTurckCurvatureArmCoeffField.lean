import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionTowerGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in

def ricBackgroundSlotCoeff (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM
          (slotInsertEndoFib (I := I) (M := M) 2 0 x (ricEndoRaisedFib (I := I) g₀ x))
      contMDiff_toFun :=
        slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
          (fun x : M => ricEndoRaisedFib (I := I) g₀ x)
          (ricEndoRaisedFib_contMDiff (I := I) g₀) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

def ricBackgroundArmCoeffField (g₀ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => ricBackgroundSlotCoeff (I := I) g₀
    | _ => 0

set_option backward.isDefEq.respectTransparency false in

omit [CompleteSpace E] in
theorem ricBackgroundArm_iteratedCovGrad_singleSum_le
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (ricBackgroundArmCoeffField (I := I) g₀)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (ricBackgroundArmCoeffField (I := I) g₀)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (ricBackgroundArmCoeffField (I := I) g₀) x₀ 2 W a

end Connection
end Integral
end DifferentialGeometry

end
