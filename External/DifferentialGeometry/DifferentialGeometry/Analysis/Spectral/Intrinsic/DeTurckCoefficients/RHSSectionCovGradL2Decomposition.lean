import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def deTurckRHSReanchor (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    SmoothCcTensor g_bg 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).hasCompactSupport

omit [BoundarylessManifold I M] in

@[simp] theorem deTurckRHSReanchor_toSection (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ).toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection := rfl

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
