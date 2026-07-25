import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem bare_laplacian_spectral_match
    (g_bg : SmoothRiemannianMetric I M)
    (Tsm : Integral.L2.SmoothCcTensor g_bg 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
        (Integral.L2.SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g_bg 0 2 Tsm)) i =
      (- Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
          (Integral.L2.SmoothCcTensor.toL2 Tsm) i := by
  have hraw : rawTensorConnLapSmooth (I := I) g_bg 0 2 Tsm
      = Tsm - oneMinusConnLapSmooth (I := I) g_bg 0 2 Tsm := by
    rw [oneMinusConnLapSmooth, sub_sub_cancel]
  have hsub :
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
          (Integral.L2.SmoothCcTensor.toL2 Tsm -
            Integral.L2.SmoothCcTensor.toL2
              (oneMinusConnLapSmooth (I := I) g_bg 0 2 Tsm)) i =
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 Tsm) i -
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2
              (oneMinusConnLapSmooth (I := I) g_bg 0 2 Tsm)) i := by
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  rw [hraw, Integral.L2.SmoothCcTensor.toL2_sub, hsub,
    tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
      (I := I) (M := M) g_bg (hCompact (I := I) (M := M) g_bg) Tsm i]
  ring

end DifferentialGeometry.PDE.RicciFlow
