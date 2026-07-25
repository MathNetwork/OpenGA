import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Analysis.Spectral.Intrinsic.ConnectionLaplacianMaximalRegularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.PointwiseDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckInitialDataExistence

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]

theorem deTurckRicci_shortTime_existence_of_closed
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := by
  obtain ⟨T, g_DT, hbundle⟩ :=
    deturck_ricci_flow_parabolic_short_time_existence (I := I) g₀ g_bg
  exact ⟨T, g_DT, hbundle.1⟩

end DifferentialGeometry.PDE.RicciFlow
