import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.MemW1pResidualFull
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.Cauchy
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.Identification

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace FChartResidualMemW1p

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.MemW1pFChartResidualFull
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqIdentification

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem fChartResidual_memW1p_truly_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  fChartResidual_memW1p_unconditional (I := I) (M := M) g α hu_h
    (smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy
      (I := I) (M := M) g α hu_h)
    (smoothApproxSeq_smoothFChartResidual_limit_eq_fChartResidual
      (I := I) (M := M) g α hu_h)

end FChartResidualMemW1p
end Laplacian
end Analysis
end DifferentialGeometry

end
