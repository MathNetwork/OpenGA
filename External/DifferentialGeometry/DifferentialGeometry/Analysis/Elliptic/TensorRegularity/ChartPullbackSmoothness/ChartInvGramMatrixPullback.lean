import DifferentialGeometry.Analysis.Elliptic.MetricExtension

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGramMatrix_pullback_contDiffOn_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartInvGramMatrix (I := I) g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  invGramOnEuclid_contDiffOn (I := I) g α k l

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
