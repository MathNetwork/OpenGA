import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNormEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffWkpNorm

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
lemma finsetSum_eNNReal_ofReal_mul_le
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (C : ι → ℝ) (A : ℝ≥0∞)
    (hC : ∀ j ∈ s, 0 ≤ C j)
    (hbd : ∀ j ∈ s, f j ≤ ENNReal.ofReal (C j) * A) :
    ∑ j ∈ s, f j ≤ ENNReal.ofReal (∑ j ∈ s, C j) * A := by
  classical
  calc ∑ j ∈ s, f j
      ≤ ∑ j ∈ s, ENNReal.ofReal (C j) * A := Finset.sum_le_sum hbd
    _ = (∑ j ∈ s, ENNReal.ofReal (C j)) * A := by rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ j ∈ s, C j) * A := by
        rw [ENNReal.ofReal_sum_of_nonneg hC]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
