import DifferentialGeometry.Analysis.Spectral.Scalar.EigenBasis

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

abbrev EigenIdx (g : SmoothRiemannianMetric I M) : Type _ :=
  Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
    Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))

noncomputable abbrev EigenIdx.lambda
    {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  laplacianEigenvalueOf i.fst.val

omit [NeZero (Module.finrank ℝ E)] in
theorem EigenIdx.lambda_nonneg
    {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
  laplacianEigenvalueOf_nonneg (I := I) (M := M) i.fst

end Spectral
end Laplacian
end Analysis
end DifferentialGeometry

end
