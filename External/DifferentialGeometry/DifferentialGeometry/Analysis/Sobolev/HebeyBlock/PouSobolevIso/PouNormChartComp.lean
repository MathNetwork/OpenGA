import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist


namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
theorem pou_weighted_norm_equals_chart_component_norm_up_to_constant
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal :=
  fibrewise_gram_twist_estimate (I := I) (M := M) g r s

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
