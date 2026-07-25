import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.L2BanachIso
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.ChartFrameNorm
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.NablaTensorFormula
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.IteratedNabla
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.PouNormChartComp
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.AssemblePouIso

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_sobolev_intrinsic_nabla_equivalence_tensors_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
  assemble_pou_h1_iso_intrinsic_h1 (I := I) (M := M) g r s

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
