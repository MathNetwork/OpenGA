import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

abbrev H1Compl (g : SmoothRiemannianMetric I M) : Type _ :=
  UniformSpace.Completion (SmoothScalar g)

noncomputable def smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] H1Compl g :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToH1Compl_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g f = (f : H1Compl g) :=
  rfl

example (g : SmoothRiemannianMetric I M) : Type _ := H1Compl g

example (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (H1Compl g) := inferInstance

example (g : SmoothRiemannianMetric I M) :
    InnerProductSpace ℝ (H1Compl g) := inferInstance

example (g : SmoothRiemannianMetric I M) :
    CompleteSpace (H1Compl g) := inferInstance

end Laplacian
end Analysis
end DifferentialGeometry

end
