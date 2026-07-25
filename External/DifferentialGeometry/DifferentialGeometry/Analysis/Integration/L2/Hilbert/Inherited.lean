import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section InheritedInstances

variable [T2Space M] [SigmaCompactSpace M]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    NormedAddCommGroup (TensorL2 r s g) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    NormedSpace ℝ (TensorL2 r s g) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (TensorL2 r s g) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CompleteSpace (TensorL2 r s g) := inferInstance

end InheritedInstances

end L2
end Integral
end DifferentialGeometry

end
