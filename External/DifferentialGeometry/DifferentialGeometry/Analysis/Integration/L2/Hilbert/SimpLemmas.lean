import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion


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

namespace SmoothCcTensor

section SimpLemmas

variable [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


@[simp] theorem toL2_zero :
    (toL2 (g := g) (r := r) (s := s)) 0 = 0 :=
  ContinuousLinearMap.map_zero _


@[simp] theorem toL2_add (S T : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (S + T) =
      (toL2 (g := g) (r := r) (s := s)) S +
        (toL2 (g := g) (r := r) (s := s)) T :=
  ContinuousLinearMap.map_add _ _ _


@[simp] theorem toL2_neg (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (-S) =
      -((toL2 (g := g) (r := r) (s := s)) S) :=
  ContinuousLinearMap.map_neg _ _


@[simp] theorem toL2_sub (S T : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (S - T) =
      (toL2 (g := g) (r := r) (s := s)) S -
        (toL2 (g := g) (r := r) (s := s)) T :=
  ContinuousLinearMap.map_sub _ _ _


@[simp] theorem toL2_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (c • S) =
      c • ((toL2 (g := g) (r := r) (s := s)) S) :=
  ContinuousLinearMap.map_smul _ _ _

end SimpLemmas

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
