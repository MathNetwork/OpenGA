import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Operator.L2PMap

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


def dirichletForm (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s → SmoothCcTensor g r s → ℝ :=
  fun T S => - (@inner ℝ _ _
      ((connLaplacianL2 (I := I) g r s)
        ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T,
          toL2_mem_connLaplacianL2_domain (I := I) g r s T⟩)
      (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S))


omit [CompactSpace M] in
theorem dirichletForm_eq_neg_inner_laplacian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    dirichletForm (I := I) g r s T S =
      - (@inner ℝ _ _
          ((connLaplacianL2 (I := I) g r s)
            ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩)
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S)) := by
  unfold dirichletForm
  rfl

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
