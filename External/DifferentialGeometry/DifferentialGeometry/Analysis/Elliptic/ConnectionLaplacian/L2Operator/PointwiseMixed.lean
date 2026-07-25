import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs


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


def connLaplacianMixed (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) : TensorRSSpace r s I x :=
  rawTensorConnLap (I := I) g r s (fun b : M => T b) x


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma connLaplacianMixed_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) (x : M) :
    connLaplacianMixed (I := I) g r s T x =
      rawTensorConnLap (I := I) g r s (fun b : M => T b) x := rfl


def connLaplacianMixedSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    M → (Π x : M, TensorRSSpace r s I x) :=
  fun _ x => connLaplacianMixed (I := I) g r s T x


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connLaplacianMixed_scalar_eq_function
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 0 ℝ E,
      (fun x : M => TensorRSSpace 0 0 I x)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∃ c : ℝ,
      connLaplacian_function (I := I) g hf x = c ∧
      connLaplacianMixed (I := I) g 0 0 T x =
        rawTensorConnLap (I := I) g 0 0 (fun b : M => T b) x := by
  refine ⟨connLaplacian_function (I := I) g hf x, rfl, ?_⟩
  exact connLaplacianMixed_def (I := I) g 0 0 T x

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
