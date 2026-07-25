import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem inner_self_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    (inner ℝ T T : ℝ) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hclm : (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s x T T : ℝ) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) :=
    tensorRSRiemannianInnerCLM_apply (I := I) (M := M) g r s x T T
  rw [← hclm]
  rfl

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] in
theorem norm_eq_sqrt_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖T‖ =
      Real.sqrt
        (tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel T) (TensorRSSpace.toModel T)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [← inner_self_eq_tensorInnerPointwise (I := I) (M := M) g r s x T]
  rw [real_inner_self_eq_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] in
theorem norm_eq_of_tensorInnerPointwise_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T S : TensorRSSpace r s I x)
    (h : tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel S) (TensorRSSpace.toModel S)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖T‖ = ‖S‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x T,
    norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x S, h]

end Connection
end Integral
end DifferentialGeometry

end
