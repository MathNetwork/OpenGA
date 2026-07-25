import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLe
import Mathlib.Topology.Order.Compact


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def riemannianFrameScalar
    (g : SmoothRiemannianMetric I M) (b : M) (S : TensorRSSpace 0 2 I b) : ℝ :=
  (riemannianFiberNormSq_le_pointwise_witness (I := I) (M := M) g 0 2 b S).choose

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma riemannianFrameScalar_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) (S : TensorRSSpace 0 2 I b) :
    0 ≤ riemannianFrameScalar (I := I) (M := M) g b S :=
  (riemannianFiberNormSq_le_pointwise_witness (I := I) (M := M) g 0 2 b S).choose_spec.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma riemannianFiberNormSq_le_frameScalar_sq
    (g : SmoothRiemannianMetric I M) (b : M) (S : TensorRSSpace 0 2 I b) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 b S ≤
      ‖S‖ ^ 2 * riemannianFrameScalar (I := I) (M := M) g b S ^ 2 := by
  have h := (riemannianFiberNormSq_le_pointwise_witness
    (I := I) (M := M) g 0 2 b S).choose_spec.2
  refine h.trans (le_of_eq ?_)
  unfold riemannianFrameScalar
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.zero_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_riemannOp_tensorCov_le_witness
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
      ‖riemannOp (tensorCov (I := I) g 0 2) x v w T‖ ^ 2 *
        riemannianFrameScalar (I := I) (M := M) g x
          (riemannOp (tensorCov (I := I) g 0 2) x v w T) ^ 2 :=
  riemannianFiberNormSq_le_frameScalar_sq (I := I) (M := M) g x
    (riemannOp (tensorCov (I := I) g 0 2) x v w T)

noncomputable def curvatureFiberNormBoundSq
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (x : M) : ℝ :=
  ‖riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)‖ ^ 2 *
    riemannianFrameScalar (I := I) (M := M) g x
      (riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)) ^ 2

omit [NeZero (Module.finrank ℝ E)] in
lemma curvatureFiberNormBoundSq_nonneg
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (x : M) :
    0 ≤ curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x := by
  unfold curvatureFiberNormBoundSq
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_riemannOp_tensorCov_le_curvatureFiberNormBoundSq
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)) ≤
      curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x :=
  riemannianFiberNormSq_riemannOp_tensorCov_le_witness (I := I) (M := M) g x
    (X x) (Y x) (T x)

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_bound_riemannianFiberNormSq_riemannOp_tensorCov
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (hbdd : BddAbove (Set.range
      (fun x : M => curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)) ≤ K := by
  classical
  set f : M → ℝ := fun x => curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x
    with hf_def
  set K : ℝ := sSup (Set.range f) with hK_def
  have h_le_K : ∀ x : M, f x ≤ K := by
    intro x
    exact le_csSup hbdd (Set.mem_range_self x)
  refine ⟨K, ?_, ?_⟩
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hrange : Set.range f = (∅ : Set ℝ) := by
        rw [Set.range_eq_empty_iff]; exact hM
      rw [hK_def, hrange, Real.sSup_empty]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (curvatureFiberNormBoundSq_nonneg (I := I) (M := M) g X Y T x₀)
        (h_le_K x₀)
  · intro x
    exact le_trans
      (riemannianFiberNormSq_riemannOp_tensorCov_le_curvatureFiberNormBoundSq
        (I := I) (M := M) g X Y T x)
      (h_le_K x)

end Connection
end Integral
end DifferentialGeometry

end
