import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma exists_fiberNormSq_le_factor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    ∃ B : ℝ, 0 ≤ B ∧
      riemannianFiberNormSq (I := I) (M := M) g r s x T ≤ ‖T‖ ^ 2 * B := by
  obtain ⟨Ab, hAb_nonneg, hbound⟩ :=
    riemannianFiberNormSq_le_pointwise_witness (I := I) (M := M) g r s x T
  refine ⟨_, ?_, hbound⟩
  refine mul_nonneg (pow_nonneg ?_ _) (pow_nonneg hAb_nonneg _)
  unfold metricInnerOpNorm
  exact norm_nonneg _

noncomputable def curvValueFrameScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) : ℝ :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose

omit [NeZero (Module.finrank ℝ E)] in
lemma curvValueFrameScalar_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    0 ≤ curvValueFrameScalar (I := I) (M := M) g r s x v w T :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose_spec.1

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_tensorCov_fiberNormSq_le_frameScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x v w T) ≤
      ‖riemannOp (tensorCov (I := I) g r s) x v w T‖ ^ 2 *
        curvValueFrameScalar (I := I) (M := M) g r s x v w T :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose_spec.2

noncomputable def curvContractionFiberNormBoundSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) : ℝ :=
  ‖riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)‖ ^ 2 *
    curvValueFrameScalar (I := I) (M := M) g r s x (X x) (Y x) (Z x)

omit [NeZero (Module.finrank ℝ E)] in
lemma curvContractionFiberNormBoundSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) :
    0 ≤ curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x := by
  unfold curvContractionFiberNormBoundSq
  exact mul_nonneg (sq_nonneg _)
    (curvValueFrameScalar_nonneg (I := I) (M := M) g r s x (X x) (Y x) (Z x))

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_tensorCov_fiberNormSq_le_boundSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)) ≤
      curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x :=
  riemannOp_tensorCov_fiberNormSq_le_frameScalar (I := I) (M := M) g r s x
    (X x) (Y x) (Z x)

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_bound_riemannOp_tensorCov_fiberNormSq
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (hbdd : BddAbove (Set.range
      (fun x : M => curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)) ≤ K := by
  classical
  set f : M → ℝ := fun x => curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x
    with hf_def
  set K : ℝ := sSup (Set.range f) with hK_def
  have h_le_K : ∀ x : M, f x ≤ K := fun x => le_csSup hbdd (Set.mem_range_self x)
  refine ⟨K, ?_, ?_⟩
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hrange : Set.range f = (∅ : Set ℝ) := by
        rw [Set.range_eq_empty_iff]; exact hM
      rw [hK_def, hrange, Real.sSup_empty]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (curvContractionFiberNormBoundSq_nonneg (I := I) (M := M) g r s X Y Z x₀)
        (h_le_K x₀)
  · intro x
    exact le_trans
      (riemannOp_tensorCov_fiberNormSq_le_boundSq (I := I) (M := M) g r s X Y Z x)
      (h_le_K x)

end Connection
end Integral
end DifferentialGeometry

end
